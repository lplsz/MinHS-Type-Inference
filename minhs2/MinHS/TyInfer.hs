module MinHS.TyInfer where

import qualified MinHS.Env as E
import MinHS.Syntax
import MinHS.Subst
import MinHS.TCMonad

import Data.Monoid (Monoid (..), (<>))
import Data.Foldable (foldMap)
import Data.List (nub, union, (\\))

primOpType :: Op -> QType
primOpType Gt   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Ge   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Lt   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Le   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Eq   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Ne   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Neg  = Ty $ Base Int `Arrow` Base Int
primOpType Fst  = Forall "a" $ Forall "b" $ Ty $ (TypeVar "a" `Prod` TypeVar "b") `Arrow` TypeVar "a"
primOpType Snd  = Forall "a" $ Forall "b" $ Ty $ (TypeVar "a" `Prod` TypeVar "b") `Arrow` TypeVar "b"
primOpType _    = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Int)

-- Convert ConstType to QType
constType :: Id -> Maybe QType
constType "True"  = Just $ Ty $ Base Bool
constType "False" = Just $ Ty $ Base Bool
constType "()"    = Just $ Ty $ Base Unit
constType "Pair"  = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "a" `Arrow` (TypeVar "b" `Arrow` (TypeVar "a" `Prod` TypeVar "b"))
constType "Inl"   = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "a" `Arrow` (TypeVar "a" `Sum` TypeVar "b")
constType "Inr"   = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "b" `Arrow` (TypeVar "a" `Sum` TypeVar "b")
constType _       = Nothing

type Gamma = E.Env QType

initialGamma :: Gamma
initialGamma = E.empty

-- Given a type, return all the type variables in it
tv :: Type -> [Id]
tv = tv'
 where
   tv' (TypeVar x) = [x]
   tv' (Prod  a b) = tv a `union` tv b
   tv' (Sum   a b) = tv a `union` tv b
   tv' (Arrow a b) = tv a `union` tv b
   tv' (Base c   ) = []

-- Given Qtype, return all type variables in q
tvQ :: QType -> [Id]
tvQ (Forall x t) = filter (/= x) $ tvQ t
tvQ (Ty t) = tv t

-- Return all type variables in the env
tvGamma :: Gamma -> [Id]
tvGamma = nub . foldMap tvQ

infer :: Program -> Either TypeError Program
infer program = do (p',tau, s) <- runTC $ inferProgram initialGamma program
                   return p'

unquantify :: QType -> TC Type
{-
Normally this implementation would be possible:

unquantify (Ty t) = return t
unquantify (Forall x t) = do x' <- fresh
                             unquantify (substQType (x =:x') t)

However as our "fresh" names are not checked for collisions with names bound in the type
we avoid capture entirely by first replacing each bound
variable with a guaranteed non-colliding variable with a numeric name,
and then substituting those numeric names for our normal fresh variables
-}

unquantify = unquantify' 0 emptySubst
unquantify' :: Int -> Subst -> QType -> TC Type
unquantify' i s (Ty t) = return $ substitute s t
unquantify' i s (Forall x t) = do x' <- fresh
                                  unquantify' (i + 1)
                                              ((show i =: x') <> s)
                                              (substQType (x =:TypeVar (show i)) t)

unify :: Type -> Type -> TC Subst
-- Both are type variables
unify (TypeVar v1) (TypeVar v1) = return emptySubst
unify (TypeVar v1) (TypeVar v2) = return (v1 =: TypeVar v2)

-- Both are primitive types
unify (Base t1) (Base t1) = return emptySubst
unify (Base t1) (Base t2) = typeError & TypeMismatch t1 t2

-- Both are product types
unify (Prod t11 t22) (Prod t21 t22) = unifyProSumFun t11 t22 t21 t22

-- Both are sum types
unify (Sum t11 t22) (Sum t21 t22) = unifyProSumFun t11 t22 t21 t22

-- Both are function types
unify (Arrow t11 t22) (Arrow t21 t22) = unifyProSumFun t11 t22 t21 t22

-- One type variable v and arbitrary term t
unify (TypeVar v) t = 
    if v `elem` tv t 
        then typeError $ OccursCheckFailed v t
        else return (v =: t)

unify _ _ = error "No unifier"

unifyProSumFun :: Type -> Type -> Type -> Type -> TC Subst
unifyProSumFun t11 t22 t21 t22 = do
    s   <- unify t11 t21
    s'  <- unify (substitute s t12) (substitute s t22)
    return (s <> s')

generalise :: Gamma -> Type -> QType
-- generalise env (Ty t) = tv t \\ tvGamma env
generalise g t = error "implement me"

inferProgram :: Gamma -> Program -> TC (Program, Type, Subst)
inferProgram env bs = error "implement me! don't forget to run the result substitution on the"
                            "entire expression using allTypes from Syntax.hs"

inferExp :: Gamma -> Exp -> TC (Exp, Type, Subst)
inferExp env a@(Num i) = return (a, Base Int, emptySubst)

inferExp env a@(Con id) = case constType id of 
    Just v      -> do v' <- unquantify v; return (a, v', emptySubst) 
    Nothing     -> typeError $ NoSuchConstructor id

inferExp env a@(Prim op) = do 
    t       <- primOpType op
    t'      <- unquantify t
    return (a, t', emptySubst)

inferExp env (Var id) = case lookup env id of
    Just v      -> inferExp env v
    Nothing     -> typeError $ NoSuchVariable id

inferExp env (If e e1 e2) = do
    (e', tau, t)        <- inferExp env e
    u                   <- unify tau (Base Bool) 
    (e1', tau1, t1)     <- inferExp env' @(substGamma (u <> t) env) e1
    (e2', tau2, t2)     <- inferExp (substGamma t1 env') e2
    u'                  <- unify (substitute t2 tau1) tau2
    return (If e' e1' e2', substitute u' tau2, (u' <> t2 <> t1 <> u <> t))

inferExp env (Apply e1 e2) = do
    (e1', tau1, t)      <- inferExp env e1
    (e2', tau2, t')     <- inferExp (substGamma t env) e2
    u                   <- unify (substitute t' tau1) (Arrow tau2 a@(fresh))
    let e1'' = allTypes 
    return (Apply e1' e2', substitute u a, u <> t' <> t)

inferExp env (Let (Bind id _ [] e1) e2) = do
    (e1', tau, t)       <- inferExp env e1
    (e2', tau', t')     <- inferExp (substGamma t env') e2 
    return (Let [Bind id (Just (generalise env' tau)) [] e1'] e2', tau', t <> t')
        where env' = E.add env (id, (generalise (substGamma t, env) tau))

-- inferExp env (Let ((Bind id _ [] ):xs)) = let 



inferExp g _ = error "Implement me!"
-- -- Note: this is the only case you need to handle for case expressions
-- inferExp g (Case e [Alt "Inl" [x] e1, Alt "Inr" [y] e2])
-- inferExp g (Case e _) = typeError MalformedAlternatives

