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
   tv' (Base _   ) = []

-- Given Qtype, return all type variables in q
tvQ :: QType -> [Id]
tvQ (Forall x t) = filter (/= x) $ tvQ t
tvQ (Ty t) = tv t

-- Return all type variables in the env
tvGamma :: Gamma -> [Id]
tvGamma = nub . foldMap tvQ

infer :: Program -> Either TypeError Program
infer program = do (p', _, _) <- runTC $ inferProgram initialGamma program
                   return p'

-- Add fresh variable for forall
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
unify (TypeVar v1) (TypeVar v2) = 
    if v1 == v2 
        then return emptySubst
        else return (v1 =: TypeVar v2)

-- Both are primitive types
unify (Base t1) (Base t2) = 
    if t1 == t2 
        then return emptySubst
        else typeError $ TypeMismatch (Base t1) (Base t2)

-- Both are product types
unify (Prod t11 t12) (Prod t21 t22) = unifyProSumFun t11 t12 t21 t22

-- Both are sum types
unify (Sum t11 t12) (Sum t21 t22) = unifyProSumFun t11 t12 t21 t22

-- Both are function types
unify (Arrow t11 t12) (Arrow t21 t22) = unifyProSumFun t11 t12 t21 t22

-- One type variable v and arbitrary term t
unify (TypeVar v) t = 
    if v `elem` tv t 
        then typeError $ OccursCheckFailed v t
        else return (v =: t)

unify t (TypeVar v) = 
    if v `elem` tv t 
        then typeError $ OccursCheckFailed v t
        else return (v =: t)

unify t1 t2 = error $ "No unifier for " ++ show t1 ++ " " ++ show t2 

-- Helper function that unifers product, sum and function type
unifyProSumFun :: Type -> Type -> Type -> Type -> TC Subst
unifyProSumFun t11 t12 t21 t22 = do
    s   <- unify t11 t21
    s'  <- unify (substitute s t12) (substitute s t22)
    return (s <> s')

-- For all varaible in the list difference, generalise them with forall
generalise :: Gamma -> Type -> QType
generalise env t = foldr Forall (Ty t) (tv t \\ tvGamma env)
generalise _ _ = error "implement me"

inferProgram :: Gamma -> Program -> TC (Program, Type, Subst)
inferProgram env [Bind id _ _ e1] = do
    (e1', t, s)      <- inferExp env e1
    -- Generalise the type and update type annotation
    let new_p = [Bind id (Just $ generalise env t) [] (allTypes (substQType s) e1')]
    return (new_p, t, s)

inferProgram _ _ = error "implement me! don't forget to run the result substitution on the"
                            "entire expression using allTypes from Syntax.hs"

inferExp :: Gamma -> Exp -> TC (Exp, Type, Subst)
-- Constant
inferExp _ a@(Num _) = return (a, Base Int, emptySubst)

inferExp _ a@(Con id) = case constType id of 
    Just v      -> do v' <- unquantify v; return (a, v', emptySubst) 
    Nothing     -> typeError $ NoSuchConstructor id

inferExp _ a@(Prim op) = do 
    t         <- unquantify $ primOpType op
    return (a, t, emptySubst)

-- Variable
inferExp env (Var id) = case E.lookup env id of
    Just v      -> do v' <- unquantify v; return (Var id, v', emptySubst)
    Nothing     -> typeError $ NoSuchVariable id

-- If
inferExp env (If e e1 e2) = do
    (e', tau, t)        <- inferExp env e
    u                   <- unify tau (Base Bool) 
    (e1', tau1, t1)     <- inferExp (substGamma (u <> t) env) e1
    (e2', tau2, t2)     <- inferExp (substGamma (t1 <> u <> t) env) e2
    u'                  <- unify (substitute t2 tau1) tau2
    return (If e' e1' e2', substitute u' tau2, u' <> t2 <> t1 <> u <> t)

-- Function Application
inferExp env (App e1 e2) = do
    (e1', tau1, t)      <- inferExp env e1
    (e2', tau2, t')     <- inferExp (substGamma t env) e2
    alpha               <- fresh
    u                   <- unify (substitute t' tau1) (Arrow tau2 alpha)
    return (App e1' e2', substitute u alpha, u <> t' <> t)

-- Let
-- Single Bind
inferExp env (Let [Bind id _ [] e1] e2) = do
    (e1', tau, t)       <- inferExp env e1
    let env' = E.add (substGamma t env) (id, generalise (substGamma t env) tau) 
    (e2', tau', t')     <- inferExp (substGamma t env') e2 
    return (Let [Bind id (Just (generalise env' tau)) [] e1'] e2', tau', t' <> t)

-- Multiple Binds
inferExp env (Let xs e2) = do
    (env', xs', t)      <- inferMultiLet env xs [] emptySubst
    (e2', tau', t')     <- inferExp env' e2
    return (Let xs' e2', tau', t' <> t)    

-- Recfun
inferExp env (Recfun (Bind id _ [x] e)) = do
    alpha1          <- fresh
    alpha2          <- fresh
    (e', tau, t)    <- inferExp (E.addAll env [(x, Ty alpha1), (id, Ty alpha2)]) e
    u               <- unify (substitute t alpha2) (Arrow (substitute t alpha1) tau)
    let ty = substitute u (Arrow (substitute t alpha1) tau)
    return (Recfun (Bind id (Just $ Ty ty) [x] e'), ty, u <> t)

-- N-ary Recfun
inferExp env (Recfun (Bind id _ xs e)) = do
    env'            <- bindArgs env xs
    alpha2          <- fresh
    (e', tau, t)    <- inferExp (E.add env' (id, Ty alpha2)) e
    u               <- unify (substitute t alpha2) (nAryType (substGamma t env') xs tau)
    let ty = substitute u (nAryType (substGamma t env') xs tau)
    return (Recfun (Bind id (Just $ Ty ty) xs e'), ty, u <> t)

-- Case
inferExp env (Case e [Alt "Inl" [x] e1, Alt "Inr" [y] e2]) = do
    (e', tau, t)        <- inferExp env e
    a_l                 <- fresh
    a_r                 <- fresh

    let env' = substGamma t (E.add env (x, Ty a_l))
    (e1', tau_l, t1)    <- inferExp env' e1

    let env'' = substGamma (t1 <> t) (E.add env (y, Ty a_r))
    (e2', tau_r, t2)    <- inferExp env'' e2

    let tl1 = substitute (t2 <> t1 <> t) (Sum a_l a_r)
        tl2 = substitute (t2 <> t1) tau
    u                   <- unify tl1 tl2

    let tr1 = substitute (u <> t2) tau_l
        tr2 = substitute u tau_r
    u'                  <- unify tr1 tr2

    let new_e = Case e' [Alt "Inl" [x] e1', Alt "Inr" [y] e2']
    return (new_e, substitute (u' <> u) tau_r, u' <> u <> t2 <> t1 <> t)

inferExp _ (Case _ _) = typeError MalformedAlternatives

inferExp _ _ = error "Implement me!"

-- -- Note: this is the only case you need to handle for case expressions
-- inferExp g (Case e [Alt "Inl" [x] e1, Alt "Inr" [y] e2])
-- inferExp g (Case e _) = typeError MalformedAlternatives


-- Recursive helper function that deal with multiple let bindings
-- Input: Env -> List of bindings -> List of type inferred bindings -> Substitution from the previous frame
-- Output: Env with the bindings added -> List of type inferred bindings -> Substitution
inferMultiLet :: Gamma -> [Bind] -> [Bind] -> Subst -> TC (Gamma, [Bind], Subst)
inferMultiLet env [] ys sub = return (env, ys, sub)

inferMultiLet env ((Bind id _ [] e1):xs) ys sub = do
    (e1', tau, t)       <- inferExp env e1
    let env' = E.add (substGamma t env) (id, generalise (substGamma t env) tau)
        newBind = Bind id (Just (generalise env' tau)) [] e1'
    inferMultiLet env' xs (ys ++ [newBind]) (t <> sub)


-- Help function that binds arguments of function with fresh unification variables
bindArgs :: Gamma -> [Id] -> TC (Gamma)
bindArgs env [] = return env
bindArgs env (x:xs) = do
    alpha   <- fresh
    bindArgs (E.add env (x, Ty alpha)) xs

-- Helper function that contruct the type signature of a n-ary functions
nAryType :: Gamma -> [Id] -> Type -> Type
nAryType _ [] tau = tau
nAryType env' (x:xs) tau = case env' `E.lookup` x of 
    Just (Ty t)     -> Arrow t (nAryType env' xs tau)
    Nothing         -> error "Variable type not found"
    