module MinHS.TCMonad ( TypeError (..)
                     , TC
                     , freshNames
                     , runTC
                     , typeError
                     , fresh
                     ) where

import MinHS.Syntax
import Control.Applicative
import Control.Monad

data TypeError = TypeMismatch Type Type
               | OccursCheckFailed Id Type  -- have
               | NoSuchVariable Id      -- have
               | NoSuchConstructor Id   -- have
               | MalformedAlternatives  -- have
               | ForallInRecfun
               deriving (Show)

-- Return: an ordinary function which lifts pure values into a TC action that returns that value


-- return a value of type a, or throw an exception.
newtype TC a = TC ([Id] -> Either TypeError ([Id], a))

instance Monad TC where
  return x = TC (\s -> Right (s,x))
  (TC a) >>= f  = TC (\s -> case a s of Left x -> Left x
                                        Right (s',v) -> let TC b = f v
                                                         in b s')

instance Applicative TC where
  pure = return
  (<*>) = ap

instance Functor TC where
  fmap = ap . pure

freshNames :: [Id]
freshNames = map pure ['a'..'z'] ++ map ((++) "a" . show) [1..]

runTC :: TC a -> Either TypeError a
runTC (TC f) = fmap snd (f freshNames)

-- Convert an Error into TC
typeError :: TypeError -> TC a
typeError = TC . const . Left

fresh :: TC Type
fresh = TC $ \(x:xs) -> Right (xs,TypeVar x)
