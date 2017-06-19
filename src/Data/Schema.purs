module Main where

import Control.Applicative.Free (FreeAp)
import Data.Exists (Exists)
import Data.Lazy (Lazy, force)
import Data.Leibniz (type (~))
import Data.Map (Map)
import Data.Maybe (Maybe)

data HCofree (g :: (Type -> Type) -> Type -> Type) (a :: Type) (i :: Type)= HCofree a (Lazy (g (HCofree g a) i))

head :: forall g a i. HCofree g a i -> a 
head (HCofree h _) = h

tail :: forall g a i. HCofree g a i -> g (HCofree g a) i
tail (HCofree _ t) = force t

newtype Schema (p :: Type -> Type) (a :: Type) (i :: Type) = Schema { runSchema :: HCofree (SchemaAlg p) a i }

data SchemaAlg (p :: Type -> Type) (g :: Type -> Type) (a :: Type) 
  = Prim (p a)
  | Rec  (FreeAp (PropSchema g a) a)
  | Sum  (Array  (Exists (Constr g a)))
  | Vect (Exists (VectElem g a))
  | Dict (Exists (DictElem g a))

data PropSchema (g :: Type -> Type) (o :: Type) (a :: Type)
  = Required (Req g o a)
  | Optional (Exists (Opt g o a))

data Req (g :: Type -> Type) (o :: Type) (a :: Type) 
  = Req { id :: String, valueSchema :: g a, accessor :: o -> a, dflt :: Maybe a } 

data Opt (g :: Type -> Type) (o :: Type) (a :: Type) (b :: Type) 
  = Opt { id :: String, valueSchema :: g b, accessor :: o -> Maybe b } (a ~ Maybe b) 

data Constr (g :: Type -> Type) (a :: Type) (b :: Type) 
  = Constr { id :: String, baseSchema :: g b, g :: b -> a, g :: a -> Maybe b }

data VectElem (g :: Type -> Type) (a :: Type) (b :: Type) = VectElem (g b) (a ~ Array b)
data DictElem (g :: Type -> Type) (a :: Type) (b :: Type) = DictElem (g b) (a ~ Map String b)

