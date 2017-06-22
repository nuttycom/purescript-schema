module Data.Schema where

import Prelude ((<<<))
import Control.Applicative.Free (FreeAp, hoistFreeAp)
import Data.Exists (Exists, mkExists, runExists)
import Data.Function (($))
import Data.Functor (map)
import Data.Profunctor (class Profunctor)
import Data.Functor.Contravariant (class Contravariant, cmap)
import Data.Lazy (Lazy, force)
import Data.Leibniz (type (~))
import Data.Map (Map)
import Data.Maybe (Maybe)

data HCofree (g :: (Type -> Type) -> Type -> Type) (a :: Type) (i :: Type) = HCofree a (Lazy (g (HCofree g a) i))

head :: forall g a i. HCofree g a i -> a 
head (HCofree h _) = h

tail :: forall g a i. HCofree g a i -> g (HCofree g a) i
tail (HCofree _ t) = force t

newtype Schema (p :: Type -> Type) (a :: Type) (i :: Type) = Schema { runSchema :: HCofree (SchemaAlg p) a i }

data SchemaAlg (p :: Type -> Type) (g :: Type -> Type) (a :: Type) 
  = Prim (p a)
  | Rec  (Props g a a)
  | Sum  (Array  (Exists (Constr g a)))
  | Vect (Exists (VectElem g a))
  | Dict (Exists (DictElem g a))

newtype Props (g :: Type -> Type) (o :: Type) (a :: Type) = Props (FreeAp (PropSchema g o) a)

instance propsPf :: Profunctor (Props g) where
  dimap f g (Props fap) = 
    Props <<< map g $ hoistFreeAp (runPropSchemaC <<< cmap f <<< PropSchemaC) fap

data PropSchema (g :: Type -> Type) (o :: Type) (a :: Type)
  = Required (Req g o a)
  | Optional (Exists (Opt g o a))

newtype PropSchemaC (g :: Type -> Type) (a :: Type) (o :: Type) = PropSchemaC (PropSchema g o a)

runPropSchemaC :: forall g a o. PropSchemaC g a o -> PropSchema g o a
runPropSchemaC (PropSchemaC s) = s

instance propsSchemaC :: Contravariant (PropSchemaC g a) where
   cmap :: forall o n. (n -> o) -> PropSchemaC g a o -> PropSchemaC g a n
   cmap f (PropSchemaC (Required r)) = 
     PropSchemaC <<< Required $ cmapReq f r
 
   cmap f (PropSchemaC (Optional optEx)) = 
     PropSchemaC <<< Optional $ runExists (mkExists <<< cmapOpt f) optEx 

data Req (g :: Type -> Type) (o :: Type) (a :: Type) 
  = Req { id :: String, valueSchema :: g a, accessor :: o -> a, dflt :: Maybe a } 

cmapReq :: forall g o n a. (n -> o) -> Req g o a -> Req g n a
cmapReq f (Req r) = Req (r { accessor = r.accessor <<< f })

data Opt (g :: Type -> Type) (o :: Type) (a :: Type) (b :: Type) 
  = Opt { id :: String, valueSchema :: g b, accessor :: o -> Maybe b } (a ~ Maybe b) 

cmapOpt :: forall g o n a b. (n -> o) -> Opt g o a b -> Opt g n a b
cmapOpt f (Opt r proof) = Opt (r { accessor = r.accessor <<< f }) proof

data Constr (g :: Type -> Type) (a :: Type) (b :: Type) 
  = Constr { id :: String, baseSchema :: g b, g :: b -> a, g :: a -> Maybe b }

data VectElem (g :: Type -> Type) (a :: Type) (b :: Type) = VectElem (g b) (a ~ Array b)
data DictElem (g :: Type -> Type) (a :: Type) (b :: Type) = DictElem (g b) (a ~ Map String b)
