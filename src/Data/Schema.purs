module Data.Schema where

import Prelude ((<<<), class Apply, apply)
import Control.Applicative (class Applicative, pure)
import Control.Applicative.Free (FreeAp, hoistFreeAp)
import Data.Exists (Exists, mkExists, runExists)
import Data.Function (($))
import Data.Functor (class Functor, map)
import Data.Functor.Hoist (Hoist)
import Data.NaturalTransformation (type (~>))
import Data.Newtype (class Newtype, wrap, unwrap)
import Data.Profunctor (class Profunctor, rmap)
import Data.Functor.Contravariant (class Contravariant, cmap)
import Data.Lazy (Lazy, defer, force)
import Data.Leibniz (type (~))
import Data.Map (Map)
import Data.Maybe (Maybe)

data HCofree (g :: (Type -> Type) -> Type -> Type) (a :: Type) (i :: Type)
  = HCofree a (Lazy (g (HCofree g a) i))

class HFunctor (f :: (Type -> Type) -> Type -> Type) where
  hoist :: forall g h. Hoist (f g) (f h) g h

type HNaturalTransformation (g :: (Type -> Type) -> Type -> Type) (h :: (Type -> Type) -> Type -> Type) = forall m a. g m a -> h m a

newtype HCofreeF (g :: (Type -> Type) -> Type -> Type) (i :: Type) (a :: Type)
  = HCofreeF (HCofree g a i)

instance hCofreeFNewtype :: Newtype (HCofreeF g i a) (HCofree g a i) where
  wrap = HCofreeF
  unwrap (HCofreeF fa) = fa

--instance hCofreeFFunctor :: (HFunctor g) => Functor (HCofreeF g i) where
--  map = loop 
--   loop f (HCofreeF (HCofree h ga)) = wrap $ HCofree (f h) (defer $ \_ -> hmap (unwrap <<< loop f <<< wrap <<< force) ga)

head :: forall g a i. HCofree g a i -> a
head (HCofree h _) = h

tail :: forall g a i. HCofree g a i -> g (HCofree g a) i
tail (HCofree _ t) = force t

newtype Schema (p :: Type -> Type) (i :: Type) (a :: Type)
  = Schema (HCofree (SchemaAlg p) a i)

--instance schemaFunctor :: Functor (Schema p i) where
--  map f (Schema cf) = Schema $ loop f cf where
--    loop f (HCofree hd tl) = HCofree (f hd) (defer \_ -> hoist (loop f) (force tl))

data SchemaAlg (p :: Type -> Type) (g :: Type -> Type) (a :: Type)
  = Prim (p a)
  | Rec  (Props g a a)
  | Sum  (Array  (Exists (Constr g a)))
  | Vect (Exists (VectElem g a))
  | Dict (Exists (DictElem g a))

instance schemaAlgHFunctor :: HFunctor (SchemaAlg p) where
  hoist :: forall g h. (g ~> h) -> SchemaAlg p g ~> SchemaAlg p h
  hoist nt (Prim pa) = Prim pa
  hoist nt (Rec (Props fa)) = Rec $ Props (hoistFreeAp (hoistPropSchema nt) fa)
  hoist nt (Sum xs) = Sum $ map (runExists (mkExists <<< hoistConstr nt)) xs
  hoist nt (Vect eve) = Vect $ (runExists (mkExists <<< hoistVectElem nt) eve)
  hoist nt (Dict eve) = Dict $ (runExists (mkExists <<< hoistDictElem nt) eve)

newtype Props (g :: Type -> Type) (o :: Type) (a :: Type) = Props (FreeAp (PropSchema g o) a)

instance propsNewtype :: Newtype (Props g o a) (FreeAp (PropSchema g o) a) where
  wrap = Props
  unwrap (Props fa) = fa

instance propsProfunctor :: Profunctor (Props g) where
  dimap f g (Props fa) =
    Props <<< map g $ hoistFreeAp (runPropSchemaC <<< cmap f <<< PropSchemaC) fa

instance propsFunctor :: Functor (Props g a) where
  map = rmap

instance propsApply :: Apply (Props g a) where
  apply (Props f) (Props fa) = Props $ apply f fa

instance propsApplicative :: Applicative (Props g a) where
  pure = Props <<< pure

data PropSchema (g :: Type -> Type) (o :: Type) (a :: Type)
  = Required (Req g o a)
  | Optional (Exists (Opt g o a))

newtype PropSchemaC (g :: Type -> Type) (a :: Type) (o :: Type) = PropSchemaC (PropSchema g o a)

hoistPropSchema :: forall f g o. Hoist (PropSchema f o) (PropSchema g o) f g
hoistPropSchema nt (Required req)   = Required $ hoistReq nt req
hoistPropSchema nt (Optional optEx) = Optional $ runExists (mkExists <<< hoistOpt nt) optEx

runPropSchemaC :: forall g a o. PropSchemaC g a o -> PropSchema g o a
runPropSchemaC (PropSchemaC s) = s

instance propSchemaContravariant :: Contravariant (PropSchemaC g a) where
   cmap :: forall o n. (n -> o) -> PropSchemaC g a o -> PropSchemaC g a n
   cmap f (PropSchemaC (Required r)) =
     PropSchemaC <<< Required $ cmapReq f r

   cmap f (PropSchemaC (Optional optEx)) =
     PropSchemaC <<< Optional $ runExists (mkExists <<< cmapOpt f) optEx

data Req (g :: Type -> Type) (o :: Type) (a :: Type)
  = Req { id :: String, valueSchema :: g a, accessor :: o -> a, dflt :: Maybe a }

cmapReq :: forall g o n a. (n -> o) -> Req g o a -> Req g n a
cmapReq f (Req r) = Req (r { accessor = r.accessor <<< f })

hoistReq :: forall g h o a. Hoist (Req g o) (Req h o) g h
hoistReq nt (Req r) = Req r { valueSchema = nt r.valueSchema }

data Opt (g :: Type -> Type) (o :: Type) (a :: Type) (b :: Type)
  = Opt { id :: String, valueSchema :: g b, accessor :: o -> Maybe b } (a ~ Maybe b)

cmapOpt :: forall g o n a b. (n -> o) -> Opt g o a b -> Opt g n a b
cmapOpt f (Opt r proof) = Opt (r { accessor = r.accessor <<< f }) proof

hoistOpt :: forall g h o a b. (g ~> h) -> Opt g o a b -> Opt h o a b
hoistOpt nt (Opt r proof) = Opt (r { valueSchema = nt r.valueSchema }) proof

data Constr (g :: Type -> Type) (a :: Type) (b :: Type)
  = Constr { id :: String, baseSchema :: g b, g :: b -> a, g :: a -> Maybe b }

hoistConstr :: forall g h a b. (g ~> h) -> Constr g a b -> Constr h a b
hoistConstr nt (Constr r) = Constr r { baseSchema = nt r.baseSchema }

data VectElem (g :: Type -> Type) (a :: Type) (b :: Type) = VectElem (g b) (a ~ Array b)

hoistVectElem :: forall g h a b. (g ~> h) -> VectElem g a b -> VectElem h a b
hoistVectElem nt (VectElem gb proof) = VectElem (nt gb) proof

data DictElem (g :: Type -> Type) (a :: Type) (b :: Type) = DictElem (g b) (a ~ Map String b)

hoistDictElem :: forall g h a b. (g ~> h) -> DictElem g a b -> DictElem h a b
hoistDictElem nt (DictElem gb proof) = DictElem (nt gb) proof

