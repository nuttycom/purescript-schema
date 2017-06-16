module Main where

import Control.Applicative.Free (FreeAp)
import Data.Exists (Exists)
import Data.Leibniz (type (~))
import Data.Map (Map)
import Data.Maybe (Maybe)

data SchemaAlg p a 
  = Prim (p a)
  | Rec  (FreeAp (PropSchema a p) a)
  | Vect (Exists (VectElem p a))
  | Sum  (Array  (Exists (Constr p a)))
  | Dict (Exists (DictElem p a))

data VectElem p a b = VectElem (SchemaAlg p b) (a ~ Array b)
data DictElem p a b = DictElem (SchemaAlg p b) (a ~ Map String b)

data PropSchema o p a 
  = Required (Req o p a)
  | Optional (Exists (Opt o p a))

data Req o p a   = Req { id :: String, valueSchema :: SchemaAlg p a, accessor :: o -> a, dflt :: Maybe a } 
data Opt o p a b = Opt { id :: String, valueSchema :: SchemaAlg p b, accessor :: o -> Maybe b } (a ~ Maybe b) 

data Constr p a b = Constr { id :: String, baseSchema :: SchemaAlg p b, f :: b -> a, g :: a -> Maybe b }
