module Cata where

import Data.Function
import Prelude.Unicode
import qualified GHC.Exts as Base (IsList (..))

type Y ∷ (* → *) → *
data Y (f ∷ * → *) = Y {y ∷ f (Y f)}

cata ∷ ((Y f → α) → f (Y f) → f α) → (f α → α) → Y f → α
cata fmap = fix \ κ f → f ∘ fmap (κ f) ∘ y

ana ∷ ((α → Y f) → f α → f (Y f)) → (α → f α) → α → Y f
ana fmap = fix \ α f → Y ∘ fmap (α f) ∘ f

data SimpleList α recursion = SimpleCons α recursion | SimpleEnd deriving (Prelude.Functor, Prelude.Eq, Prelude.Show)

deriving instance Eq (f (Y f)) ⇒ Eq (Y f)
deriving instance Show (f (Y f)) ⇒ Show (Y f)

simpleListToPreludeList ∷ forall α. Y (SimpleList α) → [α]
simpleListToPreludeList = cata Prelude.fmap f
  where
    f (SimpleCons value remainder) = value: remainder
    f SimpleEnd = [ ]

preludeListToSimpleList ∷ forall α. [α] → Y (SimpleList α)
preludeListToSimpleList = ana Prelude.fmap f
  where
    f (value: remainder) = SimpleCons value remainder
    f [ ] = SimpleEnd

instance Base.IsList (Y (SimpleList α)) where
  type Item (Y (SimpleList α)) = α
  toList = simpleListToPreludeList
  fromList = preludeListToSimpleList

foldrViaCataForSimpleList ∷ (α → β → β) → β → Y (SimpleList α) → β
foldrViaCataForSimpleList f z = cata Prelude.fmap g
  where
    g SimpleEnd = z
    g (SimpleCons x y) = x `f` y

id ∷ Functor f ⇒ Y f → Y f
id = cata Prelude.fmap Cata.Y

const ∷ Functor f ⇒ α → Y f → α
const = cata Prelude.fmap ∘ Prelude.const
