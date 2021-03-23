{-# options_ghc -Wno-name-shadowing #-}

module Cata where

import Data.Function
import Prelude.Unicode
import Numeric.Natural.Unicode
import qualified GHC.Exts as Base (IsList (..))
import Data.Bifunctor
import Data.Bifoldable
import Control.Applicative
import Data.Monoid (Sum (Sum), getSum)

type Y ∷ (* → *) → *
data Y (f ∷ * → *) = Y {y ∷ f (Y f)}

deriving instance Eq (f (Y f)) ⇒ Eq (Y f)
deriving instance Show (f (Y f)) ⇒ Show (Y f)

cata ∷ ((Y f → α) → f (Y f) → f α) → (f α → α) → Y f → α
cata fmap = fix \ κ f → f ∘ fmap (κ f) ∘ y

cata' ∷ ((Y' f α → β) → f α (Y' f α) → f α β) → (f α β → β) → Y' f α → β
cata' fmap = fix \ κ f → f ∘ fmap (κ f) ∘ y'

ana ∷ ((α → Y f) → f α → f (Y f)) → (α → f α) → α → Y f
ana fmap = fix \ α f → Y ∘ fmap (α f) ∘ f

data SimpleList α recursion = SimpleCons α recursion | SimpleEnd deriving (Prelude.Functor, Prelude.Eq, Prelude.Show)

instance Bifoldable SimpleList where
  bifoldMap _ _ SimpleEnd = mempty
  bifoldMap f g (SimpleCons value remainder) = f value <> g remainder

instance Bifunctor SimpleList where
  bimap f g (SimpleCons value remainder) = SimpleCons (f value) (g remainder)
  bimap _ _ SimpleEnd = SimpleEnd

newtype Y' f α = Y' {y' ∷ f α (Y' f α)}

deriving instance Eq (f α (Y' f α)) ⇒ Eq (Y' f α)
deriving instance Show (f α (Y' f α)) ⇒ Show (Y' f α)

instance Bifunctor f ⇒ Functor (Y' f) where
  fmap f = cata' second (Y' ∘ first f)

instance Applicative (Y' SimpleList) where
  pure x = Y' (SimpleCons x (Y' SimpleEnd))
  _ <*> Y' SimpleEnd = Y' SimpleEnd
  fs <*> Y' (SimpleCons x xs) = fmap ($ x) fs <|> fs <*> xs

instance Alternative (Y' SimpleList) where
  empty = Y' SimpleEnd
  Y' SimpleEnd <|> xs = xs
  Y' (SimpleCons x xs) <|> ys = Y' (SimpleCons x (xs <|> ys))

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

length ∷ (Bifunctor f, Bifoldable f) ⇒ Y' f α → ℕ
length = getSum ∘ cata' second (bifoldMap (Prelude.const (Sum 1)) Prelude.id)
