{-# options_ghc -Wno-name-shadowing #-}

module Cata where

import Data.Function
import Prelude.Unicode
import Numeric.Natural.Unicode
import qualified GHC.Exts as Base (IsList (..))
import Data.Bifunctor
import Data.Bifunctor.TH
import Data.Bifoldable
import Control.Applicative
import Data.Monoid (Sum (Sum), getSum)
import Generic.Data
import Data.Functor.Compose
import Data.Functor.Classes

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

newtype Y' f α = Y' {y' ∷ f α (Y' f α)}

deriving instance Eq (f α (Y' f α)) ⇒ Eq (Y' f α)
deriving instance Show (f α (Y' f α)) ⇒ Show (Y' f α)

instance Bifunctor f ⇒ Functor (Y' f) where
  fmap f = cata' second (Y' ∘ first f)

data SimpleList α recursion = SimpleCons α recursion | SimpleEnd deriving (Prelude.Functor, Prelude.Eq, Prelude.Show)

$(deriveBifunctor ''SimpleList)
$(deriveBifoldable ''SimpleList)

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

type (+) = Either
infixl 5 +

type α × β = (α, β)
infixl 6 ×
type Π = (, )

newtype ListFunctor α recursion = ListFunctor {listFunctor ∷ ( ) + α × recursion} deriving (Show, Eq, Ord, Functor)
type List = Y' ListFunctor

$(deriveBifunctor ''ListFunctor)
$(deriveBifoldable ''ListFunctor)

link ∷ α → List α → List α
link x xs = Y' (ListFunctor (Right (x, xs)))
end ∷ List α
end = Y' (ListFunctor (Left ( )))

instance Base.IsList (List α) where
  type Item (List α) = α
  toList (Y' (ListFunctor (Left ( )))) = [ ]
  toList (Y' (ListFunctor (Right (x, xs)))) = x: Base.toList xs
  fromList (x: xs) = x `link` Base.fromList xs
  fromList [ ] = end

data Pair α = Pair α α deriving (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
instance Show1 Pair where
  liftShowsPrec = gliftShowsPrec

type f ∘ g = Compose f g
infixl 4 ∘
pattern C x = Compose x

newtype TreeFunctor α β = TreeFunctor (α × (( ) + Pair β))
type Tree = Y' TreeFunctor

$(deriveBifunctor ''TreeFunctor)
$(deriveBifoldable ''TreeFunctor)

leaf ∷ α → Tree α
leaf x = (Y' ∘ TreeFunctor) (x, Left ( ))

branch ∷ α → Tree α → Tree α → Tree α
branch x t₁ t₂ = (Y' ∘ TreeFunctor) (x, (Right (Pair t₁ t₂)))

example ∷ Tree ℤ
example = branch 0 (branch 1 (leaf 2) (leaf 3)) ((leaf 4))
