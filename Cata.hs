{-# options_ghc -Wno-name-shadowing #-}

module Cata where

import Data.Function
import qualified Data.Function as Base
import Prelude.Unicode
import Numeric.Natural.Unicode
import qualified GHC.Exts as Base (IsList (..))
import Data.Bifunctor
import Data.Bifunctor.TH
import Data.Bifoldable
import Data.Bitraversable
import Control.Applicative
import Generic.Data
import Data.Functor.Compose
import Data.Functor.Classes
import Data.Semigroup
import qualified Data.Foldable as Foldable

diagonal ∷ α → (α, α)
diagonal x = (x, x)

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

ana' ∷ ((α -> Y' f γ) -> f γ α -> f γ (Y' f γ)) → (α → f γ α) → α → Y' f γ
ana' fmap algebra = fix \ α → Y' ∘ fmap α ∘ algebra

newtype Y' f α = Y' {y' ∷ f α (Y' f α)}

deriving instance Eq (f α (Y' f α)) ⇒ Eq (Y' f α)
deriving instance Show (f α (Y' f α)) ⇒ Show (Y' f α)

instance Bifunctor f ⇒ Functor (Y' f) where
  fmap f = cata' second (Y' ∘ first f)

instance (Bifunctor f, Bifoldable f) ⇒ Foldable (Y' f) where
  foldMap f = cata' second (bifoldMap f id)

instance (Bifunctor f, Bitraversable f) ⇒ Traversable (Y' f) where
  traverse f = cata' second (fmap Y' ∘ bitraverse f Prelude.id)

data SimpleList α recursion = SimpleCons α recursion | SimpleEnd deriving (Prelude.Functor, Prelude.Eq, Prelude.Show)

$(deriveBifunctor ''SimpleList)
$(deriveBifoldable ''SimpleList)
$(deriveBitraversable ''SimpleList)

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
type Σ = Either

type α × β = (α, β)
infixl 6 ×
type Π = (, )

newtype ListFunctor α recursion = ListFunctor {listFunctor ∷ ( ) + α × recursion} deriving (Show, Eq, Ord, Functor, Foldable, Traversable, Generic, Generic1)
type List = Y' ListFunctor

$(deriveBifunctor ''ListFunctor)
$(deriveBifoldable ''ListFunctor)
$(deriveBitraversable ''ListFunctor)

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
pattern C ∷ forall k k' (f ∷ k → *) (g ∷ k' → k) (a ∷ k'). f (g a) → Compose f g a
pattern C x = Compose x

newtype TreeFunctor α β = TreeFunctor (α × (( ) + List β)) deriving (Eq, Show, Functor, Foldable, Traversable, Generic, Generic1)
type Tree = Y' TreeFunctor

-- I have to inline a chunk of splices derived from `TreeFunctor` with `Pair`
-- instead of `List`, and some associated internal code from `bifunctors`.

bimapConst :: p b d -> (a -> b) -> (c -> d) -> p a c -> p b d
bimapConst = Base.const . Base.const . Base.const
{-# INLINE bimapConst #-}

bifoldrConst :: c -> (a -> c -> c) -> (b -> c -> c) -> c -> p a b -> c
bifoldrConst = Base.const . Base.const . Base.const . Base.const
{-# INLINE bifoldrConst #-}

bifoldMapConst :: m -> (a -> m) -> (b -> m) -> p a b -> m
bifoldMapConst = Base.const . Base.const . Base.const
{-# INLINE bifoldMapConst #-}

bitraverseConst :: f (t c d) -> (a -> f c) -> (b -> f d) -> t a b -> f (t c d)
bitraverseConst = Base.const . Base.const . Base.const
{-# INLINE bitraverseConst #-}

instance Bifunctor TreeFunctor where
  bimap
    = \ f g value
        -> (((bimapConst
                (case value of {
                    TreeFunctor _arg1
                      -> TreeFunctor
                          (case _arg1 of {
                              (,) _arg1 _arg2
                                -> ((,) (f _arg1))
                                    (((bimap (\ _n -> _n))
                                        (\ _n -> (fmap g) _n))
                                        _arg2) }) }))
                f)
              g)
              value

instance Bifoldable TreeFunctor where
  bifoldr
    = \ f g z value
        -> ((((bifoldrConst
                  (case value of {
                    TreeFunctor _arg1
                      -> ((\ _n1 n2
                              -> case _n1 of {
                                  (,) _arg1 _arg2
                                    -> (f _arg1)
                                          (((\ _n1 n2
                                              -> (((bifoldr (\ _n1 n2 -> n2))
                                                      (\ _n1 n2
                                                        -> ((foldr g) n2) _n1))
                                                    n2)
                                                    _n1)
                                              _arg2)
                                            n2) })
                            _arg1)
                            z }))
                f)
                g)
              z)
              value
  bifoldMap
    = \ f g value
        -> (((bifoldMapConst
                (case value of {
                    TreeFunctor _arg1
                      -> (\ _n
                            -> case _n of {
                                (,) _arg1 _arg2
                                  -> (mappend (f _arg1))
                                        (((bifoldMap (\ _n -> mempty)) (foldMap g))
                                          _arg2) })
                          _arg1 }))
                f)
              g)
              value

instance Bitraversable TreeFunctor where
  bitraverse
    = \ f g value
        -> (((bitraverseConst
                (case value of {
                    TreeFunctor _arg1
                      -> (fmap (\ b1 -> TreeFunctor b1))
                          ((\ _n
                              -> case _n of {
                                    (,) _arg1 _arg2
                                      -> ((liftA2 (\ b1 b2 -> ((,) b1) b2))
                                            (f _arg1))
                                          (((bitraverse pure) (traverse g)) _arg2) })
                              _arg1) }))
                f)
              g)
              value


leaf ∷ α → Tree α
leaf x = (Y' ∘ TreeFunctor) (x, Left ( ))

branch ∷ α → Tree α → Tree α → Tree α
branch x t₁ t₂ = (Y' ∘ TreeFunctor) (x, (Right [t₁, t₂]))

example ∷ Tree ℤ
example = branch 0 (branch 1 (leaf 2) (leaf 3)) ((leaf 4))

newtype C₂ functor γ bifunctor α β
  = C₂ {c₂ ∷ functor γ (bifunctor α β)} deriving (Show, Eq, Ord)

type Free = C₂ Σ
type Cofree = C₂ Π

instance (Functor (functor γ), Functor (functor' α)) ⇒ Functor (C₂ functor γ functor' α) where
  fmap f = C₂ ∘ fmap (fmap f) ∘ c₂

instance (Functor (functor γ), Bifunctor bifunctor) ⇒ Bifunctor (C₂ functor γ bifunctor) where
  bimap f g = C₂ ∘ fmap (bimap f g) ∘ c₂

leftmost ∷ Cofree γ bifunctor α β → γ
leftmost (C₂ (x, _)) = x

forget ∷ (Bifunctor f, Functor (f α), Foldable (f α)) ⇒ Y' (Cofree β f) α → Y' f α
forget = cata' fmap (Y' ∘ snd ∘ c₂)

newtype Third functor bifunctor α γ β = Third {third ∷ C₂ functor γ bifunctor α β}

instance (Bifunctor bifunctor, Bifunctor functor) ⇒ Bifunctor (Third functor bifunctor α) where
  bimap f g = Third ∘ C₂ ∘ bimap f (bimap Base.id g) ∘ c₂ ∘ third

instance (Bifoldable bifunctor, Bifoldable functor) ⇒ Bifoldable (Third functor bifunctor α) where
  bifoldMap f g = bifoldMap f (bifoldMap (Base.const mempty) g) ∘ c₂ ∘ third

decorative
  ∷ (Bifunctor f, Functor (f α), Foldable (f α))
  ⇒ (∀ α. (Functor (f α), Foldable (f α)) ⇒ f α β → β) → Y' f α → Y' (Cofree β f) α
decorative algebra = cata' fmap (Y' ∘ \ f → C₂ ((algebra ∘ bimap Base.id (leftmost ∘ y')) f, f))

depths ∷ ∀ (f ∷ * → * → *) α. (Bifunctor f, Functor (f α), Foldable (f α)) ⇒ Y' f α → Y' (Cofree ℕ f) α
depths = decorative algebra
  where
    algebra ∷ ∀ α. (Functor (f α), Foldable (f α)) ⇒ f α ℕ → ℕ
    algebra = (+ 1) ∘ Foldable.foldr max 0

depth ∷ ∀ (f ∷ * → * → *) α. (Bifunctor f, Functor (f α), Foldable (f α)) ⇒ Y' f α → ℕ
depth = fst ∘ c₂ ∘ y' ∘ depths

null ∷ (Bifunctor f, Bifoldable f) ⇒ Y' (f ∷ * → * → *) α → Bool
null = Foldable.null ∘ Foldable.toList

drop ∷ ∀ (f ∷ * → * → *) α. (Bifunctor f, Functor (f α), Foldable (f α)) ⇒ ℕ → Y' f α → Y' (Free ( ) f) α
drop n = cata' fmap (Y' ∘ C₂ ∘ conversion ∘ c₂) ∘ depths
  where
    conversion (i, value)
      | i ≤ n = Left ( )
      | otherwise = Right value

shallownesses ∷ ∀ (f ∷ * → * → *) α. (Functor (f α), Bifunctor f, Foldable (f α)) ⇒ Y' f α → Y' (Cofree ℕ f) α
shallownesses = ($ 0) ∘ cata' fmap algebra
  where
    algebra ∷ f α (ℕ → Y' (Cofree ℕ f) α) → ℕ → Y' (Cofree ℕ f) α
    algebra = flip \ n → Y' ∘ C₂ ∘ (n, ) ∘ fmap ($ (n + 1))

shallowness ∷ ∀ (f ∷ * → * → *) α. (Bifunctor f, Bifoldable f, Functor (f α), Foldable (f α)) ⇒ Y' f α → ℕ
shallowness = maximum ∘ Foldable.toList  ∘ cata' fmap (Y' ∘ Third) ∘ shallownesses

take ∷ (Functor (f α), Bifunctor f, Foldable (f α)) ⇒ ℕ → Y' f α → Y' (Free ( ) f) α
take n = cata' fmap (Y' ∘ C₂ ∘ conversion ∘ c₂) ∘ shallownesses
  where
    conversion ∷ (ℕ, f α (Y' (Free ( ) f) α)) → Either ( ) (f α (Y' (Free ( ) f) α))
    conversion (i, value)
      | i ≥ n = Left ( )
      | otherwise = Right value

fork ∷ (α → β₁) → (α → β₂) → α → (β₁, β₂)
fork f g x = (f x, g x)

scanFromLeaves ∷ _ ⇒ (f α β → β) → Y' f α → Y' (Cofree β f) α
scanFromLeaves algebra = ana' fmap (C₂ ∘ fork (cata' fmap algebra) y')

scanFromRoot
  ∷ ∀ f α label accumulator
  . _
  ⇒ (∀ ξ. accumulator → f α ξ → label) → (∀ ξ. accumulator → f α ξ → accumulator) → (accumulator, Y' f α) → Y' (Cofree label f) α
scanFromRoot computeLabel accumulate = ana' fmap coAlgebra
  where
    fixture ∷ (accumulator, Y' f α) → f α (accumulator, Y' f α)
    fixture (previousAccumulator, Y' tree) = let newAccumulator = accumulate previousAccumulator tree in fmap (newAccumulator, ) tree
    coAlgebra ∷ (accumulator, Y' f α) → Cofree label f α (accumulator,Y' f α)
    coAlgebra = C₂ ∘ fork (uncurry computeLabel ∘ fmap y') fixture
