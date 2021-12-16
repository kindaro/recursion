{-# options_ghc -Wno-orphans #-}

module Main where

import Data.Function
import Test.Tasty
import Test.Tasty.QuickCheck
import qualified Prelude
import Prelude.Unicode
import Prelude (IO, Eq, pure, (+), (*), traverse, fmap, Show)
import Control.Applicative (liftA2)
import qualified Control.Applicative as Base
import Control.Applicative ((<|>))
import Numeric.Natural
import qualified GHC.Exts as Base (IsList (..))
import Data.Functor.Identity
import Data.Functor.Compose
import Numeric.Natural.Unicode
import Text.Show.Pretty
import Data.Bifoldable

import qualified Cata

main ∷ IO ( )
main = defaultMain checks

checks ∷ TestTree
checks = testGroup ""
  [ testGroup "Simple list is a list."
    [ testProperty "leftwards" $ Base.toList @(Cata.Y (Cata.SimpleList ℤ)) ∘ Base.fromList ↔ Prelude.id @[ℤ]
    , testProperty "rightwards" $ Base.fromList ∘ Base.toList ↔ Prelude.id @(Cata.Y (Cata.SimpleList ℤ))
    ]
  , testGroup "List is a list."
    [ testProperty "leftwards" $ Base.toList @(Cata.List ℤ) ∘ Base.fromList ↔ Prelude.id @[ℤ]
    , testProperty "rightwards" $ Base.fromList ∘ Base.toList ↔ Prelude.id @(Cata.List ℤ)
    ]
  , testProperty "Catamorphose gives rise to identity" $ Cata.cata Prelude.fmap Cata.Y ↔ Prelude.id @(Cata.Y (Cata.SimpleList ℤ))
  , testProperty "Catamorphose gives rise to constant" $ Cata.cata @(Cata.SimpleList ℤ) Prelude.fmap (const 1) ↔ Prelude.const @ℤ 1
  , testGroup "Length is definable with respect to Alternative."
    [ testProperty "Zero" $ once $ Cata.length @Cata.SimpleList Base.empty ≡ 0
    , testProperty "Sum" $ \ xs ys → Cata.length @Cata.SimpleList @ℤ (xs <|> ys) ≡ Cata.length xs + Cata.length ys
    , testProperty "One" $ \ x → Cata.length @Cata.SimpleList @ℤ (pure x) ≡ 1
    , testProperty "Product" $ \ xs ys → Cata.length @Cata.SimpleList @(ℤ, ℤ) (liftA2 (, ) xs ys) ≡ Cata.length xs * Cata.length ys
    ]
  , testGroup "Container classes."
    [ testGroup "List."
      [ testGroup "Functor."
        [ testProperty "Identity" $ Prelude.fmap @Cata.List @ℤ id ↔ id
        , testProperty "Composition"
          \ (Fn (f ∷ ℤ → ℤ)) (Fn (g ∷ ℤ → ℤ)) → Prelude.fmap @Cata.List g ∘ Prelude.fmap f ↔ Prelude.fmap (g ∘ f)
        ]
      , testGroup "Foldable."
        [ testProperty "Prelude.length" $ Prelude.length @Cata.List @ℤ ↔ Prelude.fromIntegral ∘ Cata.length
        ]
      , testGroup "Traversable."
        [ testProperty "Identity" $ Prelude.traverse @Cata.List @_ @ℤ Identity ↔ Identity
        , testProperty "Composition" $
          \ (Fn (f ∷ ℤ → Prelude.Maybe ℤ)) (Fn (g ∷ ℤ → Prelude.Maybe ℤ))
          → Prelude.traverse @Cata.Tree (Compose ∘ fmap g ∘ f) ↔ Compose ∘ fmap (Prelude.traverse g) ∘ Prelude.traverse f
        ]
      ]
    , testGroup "Tree."
      [ testGroup "Functor."
        [ testProperty "Identity" $ Prelude.fmap @Cata.Tree @ℤ id ↔ id
        , testProperty "Composition"
          \ (Fn (f ∷ ℤ → ℤ)) (Fn (g ∷ ℤ → ℤ)) → Prelude.fmap @Cata.Tree g ∘ Prelude.fmap f ↔ Prelude.fmap (g ∘ f)
        ]
      , testGroup "Foldable."
        [ testProperty "Prelude.length" $ Prelude.length @Cata.Tree @ℤ ↔ Prelude.fromIntegral ∘ Cata.length
        ]
      , testGroup "Traversable."
        [ testProperty "Identity" $ Prelude.traverse @Cata.Tree @_ @ℤ Identity ↔ Identity
        , testProperty "Composition" $
          \ (Fn (f ∷ ℤ → Prelude.Maybe ℤ)) (Fn (g ∷ ℤ → Prelude.Maybe ℤ))
          → Prelude.traverse @Cata.Tree (Compose ∘ fmap g ∘ f) ↔ Compose ∘ fmap (Prelude.traverse g) ∘ Prelude.traverse f
        ]
      ]
    ]
  , testGroup "Traversals."
    [ testProperty "forget ∘ depths ≡ id" $ Cata.forget ∘ Cata.depths @Cata.TreeFunctor @ℤ ↔ Prelude.id
    , testProperty "depth ≡ length + 1" $ Cata.depth @Cata.ListFunctor @ℤ ↔ (+ 1) ∘ Prelude.fromIntegral ∘ Cata.length
    , testProperty "drop depth ≡ empty" \ (x ∷ Cata.Tree ℤ) → Cata.drop (Cata.depth x) x === (Cata.Y' ∘ Cata.C₂ ∘ Prelude.Left) ( )
    , testProperty "drop 0 ≡ cata Right" $ Cata.drop @Cata.TreeFunctor @ℤ 0 ↔ Cata.cata' fmap (Cata.Y' ∘ Cata.C₂ ∘ Prelude.Right)
    , testProperty "shallowness + 1 ≡ depth" $ (+1) ∘ Cata.shallowness ↔ Cata.depth @Cata.TreeFunctor @ℤ
    , testProperty "take (shallowness + 1) ≡ cata Right" \ (x ∷ Cata.Tree ℤ) → Cata.take (Cata.shallowness x + 1) x === Cata.cata' fmap (Cata.Y' ∘ Cata.C₂ ∘ Prelude.Right) x
    , testProperty "A generalization of depths"
      $ Cata.scanFromLeaves ((+ 1) ∘ bifoldr (flip const) Prelude.max 0) ↔ Cata.depths @Cata.TreeFunctor @ℕ
    , testProperty "A generalization of shallownesses"
      $ Cata.scanFromRoot const (fmap (+ 1) ∘ const) ∘ (0, ) ↔ Cata.shallownesses @Cata.TreeFunctor @ℤ
    ]
  , testGroup "Fancy morphoses."
    [ testProperty "paramorphose is a catamorphose" $ \ (Fn (algebra ∷ Cata.TreeFunctor ℤ (Cata.Tree ℤ, ℤ) → ℤ)) → Cata.para' Prelude.fmap algebra ↔ Cata.para'' Prelude.fmap algebra ]
  ]

isExtensionallyEqual ∷ (Eq β, Show β) ⇒ (α → β) → (α → β) → α → Property
isExtensionallyEqual f g x = counterexample (ppShow (f x)) (counterexample (ppShow (g x)) (f x ≡ g x))

infix 4 ↔
(↔) ∷ (Eq β, Show β) ⇒ (α → β) → (α → β) → α → Property
(↔) = isExtensionallyEqual

instance Arbitrary Natural where
  arbitrary = arbitrarySizedNatural
  shrink    = shrinkIntegral

instance CoArbitrary Natural where
  coarbitrary = coarbitraryIntegral

instance Function Natural where
  function = functionIntegral

instance (Arbitrary α, Arbitrary ((f α) (Cata.Y' f α))) ⇒ Arbitrary (Cata.Y' f α) where
  arbitrary = Prelude.fmap Cata.Y' arbitrary

instance (Arbitrary α, Arbitrary ((f α) (Cata.Y (f α)))) ⇒ Arbitrary (Cata.Y (f α)) where
  arbitrary = Prelude.fmap Cata.Y arbitrary

instance (Arbitrary α, Arbitrary recursion) ⇒ Arbitrary (Cata.SimpleList α recursion) where
  arbitrary = frequency [(1, pure Cata.SimpleEnd), (9, liftA2 Cata.SimpleCons arbitrary arbitrary)]

instance (Arbitrary α, Arbitrary recursion) ⇒ Arbitrary (Cata.ListFunctor α recursion) where
  arbitrary = Prelude.fmap Cata.ListFunctor arbitrary

instance (Arbitrary α, Arbitrary recursion) ⇒ Arbitrary (Cata.TreeFunctor α recursion) where
  arbitrary = Prelude.fmap Cata.TreeFunctor arbitrary

instance (CoArbitrary α, CoArbitrary ((f α) (Cata.Y' f α))) ⇒ CoArbitrary (Cata.Y' f α) where
  coarbitrary = coarbitrary ∘ Cata.y'

instance (CoArbitrary α, CoArbitrary recursion) ⇒ CoArbitrary (Cata.ListFunctor α recursion) where
  coarbitrary (Cata.ListFunctor value) = coarbitrary value

instance (CoArbitrary α, CoArbitrary recursion) ⇒ CoArbitrary (Cata.TreeFunctor α recursion) where
  coarbitrary (Cata.TreeFunctor value) = coarbitrary value

instance (Function α, Function ((f α) (Cata.Y' f α))) ⇒ Function (Cata.Y' f α) where
  function = functionMap Cata.y' Cata.Y'

instance (Function α, Function recursion) ⇒ Function (Cata.ListFunctor α recursion) where
  function = functionMap (\ (Cata.ListFunctor value) → value) Cata.ListFunctor

instance (Function α, Function recursion) ⇒ Function (Cata.TreeFunctor α recursion) where
  function = functionMap (\ (Cata.TreeFunctor value) → value) Cata.TreeFunctor
