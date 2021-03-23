{-# options_ghc -Wno-orphans #-}

module Main where

import Data.Function
import Test.Tasty
import Test.Tasty.QuickCheck
import qualified Prelude
import Prelude.Unicode
import Prelude (IO, Eq, Bool, pure, (+), (*))
import Control.Applicative (liftA2)
import qualified Control.Applicative as Base
import Control.Applicative ((<|>))
import Numeric.Natural

import qualified Cata

main ∷ IO ( )
main = defaultMain checks

checks ∷ TestTree
checks = testGroup ""
  [ testGroup "List is a fixed point."
    [ testProperty "leftwards" $ Cata.simpleListToPreludeList ∘ Cata.preludeListToSimpleList ↔ Prelude.id @[ℤ]
    , testProperty "rightwards" $ Cata.preludeListToSimpleList ∘ Cata.simpleListToPreludeList ↔ Prelude.id @(Cata.Y (Cata.SimpleList ℤ))
    ]
  , testProperty "Catamorphose gives rise to identity" $ Cata.cata Prelude.fmap Cata.Y ↔ Prelude.id @(Cata.Y (Cata.SimpleList ℤ))
  , testProperty "Catamorphose gives rise to constant" $ Cata.cata @(Cata.SimpleList ℤ) Prelude.fmap (const 1) ↔ Prelude.const @ℤ 1
  , testGroup "Length is definable with respect to Alternative."
    [ testProperty "Zero" $ once $ Cata.length @Cata.SimpleList Base.empty ≡ 0
    , testProperty "Sum" $ \ xs ys → Cata.length @Cata.SimpleList @ℤ (xs <|> ys) ≡ Cata.length xs + Cata.length ys
    , testProperty "One" $ \ x → Cata.length @Cata.SimpleList @ℤ (pure x) ≡ 1
    , testProperty "Product" $ \ xs ys → Cata.length @Cata.SimpleList @(ℤ, ℤ) (liftA2 (, ) xs ys) ≡ Cata.length xs * Cata.length ys
    ]
  ]

isExtensionallyEqual ∷ Eq β ⇒ (α → β) → (α → β) → α → Bool
isExtensionallyEqual f g x = f x ≡ g x

infix 4 ↔
(↔) ∷ Eq β ⇒ (α → β) → (α → β) → α → Bool
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
  arbitrary = oneof [pure Cata.SimpleEnd, liftA2 Cata.SimpleCons arbitrary arbitrary]
