------------------------------------------------------------------------
-- The Agda standard library
--
-- An irrelevant version of ⊥-elim
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --no-guardedness #-}

module Data.Empty.Irrelevant where

open import Data.Empty hiding (⊥-elim)

⊥-elim : ∀ {w} {Whatever : Set w} → .⊥ → Whatever
⊥-elim ()
