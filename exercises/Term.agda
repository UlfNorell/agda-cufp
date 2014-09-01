
module Term where

open import Prelude
open import Lists
open import Type public

Name = String

module Unchecked where

  data Term : Set where
    var : Name → Term
    lit : Nat → Term
    suc : Term
    app : Term → Term → Term
    lam : Name → Type → Term → Term

module WellTyped where

  Cxt = List (Name × Type)

  data Term (Γ : Cxt) : Type → Set where
    var : ∀ {a} (x : Name) (i : (x , a) ∈ Γ) → Term Γ a
    app : ∀ {a b} (u : Term Γ (a => b)) (v : Term Γ a) →
            Term Γ b
    lam : ∀ x a {b} (v : Term ((x , a) ∷ Γ) b) → Term Γ (a => b)
    lit : ∀ (n : Nat) → Term Γ nat
    suc : Term Γ (nat => nat)

  open Unchecked renaming (Term to Expr)

  -- Exercise: Define the erasure from well-typed to unchecked terms.
  postulate
    forgetTypes : ∀ {Γ a} → Term Γ a → Expr

module WellScoped where

  -- Exercise: Define well-scoped terms.
  Cxt = List Name

  data Term (Γ : Cxt) : Set where

  open Unchecked renaming (Term to Expr)

  -- Exercise: Define the erasure from well-typed to unchecked terms.
  postulate
    forgetScope : ∀ {Γ} → Term Γ → Expr
