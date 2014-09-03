
module TypeCheck where

open import Prelude
open import Lists

open import Term
open WellTyped
open Unchecked  renaming (Term to Expr)
open import Term.Show
open import Term.Parse

data TypeError : Set where
  parse-error : TypeError
  out-of-scope : Name → TypeError
  numbers-are-not-functions : ∀ {Γ a} → Term Γ nat → Term Γ a → TypeError
  argument-mismatch : ∀ {a′ b Γ} (a : Type) → Term Γ (a => b) → Term Γ a′ → TypeError

TC : Set → Set
TC = Either TypeError

typeError : ∀ {A} → TypeError → TC A
typeError = left

data TypeChecked Γ : Expr → Set where
  ok : ∀ a (v : Term Γ a) → TypeChecked Γ (forgetTypes v)

CheckedVar : Cxt → Name → Set
CheckedVar Γ x = Σ Type λ a → (x , a) ∈ Γ

lookupVar : ∀ (Γ : Cxt) x → TC (CheckedVar Γ x)
lookupVar [] x = left (out-of-scope x)
lookupVar ((x , a) ∷ Γ) y with x == y
lookupVar ((x , a) ∷ Γ) .x | yes refl = pure (a , zero refl)
lookupVar ((x , a) ∷ Γ) y  | no _ = second suc <$> lookupVar Γ y

checkedVar : ∀ {Γ x} → CheckedVar Γ x → TypeChecked Γ (var x)
checkedVar (a , i) = ok a (var _ i)

checkApp : ∀ {Γ e₁ e₂} → TypeChecked Γ e₁ → TypeChecked Γ e₂ → Either TypeError (TypeChecked Γ (app e₁ e₂))
checkApp (ok nat u) (ok b v) = typeError (numbers-are-not-functions u v)
checkApp (ok (a => b) u) (ok a₁ v) with a == a₁
checkApp (ok (a => b) u) (ok .a v) | yes refl = pure (ok b (app u v))
checkApp (ok (a => b) u) (ok a₁ v) | no _ = typeError (argument-mismatch a u v)

checkedLam : ∀ {Γ x a e} → TypeChecked ((x , a) ∷ Γ) e → TypeChecked Γ (lam x a e)
checkedLam (ok a v) = ok _ (lam _ _ v)

typeCheck : ∀ Γ (e : Expr) → TC (TypeChecked Γ e)
typeCheck Γ (var x)     = checkedVar <$> lookupVar Γ x
typeCheck Γ (lit n)     = pure $ ok _ (lit n)
typeCheck Γ suc         = pure $ ok _ suc
typeCheck Γ (app e₁ e₂) = typeCheck Γ e₁ >>= λ v₁ →
                          typeCheck Γ e₂ >>= λ v₂ →
                          checkApp v₁ v₂
typeCheck Γ (lam x a e) = checkedLam <$> typeCheck ((x , a) ∷ Γ) e

checkedTerm : ∀ {Γ e} → TypeChecked Γ e → Σ Type (Term Γ)
checkedTerm (ok a v) = a , v

parseAndTypeCheck : String → TC (Σ Type (Term []))
parseAndTypeCheck s =
  flip (maybe (typeError parse-error)) (parseTerm s) $ λ e →
  checkedTerm <$> typeCheck [] e

-- Show instance for type errors --

ShowTypeError : Show TypeError
ShowTypeError = record { showsPrec = λ p →
  λ { parse-error → showParen (p > 0) $ showString "Parse error"
    ; (out-of-scope x) → showParen (p > 0) $ showString ("Variable out of scope: " & x)
    ; (numbers-are-not-functions n v) →
         showParen (p > 0) $ showString "Cannot apply "
                           ∘ shows n
                           ∘ showString " of type nat to argument "
                           ∘ shows v
    ; (argument-mismatch {a′ = a′} a f v) →
         showParen (p > 0) $ showString   "Expected type " ∘ shows a
                           ∘ showString " instead of " ∘ shows a′
                           ∘ showString " in the argument " ∘ shows v
                           ∘ showString " to the function " ∘ shows f
    } }

