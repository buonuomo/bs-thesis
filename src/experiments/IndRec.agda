{-# OPTIONS --cubical #-}
--------------------------------------------------------------------------------
-- The module implements:                                                     --
--   - a failed experiment in defining terms modulo βη-≡ via induction-recursion --
--   - note that this is very unfinished and a bit messy, since I abandoned
--   - this code after I realized this wasn't a good direction to go in       --
--------------------------------------------------------------------------------

    -- This program is free software: you can redistribute it and/or modify
    -- it under the terms of the GNU General Public License as published by
    -- the Free Software Foundation, either version 3 of the License, or
    -- (at your option) any later version.

    -- This program is distributed in the hope that it will be useful,
    -- but WITHOUT ANY WARRANTY; without even the implied warranty of
    -- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    -- GNU General Public License for more details.

    -- You should have received a copy of the GNU General Public License
    -- along with this program.  If not, see <http://www.gnu.org/licenses/>.

    -- Lemmas copied from "Hereditary Substitution":
    --    Copyright Thorsten Altenkirch and Chantal Keller, 2010

    -- Copyright Noah Goodman, 2021

-- NOTE: some of the names of functions and data types are slightly different
-- from those in the thesis (the ones in the thesis make more sense), but it should
-- not be too difficult to figure out what corresponds to what

open import Cubical.Foundations.Prelude hiding (_,_; subst)

infixr 40 _⇒_
infixl 30 _,_
infix 20 _∋_

data Ty : Set where
  ○ : Ty
  _⇒_ : Ty → Ty → Ty

data Con : Set where
  ε : Con
  _,_ : Con → Ty → Con

data _∋_ : Con → Ty → Set where
  vz : ∀ {Γ σ} → Γ , σ ∋ σ
  vs : ∀ {Γ σ τ} → Γ ∋ σ → Γ , τ ∋ σ

_-_ : {σ : Ty} (Γ : Con) → Γ ∋ σ → Con
(Γ , σ) - vz = Γ
(Γ , σ) - vs x = (Γ - x) , σ

wkv : ∀ {Γ σ τ} (x : Γ ∋ σ) → (Γ - x) ∋ τ → Γ ∋ τ
wkv vz y = vs y
wkv (vs x) vz = vz
wkv (vs x) (vs y) = vs (wkv x y)

rem : ∀ {Γ σ τ}
  → (x : Γ ∋ σ)
  → (y : (Γ - x) ∋ τ)
  → (Γ - (wkv x y)) ∋ σ
rem vz _ = vz
rem (vs x) vz = x
rem (vs x) (vs y) = vs (rem x y)

conExc : ∀ {Γ σ τ}
  → (x : Γ ∋ σ)
  → (y : (Γ - x) ∋ τ)
  → (Γ - x) - y ≡ (Γ - (wkv x y)) - (rem x y)
conExc vz y = refl
conExc (vs x) vz = refl
conExc (vs {τ = τ} x) (vs y) = cong (λ Θ → Θ , τ) (conExc x y)


conExcTyEq : ∀ {Γ σ τ}
  → (x : Γ ∋ σ)
  → (y : (Γ - x) ∋ τ)
  → ((Γ - x) - y ≡ (Γ - (wkv x y)) - (rem x y)) ≡ ((Γ - x) - y ≡ (Γ - x) - y)
conExcTyEq vz y = refl
conExcTyEq (vs x) vz = refl
conExcTyEq {Γ , τ} (vs x) (vs y) i = ((Γ - x) - y) , τ ≡ conExc x y (~ i) , τ
-- conExcTyEq {Γ , τ} (vs x) (vs y) = cong (λ p → ((Γ - x) - y) , τ ≡ p , τ) (sym (conExc x y))

lem : ∀ {Γ σ τ}
  → (x : Γ ∋ σ)
  → (y : (Γ - x) ∋ τ)
  → (i : I)
  → conExcTyEq x y i ≡ (((Γ - x) - y) ≡ conExc x y (~ i))
lem vz y i = refl
lem (vs x) vz i = refl
lem (vs x) (vs y) i = refl

conExcRefl : ∀ {Γ σ τ}
  → (x : Γ ∋ σ)
  → (y : (Γ - x) ∋ τ)
  → PathP (λ i → conExcTyEq x y i) (conExc x y) refl
conExcRefl vz y = refl
conExcRefl (vs x) vz = refl
conExcRefl {Γ , τ} (vs x) (vs y) i =
  let p = (conExcRefl x y i)
   in cong (λ q → q , τ) (J _ (conExcRefl x y i) (lem x y i))


-- Changing the context in which a variable is typed

-- Note, due to cubical agda we can no longer pattern match on refl - instead we use J
!_>₀Ty : ∀ {Γ Δ σ} → Γ ≡ Δ → (Γ ∋ σ) ≡ (Δ ∋ σ)
!_>₀Ty {σ = σ} p = cong (λ Θ → Θ ∋ σ) p

!_>₀_ : ∀ {Γ Δ σ} → Γ ≡ Δ → Γ ∋ σ → Δ ∋ σ
! p >₀ v = transport (! p >₀Ty) v

data EqV : ∀ {Γ σ τ} → Γ ∋ σ → Γ ∋ τ → Set where

  same : ∀ {Γ σ} {x : Γ ∋ σ}
    → EqV x x

  diff : ∀ {Γ σ τ}
    → (x : Γ ∋ σ)
    → (y : (Γ - x) ∋ τ)
    → EqV x (wkv x y)

eq : ∀ {Γ σ τ} → (x : Γ ∋ σ) → (y : Γ ∋ τ) → EqV x y
eq vz vz = same
eq vz (vs y) = diff vz y
eq (vs x) vz = diff (vs x) vz
eq (vs x) (vs y) with eq x y
... | same = same
... | diff .x z = diff (vs x) (vs z)


-- Here is where the mutual definition begins

data _⊢_ : Con → Ty → Set

!_>₁Ty : ∀ {Γ Δ σ} → Γ ≡ Δ → (Γ ⊢ σ) ≡ (Δ ⊢ σ)
!_>₁Ty {σ = σ} p = cong (λ Θ → Θ ⊢ σ) p

-- Changing the context in which a term is typed
!_>₁_ : forall {Γ Δ σ} → (p : Γ ≡ Δ) → Γ ⊢ σ → Δ ⊢ σ
!_>₁_ {σ = σ} p v = transport (! p >₁Ty) v -- transp (λ i → (p i) ⊢ σ) i0 v



wkTm : ∀ {Γ σ τ}
  → (x : Γ ∋ σ)
  → (Γ - x) ⊢ τ
  → Γ ⊢ τ

substVar : ∀ {Γ σ τ}
  → Γ ∋ τ
  → (x : Γ ∋ σ)
  → (Γ - x) ⊢ σ
  → (Γ - x) ⊢ τ

subst : ∀ {Γ σ τ}
  → Γ ⊢ τ
  → (x : Γ ∋ σ)
  → (Γ - x) ⊢ σ
  → (Γ - x) ⊢ τ

{-# NO_POSITIVITY_CHECK #-}
data _⊢_ where

  var : ∀ {Γ σ}
    → Γ ∋ σ
    → Γ ⊢ σ

  Λ : ∀ {Γ σ τ}
    → Γ , σ ⊢ τ
    → Γ ⊢ σ ⇒ τ

  app : ∀ {Γ σ τ}
    → Γ ⊢ σ ⇒ τ
    → Γ ⊢ σ
    → Γ ⊢ τ

  beta : ∀ {Γ σ τ} (t : Γ , σ ⊢ τ) (u : Γ ⊢ σ)
    → app (Λ t) u ≡ subst t vz u

  eta : ∀ {Γ σ τ} (t : Γ ⊢ σ ⇒ τ)
    → Λ (app (wkTm vz t) (var vz)) ≡ t

  trunc : ∀ {Γ σ} → isSet (Γ ⊢ σ)

wkTmSubstExc : ∀ {Γ σ τ ρ}
 → (y : Γ ∋ σ)
 → (t : (Γ - y) ⊢ τ)
 → (x : (Γ - y) ∋ ρ)
 → (u : ((Γ - y) - x) ⊢ ρ)
 → wkTm (rem y x) (! conExc y x >₁ (subst t x u)) ≡ subst (wkTm y t) (wkv y x) (wkTm (rem y x) (! conExc y x >₁ u))
wkTmSubstExc y t x u = {!!}

wkTm x (var y) = var (wkv x y)
wkTm x (Λ t) = Λ (wkTm (vs x) t)
wkTm x (app t u) = app (wkTm x t) (wkTm x u)
wkTm x (beta t u i) = {!wkTmSubstExc (vs x) t vz u (~ i)!}
wkTm x (eta t i) = {!!}
wkTm x (trunc t u p q i j) = trunc (wkTm x t) (wkTm x u) (cong (wkTm x) p) (cong (wkTm x) q) i j


substVar x y u with eq y x
... | same = u
... | diff .y z = var z

subst (var x) y u = substVar x y u
subst (Λ t) x u = Λ (subst t (vs x) (wkTm vz u))
subst (app t₁ t₂) x u = app (subst t₁ x u) (subst t₂ x u)
subst (beta t u i) x v = {!!}
subst (eta t i) x u = {!!}
subst (trunc t u p q i j) x v = trunc (subst t x v) (subst u x v) (cong (λ y → subst y x v) p) (cong (λ y → subst y x v) q) i j
