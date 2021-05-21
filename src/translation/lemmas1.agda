{-# OPTIONS --cubical #-}
--------------------------------------------------------------------------------
-- This module implements operations to work with De Bruijn indices:          --
--   - changing the context parameterizing a variable, a term or a normal     --
--     form                                                                   --
--   - the predicate onediff, that identifies De Bruijn indices that are      --
--     consecutive in a context                                               --
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

    -- Copyright Thorsten Altenkirch and Chantal Keller, 2010

    -- Modifications and new proofs: Copyright Noah Goodman, 2021

module lemmas1 where

open import hsubst

open import Cubical.Foundations.Prelude renaming (subst to substP)

open import Cubical.Data.Equality

open import Cubical.HITs.SetTruncation
open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties


-- The ctop trick in action

substSame2 : ∀ {Γ σ τ}
  → (x : Var Γ σ)
  → eq x x ≡ same 
  → eq (vs {τ} x) (vs x) ≡ same
substSame2 x p with eq x x | ctop p
substSame2 x p | .same | reflp = refl

substSame3 : ∀ {Γ σ} → (x : Var Γ σ) → eq x x ≡ same
substSame3 vz = refl
substSame3 (vs x) = substSame2 x (substSame3 x)


substDiff2 : ∀ {Γ σ τ ρ} → (x : Var Γ σ) → (y : Var (Γ - x) τ) → eq x (wkv x y) ≡ diff x y → eq (vs {ρ} x) (vs (wkv x y)) ≡ diff (vs x) (vs y)
substDiff2 x y p with eq x (wkv x y)
substDiff2 x y p | q with ctop p
... | reflp = refl

substDiff3 : ∀ {Γ σ τ} → (x : Var Γ σ) → (y : Var (Γ - x) τ) → eq x (wkv x y) ≡ diff x y
substDiff3 vz y = refl
substDiff3 (vs x) vz = refl
substDiff3 (vs x) (vs y) = substDiff2 x y (substDiff3 x y)


-- Changing the context in which a variable is typed

!_>₀_ : ∀ {Γ Δ σ} → Γ ≡ Δ → Var Γ σ → Var Δ σ
!_>₀_ {σ = σ} p v = transport (λ i → Var (p i) σ) v

!refl₀ : ∀ {Γ σ} → (x : Var Γ σ) → (! refl >₀ x) ≡ x
!refl₀ x = transportRefl x

-- Commutation between var constructors and !_>₀_
-- Now we need to use !refl₀ because transport does not compute definitionally
!vz : ∀ {Γ Δ σ} → (p : Γ ≡ Δ) → (! (λ i → (p i) , σ) >₀ vz) ≡ vz
!vz {σ = σ} p = J (λ y q → ! (λ i → (q i) , σ) >₀ vz ≡ vz) (!refl₀ vz) p

!vsRefl : ∀ {Γ σ τ} → (x : Var Γ τ) → vs {σ} (! refl >₀ x) ≡ vs x
!vsRefl x = cong vs (!refl₀ x)

!vs : ∀ {Γ Δ σ τ} → (p : Γ ≡ Δ) → (x : Var Γ τ) → (! cong (λ Θ → Θ , σ) p >₀ (vs x)) ≡ vs (! p >₀ x)
!vs {σ = σ} {τ = τ} p x = J (λ y q → (! cong (λ Θ → Θ , σ) q >₀ (vs x)) ≡ vs (! q >₀ x)) (!refl₀ (vs x) ∙ sym (!vsRefl x)) p


-- !! is a bit tougher, and requires two lemmas
!!-lem′ : ∀ {Δ σ} → (y : Var Δ σ) → (! sym refl >₀ (! refl >₀ y)) ≡ y
!!-lem′ y = !refl₀ (! refl >₀ y) ∙ !refl₀ y

-- This is pretty counterintuitive, because there's a sort of contravariant twist happening with the motive
-- to J
!!-lem : ∀ {Γ Δ σ} → (y : Var Δ σ) → (p : Γ ≡ Δ) → (! p >₀ (! sym p >₀ y)) ≡ y
!!-lem y p = J (λ Θ q → (! sym q >₀ (! q >₀ y)) ≡ y) (!!-lem′ y) (sym p)

!! : ∀ {Γ Δ σ} → (x : Var Γ σ) → (y : Var Δ σ) → (p : Γ ≡ Δ) → x ≡ (! sym p >₀ y) → y ≡ (! p >₀ x)
!! x y p q with sym (!!-lem y p)
... | r = substP (λ z → y ≡ (! p >₀ z)) (sym q) r


-- Changing the proof

!p : ∀ {Γ Δ σ} → (v : Var Γ σ) → (p q : Γ ≡ Δ) → p ≡ q → (! p >₀ v) ≡ (! q >₀ v)
!p v p q r i = ! (r i) >₀ v

-- Changing the context in which a term is typed
!_>₁_ : ∀ {Γ Δ σ} → Γ ≡ Δ → Tm Γ σ → Tm Δ σ
!_>₁_ {σ = σ} p t = J (λ y _ → Tm y σ) t p

!refl₁ : ∀ {Γ σ} → (t : Tm Γ σ) → (! refl >₁ t) ≡ t
!refl₁ {σ = σ} t = JRefl (λ y _ → Tm y σ) t

-- Commutation between term constructors and !_>₁_

!var : ∀ {Γ Δ σ} → (p : Γ ≡ Δ) → (v : Var Γ σ) → (! p >₁ var v) ≡ var (! p >₀ v)
!var {σ = σ} p v = J (λ _ q → (! q >₁ var v) ≡ var (! q >₀ v)) (!refl₁ (var v) ∙ sym (cong var (!refl₀ v))) p

!Λ : ∀ {Γ Δ σ τ} → (p : Γ ≡ Δ) → (t : Tm (Γ , σ) τ) → (! p >₁ Λ t) ≡ Λ (! cong (λ Θ → Θ , σ) p >₁ t)
!Λ {σ = σ} {τ = τ} p t = J (λ _ q → (! q >₁ Λ t) ≡ Λ (! cong (λ Θ → Θ , σ) q >₁ t)) (!refl₁ (Λ t) ∙ sym (cong Λ (!refl₁ t))) p

!app : ∀ {Γ Δ σ τ} → (p : Γ ≡ Δ) → (t₁ : Tm Γ (σ ⇒ τ)) → (t₂ : Tm Γ σ) → (! p >₁ app t₁ t₂) ≡ app (! p >₁ t₁) (! p >₁ t₂)
!app p t₁ t₂ = J (λ _ q → (! q >₁ app t₁ t₂) ≡ app (! q >₁ t₁) (! q >₁ t₂)) (!refl₁ (app t₁ t₂) ∙ sym (cong₂ app (!refl₁ t₁) (!refl₁ t₂))) p

-- Commutation between wkTm and !_>₁_

!wkTm : ∀ {Γ Δ σ τ} → (p : Γ ≡ Δ) → (u : Tm Γ τ) → (! cong (λ Θ → Θ , σ) p >₁ wkTm vz u) ≡ wkTm vz (! p >₁ u)
!wkTm {σ = σ} p u = J (λ _ q → (! cong (λ Θ → Θ , σ) q >₁ wkTm vz u) ≡ wkTm vz (! q >₁ u)) (!refl₁ (wkTm vz u) ∙ sym (cong (wkTm vz) (!refl₁ u))) p

-- Changing term inside !_>₁_

-- | note, when the proof merely relies on unifying terms based on some equality, we can use this trick
-- whereas, when it involves a coersion, we need to use J along with JRefl
!≡₁ : ∀ {Γ Δ σ} → (p : Γ ≡ Δ) → {t₁ t₂ : Tm Γ σ} → t₁ ≡ t₂ → (! p >₁ t₁) ≡ (! p >₁ t₂)
!≡₁ _ q rewrite ctop q = refl

-- But this is still probably nicer
!≡₁′ : ∀ {Γ Δ σ} → (p : Γ ≡ Δ) → {t₁ t₂ : Tm Γ σ} → t₁ ≡ t₂ → (! p >₁ t₁) ≡ (! p >₁ t₂)
!≡₁′ p q i = ! p >₁ q i


-- Here, we provide three different proofs of vsInj, using the ctop trick,
-- a projection function with congruence, and J. They all work equally well

vsInj : ∀ {τ Γ σ} → (i j : Var Γ σ) → vs {τ} i ≡ vs j → i ≡ j
vsInj i j p with ctop p
... | reflp = refl

vsInj′ : ∀ {τ Γ σ} → (i j : Var Γ σ) → vs {τ} i ≡ vs j → i ≡ j
vsInj′ i j p = cong (vp i) p
  where
    vp : ∀ {Γ σ τ} → Var Γ σ → Var (Γ , τ) σ → Var Γ σ
    vp y vz = y
    vp _ (vs x) = x

data ⊥ : Set where

vsInj′′ : ∀ {τ Γ σ} → (i j : Var Γ σ) → vs {τ} i ≡ vs j → i ≡ j
vsInj′′ i j p = J (λ{ (vs x) q → i ≡ x; vz q → ⊥ }) refl p


-- This is all we got to, but already, it should give a decent overview of a range of different techniques
-- that one can use to translate proofs to use path equality directly. In most cases, we see
-- that the translation while perhaps a bit technical and clunky does not require too much creativity
