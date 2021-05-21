{-# OPTIONS --cubical #-}

--------------------------------------------------------------------------------
-- The module implements:                                                     --
--   - a somewhat profitable experiment in defining terms modulo βη-≡ via something
--    resembling a set quotient.
--   - a demonstration of what happens when you don't use recursion principles
--   - note that this is very unfinished and a bit messy, since I abandoned
--     this code in favor of the isomorphism approach                         --
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

-- NOTE: I'm not sure how necessary it actually is to use Id 
open import Cubical.Foundations.Id as Id public hiding (_,_) renaming (subst to idSubst)

open import Cubical.Foundations.Prelude using () renaming (_≡⟨_⟩_ to _≡p⟨_⟩_; _∎ to _∎p)

cong = ap

infixr 40 _⇒_
infixl 30 _,_
infix 20 _∋_

-- We start off with a bunch of stuff copied from "Hereditary Substitution"
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
  → ((Γ - x) - y) ≡ ((Γ - (wkv x y)) - (rem x y))
conExc vz y = refl
conExc (vs x) vz = refl
conExc (vs {τ = τ} x) (vs y) = cong (λ Θ → Θ , τ) (conExc x y)


-- Changing the context in which a variable is typed

-- Note, due to cubical agda we can no longer pattern match on refl - instead we use J
!_>₀Ty : ∀ {Γ Δ σ} → Γ ≡ Δ → (Γ ∋ σ) ≡ (Δ ∋ σ)
!_>₀Ty {σ = σ} p = cong (λ Θ → Θ ∋ σ) p

!_>₀_ : ∀ {Γ Δ σ} → Γ ≡ Δ → Γ ∋ σ → Δ ∋ σ
! p >₀ v = J _ v p

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


-- Essentially just the normal STLC
-- This is called |Tm| in the paper

data PreTm : Con → Ty → Set where
    pvar : ∀ {Γ σ}
      → Γ ∋ σ
      → PreTm Γ σ

    plam : ∀  {Γ σ τ}
      → PreTm  (Γ , σ) τ
      → PreTm  Γ (σ ⇒ τ)

    papp : ∀  {Γ σ τ}
      → PreTm  Γ (σ ⇒ τ)
      → PreTm  Γ σ
      → PreTm  Γ τ

-- weakening defined on (pre-)terms
swkTm : ∀  {Γ σ τ}
  → (x : Γ ∋ σ)
  → PreTm  (Γ - x) τ
  → PreTm  Γ τ
swkTm x (pvar y) = pvar (wkv x y)
swkTm x (plam t) = plam (swkTm (vs x) t) 
swkTm x (papp t u) = papp (swkTm x t) (swkTm x u)

-- substitution defined on (pre-)terms
ssubst : ∀  {Γ σ τ}
  → PreTm  Γ τ
  → (x : Γ ∋ σ)
  → PreTm  (Γ - x) σ
  → PreTm  (Γ - x) τ
ssubst (pvar x) y u with eq y x
... | same = u
... | diff _ z = pvar z
ssubst (plam t) x u = plam (ssubst t (vs x) (swkTm vz u))
ssubst (papp t u) x v = papp (ssubst t x v) (ssubst u x v)

-- Changing the context in which a term is typed
!_>₁_ : ∀ {Γ Δ : Con} {σ : Ty}
  → (p : Γ ≡ Δ) → PreTm Γ σ → PreTm Δ σ
!_>₁_ {σ = σ} p v = J _ v p
-- transport (! p >₁Ty) v -- transp (λ i → (p i) ⊢ σ) i0 v


-- It's fair to assume that these are either proven in "Hereditary substitution" or that we can just prove them in a non-cubical context
postulate
  substComm : forall {σ Γ τ ρ} -> (t : PreTm Γ σ) -> (x : Γ ∋ τ) -> (u₁ : PreTm (Γ - x) τ) -> (y : (Γ - x) ∋ ρ) -> (u₂ : PreTm ((Γ - x) - y) ρ) -> (! (conExc x y) >₁ ((ssubst (ssubst t x u₁) y u₂))) ≡ ssubst (ssubst t (wkv x y) (swkTm (rem x y) (! conExc x y >₁ u₂))) (rem x y) (! conExc x y >₁ ssubst u₁ y u₂)

postulate 
  swkTmSubstExc : ∀ {Γ σ τ ρ}
    → (y : Γ ∋ σ)
    → (t : PreTm (Γ - y) τ)
    → (x : (Γ - y) ∋ ρ)
    → (u : PreTm ((Γ - y) - x) ρ)
    → (swkTm (rem y x) (! conExc y x >₁ (ssubst t x u))) ≡ (ssubst (swkTm y t) (wkv y x) (swkTm (rem y x) (! conExc y x >₁ u)))

postulate 
  wkPTmEta : ∀ {Γ τ σ ρ}
    → (x : Γ ∋ ρ)
    → (t : PreTm (Γ - x) (σ ⇒ τ))
    → swkTm x (plam (papp (swkTm vz t) (pvar vz))) ≡ swkTm x t

    
-- This is our type of terms modulo βη-equivalence, where the equivalence is build into
-- the type piecewise (as opposed to using a set quotient proper with inductively defined
-- βη-≡
-- In the paper, we call this type |QTm| (not to be confused with |QTm| in the isomorphism
-- section
data _⊢_ : Con → Ty → Set where

  pre : ∀ {Γ σ}
    → PreTm Γ σ
    → _⊢_ Γ σ

  congΛ : ∀ {Γ σ τ} {t t₁ : PreTm (Γ , σ) τ}
    → Path _ (pre t) (pre t₁)
    → Path _ (pre (plam t)) (pre (plam t₁))

  congApp : ∀  {Γ σ τ} {t t₁ : PreTm Γ (σ ⇒ τ)} {u u₁ : PreTm Γ σ}
    → Path _ (pre t) (pre t₁)
    → Path _ (pre u) (pre u₁)
    → Path _ (pre (papp t u)) (pre (papp t₁ u₁))
    
  beta : ∀ {Γ σ τ} (t : PreTm (Γ , σ) τ) (u : PreTm Γ σ)
    → Path _ (pre (papp (plam t) u)) (pre (ssubst t vz u))

  eta : ∀ {Γ σ τ} (t : PreTm Γ (σ ⇒ τ))
    → Path _ (pre (plam (papp (swkTm vz t) (pvar vz)))) (pre t)

  trunc : ∀ {Γ σ} → isSetPath (Γ ⊢ σ)


-- We're able to define weakening (albeit assuming a few postulates, which seam reasonable for now)
wkTm : ∀ {Γ σ τ}
  → (x : Γ ∋ σ)
  → (Γ - x) ⊢ τ
  → Γ ⊢ τ
wkTm x (pre t) = pre (swkTm x t)
wkTm x (congΛ p i) = congΛ (congPath (wkTm (vs x)) p) i
wkTm x (congApp p q i) = congApp (congPath (wkTm x) p) (congPath (wkTm x) q) i
wkTm x (beta t u i) = idToPath (pathToId ( beta (swkTm (vs x) t) (swkTm x u) ) ∙ ((ap pre (swkTmSubstExc (vs x) t vz u)) ⁻¹)) i
wkTm x (eta t i) = pre (idToPath (wkPTmEta x t) i)
wkTm x (trunc t u p q i j) = trunc (wkTm x t) (wkTm x u) (congPath (wkTm x) p) (congPath (wkTm x) q) i j

  
-- We can see that blindly splitting on cases without relying on a recursion
-- principle gets us in trouble pretty fast (also, there are issues with this passing
-- the termination checker for some reason - fairly likely to do with the with
-- abstraction bug)
{-# TERMINATING #-}
subst : ∀ {Γ σ τ}
  → Γ ⊢ τ
  → (x : Γ ∋ σ)
  → (Γ - x) ⊢ σ
  → (Γ - x) ⊢ τ 
subst (pre pt) y (pre pu) = pre (ssubst pt y pu)
subst (pre (pvar x)) y (congΛ p i) with eq y x
... | same = congΛ p i
... | diff .y z = pre (pvar z)
subst (pre (plam pt)) y (congΛ p i) = congΛ (congPath (subst (pre pt) (vs y)) (congΛ (congPath (wkTm (vs vz)) p))) i
subst (pre (papp pt pt₁)) y (congΛ p i) = congApp (congPath (subst (pre pt) y) (congΛ p)) (congPath (subst (pre pt₁) y) (congΛ p)) i
subst (pre (pvar x)) y (congApp p q i) with eq y x
... | same = congApp p q i
... | diff .y z = pre (pvar z)
subst (pre (plam pt)) y (congApp p q i) = congΛ (λ j → subst (pre pt) (vs y) (congApp (λ k → wkTm vz (p k)) (λ k → wkTm vz (q k)) j)) i
subst (pre (papp pt pt₁)) y (congApp p q i) = congApp (λ j → subst (pre pt) y (congApp p q j)) (λ j → subst (pre pt₁) y (congApp p q j)) i
subst (pre (pvar x)) y (beta pu pv i) with eq y x
... | same = beta pu pv i
... | diff .y z = pre (pvar z)
subst (pre (plam pt)) y (beta pu pv i) = congΛ (λ j → subst (pre pt) (vs y) (compPath (beta (swkTm (vs vz) pu) (swkTm vz pv)) {!idToPath (cong pre (swkTmSubstExc ? ? ? ?))!} j)) i
subst (pre (papp pt pt₁)) y (beta pu pv i) = congApp (congPath (subst (pre pt) y) (beta pu pv)) (congPath (subst (pre pt₁) y) (beta pu pv)) i
subst (pre x) y (eta t x₁) = {!!}
subst (pre x) y (trunc u u₁ p p₁ i i₁) = trunc (subst (pre x) y u) (subst (pre x) y u₁) (λ j → subst (pre x) y (p j)) (λ j → subst (pre x) y (p₁ j)) i i₁ 
subst (congΛ p i) y (pre t) = congΛ (λ j → subst (p j) (vs y) (wkTm vz (pre t))) i
subst (congΛ p i) y (congΛ q j) = {!trunc (pre (plam (ssubst (vs ?) (plam (swkTm (vs vz) ?))))) ? ? ? i j!}
subst (congΛ p i) y (congApp x x₁ x₂) = {!!}
subst (congΛ p i) y (beta t u x) = {!!}
subst (congΛ p i) y (eta t x) = {!!}
subst (congΛ p i) y (trunc u u₁ x y₁ i₁ i₂) = {!!}
subst (congApp x x₁ x₂) y u = {!!}
subst (beta t u₁ x) y u = {!!}
subst (eta t x) y u = {!!}
subst (trunc t t₁ p p₁ i i₁) y u = trunc (subst t y u) (subst t₁ y u) (congPath (λ v → subst v y u) p) (congPath (λ v → subst v y u) p₁) i i₁

-- A bunch of older attempts, demonstrating the difficulty of this approach (especially if
-- you don't really have an idea of what you're doing, as I did when I was writing this at first)
{-
-- subst with trunc
subst : ∀ {Γ σ τ}
  → Γ ⊢ τ
  → (x : Γ ∋ σ)
  → (Γ - x) ⊢ σ
  → (Γ - x) ⊢ τ 
subst (pre pt) y (pre pu) = pre (ssubst pt y pu)
subst (pre (pvar x)) y (beta pu pv i) = {!!}
subst (pre (plam pt)) y (beta pu pv i) = (
     pre (plam (ssubst pt (vs y) (papp (plam (swkTm (vs vz) pu)) (swkTm vz pv))))
   ≡p⟨ {!!} ⟩
     
     pre (plam (ssubst pt (vs y) (swkTm vz (ssubst pu vz pv))))
 ∎p) i
subst (pre (papp pt pt₁)) y (beta pu pv i) = {!!}
subst (pre x) y (eta t x₁) = {!!}
subst (pre pt) y (trunc u u₁ p q i j) = trunc (subst (pre pt) y u ) (subst (pre pt) y u₁) (congPath (subst (pre pt) y) p) (congPath (subst (pre pt) y) q) i j
subst (beta pt pu i) y (pre pv) = (
    pre (papp (plam (ssubst pt (vs y) (swkTm vz pv))) (ssubst pu y pv))
  ≡p⟨ beta (ssubst pt (vs y) (swkTm vz pv)) (ssubst pu y pv) ⟩
    pre (ssubst (ssubst pt (vs y) (swkTm vz pv)) vz (ssubst pu y pv))
  ≡p⟨ congPath pre (idToPath ((substComm pt vz pu y pv) ⁻¹)) ⟩
    pre (ssubst (ssubst pt vz pu) y pv)
  ∎p) i
subst (beta pt pu i) y (beta pt₁ pu₁ j) = {!!} 
subst (beta pt pu i) y (eta pv j) = trunc {!!} {!!} {!!} {!!} i j
subst (beta pt pu i) y (trunc pv pv₁ p q j k) = trunc {!!} {!!} {!!} {!!} j k
subst (eta t x) y u = {!!}
subst (trunc pt pt₁ p q i j) y u = trunc (subst pt y u) (subst pt₁ y u) (congPath (λ t → subst t y u) p) (congPath (λ t → subst t y u) q) i j
-}
{-
subst (pre pt) y (pre pu) = pre (ssubst pt y pu)
subst (pre x) y (beta t u x₁) = {!!}
subst (pre x) y (eta t x₁) = {!!}
subst (beta pt pu i) y (pre pv) = (
    pre (papp (plam (ssubst pt (vs y) (swkTm vz pv))) (ssubst pu y pv))
  ≡p⟨ beta (ssubst pt (vs y) (swkTm vz pv)) (ssubst pu y pv) ⟩
    pre (ssubst (ssubst pt (vs y) (swkTm vz pv)) vz (ssubst pu y pv))
  ≡p⟨ congPath pre (idToPath ((substComm pt vz pu y pv) ⁻¹)) ⟩
    pre (ssubst (ssubst pt vz pu) y pv)
  ∎p) i
subst (beta pt pu i) y (beta pt₁ pu₁ j) = {!!}
subst (beta pt pu i) y (eta t x) = {!!}
subst (eta t x) y u = {!!}
-}
{-
subst (pre pt) y (pre pu) = pre (ssubst pt y pu)
subst (beta (pvar x) pu i) y (pre pv) = {!!}
subst (beta (plam pt) pu i) y (pre pv) = (
  pre (papp (plam (plam (ssubst pt (vs (vs y)) (swkTm vz (swkTm vz pv))))) (ssubst pu y pv))
  ≡p⟨ beta (plam (ssubst pt (vs (vs y)) (swkTm vz (swkTm vz pv)))) (ssubst pu y pv) ⟩
    pre (ssubst (plam (ssubst pt (vs (vs y)) (swkTm vz (swkTm vz pv)))) vz (ssubst pu y pv))
  ≡p⟨ reflPath ⟩
    pre (plam (ssubst (ssubst pt (vs (vs y)) (swkTm vz (swkTm vz pv))) (vs vz) (swkTm vz (ssubst pu y pv))))
  ≡p⟨ {!!} ⟩
    pre (plam (ssubst (ssubst pt (vs vz) (swkTm vz pu)) (vs y) (swkTm vz pv)))
  ∎p
  ) i
subst (beta (papp pt pt₁) pu i) y (pre pv) = {!!}
subst (eta t i) y (pre pu) = pre (ssubst {!!} y pu)
subst (pre pt) y (beta pu pv i) = (
    pre (ssubst pt y (papp (plam pu) pv))
  ≡p⟨ symPath (substPreExc pt y (papp (plam pu) pv)) ⟩
    subst (pre pt) y (pre (papp (plam pu) pv))
  ≡p⟨ {!!} ⟩
    subst (pre pt) y (pre (ssubst pu vz pv))
  ≡p⟨ {!!} ⟩
    pre (ssubst pt y (ssubst pu vz pv))
  ∎p) i
subst (beta t u₁ x₁) y (beta t₁ u x) = {!!}
subst (eta t x₁) y (beta t₁ u x) = {!!}
subst (pre pt) y (eta t₁ x) = {!!}
subst (beta t u x₁) y (eta t₁ x) = {!!}
subst (eta t x₁) y (eta t₁ x) = {!!}
-}
