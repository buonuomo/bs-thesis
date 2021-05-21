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

    -- Modifications: Copyright Noah Goodman, 2021

module lemmas1 where


open import hsubst
open import gvar

open import Relation.Binary.PropositionalEquality renaming (subst to substP)
open ≡-Reasoning


-- Proofs that involve with

substSame2 : ∀ {Γ σ τ} → (x : Var Γ σ) → eq x x ≡ same → eq (vs {τ} x) (vs x) ≡ same
substSame2 x p with eq x x  
substSame2 x refl | same = refl


substSame3 : ∀ {Γ σ} → (x : Var Γ σ) → eq x x ≡ same
substSame3 vz = refl
substSame3 (vs x) = substSame2 x (substSame3 x)


substDiff2 : ∀ {Γ σ τ ρ} → (x : Var Γ σ) → (y : Var (Γ - x) τ) → eq x (wkv x y) ≡ diff x y → eq (vs {ρ} x) (vs (wkv x y)) ≡ diff (vs x) (vs y)
substDiff2 x y p with eq x (wkv x y)
substDiff2 x y refl | .(diff x y) = refl


substDiff3 : ∀ {Γ σ τ} → (x : Var Γ σ) → (y : Var (Γ - x) τ) → eq x (wkv x y) ≡ diff x y
substDiff3 vz y = refl
substDiff3 (vs x) vz = refl
substDiff3 (vs x) (vs y) = substDiff2 x y (substDiff3 x y)


-- Changing the context in which a variable is typed

!_>₀_ : ∀ {Γ Δ σ} → Γ ≡ Δ → Var Γ σ → Var Δ σ
! refl >₀ v = v

-- We can do the same for genvars

!_>g_ : ∀ {Γ Δ σ} → Γ ≡ Δ → GenVar Γ σ → GenVar Δ σ 
! refl >g v = v


-- Commutation between var constructors and !_>₀_
!vz : ∀ {Γ Δ σ} → (p : Γ ≡ Δ) → ! cong (λ Θ → Θ , σ) p >₀ vz ≡ vz
!vz refl = refl

!vs : ∀ {Γ Δ σ τ} → (p : Γ ≡ Δ) → (x : Var Γ τ) → ! cong (λ Θ → Θ , σ) p >₀ (vs x) ≡ vs (! p >₀ x)
!vs refl _ = refl


-- commutation between gvz and !_>g_

!gvz : ∀ {Γ Δ σ τ} (p : Γ ≡ Δ) (q : τ ≡ σ) → ! cong (λ Θ → Θ , σ) p >g gvz q ≡ gvz q
!gvz refl q = refl

--  commutation between _>g_, _>₀_, and genvar isomorphism

!gv : ∀ {Γ Δ σ} (x : GenVar Γ σ) (p : Γ ≡ Δ) → ! p >₀ (gv→v x) ≡ gv→v (! p >g x)
!gv x refl = refl


-- Another commutation

!! : ∀ {Γ Δ σ} → (x : Var Γ σ) → (y : Var Δ σ) → (p : Γ ≡ Δ) → x ≡ ! sym p >₀ y → y ≡ ! p >₀ x
!! x .x refl refl = refl


-- Changing the proof

!p : ∀ {Γ Δ σ} → (v : Var Γ σ) → (p q : Γ ≡ Δ) → p ≡ q → ! p >₀ v ≡ ! q >₀ v
!p v p .p refl = refl


-- Changing the context in which a term is typed
!_>₁_ : ∀ {Γ Δ σ} → Γ ≡ Δ → Tm Γ σ → Tm Δ σ
! refl >₁ t = t


-- Commutation between term constructors and !_>₁_

!var : ∀ {Γ Δ σ} → (p : Γ ≡ Δ) → (v : Var Γ σ) → ! p >₁ var v ≡ var (! p >₀ v)
!var refl _ = refl


!Λ : ∀ {Γ Δ σ τ} → (p : Γ ≡ Δ) → (t : Tm (Γ , σ) τ) → ! p >₁ Λ t ≡ Λ (! cong (λ Θ → Θ , σ) p >₁ t)
!Λ refl _ = refl


!app : ∀ {Γ Δ σ τ} → (p : Γ ≡ Δ) → (t₁ : Tm Γ (σ ⇒ τ)) → (t₂ : Tm Γ σ) → ! p >₁ app t₁ t₂ ≡ app (! p >₁ t₁) (! p >₁ t₂)
!app refl _ _ = refl


-- Commutation between wkTm and !_>₁_

!wkTm : ∀ {Γ Δ σ τ} → (p : Γ ≡ Δ) → (u : Tm Γ τ) → ! cong (λ Θ → Θ , σ) p >₁ wkTm vz u ≡ wkTm vz (! p >₁ u)
!wkTm refl _ = refl


-- Changing term inside !_>₁_

!≡₁ : ∀ {Γ Δ σ} → (p : Γ ≡ Δ) → {t₁ t₂ : Tm Γ σ} → t₁ ≡ t₂ → ! p >₁ t₁ ≡ ! p >₁ t₂
!≡₁ _ refl = refl


-- Changing the context in which a normal form is typed

!_>₂_ : ∀ {Γ Δ σ} → Γ ≡ Δ → Nf Γ σ → Nf Δ σ
! refl >₂ u = u


-- Changing the context in which a Sp is typed

!_>₃_ : ∀ {Γ Δ σ τ} → Γ ≡ Δ → Sp Γ σ τ → Sp Δ σ τ
! refl >₃ us = us


-- Commutation between normal forms constructors and !_>₂_

!λn : ∀ {Γ Δ σ τ} → (p : Γ ≡ Δ) → (u : Nf (Γ , σ) τ) → ! p >₂ λn u ≡ λn (! cong (λ Θ → Θ , σ) p >₂ u)
!λn refl _ = refl


!ne : ∀ {Γ Δ σ} → (p : Γ ≡ Δ) → (x : Var Γ σ) → (ts : Sp Γ σ ○) → ! p >₂ ne (x , ts) ≡ ne ((! p >₀ x) , (! p >₃ ts))
!ne refl _ _ = refl


-- Commutation between functions and !_>₂_

!wkNf : ∀ {Γ Δ σ τ} → (p : Γ ≡ Δ) → (u : Nf Γ τ) → ! cong (λ Θ → Θ , σ) p >₂ wkNf vz u ≡ wkNf vz (! p >₂ u)
!wkNf refl _ = refl


!appNf : ∀ {Γ Δ σ τ} → (p : Γ ≡ Δ) → (u : Nf Γ σ) → (ts : Sp Γ σ τ) → ! p >₂ (u ◇ ts) ≡ (! p >₂ u) ◇ (! p >₃ ts)
!appNf refl _ _ = refl


-- Changing normal form inside !_>₂_

!≡₂ : ∀ {Γ Δ σ} → (p : Γ ≡ Δ) → {t₁ t₂ : Nf Γ σ} → t₁ ≡ t₂ → ! p >₂ t₁ ≡ ! p >₂ t₂
!≡₂ _ refl = refl


-- Commutation between Sp constructor and !_>₃_

!ε : ∀ {Γ Δ σ} → (p : Γ ≡ Δ) → ! p >₃ ε {σ} ≡ ε
!ε refl = refl


!, : ∀ {Γ Δ σ τ ρ} → (p : Γ ≡ Δ) → (t : Nf Γ σ) → (ts : Sp Γ τ ρ) → (! p >₃ (t , ts)) ≡ ((! p >₂ t) , (! p >₃ ts))
!, refl _ _ = refl


-- Injectivity of vs and wkv

vsInj : ∀ {τ Γ σ} → (i j : Var Γ σ) → vs {τ} i ≡ vs j → i ≡ j
vsInj i .i refl = refl


-- NOTE: the required lemma is trivial on generalized variables
wkvInjLem′ : ∀ {Γ σ τ ρ} (k : Var Γ σ) (j : GenVar ((Γ - k) , τ) ρ) (p : ρ ≡ τ) → gvz p ≡ wkvg (vs k) j → gvz p ≡ j
wkvInjLem′ k (gvz p) .p refl = refl

-- And then we just need to transport it along the isomorphism so it works on normal variables
wkvInjLem : ∀ {Γ σ τ} (k : Var Γ σ) (j : Var ((Γ - k), τ) τ) → vz ≡ wkv (vs k) j → vz ≡ j
wkvInjLem k j p =
  let
    q = cong v→gv p
    q′ = wkvInjLem′ k (v→gv j) refl (trans q (sym (wkGv (vs k) j)))
    q′′ = cong gv→v q′
  in
    trans q′′ (v→gv→v j)

-- Note, the wkvInjLem case required an interesting approach
wkvInj : ∀ {Γ σ τ} → (k : Var Γ σ) → (i j : Var (Γ - k) τ) → wkv k i ≡ wkv k j → i ≡ j
wkvInj vz vz .vz refl = refl
wkvInj vz (vs i) (vs j) p = vsInj (vs i) (vs j) p
wkvInj (vs k) vz j p = wkvInjLem k j p
wkvInj (vs k) (vs i) (vs j) p = cong vs (wkvInj k i j (vsInj (wkv k i) (wkv k j) p))

-- Basic lemma

reflExtConSym : ∀ {Γ Δ : Con} → (σ : Ty) → (p : Γ ≡ Δ) → sym {_} {Con} (cong (λ Θ → Θ , σ) p) ≡ cong (λ Θ → Θ , σ) (sym p)
reflExtConSym _ refl = refl


-- A predicate asserting that two variables in the same context follow one another

data onediff : ∀ {Γ σ τ} → Var Γ σ → Var Γ τ → Set where
  odz : ∀ {Γ σ τ} → onediff {(Γ , σ) , τ} vz (vs vz)
  ods : ∀ {Γ σ τ ρ} → (x : Var Γ σ) → (y : Var Γ τ) → onediff x y → onediff (vs {ρ} x) (vs y)


-- Properties about onediff

onediffMinus : ∀ {Γ σ} → (i j : Var Γ σ) → onediff j i → Γ - i ≡ Γ - j
onediffMinus .(vs vz) .vz odz = refl
onediffMinus {_ , τ} .(vs i) .(vs j) (ods j i p) = cong (λ Θ → Θ , τ) (onediffMinus i j p)


vsWkvEq : ∀ {Γ σ τ} → (z x : Var (Γ , τ) σ) → vs z ≡ wkv (vs vz) x → z ≡ x
vsWkvEq z vz ()
vsWkvEq z (vs x) p = vsInj z (vs x) p


mutual

  -- Again, we play the same trick with generalized variables, defining a generalized lemma
  onediffWkvAuxLem′ : ∀ {ρ Γ σ τ} → (i j : Var Γ σ) → (x : GenVar ((Γ - i) , ρ) τ) → (q : onediff j i) → (p : τ ≡ ρ) → gvz p ≡ wkvg (vs i) x → gvz p ≡ (! cong (λ Θ → Θ , ρ) (onediffMinus i j q) >g x)
  onediffWkvAuxLem′ i j (gvz p) q .p refl = sym (!gvz (onediffMinus i j q) p)

  -- and then bringing it back across the isomorphism to prove what we want
  onediffWkvAuxLem : ∀ {ρ Γ σ} → (i j : Var Γ σ) → (x : Var ((Γ - i) , ρ) ρ) → (q : onediff j i) → vz ≡ wkv (vs i) x → vz ≡ (! cong (λ Θ → Θ , ρ) (onediffMinus i j q) >₀ x)
  onediffWkvAuxLem {ρ} i j x q h =
    let
      gh = cong v→gv h
      r = onediffWkvAuxLem′ i j (v→gv x) q refl (trans gh (sym (wkGv (vs i) x)))
      r′ = cong gv→v r
    in trans r′ (trans (sym (!gv (v→gv x) (cong (λ Θ → Θ , ρ) (onediffMinus i j q)))) (cong (λ z → (! cong (λ Θ → Θ , ρ) (onediffMinus i j q) >₀ z)) (v→gv→v x)))

  onediffWkvAux : ∀ {ρ Γ σ τ} → (i j : Var Γ σ) → (z : Var ((Γ - j) , ρ) τ) → (x : Var ((Γ - i) , ρ) τ) → (q : onediff j i) → wkv (vs j) z ≡ wkv (vs i) x → z ≡ ! cong (λ Θ → Θ , ρ) (onediffMinus i j q) >₀ x
  onediffWkvAux i j vz x q h = onediffWkvAuxLem i j x q h
  onediffWkvAux {ρ} i j (vs z) (vs x) q h =
      vs z
    ≡⟨ cong vs (onediffWkv i j z x q (vsInj (wkv j z) (wkv i x) h)) ⟩
      vs (! onediffMinus i j q >₀ x)
    ≡⟨ sym (!vs (onediffMinus i j q) x) ⟩
      ! cong (λ Θ → Θ , ρ) (onediffMinus i j q) >₀ (vs x)
    ∎


  onediffWkv : ∀ {σ Γ τ} → (i j : Var Γ σ) → (z : Var (Γ - j) τ) → (x : Var (Γ - i) τ) → (p : onediff j i) → wkv j z ≡ wkv i x → z ≡ ! onediffMinus i j p >₀ x
  onediffWkv .(vs vz) .vz z x odz h = vsWkvEq z x h
  onediffWkv .(vs i) .(vs j) z x (ods j i q) h = onediffWkvAux i j z x q h
