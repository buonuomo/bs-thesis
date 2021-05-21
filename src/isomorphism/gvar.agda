{-# OPTIONS --cubical #-}
--------------------------------------------------------------------------------
-- This module defines "Generalized variables" or GVar's that allow some proofs --
-- that pattern match on variables to go through without axiom K                --
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

    -- Copyright Noah Goodman, 2021

open import Relation.Binary.PropositionalEquality hiding (subst)

open import hsubst

-- Type of generalized variables, in order to allow certain proofs to go through without K
data GenVar : Con → Ty → Set where
  gvz : ∀ {Γ σ τ} → (σ ≡ τ) → GenVar (Γ , τ) σ 
  gvs : ∀ {τ Γ σ} → GenVar Γ σ → GenVar (Γ , τ) σ


-- generalized variables are isomorphic to normal variables

gv→v : ∀ {Γ σ} → GenVar Γ σ → Var Γ σ
gv→v (gvz refl) = vz
gv→v (gvs x) = vs (gv→v x)

v→gv : ∀ {Γ σ} → Var Γ σ → GenVar Γ σ
v→gv vz = gvz refl
v→gv (vs x) = gvs (v→gv x)

v→gv→v : ∀ {Γ σ} (x : Var Γ σ) → gv→v (v→gv x) ≡ x
v→gv→v vz = refl
v→gv→v (vs x) = cong vs (v→gv→v x)

gv→v→gv : ∀ {Γ σ} (gx : GenVar Γ σ) → v→gv (gv→v gx) ≡ gx
gv→v→gv (gvz refl) = refl
gv→v→gv (gvs gx) = cong gvs (gv→v→gv gx)


-- Weakening for generalized variables

wkvg : ∀ {Γ σ τ} → (x : Var Γ σ) → GenVar (Γ - x) τ → GenVar Γ τ
wkvg vz gx = gvs gx
wkvg (vs x) (gvz p) = gvz p
wkvg (vs x) (gvs gx) = gvs (wkvg x gx)


-- Weakening on genvars's and normal vars commute with the isomorphism

gvWk : ∀ {Γ σ τ} (k : Var Γ σ) (gv : GenVar (Γ - k) τ) → wkv k (gv→v gv) ≡ gv→v (wkvg k gv)
gvWk vz gv = refl
gvWk (vs k) (gvz refl) = refl
gvWk (vs k) (gvs gv) = cong vs (gvWk k gv)

wkGv : ∀ {Γ σ τ} (k : Var Γ σ) (j : Var (Γ - k) τ) → wkvg k (v→gv j) ≡ v→gv (wkv k j)
wkGv vz j = refl
wkGv (vs k) vz = refl
wkGv (vs k) (vs j) = cong gvs (wkGv k j)
