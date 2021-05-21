{-# OPTIONS --cubical #-}
--------------------------------------------------------------------------------
-- The module implements:                                                     --
--   - the isomorphism between normal forms and terms modules βη-≡ as an HIT  --
--   - several examples of stuff we can do with these quotiented terms        --
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

module iso where

open import hsubst
open import lemmas1
open import proofs

open import Cubical.Foundations.Prelude renaming (subst to substP)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Data.Equality
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Unit
open import Cubical.Data.Maybe using (Maybe; just; nothing; just-inj)
open import Cubical.HITs.SetQuotients
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Relation.Nullary


-- Lemma that a variable x is not equal to a different variable from a context that
-- doesn't have x in it
x≢wkvx : ∀ {Γ σ} (x : Var Γ σ) (y : Var (Γ - x) σ) → ¬ x ≡ wkv x y
x≢wkvx vz y p with ctop p
... | ()
x≢wkvx (vs x) vz p with ctop p
... | ()
x≢wkvx (vs x) (vs y) p = x≢wkvx x y (ptoc (vsInj x (wkv x y) (ctop p)))

-- large elimination out of |Ty|
ty→Type : Ty → Type
ty→Type ○ = Unit
ty→Type (_ ⇒ _) = ⊥

-- Proof that Ty is discrete - this helps us later define some projection
-- functions in our proof that normal forms are discrete
-- We use large elimination to discriminate between the two different type constructors
-- I suppose this technique isn't strictly necessary because we could also use the ctop trick,
-- but in this case, I think it's cleaner
discreteTy : Discrete Ty
discreteTy ○ ○ = yes refl
discreteTy ○ (σ ⇒ τ) = no (λ p → transport (cong ty→Type p) tt)
discreteTy (σ ⇒ τ) ○ = no (λ p → transport (cong ty→Type (sym p)) tt)
discreteTy (σ ⇒ σ₁) (τ ⇒ τ₁) with discreteTy σ τ
... | no ¬p = no (λ p → ¬p (cong fstTy p))
  where
    fstTy : Ty → Ty
    fstTy ○ = ○
    fstTy (σ ⇒ _) = σ
... | yes p with discreteTy σ₁ τ₁
...   | no ¬q = no (λ q → ¬q (cong sndTy q))
  where
    sndTy : Ty → Ty
    sndTy ○ = ○
    sndTy (_ ⇒ τ) = τ
...   | yes q = yes (cong₂ _⇒_ p q)

-- |Ty| is discrete, ie. it has decidable equality
tySet : isSet Ty
tySet = Discrete→isSet discreteTy

-- Pushing with abstractions to the limit
-- first, we explicitly construct the proof of equality between a type and itself as given by the
-- decision procedure
discreteTyRefl : ∀ σ → Σ[ p ∈ σ ≡ σ ](discreteTy σ σ ≡ yes p)
discreteTyRefl ○ = refl , refl
discreteTyRefl (σ ⇒ σ₁) with discreteTy σ σ | discreteTyRefl σ 
... | _ | p , pRefl  with ctop pRefl
discreteTyRefl (σ ⇒ σ₁) | .(yes p) | p , pRefl | reflp with discreteTy σ₁ σ₁ | discreteTyRefl σ₁
discreteTyRefl (σ ⇒ σ₁) | .(yes p) | p , pRefl | reflp | _ | q , qRefl with ctop qRefl
discreteTyRefl (σ ⇒ σ₁) | .(yes p) | p , pRefl | reflp | _ | q , qRefl | reflp = (cong₂ _⇒_ p q) , refl

-- As we'd expect, our decision procedure for type equality says that a type is equal to itself
-- moreover, the proof of this equality is |refl|, which we have because Ty is an h-set
discreteTyRefl′ : ∀ σ → discreteTy σ σ ≡ yes refl
discreteTyRefl′ σ with discreteTyRefl σ
... | p , dec-σ≡yesp = dec-σ≡yesp ∙ cong yes (tySet _ _ p refl)

-- We show that normal forms have deciable equality
discreteNf : ∀ {Γ σ} → Discrete (Nf Γ σ)
discreteNe : ∀ {Γ} → Discrete (Ne Γ ○)
discreteSp : ∀ {Γ σ} → Discrete (Sp Γ σ ○)

discreteNf (λn nt) (λn nu) with discreteNf nt nu
... | yes p = yes (cong λn p)
... | no ¬p = no contr
  where
    contr : ¬ λn nt ≡ λn nu
    contr q with ctop q
    ... | reflp = ¬p refl
discreteNf (ne net) (ne neu) with discreteNe net neu
... | yes p = yes (cong ne p)
... | no ¬p = no contr
  where
    contr : ¬ ne net ≡ ne neu
    contr q with ctop q
    ... | reflp = ¬p refl

-- In both cases, we want to project out an subexpression from a |Ne Γ ○|, but the only constructor for
-- neutral terms is indexed by a type that does not parametrize the type of neutral terms, meaning
-- that we can't write the projection functions in the way we'd like, because we can't know, in general,
-- what the type of the subexpressions of an arbitrary neutral term will be from the type of that term alone.
-- But we do know the specific type of the subexpressions of the individual neutral terms we're interested, so
-- we can write specialized partial projection functions that only project out of neutral terms whose subexpressions
-- have the same types as the specific type of the terms we're dealing with
discreteNe {Γ} (_,_ {σ = σ} x spt) (y , spu) with eq x y
... | diff {τ = σ₁} .x z = no contr
  where
    π₁ : ∀ {Γ} → Ne Γ ○ → Maybe (Var Γ σ)
    π₁ {Δ} (_,_ {σ = τ} z _) with discreteTy σ τ
    ... | no ¬p = nothing
    ... | yes p = just (substP (λ v → Var Δ v) (sym p) z)

    -- project out the other type from a neutral expression
    πₜ : ∀ {Γ} → Ne Γ ○ → Ty
    πₜ (_,_ {σ = σ} _ _) = σ
    
    contr : ¬ (x , spt) ≡ (wkv x z , spu)
    contr r with discreteTy σ σ₁
    contr r | no ¬q = ¬q (cong πₜ r)
    contr r | yes q with ctop q
    contr r | yes q | reflp with discreteTy σ σ | discreteTyRefl′ σ | cong π₁ r
    contr r | yes q | reflp | pp | ppr | f with ctop ppr
    contr r | yes q | reflp | .(yes (λ _ → σ)) | ppr | f | reflp with (λ i → just (transportRefl x (~ i))) ∙∙ f ∙∙ (λ i → just (transportRefl (wkv x z) i))
    ... | h = x≢wkvx _ _ (just-inj _ _ h)

... | same with discreteSp spt spu
...   | yes q = yes (cong (x ,_) q)
...   | no ¬q = no contr
        where
          π₂ : ∀ {Δ τ} → Ne Δ τ → Maybe (Sp Δ σ τ)
          π₂ {Δ} {τ} (_,_ {σ = σ′} _ s) with discreteTy σ σ′
          ... | no ¬p = nothing
          ... | yes p = just (substP (λ z → Sp Δ z τ) (sym p) s)

          contr : ¬ (x , spt) ≡ (y , spu)
          contr r with discreteTy σ σ | ctop (discreteTyRefl′ σ) | cong π₂ r
          ... | .(yes (λ _ → σ)) | reflp | f with
            ctop ((λ i → just (transportRefl spt (~ i))) ∙∙ f ∙∙ (λ i → just (transportRefl spu i)))
          ... | reflp = ¬q refl

discreteSp ε ε = yes refl
discreteSp (nft , spt) (nfu , spu) with discreteNf nft nfu
... | no ¬p = no (λ r → ¬p (cong π₁ r))
  where
    π₁ : ∀ {Γ τ σ} → Sp Γ (τ ⇒ σ) ○ → Nf Γ τ
    π₁ (nfw , _) = nfw
... | yes p with discreteSp spt spu
...   | no ¬q = no (λ r → ¬q (cong π₂ r))
  where
    π₂ : ∀ {Γ τ σ} → Sp Γ (τ ⇒ σ) ○ → Sp Γ σ ○
    π₂ (_ , spw) = spw
...   | yes q = yes (cong₂ _,_ p q)

-- Nf Γ σ is an h-set, using the fact that if a type is discrete (has decidable equality), it is an h-set
isSetNf : ∀ {Γ σ} → isSet (Nf Γ σ)
isSetNf = Discrete→isSet discreteNf

-- In order to go from quotients to normal forms, we had to show that normalization respects the βη-equality
-- which just requires soundness, but in order to show that a quotient term is equal to itself normalized
-- (ie. that nf is a right inverse of embedding a normal form into QTm ), we need to show that our proof of
-- this fact (which uses completeness) also respects βη equivalence, ie. that if two terms a, b are βη-≡, then
-- the proofs on both of these terms that nf is a right inverse are themselves equal to each other. We'd like to use
-- the fact that we are dealing with terms in a set quotient, but the problem is that the two proofs we need to prove
-- equal are not paths between the same terms. Rather, we have a dependent path between these two proofs, in which we
-- transport the type along the path induced by a βη-≡ b. What we can do; however, is fill in the square between the two
-- paths we want to prove equal and then show that one of those paths is equal to what we want using set truncation

-- This is a bit older version of the proof, manually using doubleCompPath-filler as opposed
-- to the nicer compPathL→PathP.
{-
rightInvLem : ∀ {Γ σ} (a b : Tm Γ σ) (r : a βη-≡ b)
  → PathP (λ i → [ ⌈ ptoc (soundness r) i ⌉ ] ≡ eq/ a b r i)
          (eq/ ⌈ nf a ⌉ a (completeness a))
          (eq/ ⌈ nf b ⌉ b (completeness b))
rightInvLem {Γ} {σ} a b r =
  let
    bot   = eq/ ⌈ nf a ⌉ a (completeness a)
    top   = eq/ ⌈ nf b ⌉ b (completeness b)
    right = eq/ a b r 
    left  = cong (λ z → [ ⌈ z ⌉ ]) (ptoc (soundness r))

    y = doubleCompPath-filler (sym left) bot right 
    
    lem : sym left ∙ bot ∙ right ≡ top
    lem = squash/ _ _ (sym left ∙ bot ∙ right) top
  in
    substP (λ z → PathP (λ i → [ ⌈ ptoc (soundness r) i ⌉ ] ≡ eq/ a b r i) (eq/ ⌈ nf a ⌉ a (completeness a)) z) lem y
-}

rightInvLem : ∀ {Γ σ} (a b : Tm Γ σ) (r : a βη-≡ b)
  → PathP (λ i → [ ⌈ ptoc (soundness r) i ⌉ ] ≡ eq/ a b r i)
          (eq/ ⌈ nf a ⌉ a (completeness a))
          (eq/ ⌈ nf b ⌉ b (completeness b))
rightInvLem {Γ} {σ} a b r =
  let
    bot   = eq/ ⌈ nf a ⌉ a (completeness a)
    top   = eq/ ⌈ nf b ⌉ b (completeness b)
    right = eq/ a b r 
    left  = (λ i → [ ⌈ ptoc (soundness r) i ⌉ ])
  in
    compPathL→PathP (squash/ _ _ (sym left ∙ bot ∙ right) top)

-- Prove the isomorphism using soundness/completeness of normalization + new stuff we've
-- defined above that allows us to work with the quotients
quotientIso : ∀ {Γ σ} → Iso (Nf Γ σ) (Tm Γ σ / _βη-≡_)
Iso.fun quotientIso nt = [ ⌈ nt ⌉ ]
Iso.inv quotientIso t = rec isSetNf nf (λ t u r → ptoc (soundness r)) t
Iso.rightInv quotientIso t =
  elim {B = λ u → [ ⌈ Iso.inv quotientIso u ⌉ ] ≡ u}
       (λ u → isOfHLevelPath 2 squash/ [ ⌈ Iso.inv quotientIso u ⌉ ] u )
       (λ u → eq/ _ _ (completeness u))
       rightInvLem
       t
Iso.leftInv quotientIso nt = ptoc (stability nt)

-- The equality we're after

Nf≡Tm/βη : ∀ {Γ σ} → Nf Γ σ ≡ (Tm Γ σ / _βη-≡_)
Nf≡Tm/βη = ua (isoToEquiv quotientIso)

QTm : Con → Ty → Type
QTm Γ σ = Tm Γ σ / _βη-≡_


-- A few simple conversions

QTm≡→βη : ∀ {Γ σ} (t u : Tm Γ σ) → (_≡_ {A = QTm Γ σ} [ t ] [ u ]) → t βη-≡ u
QTm≡→βη t u p = convertnf t u (ctop (cong (Iso.inv quotientIso) p))

βη→Nf≡ : ∀ {Γ σ} (t u : Nf Γ σ) → ⌈ t ⌉ βη-≡ ⌈ u ⌉ → t ≡ u
βη→Nf≡ t u p =
  let q = cong (Iso.inv quotientIso) (eq/ _ _ p)
   in sym (Iso.leftInv quotientIso t) ∙∙ q ∙∙ Iso.leftInv quotientIso u


-- Weakening and substitution defined on QTm's

quotWk : ∀ {Γ σ τ} → (x : Var Γ σ) → QTm (Γ - x) τ → QTm Γ τ 
quotWk {Γ} {σ} {τ} x = transport (λ i → Nf≡Tm/βη {Γ - x} {τ} i → Nf≡Tm/βη {Γ} {τ} i) (wkNf {σ} {Γ} {τ} x)

quotSubst : ∀ {Γ σ τ} → QTm Γ σ → (x : Var Γ τ) → QTm (Γ - x) τ → QTm (Γ - x) σ
quotSubst {Γ} {σ} {τ} = transport (λ i → Nf≡Tm/βη {Γ} {σ} i → (x : Var Γ τ) → Nf≡Tm/βη {Γ - x} {τ} i → Nf≡Tm/βη {Γ - x} {σ} i) (_[_:=_] {τ} {Γ} {σ})


-- We can easily recover the proof that our operations defined on the quotient set respects the equivalence
-- in the appropriate ways

wkResp : ∀ {Γ σ τ} (x : Var Γ σ) (t u : Tm (Γ - x) τ) → t βη-≡ u → quotWk x [ t ] ≡ quotWk x [ u ]
wkResp x t u p i = quotWk x (eq/ t u p i)

substResp : ∀ {Γ σ τ} (t t₁ : Tm Γ σ) (x : Var Γ τ) (u u₁ : Tm (Γ - x) τ) → t βη-≡ t₁ → u βη-≡ u₁ → quotSubst [ t ] x [ u ] ≡ quotSubst [ t₁ ] x [ u₁ ]
substResp t t₁ x u u₁ p q i = quotSubst (eq/ t t₁ p i) x (eq/ u u₁ q i)


-- Weakening on normal forms defined via weakening on QTm's

wkNf′ : ∀ {Γ σ τ} (x : Var Γ σ) → Nf (Γ - x) τ → Nf Γ τ
wkNf′ {Γ} {σ} {τ} x = transport (λ i → Nf≡Tm/βη {Γ - x} {τ} (~ i) → Nf≡Tm/βη {Γ} {τ} (~ i)) (quotWk {Γ} {σ} {τ} x)

-- This form of weakening is extensionally equivalent to our original weakening function (as it should be)

nfnf : ∀ {Γ σ τ} (x : Var Γ σ) (t : Nf (Γ - x) τ) → wkNf′ x t ≡ wkNf x t
nfnf {Γ} {σ} {τ} x t =
  _ ≡⟨ cong nf (transportRefl ((transp (λ i → Tm Γ τ) i0 ⌈ wkNf x (nf (transp (λ i → Tm (Γ - x) τ) i0 (transp (λ i → Tm (Γ - x) τ) i0 ⌈ t ⌉))) ⌉))) ⟩
  _ ≡⟨ cong nf (transportRefl ⌈ wkNf x (nf (transp (λ i → Tm (Γ - x) τ) i0 (transp (λ i → Tm (Γ - x) τ) i0 ⌈ t ⌉))) ⌉) ⟩
  _ ≡⟨ Iso.leftInv quotientIso (wkNf x (nf (transp (λ i → Tm (Γ - x) τ) i0 (transp (λ i → Tm (Γ - x) τ) i0 ⌈ t ⌉))))  ⟩
  _ ≡⟨ (λ j → wkNf x (nf (transportRefl (transp (λ i → Tm (Γ - x) τ) i0 ⌈ t ⌉) j)) ) ⟩
  _ ≡⟨ (λ j → wkNf x (nf (transportRefl ⌈ t ⌉ j))) ⟩
  _ ≡⟨ cong (wkNf x) (Iso.leftInv quotientIso t) ⟩
  _ ∎

wkNfResp : ∀ {Γ σ τ} (x : Var Γ σ) (t u : Nf (Γ - x) τ) → ⌈ t ⌉ βη-≡ ⌈ u ⌉ → wkNf x t ≡ wkNf x u
wkNfResp x t u p = cong (wkNf x) (βη→Nf≡ t u p)


-- Unfortunately it doesn't really compute
_ : quotSubst {ε , ○ ⇒ ○} [ var vz ] vz [ Λ (var vz) ] ≡ [ Λ (var vz) ] 
_ = {!refl!}
