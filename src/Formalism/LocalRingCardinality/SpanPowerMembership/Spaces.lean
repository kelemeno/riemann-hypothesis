module

public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleRanksRankComplement
public import Formalism.FockGram.SymGramPosSemidef
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stdform
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Std.Tactic.BVDecide.Normalize.BitVec

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField
open scoped TensorProduct
open IsDedekindDomain

section Diag

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def sgn {A : Type} [Ring A] (b : Bool) : A := if b then -1 else 1

theorem star_sgn (b : Bool) : star (sgn b : E) = sgn b := by
  cases b <;> simp [sgn]

theorem sgn_mul_self {A : Type} [Ring A] (b : Bool) : (sgn b : A) * sgn b = 1 := by
  cases b <;> simp [sgn]

theorem sgn_ne_zero {A : Type} [Ring A] [Nontrivial A] (b : Bool) : (sgn b : A) ≠ 0 := by
  cases b <;> simp [sgn]

theorem map_sgn {A B : Type} [Ring A] [Ring B] (f : A →+* B) (b : Bool) : f (sgn b) = sgn b := by
  cases b <;> simp [sgn]

def diagForm (N : ℕ) (neg : Fin N → Bool) : (Fin N → E) →ₗ⋆[E] (Fin N → E) →ₗ[E] E :=
  LinearMap.mk₂'ₛₗ (starRingEnd E) (RingHom.id E)
    (fun x y => ∑ i, star (x i) * sgn (neg i) * y i)
    (by intro m₁ m₂ n; simp [add_mul, Finset.sum_add_distrib])
    (by intro c m n; simp only [Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [starRingEnd_apply]; ring)
    (by intro m n₁ n₂; simp [mul_add, Finset.sum_add_distrib])
    (by intro c m n; simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring)

theorem diagForm_apply (N : ℕ) (neg : Fin N → Bool) (x y : Fin N → E) :
    diagForm N neg x y = ∑ i, star (x i) * sgn (neg i) * y i := rfl

theorem diagForm_single (N : ℕ) (neg : Fin N → Bool) (i j : Fin N) :
    diagForm N neg (Pi.single i 1) (Pi.single j 1) = if i = j then (sgn (neg i) : E) else 0 := by
  rw [diagForm_apply, Finset.sum_eq_single i]
  · by_cases h : i = j
    · subst h; simp
    · simp [h]
  · intro b _ hb; simp [Pi.single_apply, hb]
  · simp

theorem diagForm_isSymm (N : ℕ) (neg : Fin N → Bool) : (diagForm (E := E) N neg).IsSymm := by
  constructor
  intro x y

  simp only [diagForm_apply, map_sum, starRingEnd_apply, star_mul', star_star, star_sgn]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem diagForm_nondeg (N : ℕ) (neg : Fin N → Bool) : (diagForm (E := E) N neg).Nondegenerate := by
  constructor
  · intro x hx
    funext i
    have h := hx (Pi.single i 1)
    rw [diagForm_apply, Finset.sum_eq_single i (fun b _ hb => by simp [hb])
      (by simp)] at h
    simp only [Pi.single_eq_same, mul_one] at h
    have := (mul_eq_zero.1 h).resolve_right (sgn_ne_zero _)
    simpa using this
  · intro y hy
    funext i
    have h := hy (Pi.single i 1)
    rw [diagForm_apply, Finset.sum_eq_single i (fun b _ hb => by simp [hb])
      (by simp)] at h
    simp only [Pi.single_eq_same, star_one, one_mul] at h
    have := (mul_eq_zero.1 h).resolve_left (sgn_ne_zero _)
    simpa using this

end Diag

section Lat

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def stdLat (N : ℕ) : Submodule (𝓞 E) (Fin N → E) :=
  Submodule.span (𝓞 E) (Set.range (Pi.basisFun E (Fin N)))

theorem stdLat_isLattice (N : ℕ) : Submodule.IsLattice E (stdLat (E := E) N) :=
  Submodule.IsLattice.of_fg E (Submodule.fg_span (Set.finite_range _))

theorem star_isIntegral (x : E) (hx : IsIntegral ℤ x) : IsIntegral ℤ (star x) :=
  hx.map (starRingEnd E).toIntAlgHom

theorem star_integral (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (s : 𝓞 E) :
    star (algebraMap (𝓞 E) E s) ∈ Set.range (algebraMap (𝓞 E) E) :=
  ⟨⟨star (s : E), hstar _ s.2⟩, rfl⟩

theorem stdLat_unimod (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (N : ℕ)
    (neg : Fin N → Bool) : Formalism.HermitianLatticesTheory.IsUnimodular (diagForm (E := E) N neg) (stdLat N) := by
  have key := (Formalism.E.hermDual (𝓞 E) E (Fin N → E) (Fin N) (diagForm N neg) (Pi.basisFun E (Fin N))
    (IsFractionRing.injective (𝓞 E) E) (star_integral hstar)).2
    (Matrix.diagonal fun i => (sgn (neg i) : 𝓞 E)) (by
      intro i j
      rw [Pi.basisFun_apply, Pi.basisFun_apply, diagForm_single]
      by_cases h : i = j
      · subst h; simp [map_sgn]
      · simp [h]) (by
      rw [Matrix.det_diagonal]
      exact Finset.prod_ne_zero_iff.2 fun i _ => sgn_ne_zero (neg i))
  exact key.2.2 (by
    rw [Matrix.det_diagonal]
    refine isUnit_iff_exists_inv.2 ⟨∏ i, (sgn (neg i) : 𝓞 E), ?_⟩
    rw [← Finset.prod_mul_distrib]
    simp [sgn_mul_self])

end Lat

section Space

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def stdSpace (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (N : ℕ) (neg : Fin N → Bool)
    (p q : ℕ) : HSpace E where
  V := Fin N → E
  hT := diagForm N neg
  herm := diagForm_isSymm N neg
  nondeg := diagForm_nondeg N neg
  rank := N
  rank_eq := Module.finrank_fin_fun E
  frame := Pi.basisFun E (Fin N)
  sig := fun _ => (p, q)
  L0 := stdLat N
  standardTuple_isLattice := stdLat_isLattice N
  baseLattice_isUnimodular := stdLat_unimod hstar N neg

variable (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x))

theorem stdSpace_gram_apply (N : ℕ) (neg : Fin N → Bool) (p q : ℕ) (i j : Fin N) :
    (stdSpace hstar N neg p q).gram i j = if i = j then (sgn (neg i) : E) else 0 := by
  show diagForm N neg ((Pi.basisFun E (Fin N)) i) ((Pi.basisFun E (Fin N)) j) = _
  simp only [Pi.basisFun_apply]
  exact diagForm_single N neg i j

def posSpace (N : ℕ) : HSpace E := stdSpace hstar N (fun _ => false) N 0

theorem posSpace_sigOK (N : ℕ) : (posSpace hstar N).SigOK := by
  intro τ
  have hg : (posSpace hstar N).gram.map τ = 1 := by
    ext i j
    rw [Matrix.map_apply]
    refine (congrArg τ (stdSpace_gram_apply hstar N (fun _ => false) N 0 i j)).trans ?_
    change τ (if i = j then (sgn false : E) else 0) = if i = j then (1 : ℂ) else 0
    by_cases h : i = j <;> simp [h, sgn]
  rw [hg]
  show Formalism.UG.HasSignature _ N 0
  have h := Formalism.UG.P.stdform_sig_one (n := Fin N)
  rw [Fintype.card_fin] at h
  exact h

end Space

section Maps

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem diagForm_single_left (N : ℕ) (neg : Fin N → Bool) (j : Fin N) (b : E) (x : Fin N → E) :
    diagForm N neg (Pi.single j b) x = star b * sgn (neg j) * x j := by
  rw [diagForm_apply, Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp)]
  simp

theorem diagForm_single_right (N : ℕ) (neg : Fin N → Bool) (x : Fin N → E) (j : Fin N) (b : E) :
    diagForm N neg x (Pi.single j b) = star (x j) * sgn (neg j) * b := by
  rw [diagForm_apply, Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp)]
  simp

end Maps

section Examples₂

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x))
  (cm : CMData F E) (T : ℕ) (hT : T.Prime) (pz : E) (hpz : star pz * pz = T)
  (hy : ∃ y : E ⊗[F] FiniteAdeleRing (𝓞 F) F,
    Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F) y * y = -1)

end Examples₂

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [StarRing E]

end SlopeTestRemainingChoices

section Adelic

theorem cT_diagonal {n A : Type} [Fintype n] [DecidableEq n] [CommRing A] (σ : A →+* A)
    (d : n → A) : Formalism.UG.cT σ (Matrix.diagonal d) = Matrix.diagonal (fun i => σ (d i)) := by
  ext i j
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

theorem diag_congr {n A : Type} [Fintype n] [DecidableEq n] [CommRing A] (σ : A →+* A)
    (d s t : n → A) (h : ∀ i, σ (d i) * s i * d i = t i) :
    Formalism.UG.cT σ (Matrix.diagonal d) * Matrix.diagonal s * Matrix.diagonal d = Matrix.diagonal t := by
  rw [cT_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact h i

def diagUnit {n A : Type} [Fintype n] [DecidableEq n] [CommRing A] (d d' : n → A)
    (h : ∀ i, d i * d' i = 1) : GL n A where
  val := Matrix.diagonal d
  inv := Matrix.diagonal d'
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    convert Matrix.diagonal_one
    exact h _
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    convert Matrix.diagonal_one
    rw [mul_comm]
    exact h _

theorem diagUnit_val {n A : Type} [Fintype n] [DecidableEq n] [CommRing A] (d d' : n → A)
    (h : ∀ i, d i * d' i = 1) : (diagUnit d d' h : Matrix n n A) = Matrix.diagonal d := rfl

end Adelic

section Examples₂

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x))
  (cm : CMData F E) (T : ℕ) (hT : T.Prime) (pz : E) (hpz : star pz * pz = T)
  (hy : ∃ y : E ⊗[F] FiniteAdeleRing (𝓞 F) F,
    Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F) y * y = -1)

end Examples₂

section Examples₂

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x))
  (cm : CMData F E) (T : ℕ) (hT : T.Prime) (pz : E) (hpz : star pz * pz = T)
  (hy : ∃ y : E ⊗[F] FiniteAdeleRing (𝓞 F) F,
    Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F) y * y = -1)

end Examples₂

end Formalism.BasicNotions.Examples₂
