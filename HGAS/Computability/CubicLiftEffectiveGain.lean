import HGAS.Computability.CubicLiftCodeCompiler
import HGAS.Lyapunov.ExactGridPositivityComputability
import Mathlib.Tactic

/-!
# Fixed-parameter computable gains for the cubic lift

The geometric constants in transverse stabilization depend only on the
fixed pair `(n,k)`.  The dependence on the input field is linear.  This
module makes that separation explicit and uses it to hard-code one natural
constant for each fixed `(n,k)`, while scaling the gain by an executable
coefficient `ℓ¹` bound.

The computability statement is deliberately **nonuniform in `(n,k)`**:
for each fixed pair, one natural multiplier is chosen and hard-coded.
The input field is then transformed by a primitive-recursive function.
We do not claim here a single algorithm that receives varying `n` and `k`
and computes the analytic multiplier.
-/

namespace HGAS.Veronese

open scoped BigOperators

noncomputable section

variable {n k : ℕ}

theorem cubicLiftPolynomial_add
    (p q : MvPolynomial (Fin n) ℚ) :
    cubicLiftPolynomial k (p + q) =
      cubicLiftPolynomial k p + cubicLiftPolynomial k q := by
  rw [cubicLiftPolynomial_eq_sum_multiIndex,
    cubicLiftPolynomial_eq_sum_multiIndex,
    cubicLiftPolynomial_eq_sum_multiIndex,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [MvPolynomial.coeff_add, map_add]
  ring

theorem cubicLiftPolynomial_C_mul
    (c : ℚ) (p : MvPolynomial (Fin n) ℚ) :
    cubicLiftPolynomial k (MvPolynomial.C c * p) =
      MvPolynomial.C c * cubicLiftPolynomial k p := by
  rw [cubicLiftPolynomial_eq_sum_multiIndex,
    cubicLiftPolynomial_eq_sum_multiIndex, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [MvPolynomial.coeff_C_mul]
  rw [map_mul]
  ring

theorem cubicLiftPolynomial_zero :
    cubicLiftPolynomial k (0 : MvPolynomial (Fin n) ℚ) = 0 := by
  rw [cubicLiftPolynomial_eq_sum_multiIndex]
  simp

def addPolynomialField
    (F G : HGAS.PolynomialField n) : HGAS.PolynomialField n :=
  fun i => F i + G i

def scalePolynomialField
    (c : ℚ) (F : HGAS.PolynomialField n) : HGAS.PolynomialField n :=
  fun i => MvPolynomial.C c * F i

theorem transportedSourcePolynomial_add
    (F G : HGAS.PolynomialField n) (a : MultiIndex n k) :
    transportedSourcePolynomial (addPolynomialField F G) a =
      transportedSourcePolynomial F a +
        transportedSourcePolynomial G a := by
  simp only [transportedSourcePolynomial, addPolynomialField,
    mul_add, Finset.sum_add_distrib]

theorem transportedSourcePolynomial_scale
    (c : ℚ) (F : HGAS.PolynomialField n)
    (a : MultiIndex n k) :
    transportedSourcePolynomial (scalePolynomialField c F) a =
      MvPolynomial.C c * transportedSourcePolynomial F a := by
  simp only [transportedSourcePolynomial, scalePolynomialField]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem cubicLiftField_add
    (F G : HGAS.PolynomialField n) :
    cubicLiftField (k := k) (addPolynomialField F G) =
      fun a => cubicLiftField (k := k) F a +
        cubicLiftField (k := k) G a := by
  funext a
  simp only [cubicLiftField, transportedSourcePolynomial_add,
    cubicLiftPolynomial_add]

theorem cubicLiftField_scale
    (c : ℚ) (F : HGAS.PolynomialField n) :
    cubicLiftField (k := k) (scalePolynomialField c F) =
      fun a => MvPolynomial.C c *
        cubicLiftField (k := k) F a := by
  funext a
  simp only [cubicLiftField, transportedSourcePolynomial_scale,
    cubicLiftPolynomial_C_mul]

theorem evaluatedCubicLift_add
    (F G : HGAS.PolynomialField n)
    (y : RealVeroneseSpace n k) :
    evaluatedCubicLift (k := k) (addPolynomialField F G) y =
      evaluatedCubicLift (k := k) F y +
        evaluatedCubicLift (k := k) G y := by
  funext a
  simp [evaluatedCubicLift, cubicLiftField_add,
    evalCoordinateField_apply]

theorem evaluatedCubicLift_scale
    (c : ℚ) (F : HGAS.PolynomialField n)
    (y : RealVeroneseSpace n k) :
    evaluatedCubicLift (k := k) (scalePolynomialField c F) y =
      (c : ℝ) • evaluatedCubicLift (k := k) F y := by
  funext a
  simp [evaluatedCubicLift, cubicLiftField_scale,
    evalCoordinateField_apply]

theorem weightedRadialReward_add
    (G H : RealVeroneseSpace n k → RealVeroneseSpace n k)
    (y : RealVeroneseSpace n k) :
    weightedRadialReward (fun z => G z + H z) y =
      weightedRadialReward G y + weightedRadialReward H y := by
  exact weightedInner_add_right y (G y) (H y)

theorem weightedRadialReward_smul
    (c : ℝ)
    (G : RealVeroneseSpace n k → RealVeroneseSpace n k)
    (y : RealVeroneseSpace n k) :
    weightedRadialReward (fun z => c • G z) y =
      c * weightedRadialReward G y := by
  exact weightedInner_smul_right c y (G y)

theorem weightedAngularField_add
    (G H : RealVeroneseSpace n k → RealVeroneseSpace n k)
    (y : RealVeroneseSpace n k) :
    weightedAngularField (fun z => G z + H z) y =
      weightedAngularField G y + weightedAngularField H y := by
  funext a
  simp only [weightedAngularField, weightedRadialReward_add,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem weightedAngularField_smul
    (c : ℝ)
    (G : RealVeroneseSpace n k → RealVeroneseSpace n k)
    (y : RealVeroneseSpace n k) :
    weightedAngularField (fun z => c • G z) y =
      c • weightedAngularField G y := by
  funext a
  simp only [weightedAngularField, weightedRadialReward_smul,
    Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

theorem penaltyLieDerivative_add
    (G H : RealVeroneseSpace n k → RealVeroneseSpace n k)
    (y : RealVeroneseSpace n k) :
    penaltyLieDerivative
        (fun z => weightedAngularField G z +
          weightedAngularField H z) y =
      penaltyLieDerivative (weightedAngularField G) y +
        penaltyLieDerivative (weightedAngularField H) y := by
  exact weightedInner_add_right _ _ _

theorem penaltyLieDerivative_smul
    (c : ℝ)
    (G : RealVeroneseSpace n k → RealVeroneseSpace n k)
    (y : RealVeroneseSpace n k) :
    penaltyLieDerivative
        (fun z => c • weightedAngularField G z) y =
      c * penaltyLieDerivative (weightedAngularField G) y := by
  exact weightedInner_smul_right c _ _

/-- The two input-dependent estimates needed by transverse
stabilization, separated from the fixed Morse--Bott constants. -/
structure CubicLiftLinearBounds
    (F : HGAS.PolynomialField n) (k : ℕ) where
  C : ℝ
  A : ℝ
  C_nonneg : 0 ≤ C
  A_nonneg : 0 ≤ A
  angularTangency :
    ∀ y : RealVeroneseSpace n k,
      Q y = 1 →
        |penaltyLieDerivative
            (weightedAngularField
              (evaluatedCubicLift (k := k) F)) y| ≤
          C * completeToricEnergy y
  radialBound :
    ∀ y : RealVeroneseSpace n k,
      Q y = 1 →
        |weightedRadialReward
            (evaluatedCubicLift (k := k) F) y| ≤ A

/-- Transport a package of estimates across equality of polynomial
fields.  Naming this transport avoids dependent-rewrite noise later. -/
def CubicLiftLinearBounds.cast
    {F G : HGAS.PolynomialField n}
    (h : F = G) (b : CubicLiftLinearBounds F k) :
    CubicLiftLinearBounds G k :=
  h ▸ b

@[simp] theorem CubicLiftLinearBounds.cast_C
    {F G : HGAS.PolynomialField n}
    (h : F = G) (b : CubicLiftLinearBounds F k) :
    (b.cast h).C = b.C := by
  cases h
  rfl

@[simp] theorem CubicLiftLinearBounds.cast_A
    {F G : HGAS.PolynomialField n}
    (h : F = G) (b : CubicLiftLinearBounds F k) :
    (b.cast h).A = b.A := by
  cases h
  rfl

theorem exists_cubicLiftLinearBounds
    (F : HGAS.PolynomialField n)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F)
    (hk : 1 ≤ k) :
    Nonempty (CubicLiftLinearBounds F k) := by
  obtain ⟨C, hC, hangular⟩ :=
    exists_cubicLift_angularPenaltyLieDerivative_linear_bound
      F hF hk
  obtain ⟨A, hA, hradial⟩ :=
    exists_radialReward_bound_on_weightedUnitSphere
      (continuous_evaluatedCubicLift (k := k) F)
  exact ⟨{
    C := C
    A := A
    C_nonneg := hC
    A_nonneg := hA
    angularTangency := hangular
    radialBound := hradial
  }⟩

def zeroPolynomialField (n : ℕ) : HGAS.PolynomialField n :=
  fun _ => 0

theorem cubicLiftField_zero :
    cubicLiftField (k := k) (zeroPolynomialField n) =
      fun _ => 0 := by
  funext a
  simp [cubicLiftField, transportedSourcePolynomial,
    zeroPolynomialField, cubicLiftPolynomial_zero]

theorem evaluatedCubicLift_zero
    (y : RealVeroneseSpace n k) :
    evaluatedCubicLift (k := k) (zeroPolynomialField n) y = 0 := by
  funext a
  simp [evaluatedCubicLift, cubicLiftField_zero,
    evalCoordinateField_apply]

def CubicLiftLinearBounds.zero (n k : ℕ) :
    CubicLiftLinearBounds (zeroPolynomialField n) k where
  C := 0
  A := 0
  C_nonneg := le_rfl
  A_nonneg := le_rfl
  angularTangency := by
    intro y _
    rw [show evaluatedCubicLift (k := k)
          (zeroPolynomialField n) = fun _ => 0 by
      funext z
      exact evaluatedCubicLift_zero z]
    simp [weightedAngularField, weightedRadialReward,
      penaltyLieDerivative, weightedInner]
  radialBound := by
    intro y _
    rw [show evaluatedCubicLift (k := k)
          (zeroPolynomialField n) = fun _ => 0 by
      funext z
      exact evaluatedCubicLift_zero z]
    simp [weightedRadialReward, weightedInner]

def CubicLiftLinearBounds.add
    {F G : HGAS.PolynomialField n}
    (bF : CubicLiftLinearBounds F k)
    (bG : CubicLiftLinearBounds G k) :
    CubicLiftLinearBounds (addPolynomialField F G) k where
  C := bF.C + bG.C
  A := bF.A + bG.A
  C_nonneg := add_nonneg bF.C_nonneg bG.C_nonneg
  A_nonneg := add_nonneg bF.A_nonneg bG.A_nonneg
  angularTangency := by
    intro y hQ
    rw [show evaluatedCubicLift (k := k)
          (addPolynomialField F G) =
        fun z => evaluatedCubicLift (k := k) F z +
          evaluatedCubicLift (k := k) G z by
      funext z
      exact evaluatedCubicLift_add F G z]
    rw [show weightedAngularField
          (fun z => evaluatedCubicLift (k := k) F z +
            evaluatedCubicLift (k := k) G z) =
        fun z => weightedAngularField
            (evaluatedCubicLift (k := k) F) z +
          weightedAngularField
            (evaluatedCubicLift (k := k) G) z by
      funext z
      exact weightedAngularField_add _ _ z]
    rw [penaltyLieDerivative_add]
    calc
      |penaltyLieDerivative
            (weightedAngularField
              (evaluatedCubicLift (k := k) F)) y +
          penaltyLieDerivative
            (weightedAngularField
              (evaluatedCubicLift (k := k) G)) y| ≤
        |penaltyLieDerivative
            (weightedAngularField
              (evaluatedCubicLift (k := k) F)) y| +
          |penaltyLieDerivative
            (weightedAngularField
              (evaluatedCubicLift (k := k) G)) y| :=
        abs_add_le _ _
      _ ≤ bF.C * completeToricEnergy y +
          bG.C * completeToricEnergy y :=
        add_le_add (bF.angularTangency y hQ)
          (bG.angularTangency y hQ)
      _ = (bF.C + bG.C) * completeToricEnergy y := by ring
  radialBound := by
    intro y hQ
    rw [show evaluatedCubicLift (k := k)
          (addPolynomialField F G) =
        fun z => evaluatedCubicLift (k := k) F z +
          evaluatedCubicLift (k := k) G z by
      funext z
      exact evaluatedCubicLift_add F G z]
    rw [weightedRadialReward_add]
    exact (abs_add_le _ _).trans
      (add_le_add (bF.radialBound y hQ)
        (bG.radialBound y hQ))

def CubicLiftLinearBounds.scale
    {F : HGAS.PolynomialField n}
    (c : ℚ) (b : CubicLiftLinearBounds F k) :
    CubicLiftLinearBounds (scalePolynomialField c F) k where
  C := |(c : ℝ)| * b.C
  A := |(c : ℝ)| * b.A
  C_nonneg := mul_nonneg (abs_nonneg _) b.C_nonneg
  A_nonneg := mul_nonneg (abs_nonneg _) b.A_nonneg
  angularTangency := by
    intro y hQ
    rw [show evaluatedCubicLift (k := k)
          (scalePolynomialField c F) =
        fun z => (c : ℝ) • evaluatedCubicLift (k := k) F z by
      funext z
      exact evaluatedCubicLift_scale c F z]
    rw [show weightedAngularField
          (fun z => (c : ℝ) •
            evaluatedCubicLift (k := k) F z) =
        fun z => (c : ℝ) •
          weightedAngularField
            (evaluatedCubicLift (k := k) F) z by
      funext z
      exact weightedAngularField_smul _ _ z]
    rw [penaltyLieDerivative_smul,
      abs_mul]
    calc
      |(c : ℝ)| *
          |penaltyLieDerivative
            (weightedAngularField
              (evaluatedCubicLift (k := k) F)) y| ≤
        |(c : ℝ)| *
          (b.C * completeToricEnergy y) :=
        mul_le_mul_of_nonneg_left
          (b.angularTangency y hQ) (abs_nonneg _)
      _ = |(c : ℝ)| * b.C *
          completeToricEnergy y := by ring
  radialBound := by
    intro y hQ
    rw [show evaluatedCubicLift (k := k)
          (scalePolynomialField c F) =
        fun z => (c : ℝ) • evaluatedCubicLift (k := k) F z by
      funext z
      exact evaluatedCubicLift_scale c F z]
    rw [weightedRadialReward_smul, abs_mul]
    exact mul_le_mul_of_nonneg_left
      (b.radialBound y hQ) (abs_nonneg _)

def monomialBasisField
    (i : Fin n) (a : MultiIndex n d) :
    HGAS.PolynomialField n :=
  fun j =>
    if j = i then
      MvPolynomial.monomial (multiIndexFinsupp a) 1
    else 0

theorem monomialBasisField_isHomogeneous
    (i : Fin n) (a : MultiIndex n d) :
    HGAS.IsHomogeneousOfDegree d
      (monomialBasisField i a) := by
  intro j
  by_cases hji : j = i
  · simp only [monomialBasisField, hji, if_pos]
    exact MvPolynomial.isHomogeneous_monomial 1
      (multiIndexFinsupp_degree a)
  · simp only [monomialBasisField, hji]
    exact MvPolynomial.isHomogeneous_zero _ _ _

def basisLinearBounds
    (n k : ℕ) (hk : 1 ≤ k)
    (i : Fin n) (a : MultiIndex n (2 * k + 1)) :
    CubicLiftLinearBounds (monomialBasisField i a) k :=
  Classical.choice
    (exists_cubicLiftLinearBounds
      (monomialBasisField i a)
      (monomialBasisField_isHomogeneous i a) hk)

def sumPolynomialFields
    {ι : Type*} (s : Finset ι)
    (F : ι → HGAS.PolynomialField n) :
    HGAS.PolynomialField n :=
  ∑ i ∈ s, F i

theorem nonempty_cubicLiftLinearBounds_sum
    {ι : Type*}
    (s : Finset ι)
    (F : ι → HGAS.PolynomialField n)
    (b : ∀ i, CubicLiftLinearBounds (F i) k) :
    Nonempty
      (CubicLiftLinearBounds (sumPolynomialFields s F) k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨by
        simpa [sumPolynomialFields, zeroPolynomialField] using
          CubicLiftLinearBounds.zero n k⟩
  | @insert a s ha ih =>
      obtain ⟨bs⟩ := ih
      exact ⟨by
        have hadd := (b a).add bs
        simpa [sumPolynomialFields, ha, addPolynomialField] using hadd⟩

def CubicLiftLinearBounds.sum
    {ι : Type*}
    (s : Finset ι)
    (F : ι → HGAS.PolynomialField n)
    (b : ∀ i, CubicLiftLinearBounds (F i) k) :
    CubicLiftLinearBounds (sumPolynomialFields s F) k :=
  Classical.choice
    (nonempty_cubicLiftLinearBounds_sum s F b)

theorem exists_cubicLiftLinearBounds_sum_exact
    {ι : Type*}
    (s : Finset ι)
    (F : ι → HGAS.PolynomialField n)
    (b : ∀ i, CubicLiftLinearBounds (F i) k) :
    ∃ bs : CubicLiftLinearBounds (sumPolynomialFields s F) k,
      bs.C = ∑ i ∈ s, (b i).C ∧
      bs.A = ∑ i ∈ s, (b i).A := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨by
        simpa [sumPolynomialFields, zeroPolynomialField] using
          CubicLiftLinearBounds.zero n k, ?_, ?_⟩ <;> rfl
  | @insert a s ha ih =>
      obtain ⟨bs, hC, hA⟩ := ih
      let bins := (b a).add bs
      have hfield :
          sumPolynomialFields (insert a s) F =
            addPolynomialField (F a)
              (sumPolynomialFields s F) := by
        rw [sumPolynomialFields, Finset.sum_insert ha]
        funext j
        rfl
      let bout :
          CubicLiftLinearBounds
            (sumPolynomialFields (insert a s) F) k := {
        C := (b a).C + bs.C
        A := (b a).A + bs.A
        C_nonneg := add_nonneg (b a).C_nonneg bs.C_nonneg
        A_nonneg := add_nonneg (b a).A_nonneg bs.A_nonneg
        angularTangency := by
          rw [hfield]
          exact bins.angularTangency
        radialBound := by
          rw [hfield]
          exact bins.radialBound
      }
      refine ⟨bout, ?_, ?_⟩
      · change (b a).C + bs.C =
          ∑ i ∈ insert a s, (b i).C
        rw [Finset.sum_insert ha, hC]
      · change (b a).A + bs.A =
          ∑ i ∈ insert a s, (b i).A
        rw [Finset.sum_insert ha, hA]

theorem polynomial_eq_sum_degree_multiIndex
    {p : MvPolynomial (Fin n) ℚ}
    (hp : p.IsHomogeneous d) :
    p =
      ∑ a : MultiIndex n d,
        MvPolynomial.monomial (multiIndexFinsupp a)
          (MvPolynomial.coeff (multiIndexFinsupp a) p) := by
  classical
  let target : Finset (MultiIndex n d) :=
    Finset.univ.filter fun a => multiIndexFinsupp a ∈ p.support
  have hreindex :
      (∑ m ∈ p.support,
          MvPolynomial.monomial m (MvPolynomial.coeff m p)) =
        ∑ a ∈ target,
          MvPolynomial.monomial (multiIndexFinsupp a)
            (MvPolynomial.coeff (multiIndexFinsupp a) p) := by
    apply Finset.sum_bij
      (fun m hm =>
        multiIndexOfFinsupp m
          (finsuppDegree_eq_of_isHomogeneous hp hm))
    · intro m hm
      simp only [target, Finset.mem_filter,
        Finset.mem_univ, true_and]
      simpa using hm
    · intro m₁ hm₁ m₂ hm₂ heq
      have := congrArg multiIndexFinsupp heq
      simpa using this
    · intro a ha
      refine ⟨multiIndexFinsupp a, ?_, ?_⟩
      · exact (Finset.mem_filter.mp ha).2
      · apply Subtype.ext
        funext i
        simp
    · intro m hm
      simp
  have htarget :
      (∑ a ∈ target,
          MvPolynomial.monomial (multiIndexFinsupp a)
            (MvPolynomial.coeff (multiIndexFinsupp a) p)) =
        ∑ a : MultiIndex n d,
          MvPolynomial.monomial (multiIndexFinsupp a)
            (MvPolynomial.coeff (multiIndexFinsupp a) p) := by
    change
      (∑ a ∈ target,
          MvPolynomial.monomial (multiIndexFinsupp a)
            (MvPolynomial.coeff (multiIndexFinsupp a) p)) =
        ∑ a ∈ (Finset.univ : Finset (MultiIndex n d)),
          MvPolynomial.monomial (multiIndexFinsupp a)
            (MvPolynomial.coeff (multiIndexFinsupp a) p)
    apply Finset.sum_subset
    · intro a _
      exact Finset.mem_univ a
    · intro a _ hnot
      have hsupport : multiIndexFinsupp a ∉ p.support := by
        intro h
        exact hnot
          (Finset.mem_filter.mpr ⟨Finset.mem_univ a, h⟩)
      have hcoeff :
          MvPolynomial.coeff (multiIndexFinsupp a) p = 0 := by
        by_contra hne
        exact hsupport (MvPolynomial.mem_support_iff.mpr hne)
      rw [hcoeff]
      simp
  calc
    p = ∑ m ∈ p.support,
        MvPolynomial.monomial m (MvPolynomial.coeff m p) :=
      (MvPolynomial.support_sum_monomial_coeff p).symm
    _ = ∑ a ∈ target,
        MvPolynomial.monomial (multiIndexFinsupp a)
          (MvPolynomial.coeff (multiIndexFinsupp a) p) :=
      hreindex
    _ = ∑ a : MultiIndex n d,
        MvPolynomial.monomial (multiIndexFinsupp a)
          (MvPolynomial.coeff (multiIndexFinsupp a) p) :=
      htarget

def homogeneousFieldExpansion
    (d : ℕ) (F : HGAS.PolynomialField n) :
    HGAS.PolynomialField n :=
  ∑ i : Fin n,
    ∑ a : MultiIndex n d,
      scalePolynomialField
        (MvPolynomial.coeff (multiIndexFinsupp a) (F i))
        (monomialBasisField i a)

theorem homogeneousFieldExpansion_eq
    (F : HGAS.PolynomialField n)
    (hF : HGAS.IsHomogeneousOfDegree d F) :
    homogeneousFieldExpansion d F = F := by
  funext j
  simp only [homogeneousFieldExpansion, Finset.sum_apply,
    scalePolynomialField, monomialBasisField]
  rw [Finset.sum_eq_single j]
  · simp only [if_pos]
    calc
      (∑ a : MultiIndex n d,
          MvPolynomial.C
              (MvPolynomial.coeff (multiIndexFinsupp a) (F j)) *
            MvPolynomial.monomial (multiIndexFinsupp a) 1) =
        ∑ a : MultiIndex n d,
          MvPolynomial.monomial (multiIndexFinsupp a)
            (MvPolynomial.coeff (multiIndexFinsupp a) (F j)) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [MvPolynomial.C_mul_monomial]
          norm_num
      _ = F j :=
        (polynomial_eq_sum_degree_multiIndex (hF j)).symm
  · intro i _ hne
    simp [Ne.symm hne]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

def basisBoundMass (n k : ℕ) (hk : 1 ≤ k) : ℝ :=
  ∑ i : Fin n,
    ∑ a : MultiIndex n (2 * k + 1),
      ((basisLinearBounds n k hk i a).C +
        (basisLinearBounds n k hk i a).A)

def basisUniformBound (n k : ℕ) (hk : 1 ≤ k) : ℝ :=
  1 + basisBoundMass n k hk

theorem basisBoundMass_nonneg
    (n k : ℕ) (hk : 1 ≤ k) :
    0 ≤ basisBoundMass n k hk := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro a _
  exact add_nonneg
    (basisLinearBounds n k hk i a).C_nonneg
    (basisLinearBounds n k hk i a).A_nonneg

theorem basisUniformBound_pos
    (n k : ℕ) (hk : 1 ≤ k) :
    0 < basisUniformBound n k hk := by
  exact add_pos_of_pos_of_nonneg zero_lt_one
    (basisBoundMass_nonneg n k hk)

theorem basis_C_le_uniform
    (n k : ℕ) (hk : 1 ≤ k)
    (i : Fin n) (a : MultiIndex n (2 * k + 1)) :
    (basisLinearBounds n k hk i a).C ≤
      basisUniformBound n k hk := by
  let B := basisLinearBounds n k hk
  have hterm :
      (B i a).C ≤ (B i a).C + (B i a).A :=
    le_add_of_nonneg_right (B i a).A_nonneg
  have hinner :
      (B i a).C + (B i a).A ≤
        ∑ b : MultiIndex n (2 * k + 1),
          ((B i b).C + (B i b).A) := by
    apply Finset.single_le_sum
      (s := (Finset.univ : Finset (MultiIndex n (2 * k + 1))))
      (f := fun b => (B i b).C + (B i b).A)
    · intro b _
      exact add_nonneg (B i b).C_nonneg (B i b).A_nonneg
    · exact Finset.mem_univ a
  have houter :
      (∑ b : MultiIndex n (2 * k + 1),
          ((B i b).C + (B i b).A)) ≤
        basisBoundMass n k hk := by
    unfold basisBoundMass
    apply Finset.single_le_sum
      (s := (Finset.univ : Finset (Fin n)))
      (f := fun j =>
        ∑ b : MultiIndex n (2 * k + 1),
          ((basisLinearBounds n k hk j b).C +
            (basisLinearBounds n k hk j b).A))
    · intro j _
      apply Finset.sum_nonneg
      intro b _
      exact add_nonneg (B j b).C_nonneg (B j b).A_nonneg
    · exact Finset.mem_univ i
  calc
    (B i a).C ≤ (B i a).C + (B i a).A := hterm
    _ ≤ ∑ b : MultiIndex n (2 * k + 1),
        ((B i b).C + (B i b).A) := hinner
    _ ≤ basisBoundMass n k hk := houter
    _ ≤ 1 + basisBoundMass n k hk := by linarith

theorem basis_A_le_uniform
    (n k : ℕ) (hk : 1 ≤ k)
    (i : Fin n) (a : MultiIndex n (2 * k + 1)) :
    (basisLinearBounds n k hk i a).A ≤
      basisUniformBound n k hk := by
  let B := basisLinearBounds n k hk
  have hterm :
      (B i a).A ≤ (B i a).C + (B i a).A :=
    le_add_of_nonneg_left (B i a).C_nonneg
  have hinner :
      (B i a).C + (B i a).A ≤
        ∑ b : MultiIndex n (2 * k + 1),
          ((B i b).C + (B i b).A) := by
    apply Finset.single_le_sum
      (s := (Finset.univ : Finset (MultiIndex n (2 * k + 1))))
      (f := fun b => (B i b).C + (B i b).A)
    · intro b _
      exact add_nonneg (B i b).C_nonneg (B i b).A_nonneg
    · exact Finset.mem_univ a
  have houter :
      (∑ b : MultiIndex n (2 * k + 1),
          ((B i b).C + (B i b).A)) ≤
        basisBoundMass n k hk := by
    unfold basisBoundMass
    apply Finset.single_le_sum
      (s := (Finset.univ : Finset (Fin n)))
      (f := fun j =>
        ∑ b : MultiIndex n (2 * k + 1),
          ((basisLinearBounds n k hk j b).C +
            (basisLinearBounds n k hk j b).A))
    · intro j _
      apply Finset.sum_nonneg
      intro b _
      exact add_nonneg (B j b).C_nonneg (B j b).A_nonneg
    · exact Finset.mem_univ i
  calc
    (B i a).A ≤ (B i a).C + (B i a).A := hterm
    _ ≤ ∑ b : MultiIndex n (2 * k + 1),
        ((B i b).C + (B i b).A) := hinner
    _ ≤ basisBoundMass n k hk := houter
    _ ≤ 1 + basisBoundMass n k hk := by linarith

/-! ## A coefficientwise bound for every homogeneous input

The choices in `basisLinearBounds` concern only the fixed finite collection
of coordinate monomials.  An arbitrary homogeneous field is the sum of
those monomials with its rational coefficients.  Linearity therefore gives
a bound whose only input-dependent quantity is the coefficient `ℓ¹` norm.
-/

def coefficientBasisField
    (F : HGAS.PolynomialField n) (d : ℕ)
    (q : Fin n × MultiIndex n d) :
    HGAS.PolynomialField n :=
  scalePolynomialField
    (MvPolynomial.coeff (multiIndexFinsupp q.2) (F q.1))
    (monomialBasisField q.1 q.2)

def coefficientBasisBounds
    (F : HGAS.PolynomialField n) (k : ℕ) (hk : 1 ≤ k)
    (q : Fin n × MultiIndex n (2 * k + 1)) :
    CubicLiftLinearBounds (coefficientBasisField F (2 * k + 1) q) k :=
  (basisLinearBounds n k hk q.1 q.2).scale
    (MvPolynomial.coeff (multiIndexFinsupp q.2) (F q.1))

def homogeneousFieldFlatExpansion
    (d : ℕ) (F : HGAS.PolynomialField n) :
    HGAS.PolynomialField n :=
  sumPolynomialFields
    (Finset.univ :
      Finset (Fin n × MultiIndex n d))
    (coefficientBasisField F d)

theorem homogeneousFieldFlatExpansion_eq_nested
    (d : ℕ) (F : HGAS.PolynomialField n) :
    homogeneousFieldFlatExpansion d F =
      homogeneousFieldExpansion d F := by
  funext j
  simp only [homogeneousFieldFlatExpansion, sumPolynomialFields,
    coefficientBasisField, homogeneousFieldExpansion,
    Finset.sum_apply]
  rw [Fintype.sum_prod_type]

theorem homogeneousFieldFlatExpansion_eq
    (F : HGAS.PolynomialField n)
    (hF : HGAS.IsHomogeneousOfDegree d F) :
    homogeneousFieldFlatExpansion d F = F :=
  (homogeneousFieldFlatExpansion_eq_nested d F).trans
    (homogeneousFieldExpansion_eq F hF)

/-- The real coefficient `ℓ¹` norm of the degree-`d` part of a field.
For a degree-`d` homogeneous field this is the norm of its complete finite
coefficient vector. -/
def fieldCoefficientL1
    (d : ℕ) (F : HGAS.PolynomialField n) : ℝ :=
  ∑ i : Fin n,
    ∑ a : MultiIndex n d,
      |((MvPolynomial.coeff (multiIndexFinsupp a) (F i) : ℚ) : ℝ)|

theorem fieldCoefficientL1_nonneg
    (d : ℕ) (F : HGAS.PolynomialField n) :
    0 ≤ fieldCoefficientL1 d F := by
  apply Finset.sum_nonneg
  intro i _
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem exists_cubicLiftLinearBounds_coefficientwise
    (F : HGAS.PolynomialField n)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F)
    (hk : 1 ≤ k) :
    ∃ b : CubicLiftLinearBounds F k,
      b.C =
        ∑ q : Fin n × MultiIndex n (2 * k + 1),
          |((MvPolynomial.coeff (multiIndexFinsupp q.2)
              (F q.1) : ℚ) : ℝ)| *
            (basisLinearBounds n k hk q.1 q.2).C ∧
      b.A =
        ∑ q : Fin n × MultiIndex n (2 * k + 1),
          |((MvPolynomial.coeff (multiIndexFinsupp q.2)
              (F q.1) : ℚ) : ℝ)| *
            (basisLinearBounds n k hk q.1 q.2).A := by
  let s : Finset (Fin n × MultiIndex n (2 * k + 1)) :=
    Finset.univ
  obtain ⟨bflat, hC, hA⟩ :=
    exists_cubicLiftLinearBounds_sum_exact
      (k := k) s
      (coefficientBasisField F (2 * k + 1))
      (coefficientBasisBounds F k hk)
  have hfield :
      sumPolynomialFields s
          (coefficientBasisField F (2 * k + 1)) = F := by
    simpa [s, homogeneousFieldFlatExpansion] using
      homogeneousFieldFlatExpansion_eq F hF
  let b : CubicLiftLinearBounds F k := bflat.cast hfield
  refine ⟨b, ?_, ?_⟩
  · rw [show b.C = bflat.C by simp [b]]
    rw [hC]
    simp only [s, coefficientBasisBounds,
      CubicLiftLinearBounds.scale]
  · rw [show b.A = bflat.A by simp [b]]
    rw [hA]
    simp only [s, coefficientBasisBounds,
      CubicLiftLinearBounds.scale]

theorem exists_cubicLiftLinearBounds_uniform
    (F : HGAS.PolynomialField n)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F)
    (hk : 1 ≤ k) :
    ∃ b : CubicLiftLinearBounds F k,
      b.C ≤ basisUniformBound n k hk *
          fieldCoefficientL1 (2 * k + 1) F ∧
      b.A ≤ basisUniformBound n k hk *
          fieldCoefficientL1 (2 * k + 1) F := by
  obtain ⟨b, hC, hA⟩ :=
    exists_cubicLiftLinearBounds_coefficientwise F hF hk
  refine ⟨b, ?_, ?_⟩
  · rw [hC, fieldCoefficientL1,
      ← Fintype.sum_prod_type
        (fun q : Fin n × MultiIndex n (2 * k + 1) =>
          |((MvPolynomial.coeff (multiIndexFinsupp q.2)
              (F q.1) : ℚ) : ℝ)|),
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q _
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_left
        (basis_C_le_uniform n k hk q.1 q.2)
        (abs_nonneg
          (((MvPolynomial.coeff (multiIndexFinsupp q.2)
            (F q.1) : ℚ) : ℝ))))
  · rw [hA, fieldCoefficientL1,
      ← Fintype.sum_prod_type
        (fun q : Fin n × MultiIndex n (2 * k + 1) =>
          |((MvPolynomial.coeff (multiIndexFinsupp q.2)
              (F q.1) : ℚ) : ℝ)|),
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q _
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_left
        (basis_A_le_uniform n k hk q.1 q.2)
        (abs_nonneg
          (((MvPolynomial.coeff (multiIndexFinsupp q.2)
            (F q.1) : ℚ) : ℝ))))

/-! ## Fixed geometric constants

For fixed `n` and `k`, every analytic constant below is fixed once and for
all.  In particular, the natural number `M` is not computed from the input
field.  Hard-coding a fixed natural in a program is computable, even though
our existence proof chooses it nonconstructively from real inequalities.
Thus the result in this section is fixed-parameter computability, not
uniform computability in varying `(n,k)`.
-/

structure FixedCubicGainParameters
    (n k : ℕ) (hk : 1 ≤ k) where
  c : ℝ
  η : ℝ
  M : ℕ
  c_pos : 0 < c
  η_pos : 0 < η
  M_pos : 0 < M
  morseBott :
    ∀ y : RealVeroneseSpace n k,
      Q y = 1 →
        completeToricEnergy y ≤ η →
          c * completeToricEnergy y ≤ penaltyDissipation y
  angularScale :
    basisUniformBound n k hk < (M : ℝ) * c
  radialScale :
    basisUniformBound n k hk + 1 ≤
      4 * (M : ℝ) * η

theorem nonempty_fixedCubicGainParameters
    (n k : ℕ) (hk : 1 ≤ k) :
    Nonempty (FixedCubicGainParameters n k hk) := by
  obtain ⟨c, η, hc, hη, hMorseBott⟩ :=
    exists_positive_morseBott_coercivity_constants
      (n := n) hk
  let B := basisUniformBound n k hk
  let threshold : ℝ :=
    max 0 (max (B / c) ((B + 1) / (4 * η)))
  obtain ⟨M, hM⟩ := exists_nat_gt threshold
  have hM0 : (0 : ℝ) < M :=
    lt_of_le_of_lt (le_max_left _ _) hM
  have hMB : B / c < (M : ℝ) :=
    lt_of_le_of_lt
      (le_trans (le_max_left _ _)
        (le_max_right 0
          (max (B / c) ((B + 1) / (4 * η)))))
      hM
  have hMR : (B + 1) / (4 * η) < (M : ℝ) :=
    lt_of_le_of_lt
      (le_trans (le_max_right _ _)
        (le_max_right 0
          (max (B / c) ((B + 1) / (4 * η)))))
      hM
  have hAngular : B < (M : ℝ) * c :=
    (div_lt_iff₀ hc).mp hMB
  have hfourEta : 0 < 4 * η := mul_pos (by norm_num) hη
  have hRadial : B + 1 ≤ 4 * (M : ℝ) * η := by
    have hstrict : B + 1 < (M : ℝ) * (4 * η) :=
      (div_lt_iff₀ hfourEta).mp hMR
    nlinarith
  have hMnat : 0 < M := by
    exact_mod_cast hM0
  exact ⟨{
    c := c
    η := η
    M := M
    c_pos := hc
    η_pos := hη
    M_pos := hMnat
    morseBott := hMorseBott
    angularScale := hAngular
    radialScale := hRadial
  }⟩

noncomputable def fixedCubicGainParameters
    (n k : ℕ) (hk : 1 ≤ k) :
    FixedCubicGainParameters n k hk :=
  Classical.choice
    (nonempty_fixedCubicGainParameters n k hk)

/-! ## Executable coefficient norm and gain

The raw sparse code may contain repeated monomials and cancellations.
Consequently we extract each semantic coefficient with
`PolynomialCode.coefficient` before taking its absolute value.  The
enumeration runs over every exponent of the fixed homogeneous degree, so
the decoded result is exactly `1 + ‖F‖₁`, not merely a syntactic bound.
-/

def rationalCodeSum (l : List HGAS.RationalCode) :
    HGAS.RationalCode :=
  l.foldr HGAS.RationalCode.add HGAS.RationalCode.zero

@[simp] theorem decode_rationalCodeSum
    (l : List HGAS.RationalCode) :
    HGAS.RationalCode.decode (rationalCodeSum l) =
      (l.map HGAS.RationalCode.decode).sum := by
  induction l with
  | nil => simp [rationalCodeSum]
  | cons q l ih =>
      change
        HGAS.RationalCode.decode
            (HGAS.RationalCode.add q (rationalCodeSum l)) =
          HGAS.RationalCode.decode q +
            (l.map HGAS.RationalCode.decode).sum
      rw [HGAS.RationalCode.decode_add, ih]

theorem rationalCodeSum_primrec :
    Primrec rationalCodeSum := by
  have hstep :
      Primrec₂
        (fun (_ : List HGAS.RationalCode)
          (state : HGAS.RationalCode × HGAS.RationalCode) =>
          HGAS.RationalCode.add state.1 state.2) :=
    HGAS.RationalCode.add_primrec.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.right)
  exact
    (Primrec.list_foldr Primrec.id
      (Primrec.const HGAS.RationalCode.zero) hstep).of_eq
      fun _ => rfl

def degreeCoefficientL1Code
    (n d : ℕ) (p : HGAS.PolynomialCode n) :
    HGAS.RationalCode :=
  rationalCodeSum
    (List.ofFn fun j : Fin (cubicLiftCodeDimension n d) =>
      HGAS.RationalCode.abs
        (HGAS.PolynomialCode.coefficient
          (sourceExponentAt n d j) p))

theorem degreeCoefficientL1Code_primrec
    (n d : ℕ) :
    Primrec (degreeCoefficientL1Code n d) := by
  apply rationalCodeSum_primrec.comp
  apply Primrec.list_ofFn
  intro j
  exact HGAS.RationalCode.abs_primrec.comp
    (HGAS.PolynomialCode.coefficient_primrec.comp
      (Primrec.const (sourceExponentAt n d j))
      Primrec.id)

@[simp] theorem exponentCode_decode_sourceExponentAt
    (n d : ℕ)
    (j : Fin (cubicLiftCodeDimension n d)) :
    HGAS.ExponentCode.decode (sourceExponentAt n d j) =
      multiIndexFinsupp ((degreeIndexEquiv n d).symm j) := by
  ext i
  simp [sourceExponentAt, HGAS.ExponentCode.decode,
    multiIndexFinsupp]

@[simp] theorem exponentCode_decode_multiIndex
    (a : MultiIndex n d) :
    HGAS.ExponentCode.decode a.1 = multiIndexFinsupp a := by
  ext i
  simp [HGAS.ExponentCode.decode, multiIndexFinsupp]

@[simp] theorem decode_degreeCoefficientL1Code
    (n d : ℕ) (p : HGAS.PolynomialCode n) :
    HGAS.RationalCode.decode (degreeCoefficientL1Code n d p) =
      ∑ a : MultiIndex n d,
        |MvPolynomial.coeff (multiIndexFinsupp a)
          (HGAS.PolynomialCode.decode p)| := by
  rw [degreeCoefficientL1Code, decode_rationalCodeSum,
    List.map_ofFn, List.sum_ofFn]
  symm
  apply Fintype.sum_equiv (degreeIndexEquiv n d)
  intro a
  simp [sourceExponentAt, degreeIndexEquiv]

def fieldCoefficientScaleCode
    (n d : ℕ) (F : HGAS.PolynomialFieldCode n) :
    HGAS.RationalCode :=
  HGAS.RationalCode.add HGAS.RationalCode.one
    (rationalCodeSum
      (List.ofFn fun i : Fin n =>
        degreeCoefficientL1Code n d (F i)))

theorem fieldCoefficientScaleCode_primrec
    (n d : ℕ) :
    Primrec (fieldCoefficientScaleCode n d) := by
  apply HGAS.RationalCode.add_primrec.comp
  · exact Primrec.const HGAS.RationalCode.one
  · apply rationalCodeSum_primrec.comp
    apply Primrec.list_ofFn
    intro i
    exact (degreeCoefficientL1Code_primrec n d).comp
      (Primrec.fin_app.comp Primrec.id (Primrec.const i))

@[simp] theorem decode_fieldCoefficientScaleCode
    (n d : ℕ) (F : HGAS.PolynomialFieldCode n) :
    HGAS.RationalCode.decode (fieldCoefficientScaleCode n d F) =
      1 +
        ∑ i : Fin n,
          ∑ a : MultiIndex n d,
            |MvPolynomial.coeff (multiIndexFinsupp a)
              (HGAS.PolynomialCode.decode (F i))| := by
  simp [fieldCoefficientScaleCode, List.sum_ofFn]

/-- For each fixed `(n,k)`, the input-computable gain.  Its only
input-dependent operations are rational absolute value, addition, and
multiplication.  The natural multiplier is the fixed, nonuniformly selected
constant for that pair. -/
def effectiveCubicGainCode
    (n k : ℕ) (hk : 1 ≤ k)
    (F : HGAS.PolynomialFieldCode n) :
    HGAS.RationalCode :=
  HGAS.RationalCode.mul
    (HGAS.RationalCode.ofNat
      (fixedCubicGainParameters n k hk).M)
    (fieldCoefficientScaleCode n (2 * k + 1) F)

theorem effectiveCubicGainCode_primrec
    (n k : ℕ) (hk : 1 ≤ k) :
    Primrec (effectiveCubicGainCode n k hk) := by
  apply HGAS.RationalCode.mul_primrec.comp
  · exact Primrec.const
      (HGAS.RationalCode.ofNat
        (fixedCubicGainParameters n k hk).M)
  · exact fieldCoefficientScaleCode_primrec n (2 * k + 1)

@[simp] theorem decode_effectiveCubicGainCode
    (n k : ℕ) (hk : 1 ≤ k)
    (F : HGAS.PolynomialFieldCode n) :
    HGAS.RationalCode.decode (effectiveCubicGainCode n k hk F) =
      ((fixedCubicGainParameters n k hk).M : ℚ) *
        (1 +
          ∑ i : Fin n,
            ∑ a : MultiIndex n (2 * k + 1),
              |MvPolynomial.coeff (multiIndexFinsupp a)
                (HGAS.PolynomialCode.decode (F i))|) := by
  simp [effectiveCubicGainCode]

theorem real_decode_effectiveCubicGainCode
    (n k : ℕ) (hk : 1 ≤ k)
    (F : HGAS.PolynomialFieldCode n) :
    ((HGAS.RationalCode.decode
      (effectiveCubicGainCode n k hk F) : ℚ) : ℝ) =
      ((fixedCubicGainParameters n k hk).M : ℝ) *
        (1 + fieldCoefficientL1 (2 * k + 1)
          (HGAS.PolynomialFieldCode.decode F)) := by
  rw [decode_effectiveCubicGainCode]
  push_cast
  simp only [fieldCoefficientL1,
    HGAS.PolynomialFieldCode.decode]

theorem decode_effectiveCubicGainCode_pos
    (n k : ℕ) (hk : 1 ≤ k)
    (F : HGAS.PolynomialFieldCode n) :
    0 < HGAS.RationalCode.decode
      (effectiveCubicGainCode n k hk F) := by
  have hreal :
      0 <
        ((HGAS.RationalCode.decode
          (effectiveCubicGainCode n k hk F) : ℚ) : ℝ) := by
    rw [real_decode_effectiveCubicGainCode]
    exact mul_pos
      (by
        exact_mod_cast
          (fixedCubicGainParameters n k hk).M_pos)
      (by
        linarith [fieldCoefficientL1_nonneg
          (2 * k + 1) (HGAS.PolynomialFieldCode.decode F)])
  exact_mod_cast hreal

/-- For fixed `(n,k)`, the input-computable gain satisfies all analytic
hypotheses required by the cubic stabilization theorem.  This is the bridge
between the finite code calculation and the semantic flow construction. -/
theorem exists_effectiveCubicLiftStabilizationBounds
    (Fcode : HGAS.PolynomialFieldCode n)
    (hF :
      HGAS.IsHomogeneousOfDegree (2 * k + 1)
        (HGAS.PolynomialFieldCode.decode Fcode))
    (hk : 1 ≤ k) :
    ∃ b : CubicLiftStabilizationBounds
        (HGAS.PolynomialFieldCode.decode Fcode) k,
      b.K =
        HGAS.RationalCode.decode
          (effectiveCubicGainCode n k hk Fcode) := by
  let F := HGAS.PolynomialFieldCode.decode Fcode
  let p := fixedCubicGainParameters n k hk
  let B := basisUniformBound n k hk
  let L := fieldCoefficientL1 (2 * k + 1) F
  obtain ⟨b, hC, hA⟩ :=
    exists_cubicLiftLinearBounds_uniform F hF hk
  have hL : 0 ≤ L :=
    fieldCoefficientL1_nonneg (2 * k + 1) F
  have hB : 0 ≤ B :=
    le_of_lt (basisUniformBound_pos n k hk)
  have hscale : 0 < 1 + L := by linarith
  let K : ℚ :=
    HGAS.RationalCode.decode
      (effectiveCubicGainCode n k hk Fcode)
  have hKreal :
      (K : ℝ) = (p.M : ℝ) * (1 + L) := by
    simpa [K, p, L, F] using
      real_decode_effectiveCubicGainCode n k hk Fcode
  have hKpos : 0 < K :=
    decode_effectiveCubicGainCode_pos n k hk Fcode
  have hAngular : b.C < (K : ℝ) * p.c := by
    calc
      b.C ≤ B * L := by simpa [B, L] using hC
      _ ≤ B * (1 + L) :=
        mul_le_mul_of_nonneg_left (by linarith) hB
      _ < ((p.M : ℝ) * p.c) * (1 + L) :=
        mul_lt_mul_of_pos_right
          (by simpa [B, p] using p.angularScale)
          hscale
      _ = (K : ℝ) * p.c := by rw [hKreal]; ring
  have hRadial : b.A + 1 ≤ 4 * (K : ℝ) * p.η := by
    have hA' : b.A ≤ B * L := by
      simpa [B, L] using hA
    calc
      b.A + 1 ≤ B * L + 1 :=
        by simpa [add_comm] using add_le_add_right hA' 1
      _ ≤ (B + 1) * (1 + L) := by nlinarith
      _ ≤ (4 * (p.M : ℝ) * p.η) * (1 + L) :=
        mul_le_mul_of_nonneg_right
          (by simpa [B, p] using p.radialScale)
          (le_of_lt hscale)
      _ = 4 * (K : ℝ) * p.η := by rw [hKreal]; ring
  refine ⟨{
    c := p.c
    η := p.η
    C := b.C
    A := b.A
    K := K
    c_pos := p.c_pos
    η_pos := p.η_pos
    C_nonneg := b.C_nonneg
    A_nonneg := b.A_nonneg
    K_pos := hKpos
    morseBott := p.morseBott
    angularTangency := b.angularTangency
    radialBound := b.radialBound
    angularGain := hAngular
    radialGain := hRadial
  }, rfl⟩

/-! ## A total compiler on raw field codes

Malformed source codes are negative instances of `HGASQ` by definition.
The compiler therefore sends them to the zero cubic field, which is also a
negative GAS instance as soon as the ambient space has a nonzero vector.
-/

def zeroPolynomialFieldCode (m : ℕ) :
    HGAS.PolynomialFieldCode m :=
  fun _ => HGAS.PolynomialCode.zero

theorem zeroPolynomialFieldCode_homogeneous
    (m d : ℕ) :
    HGAS.PolynomialFieldCode.homogeneous d
      (zeroPolynomialFieldCode m) = true := by
  rw [HGAS.PolynomialFieldCode.homogeneous_eq_true_iff]
  intro i
  rw [show HGAS.PolynomialCode.decode
      (zeroPolynomialFieldCode m i) = 0 by
    simp [zeroPolynomialFieldCode]]
  exact MvPolynomial.isHomogeneous_zero _ _ _

theorem realize_zeroPolynomialFieldCode
    (m : ℕ) :
    HGAS.PolynomialFieldCode.realize
        (zeroPolynomialFieldCode m) =
      (fun _ : Fin m → ℝ => (0 : Fin m → ℝ)) := by
  funext x i
  simp [zeroPolynomialFieldCode,
    HGAS.PolynomialFieldCode.realize_apply]

theorem zeroVectorField_not_globallyAsymptoticallyStable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (hx : x ≠ 0) :
    ¬ HGAS.GloballyAsymptoticallyStable
        (fun _ : E => (0 : E)) 0 := by
  intro hGAS
  have htrajectory :
      HGAS.IsForwardTrajectory
        (fun _ : E => (0 : E)) (fun _ : ℝ => x) x :=
    HGAS.IsForwardTrajectory.const_of_equilibrium rfl
  have hdist : 0 < dist x 0 :=
    dist_pos.mpr hx
  obtain ⟨T, _hT, hafter⟩ :=
    hGAS.attractive x (fun _ : ℝ => x) htrajectory
      (dist x 0 / 2) (by linarith)
  have hcontradiction := hafter T le_rfl
  linarith

def sourceBasisVector (i : Fin n) : Fin n → ℝ :=
  fun j => if j = i then 1 else 0

theorem sourceBasisVector_ne_zero
    (i : Fin n) :
    sourceBasisVector i ≠ 0 := by
  intro h
  have := congrFun h i
  simp [sourceBasisVector] at this

theorem sourceBasisVector_mem_unitSphere
    (i : Fin n) :
    sourceBasisVector i ∈ sourceUnitSphere n := by
  simp [sourceUnitSphere, sourceRadiusSq, sourceBasisVector,
    Finset.sum_ite_eq', Finset.mem_univ]

def sourceUnitSpherePointOfPos
    (n : ℕ) (hn : 0 < n) :
    sourceUnitSphere n :=
  let i : Fin n := ⟨0, hn⟩
  ⟨sourceBasisVector i, sourceBasisVector_mem_unitSphere i⟩

def targetBasisVector
    (n k : ℕ) (i : Fin n) :
    Fin (cubicLiftCodeDimension n k) → ℝ :=
  let j := cubicLiftIndexEquiv n k (pureMultiIndex (k := k) i)
  fun q => if q = j then 1 else 0

theorem targetBasisVector_ne_zero
    (n k : ℕ) (i : Fin n) :
    targetBasisVector n k i ≠ 0 := by
  intro h
  let j := cubicLiftIndexEquiv n k (pureMultiIndex (k := k) i)
  have := congrFun h j
  simp [targetBasisVector, j] at this

theorem zeroTargetCode_not_hgasQ
    (n k : ℕ) (hn : 0 < n) :
    ¬ HGAS.HGASQ (cubicLiftCodeDimension n k) 3
      (zeroPolynomialFieldCode (cubicLiftCodeDimension n k)) := by
  intro h
  let i : Fin n := ⟨0, hn⟩
  have hzero :
      ¬ HGAS.GloballyAsymptoticallyStable
          (fun _ : Fin (cubicLiftCodeDimension n k) → ℝ =>
            (0 : Fin (cubicLiftCodeDimension n k) → ℝ)) 0 :=
    zeroVectorField_not_globallyAsymptoticallyStable
      (targetBasisVector n k i)
      (targetBasisVector_ne_zero n k i)
  apply hzero
  rw [← realize_zeroPolynomialFieldCode]
  exact h.2

/-- Total fixed-parameter compiler.  The Boolean guard is part of the
program, so the reduction is defined on every raw sparse field code. -/
def effectiveCubicReductionCode
    (n k : ℕ) (hk : 1 ≤ k)
    (F : HGAS.PolynomialFieldCode n) :
    HGAS.PolynomialFieldCode (cubicLiftCodeDimension n k) :=
  bif HGAS.PolynomialFieldCode.homogeneous (2 * k + 1) F then
    stabilizedCubicFieldCode n k F
      (effectiveCubicGainCode n k hk F)
  else
    zeroPolynomialFieldCode (cubicLiftCodeDimension n k)

theorem effectiveCubicReductionCode_primrec
    (n k : ℕ) (hk : 1 ≤ k) :
    Primrec (effectiveCubicReductionCode n k hk) := by
  apply Primrec.cond
  · exact
      (HGAS.PolynomialFieldCode.homogeneous_primrec n).comp
        (Primrec.pair (Primrec.const (2 * k + 1)) Primrec.id)
  · exact
      (stabilizedCubicFieldCode_primrec n k).comp
        Primrec.id (effectiveCubicGainCode_primrec n k hk)
  · exact Primrec.const
      (zeroPolynomialFieldCode (cubicLiftCodeDimension n k))

theorem effectiveCubicReductionCode_homogeneous
    (n k : ℕ) (hk : 1 ≤ k)
    (F : HGAS.PolynomialFieldCode n) :
    HGAS.PolynomialFieldCode.homogeneous 3
      (effectiveCubicReductionCode n k hk F) = true := by
  by_cases h :
      HGAS.PolynomialFieldCode.homogeneous (2 * k + 1) F = true
  · simp [effectiveCubicReductionCode, h,
      stabilizedCubicFieldCode_homogeneous]
  · have hf :
        HGAS.PolynomialFieldCode.homogeneous (2 * k + 1) F = false :=
      Bool.eq_false_of_not_eq_true h
    simp [effectiveCubicReductionCode, hf,
      zeroPolynomialFieldCode_homogeneous]

theorem effectiveCubicReductionCode_hgasQ_iff_of_homogeneous
    (n k : ℕ) (hn : 0 < n) (hk : 1 ≤ k)
    (Fcode : HGAS.PolynomialFieldCode n)
    (hvalid :
      HGAS.PolynomialFieldCode.homogeneous
        (2 * k + 1) Fcode = true) :
    HGAS.HGASQ n (2 * k + 1) Fcode ↔
      HGAS.HGASQ (cubicLiftCodeDimension n k) 3
        (effectiveCubicReductionCode n k hk Fcode) := by
  have hF :
      HGAS.IsHomogeneousOfDegree (2 * k + 1)
        (HGAS.PolynomialFieldCode.decode Fcode) :=
    (HGAS.PolynomialFieldCode.homogeneous_eq_true_iff
      (2 * k + 1) Fcode).mp hvalid
  letI : Nonempty (sourceUnitSphere n) :=
    ⟨sourceUnitSpherePointOfPos n hn⟩
  have hreduction :
      effectiveCubicReductionCode n k hk Fcode =
        stabilizedCubicFieldCode n k Fcode
          (effectiveCubicGainCode n k hk Fcode) := by
    simp [effectiveCubicReductionCode, hvalid]
  have htargetValid :
      HGAS.PolynomialFieldCode.homogeneous 3
        (effectiveCubicReductionCode n k hk Fcode) = true :=
    effectiveCubicReductionCode_homogeneous n k hk Fcode
  rw [HGAS.hgasQ_iff_of_homogeneous Fcode hvalid,
    HGAS.hgasQ_iff_of_homogeneous
      (effectiveCubicReductionCode n k hk Fcode) htargetValid,
    hreduction,
    globallyAsymptoticallyStable_realize_stabilizedCode_iff]
  obtain ⟨b, hbK⟩ :=
    exists_effectiveCubicLiftStabilizationBounds Fcode hF hk
  rw [← hbK]
  change
    HGAS.GloballyAsymptoticallyStable
        (evaluatedSourceField
          (HGAS.PolynomialFieldCode.decode Fcode)) 0 ↔
      HGAS.GloballyAsymptoticallyStable
        (evaluatedStabilizedCubicField b) 0
  exact sourceGAS_iff_stabilizedCubicGAS b hF hk

/-- Exact correctness of the total compiler on arbitrary raw codes. -/
theorem effectiveCubicReductionCode_hgasQ_iff
    (n k : ℕ) (hn : 0 < n) (hk : 1 ≤ k)
    (Fcode : HGAS.PolynomialFieldCode n) :
    HGAS.HGASQ n (2 * k + 1) Fcode ↔
      HGAS.HGASQ (cubicLiftCodeDimension n k) 3
        (effectiveCubicReductionCode n k hk Fcode) := by
  by_cases hvalid :
      HGAS.PolynomialFieldCode.homogeneous
        (2 * k + 1) Fcode = true
  · exact effectiveCubicReductionCode_hgasQ_iff_of_homogeneous
      n k hn hk Fcode hvalid
  · have hfalse :
        HGAS.PolynomialFieldCode.homogeneous
          (2 * k + 1) Fcode = false :=
      Bool.eq_false_of_not_eq_true hvalid
    have hsource :
        ¬ HGAS.HGASQ n (2 * k + 1) Fcode := by
      intro h
      exact hvalid h.1
    have hreduction :
        effectiveCubicReductionCode n k hk Fcode =
          zeroPolynomialFieldCode
            (cubicLiftCodeDimension n k) := by
      simp [effectiveCubicReductionCode, hfalse]
    have htarget :
        ¬ HGAS.HGASQ (cubicLiftCodeDimension n k) 3
          (effectiveCubicReductionCode n k hk Fcode) := by
      rw [hreduction]
      exact zeroTargetCode_not_hgasQ n k hn
    exact ⟨fun h => (hsource h).elim,
      fun h => (htarget h).elim⟩

/-- **Fixed-parameter computable reduction from every odd homogeneous
degree to cubic degree.**

For each fixed positive source dimension `n` and fixed `k ≥ 1`, the
function `effectiveCubicReductionCode n k hk` is a many-one reduction from
degree `2k+1` rational homogeneous GAS to cubic rational homogeneous GAS
in the fixed target dimension `card (MultiIndex n k)`.
-/
theorem hgasQ_manyOneReducible_cubic
    (n k : ℕ) (hn : 0 < n) (hk : 1 ≤ k) :
    HGAS.HGASQ n (2 * k + 1) ≤₀
      HGAS.HGASQ (cubicLiftCodeDimension n k) 3 := by
  exact ⟨effectiveCubicReductionCode n k hk,
    (effectiveCubicReductionCode_primrec n k hk).to_comp,
    effectiveCubicReductionCode_hgasQ_iff n k hn hk⟩

end

end HGAS.Veronese
