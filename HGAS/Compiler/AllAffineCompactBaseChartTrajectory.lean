import HGAS.Compiler.AllAffineCompactSourceTrajectory
import HGAS.Compiler.AllAffinePositiveCentralTrajectory
import Mathlib.Tactic

/-!
# The finite chart of the all-affine compact base

The all-affine compiler first replaces `z ∈ ℝⁿ` by one central sphere

```text
                         (x,w),   ‖x‖²+w²=1,
```

and only later adjoins the accumulator sphere.  Existing finite-chart
lemmas recover `z=x/w` from the *complete* source.  A canonical component,
however, lives naturally in the compact base before that final sphere is
added.  This module supplies the corresponding base-only interface.

On any base trajectory that remains in `w ≠ 0`, the recovered affine
coordinate solves

```text
                 z' = (1+‖z‖²)⁻ᴷ P(z)
```

when the clearing exponent is `2K`.  The statements are formulated for an
arbitrary complete base-space curve, making them reusable for orbit
closures and invariant components.
-/

namespace HGAS

open _root_.MvPolynomial
open Set

noncomputable section

namespace CompactAccumulatorPipelineCode

namespace AllAffineCompactBaseChartTrajectory

open AllAffineCompactSourceChart
open AllAffineCompactSourceTrajectory

variable {n : ℕ}

/-- Old compact coordinates of the one-block base. -/
def oldPoint (b : BaseSpace (layout n)) : Fin n → ℝ :=
  fun j ↦ b.1
    (MixedCentralPolynomialCode.xIndex (k := 1) j)

/-- The unique central chart coordinate of the one-block base. -/
def weight (b : BaseSpace (layout n)) : ℝ :=
  b.1 (MixedCentralPolynomialCode.wIndex (n := n) 0)

theorem continuous_oldPoint :
    Continuous
      (oldPoint : BaseSpace (layout n) → (Fin n → ℝ)) := by
  apply continuous_pi
  intro j
  exact
    (continuous_apply
      (MixedCentralPolynomialCode.xIndex (k := 1) j)).comp
      continuous_subtype_val

theorem continuous_weight :
    Continuous (weight : BaseSpace (layout n) → ℝ) :=
  (continuous_apply
    (MixedCentralPolynomialCode.wIndex (n := n) 0)).comp
    continuous_subtype_val

/-- The finite interior of the compact base. -/
def finiteInterior :
    Set (BaseSpace (layout n)) :=
  {b | weight b ≠ 0}

/-- A base point equipped with the fact that its central coordinate is
nonzero. -/
abbrev FiniteBaseSpace (n : ℕ) :=
  finiteInterior (n := n)

/-- The base coordinates form the ordinary central sphere. -/
theorem sphereEquation
    (b : BaseSpace (layout n)) :
    normSq (oldPoint b) + weight b ^ 2 = 1 := by
  have hb :
      MixedCentralPolynomialCode.chartPoint
          (oldPoint b) (fun _ : Fin 1 ↦ weight b) =
        b.1 := by
    have hw :
        (fun _ : Fin 1 ↦ weight b) =
          fun c ↦ b.1
            (MixedCentralPolynomialCode.wIndex (n := n) c) := by
      funext c
      have hc : c = 0 := Subsingleton.elim _ _
      subst c
      rfl
    rw [hw]
    exact
      MixedCentralPolynomialCode.chartPoint_decompose b.1
  have h :=
    b.2 (finSumFinEquiv
      (Sum.inl (0 : Fin 1) : Fin 1 ⊕ Fin 0))
  rw [← hb] at h
  rw [MixedCentralPolynomialCode.sourceBlockNormSq_targetBlock,
    MixedCentralPolynomialCode.targetBlockNormSq_affine] at h
  simpa only [
    MixedCentralPolynomialCode.affineBlockNormSq,
    AllAffineCompactSourceChart.layout,
    MixedCentralPolynomialCode.oneBlockAllAffineLayout,
    if_pos rfl, normSq, dot, pow_two, oldPoint, weight] using h

/-- The canonical finite central chart associated with a finite base
point. -/
def finiteCentralChartPoint
    (b : FiniteBaseSpace n) :
    FiniteCentralChart n :=
  ⟨⟨(oldPoint b.1, weight b.1), sphereEquation b.1⟩, b.2⟩

/-- Recover the affine coordinate `z=x/w`. -/
def affinePoint
    (b : FiniteBaseSpace n) :
    Fin n → ℝ :=
  centralChartCoordinate (finiteCentralChartPoint b)

@[simp]
theorem affinePoint_apply
    (b : FiniteBaseSpace n) (j : Fin n) :
    affinePoint b j = oldPoint b.1 j / weight b.1 :=
  rfl

theorem continuous_finiteCentralChartPoint :
    Continuous
      (finiteCentralChartPoint :
        FiniteBaseSpace n → FiniteCentralChart n) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact
    (continuous_oldPoint.comp continuous_subtype_val).prodMk
      (continuous_weight.comp continuous_subtype_val)

theorem continuous_affinePoint :
    Continuous
      (affinePoint : FiniteBaseSpace n → (Fin n → ℝ)) :=
  continuous_centralChartCoordinate.comp
    continuous_finiteCentralChartPoint

/-- The positive base point belongs to the finite base chart. -/
def finitePositiveBasePoint
    (z : Fin n → ℝ) :
    FiniteBaseSpace n :=
  ⟨AllAffinePositiveCentralTrajectory.positiveBasePoint z, by
    change
      (AllAffinePositiveCentralTrajectory.positiveBasePoint z).1
          (MixedCentralPolynomialCode.wIndex (n := n) 0) ≠
        0
    rw [AllAffinePositiveCentralTrajectory.positiveBasePoint_wIndex]
    exact positiveCentralScale_ne_zero z⟩

/-- Recovering affine coordinates from their positive compactification is
the identity. -/
@[simp]
theorem affinePoint_finitePositiveBasePoint
    (z : Fin n → ℝ) :
    affinePoint (finitePositiveBasePoint z) = z := by
  funext j
  rw [affinePoint_apply]
  change
    (AllAffinePositiveCentralTrajectory.positiveBasePoint z).1
          (MixedCentralPolynomialCode.xIndex (k := 1) j) /
        (AllAffinePositiveCentralTrajectory.positiveBasePoint z).1
          (MixedCentralPolynomialCode.wIndex (n := n) 0) =
      z j
  rw [
    AllAffinePositiveCentralTrajectory.positiveBasePoint_xIndex,
    AllAffinePositiveCentralTrajectory.positiveBasePoint_wIndex]
  exact
    congrFun
      (centralChartCoordinate_positiveCentralChartPoint z) j

/-- Compact old coordinates are `x=wz`. -/
theorem oldPoint_eq_weight_mul_affinePoint
    (b : FiniteBaseSpace n) (j : Fin n) :
    oldPoint b.1 j =
      weight b.1 * affinePoint b j := by
  rw [affinePoint_apply]
  exact
    (mul_div_cancel₀ (oldPoint b.1 j) b.2).symm

/-- The positive affine reconstruction of the literal base point. -/
theorem scaledChartPoint_affinePoint
    (b : FiniteBaseSpace n) :
    MixedCentralPolynomialCode.scaledChartPoint
        (layout n) (fun _ : Fin 1 ↦ weight b.1) (affinePoint b) =
      b.1.1 := by
  funext q
  obtain ⟨j | c, rfl⟩ := finSumFinEquiv.surjective q
  · rw [show
      finSumFinEquiv (Sum.inl j : Fin n ⊕ Fin 1) =
        MixedCentralPolynomialCode.xIndex (k := 1) j by
          rfl]
    rw [MixedCentralPolynomialCode.scaledChartPoint_xIndex]
    change
      weight b.1 * affinePoint b j =
        oldPoint b.1 j
    exact (oldPoint_eq_weight_mul_affinePoint b j).symm
  · have hc : c = 0 := Subsingleton.elim _ _
    subst c
    rw [show
      finSumFinEquiv (Sum.inr (0 : Fin 1) : Fin n ⊕ Fin 1) =
        MixedCentralPolynomialCode.wIndex (n := n) 0 by
          rfl]
    rw [MixedCentralPolynomialCode.scaledChartPoint_wIndex]
    rfl

/-- The even compact chart power equals the intrinsic affine slowdown. -/
theorem weight_evenPow_eq_affineSpeed
    (K : ℕ) (b : FiniteBaseSpace n) :
    weight b.1 ^ (2 * K) =
      affineSpeed K (affinePoint b) := by
  have hden :
      1 + normSq (affinePoint b) ≠ 0 :=
    ne_of_gt (one_add_normSq_pos (affinePoint b))
  have hsphere := sphereEquation b.1
  have hx :
      normSq (oldPoint b.1) =
        weight b.1 ^ 2 * normSq (affinePoint b) := by
    unfold normSq dot
    simp_rw [oldPoint_eq_weight_mul_affinePoint]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hx] at hsphere
  have hsq :
      weight b.1 ^ 2 =
        (1 + normSq (affinePoint b))⁻¹ := by
    apply (mul_eq_one_iff_eq_inv₀ hden).mp
    nlinarith
  rw [pow_mul, hsq]
  rfl

variable
  (K : ℕ) (P : PolynomialFieldCode n)

/-- Literal base-field velocity of an old compact coordinate, expressed
in finite-chart affine variables. -/
theorem realize_baseFieldCode_oldPoint
    (hP :
      ∀ j,
        MixedCentralPolynomialCode.TermsAffineBlockDegreeLE
          (layout n) (2 * K) (P j))
    (b : FiniteBaseSpace n) (j : Fin n) :
    PolynomialFieldCode.realize
        (baseFieldCode (layout n) (2 * K) P) b.1.1
        (MixedCentralPolynomialCode.xIndex (k := 1) j) =
      centralCompactXField
        (affineSpeed K (affinePoint b))
        (weight b.1) (oldPoint b.1)
        (PolynomialFieldCode.realize P (affinePoint b)) j := by
  rw [PolynomialFieldCode.realize_apply, baseFieldCode]
  rw [← scaledChartPoint_affinePoint b]
  rw [MixedCentralPolynomialCode.eval₂Hom_fieldCode_scaledChart
    (layout n) (2 * K) P hP
    (MixedCentralPolynomialCode.xIndex (k := 1) j)
    (fun _ : Fin 1 ↦ weight b.1) (affinePoint b)]
  simp only [MixedCentralPolynomialCode.mixedAmbientField,
    MixedCentralPolynomialCode.finSumFinEquiv_symm_xIndex]
  rw [slowdown_eq_weight_pow, weight_evenPow_eq_affineSpeed]
  rw [mixedXField_eq_centralCompactXField]
  rw [show
    MixedCentralPolynomialCode.scaledSourcePoint
        (layout n) (fun _ : Fin 1 ↦ weight b.1) (affinePoint b) =
      oldPoint b.1 by
        funext i
        change
          weight b.1 * affinePoint b i = oldPoint b.1 i
        exact (oldPoint_eq_weight_mul_affinePoint b i).symm]
  have hp :
      (fun i ↦
        eval₂Hom (algebraMap ℚ ℝ) (affinePoint b)
          (PolynomialCode.decode (P i))) =
        PolynomialFieldCode.realize P (affinePoint b) := by
    funext i
    rw [PolynomialFieldCode.realize_apply]
  rw [hp]

/-- Literal base-field velocity of the central chart coordinate. -/
theorem realize_baseFieldCode_weight
    (hP :
      ∀ j,
        MixedCentralPolynomialCode.TermsAffineBlockDegreeLE
          (layout n) (2 * K) (P j))
    (b : FiniteBaseSpace n) :
    PolynomialFieldCode.realize
        (baseFieldCode (layout n) (2 * K) P) b.1.1
        (MixedCentralPolynomialCode.wIndex (n := n) 0) =
      centralCompactWField
        (affineSpeed K (affinePoint b))
        (weight b.1) (oldPoint b.1)
        (PolynomialFieldCode.realize P (affinePoint b)) := by
  rw [PolynomialFieldCode.realize_apply, baseFieldCode]
  rw [← scaledChartPoint_affinePoint b]
  rw [MixedCentralPolynomialCode.eval₂Hom_fieldCode_scaledChart
    (layout n) (2 * K) P hP
    (MixedCentralPolynomialCode.wIndex (n := n) 0)
    (fun _ : Fin 1 ↦ weight b.1) (affinePoint b)]
  simp only [MixedCentralPolynomialCode.mixedAmbientField,
    MixedCentralPolynomialCode.finSumFinEquiv_symm_wIndex]
  rw [slowdown_eq_weight_pow, weight_evenPow_eq_affineSpeed]
  rw [mixedWField_eq_centralCompactWField]
  rw [show
    MixedCentralPolynomialCode.scaledSourcePoint
        (layout n) (fun _ : Fin 1 ↦ weight b.1) (affinePoint b) =
      oldPoint b.1 by
        funext i
        change
          weight b.1 * affinePoint b i = oldPoint b.1 i
        exact (oldPoint_eq_weight_mul_affinePoint b i).symm]
  have hp :
      (fun i ↦
        eval₂Hom (algebraMap ℚ ℝ) (affinePoint b)
          (PolynomialCode.decode (P i))) =
        PolynomialFieldCode.realize P (affinePoint b) := by
    funext i
    rw [PolynomialFieldCode.realize_apply]
  rw [hp]

/-- Exact finite-base-chart semantics of one compiled drift coordinate. -/
theorem baseDriftBCF_eq
    {m : ℕ}
    (κ : RationalCode)
    (h : Fin m → PolynomialCode n)
    (hh :
      ∀ i,
        MixedCentralPolynomialCode.TermsAffineBlockDegreeLE
          (layout n) (2 * K) (h i))
    (b : FiniteBaseSpace n) (i : Fin m) :
    baseDriftBCF (layout n) (2 * K) κ h b.1 i =
      (RationalCode.decode κ : ℝ) *
        affineSpeed K (affinePoint b) *
          eval₂Hom (algebraMap ℚ ℝ) (affinePoint b)
            (PolynomialCode.decode (h i)) := by
  rw [baseDriftBCF_apply]
  rw [← scaledChartPoint_affinePoint b]
  rw [eval₂Hom_slowedDriftCode_scaledChart
    (layout n) (2 * K) κ h hh i
    (fun _ : Fin 1 ↦ weight b.1) (affinePoint b)]
  rw [slowdown_eq_weight_pow,
    weight_evenPow_eq_affineSpeed]

/-- Recover the affine derivative from any complete base curve that stays
in the finite central chart. -/
theorem affinePoint_hasDerivAt
    (hP :
      ∀ j,
        MixedCentralPolynomialCode.TermsAffineBlockDegreeLE
          (layout n) (2 * K) (P j))
    (η : ℝ → BaseSpace (layout n))
    (hη :
      IsIntegralCurve
        (fun t ↦ (η t).1)
        (fun _ y ↦
          PolynomialFieldCode.realize
            (baseFieldCode (layout n) (2 * K) P) y))
    (hfinite : ∀ t, weight (η t) ≠ 0)
    (t : ℝ) :
    HasDerivAt
      (fun s ↦
        affinePoint
          (⟨η s, hfinite s⟩ : FiniteBaseSpace n))
      (affineSpeed K
          (affinePoint
            (⟨η t, hfinite t⟩ : FiniteBaseSpace n)) •
        PolynomialFieldCode.realize P
          (affinePoint
            (⟨η t, hfinite t⟩ : FiniteBaseSpace n))) t := by
  let q : ℝ → FiniteCentralChart n :=
    fun s ↦ finiteCentralChartPoint
      (⟨η s, hfinite s⟩ : FiniteBaseSpace n)
  let f : ℝ → ℝ :=
    fun s ↦ affineSpeed K
      (affinePoint
        (⟨η s, hfinite s⟩ : FiniteBaseSpace n))
  let p : ℝ → Fin n → ℝ :=
    fun s ↦ PolynomialFieldCode.realize P
      (affinePoint
        (⟨η s, hfinite s⟩ : FiniteBaseSpace n))
  have hX :
      ∀ j,
        HasDerivAt
          (fun s ↦ (q s).1.1.1 j)
          (centralCompactXField
            (f t) (q t).1.1.2 (q t).1.1.1 (p t) j) t := by
    intro j
    have hcoord :=
      (hasDerivAt_pi.mp (hη t))
        (MixedCentralPolynomialCode.xIndex (k := 1) j)
    have hvelocity :=
      realize_baseFieldCode_oldPoint K P hP
        (⟨η t, hfinite t⟩ : FiniteBaseSpace n) j
    have hcoord' := hcoord.congr_deriv hvelocity
    simpa only [q, f, p, finiteCentralChartPoint] using hcoord'
  have hW :
      HasDerivAt
        (fun s ↦ (q s).1.1.2)
        (centralCompactWField
          (f t) (q t).1.1.2 (q t).1.1.1 (p t)) t := by
    have hcoord :=
      (hasDerivAt_pi.mp (hη t))
        (MixedCentralPolynomialCode.wIndex (n := n) 0)
    have hvelocity :=
      realize_baseFieldCode_weight K P hP
        (⟨η t, hfinite t⟩ : FiniteBaseSpace n)
    have hcoord' := hcoord.congr_deriv hvelocity
    simpa only [q, f, p, finiteCentralChartPoint] using hcoord'
  have hchart :=
    centralChartCoordinate_hasDerivAt q f p t hX hW
  rw [hasDerivAt_pi]
  intro j
  simpa only [q, f, p, affinePoint, Pi.smul_apply,
    smul_eq_mul] using hchart j

/-- Vector-field form of the recovered finite-chart affine equation. -/
theorem affinePoint_isIntegralCurve
    (hP :
      ∀ j,
        MixedCentralPolynomialCode.TermsAffineBlockDegreeLE
          (layout n) (2 * K) (P j))
    (η : ℝ → BaseSpace (layout n))
    (hη :
      IsIntegralCurve
        (fun t ↦ (η t).1)
        (fun _ y ↦
          PolynomialFieldCode.realize
            (baseFieldCode (layout n) (2 * K) P) y))
    (hfinite : ∀ t, weight (η t) ≠ 0) :
    IsIntegralCurve
      (fun t ↦
        affinePoint
          (⟨η t, hfinite t⟩ : FiniteBaseSpace n))
      (fun _ z ↦
        timeScaledField (affineSpeed K)
          (PolynomialFieldCode.realize P) z) := by
  intro t
  simpa only [timeScaledField] using
    affinePoint_hasDerivAt K P hP η hη hfinite t

end AllAffineCompactBaseChartTrajectory

end CompactAccumulatorPipelineCode

end

end HGAS
