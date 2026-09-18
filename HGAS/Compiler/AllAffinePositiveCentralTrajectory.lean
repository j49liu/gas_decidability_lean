import HGAS.Compiler.AllAffineCompactSourceTrajectory
import HGAS.Compactification.PositiveCentralChartTrajectory
import HGAS.Dynamics.IntegralCurveReciprocalTimeChange
import HGAS.Dynamics.PositiveIntegralClockUniformLower
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# Forward trajectories in the positive all-affine central chart

This module complements `AllAffineCompactSourceTrajectory`.  That file
starts with a compact orbit in the finite central chart and recovers its
affine trajectory.  Here we go in the opposite direction.

Suppose that

```text
                         z'(t) = P(z(t))
```

is a complete affine trajectory.  For the one-block compactification with
clearing exponent `2K`, put

```text
        a_K(z) = (1 + ‖z‖²)⁻ᴷ,
        r(t)   = 1 / a_K(z(t)),
        A(t)   = ∫₀ᵗ r(s) ds.
```

Because `0 < a_K ≤ 1`, one has `r ≥ 1`.  Thus `A` is a global increasing
clock on the whole real line.  If `B=A⁻¹`, then

```text
                         z̃(τ) = z(B(τ))
```

solves `z̃' = a_K(z̃) P(z̃)`.  Its positive central lift

```text
          x = z̃ / sqrt (1 + ‖z̃‖²),
          w = 1  / sqrt (1 + ‖z̃‖²)
```

therefore solves the literal denominator-cleared polynomial field emitted
by the all-affine compiler.

The construction is intentionally split into reusable pieces:

* `positiveBasePoint` embeds any affine point in the positive sheet of the
  compiler's compact base;
* `reciprocalAffineClock` packages the automatic global clock;
* `positiveBaseCurve_isIntegralCurve` proves the literal compiled ODE;
* `positiveBaseCurve_eq_baseFlow` identifies the constructed curve with
  the canonical compact base flow by uniqueness.
-/

namespace HGAS

open Function Metric Set

noncomputable section

namespace CompactAccumulatorPipelineCode

namespace AllAffinePositiveCentralTrajectory

open AllAffineCompactSourceChart
open AllAffineCompactSourceTrajectory

variable {n : ℕ}

/-- The positive central compactification of an affine point, represented
in the exact one-block base space used by the compiler. -/
def positiveBasePoint
    (z : Fin n → ℝ) :
    BaseSpace (layout n) := by
  let w : ℝ := positiveCentralScale z
  refine
    ⟨MixedCentralPolynomialCode.scaledChartPoint
        (layout n) (fun _ : Fin 1 ↦ w) z, ?_⟩
  intro d
  rw [MixedCentralPolynomialCode.sourceBlockNormSq_targetBlock]
  apply
    MixedCentralPolynomialCode.scaledChartPoint_on_target_spheres
      (layout n) (fun _ : Fin 1 ↦ w) z
  · intro b
    have hb : b = 0 := Subsingleton.elim _ _
    subst b
    have hnorm :
        MixedCentralPolynomialCode.affineBlockNormSq
            (layout n)
            (MixedCentralPolynomialCode.scaledSourcePoint
              (layout n) (fun _ : Fin 1 ↦ w) z) 0 =
          w ^ 2 * normSq z := by
      unfold MixedCentralPolynomialCode.affineBlockNormSq
        normSq dot
      simp only [AllAffineCompactSourceChart.layout,
        MixedCentralPolynomialCode.oneBlockAllAffineLayout,
        MixedCentralPolynomialCode.scaledSourcePoint,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [if_true]
      ring
    rw [hnorm]
    have hscale := positiveCentralScale_sq_mul z
    dsimp only [w] at hscale ⊢
    nlinarith
  · intro c
    exact Fin.elim0 c

@[simp]
theorem positiveBasePoint_xIndex
    (z : Fin n → ℝ) (j : Fin n) :
    (positiveBasePoint z).1
        (MixedCentralPolynomialCode.xIndex (k := 1) j) =
      (positiveCentralChartPoint z).1.1.1 j := by
  change
    MixedCentralPolynomialCode.scaledChartPoint
        (layout n) (fun _ : Fin 1 ↦ positiveCentralScale z) z
        (MixedCentralPolynomialCode.xIndex (k := 1) j) =
      positiveCentralScale z * z j
  simp [AllAffineCompactSourceChart.layout]

@[simp]
theorem positiveBasePoint_wIndex
    (z : Fin n → ℝ) :
    (positiveBasePoint z).1
        (MixedCentralPolynomialCode.wIndex (n := n) 0) =
      (positiveCentralChartPoint z).1.1.2 := by
  change
    MixedCentralPolynomialCode.scaledChartPoint
        (layout n) (fun _ : Fin 1 ↦ positiveCentralScale z) z
        (MixedCentralPolynomialCode.wIndex (n := n) 0) =
      positiveCentralScale z
  simp

@[simp]
theorem positiveBasePoint_finSum_inl
    (z : Fin n → ℝ) (j : Fin n) :
    (positiveBasePoint z).1
        (finSumFinEquiv (Sum.inl j : Fin n ⊕ Fin 1)) =
      (positiveCentralChartPoint z).1.1.1 j := by
  rw [show
    finSumFinEquiv (Sum.inl j : Fin n ⊕ Fin 1) =
      MixedCentralPolynomialCode.xIndex (k := 1) j by
        rfl]
  exact positiveBasePoint_xIndex z j

@[simp]
theorem positiveBasePoint_finSum_inr
    (z : Fin n → ℝ) (b : Fin 1) :
    (positiveBasePoint z).1
        (finSumFinEquiv (Sum.inr b : Fin n ⊕ Fin 1)) =
      (positiveCentralChartPoint z).1.1.2 := by
  have hb : b = 0 := Subsingleton.elim _ _
  subst b
  rw [show
    finSumFinEquiv (Sum.inr (0 : Fin 1) : Fin n ⊕ Fin 1) =
      MixedCentralPolynomialCode.wIndex (n := n) 0 by
        rfl]
  exact positiveBasePoint_wIndex z

/-- In the positive chart, the compiler's even projective slowdown is
exactly the intrinsic affine speed. -/
theorem positiveCentralScale_evenPow_eq_affineSpeed
    (K : ℕ) (z : Fin n → ℝ) :
    positiveCentralScale z ^ (2 * K) =
      affineSpeed K z := by
  rw [pow_mul]
  have hsq :
      positiveCentralScale z ^ 2 =
        (1 + normSq z)⁻¹ := by
    simpa only [positiveCentralChartPoint_w] using
      positiveCentralChartPoint_w_sq z
  rw [hsq]
  rfl

variable
  (K : ℕ)
  (P : PolynomialFieldCode n)

/-- Literal compiled velocity of an old compact coordinate at the positive
central lift of an affine point. -/
theorem realize_baseFieldCode_positiveBasePoint_x
    (hP :
      ∀ j,
        MixedCentralPolynomialCode.TermsAffineBlockDegreeLE
          (layout n) (2 * K) (P j))
    (z : Fin n → ℝ) (j : Fin n) :
    PolynomialFieldCode.realize
        (baseFieldCode (layout n) (2 * K) P)
        (positiveBasePoint z).1
        (MixedCentralPolynomialCode.xIndex (k := 1) j) =
      centralCompactXField
        (affineSpeed K z)
        (positiveCentralChartPoint z).1.1.2
        (positiveCentralChartPoint z).1.1.1
        (PolynomialFieldCode.realize P z) j := by
  change
    _root_.MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (MixedCentralPolynomialCode.scaledChartPoint
          (layout n) (fun _ : Fin 1 ↦ positiveCentralScale z) z)
        (PolynomialCode.decode
          (MixedCentralPolynomialCode.fieldCode
            (layout n) (2 * K) P
            (MixedCentralPolynomialCode.xIndex (k := 1) j))) =
      _
  rw [MixedCentralPolynomialCode.eval₂Hom_fieldCode_scaledChart
    (layout n) (2 * K) P hP
    (MixedCentralPolynomialCode.xIndex (k := 1) j)
    (fun _ : Fin 1 ↦ positiveCentralScale z) z]
  simp only [MixedCentralPolynomialCode.mixedAmbientField,
    MixedCentralPolynomialCode.finSumFinEquiv_symm_xIndex]
  rw [slowdown_eq_weight_pow,
    positiveCentralScale_evenPow_eq_affineSpeed]
  rw [mixedXField_eq_centralCompactXField]
  have hx :
      MixedCentralPolynomialCode.scaledSourcePoint
          (layout n) (fun _ : Fin 1 ↦ positiveCentralScale z) z =
        (positiveCentralChartPoint z).1.1.1 := by
    funext i
    change
      positiveCentralScale z * z i =
        positiveCentralScale z * z i
    rfl
  have hp :
      (fun i ↦
        _root_.MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) z
          (PolynomialCode.decode (P i))) =
        PolynomialFieldCode.realize P z := by
    funext i
    rw [PolynomialFieldCode.realize_apply]
  rw [hx, hp]
  simp only [positiveCentralChartPoint_w]

/-- Literal compiled velocity of the central weight at the positive lift. -/
theorem realize_baseFieldCode_positiveBasePoint_w
    (hP :
      ∀ j,
        MixedCentralPolynomialCode.TermsAffineBlockDegreeLE
          (layout n) (2 * K) (P j))
    (z : Fin n → ℝ) :
    PolynomialFieldCode.realize
        (baseFieldCode (layout n) (2 * K) P)
        (positiveBasePoint z).1
        (MixedCentralPolynomialCode.wIndex (n := n) 0) =
      centralCompactWField
        (affineSpeed K z)
        (positiveCentralChartPoint z).1.1.2
        (positiveCentralChartPoint z).1.1.1
        (PolynomialFieldCode.realize P z) := by
  change
    _root_.MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (MixedCentralPolynomialCode.scaledChartPoint
          (layout n) (fun _ : Fin 1 ↦ positiveCentralScale z) z)
        (PolynomialCode.decode
          (MixedCentralPolynomialCode.fieldCode
            (layout n) (2 * K) P
            (MixedCentralPolynomialCode.wIndex (n := n) 0))) =
      _
  rw [MixedCentralPolynomialCode.eval₂Hom_fieldCode_scaledChart
    (layout n) (2 * K) P hP
    (MixedCentralPolynomialCode.wIndex (n := n) 0)
    (fun _ : Fin 1 ↦ positiveCentralScale z) z]
  simp only [MixedCentralPolynomialCode.mixedAmbientField,
    MixedCentralPolynomialCode.finSumFinEquiv_symm_wIndex]
  rw [slowdown_eq_weight_pow,
    positiveCentralScale_evenPow_eq_affineSpeed]
  rw [mixedWField_eq_centralCompactWField]
  have hx :
      MixedCentralPolynomialCode.scaledSourcePoint
          (layout n) (fun _ : Fin 1 ↦ positiveCentralScale z) z =
        (positiveCentralChartPoint z).1.1.1 := by
    funext i
    change
      positiveCentralScale z * z i =
        positiveCentralScale z * z i
    rfl
  have hp :
      (fun i ↦
        _root_.MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) z
          (PolynomialCode.decode (P i))) =
        PolynomialFieldCode.realize P z := by
    funext i
    rw [PolynomialFieldCode.realize_apply]
  rw [hx, hp]
  simp only [positiveCentralChartPoint_w]

/-- The reciprocal projective slowdown along an affine curve. -/
def reciprocalAffineClockWeight
    (γ : ℝ → (Fin n → ℝ)) (t : ℝ) : ℝ :=
  (affineSpeed K (γ t))⁻¹

/-- The reciprocal projective slowdown is continuous along every integral
curve. -/
theorem continuous_reciprocalAffineClockWeight
    {γ : ℝ → (Fin n → ℝ)}
    (hγ :
      IsIntegralCurve γ
        (fun _ z ↦ PolynomialFieldCode.realize P z)) :
    Continuous (reciprocalAffineClockWeight K γ) := by
  exact
    ((continuous_affineSpeed K).comp hγ.continuous).inv₀
      (fun t ↦ (affineSpeed_pos K (γ t)).ne')

/-- The reciprocal projective slowdown is at least one.  This elementary
estimate is what makes the compact clock global in both time directions. -/
theorem one_le_reciprocalAffineClockWeight
    (γ : ℝ → (Fin n → ℝ)) (t : ℝ) :
    1 ≤ reciprocalAffineClockWeight K γ t := by
  unfold reciprocalAffineClockWeight
  exact
    (one_le_inv₀ (affineSpeed_pos K (γ t))).2
      (affineSpeed_le_one K (γ t))

/-- Every complete affine integral curve carries an automatic global
reciprocal clock for the all-affine compactification. -/
def reciprocalAffineClock
    {γ : ℝ → (Fin n → ℝ)}
    (hγ :
      IsIntegralCurve γ
        (fun _ z ↦ PolynomialFieldCode.realize P z)) :
    PositiveIntegralClock (reciprocalAffineClockWeight K γ) :=
  positiveIntegralClock_of_uniformLowerBound
    (continuous_reciprocalAffineClockWeight K P hγ)
    (by norm_num : (0 : ℝ) < 1)
    (one_le_reciprocalAffineClockWeight K γ)

/-- Affine trajectory expressed in the slower compact time. -/
def slowedAffineCurve
    {γ : ℝ → (Fin n → ℝ)}
    (hγ :
      IsIntegralCurve γ
        (fun _ z ↦ PolynomialFieldCode.realize P z))
    (τ : ℝ) :
    Fin n → ℝ :=
  γ
    ((PositiveIntegralClock.orderIso
      (reciprocalAffineClock K P hγ)).symm τ)

/-- In compact time, the affine trajectory solves the intrinsically slowed
polynomial equation. -/
theorem slowedAffineCurve_isIntegralCurve
    {γ : ℝ → (Fin n → ℝ)}
    (hγ :
      IsIntegralCurve γ
        (fun _ z ↦ PolynomialFieldCode.realize P z)) :
    IsIntegralCurve
      (slowedAffineCurve K P hγ)
      (fun _ z ↦
        timeScaledField (affineSpeed K)
          (PolynomialFieldCode.realize P) z) := by
  exact
    _root_.HGAS.IsIntegralCurve.reparametrize_to_timeScaledField hγ
      (reciprocalAffineClock K P hγ)

/-- Positive compact lift of the slowed affine trajectory. -/
def positiveBaseCurve
    {γ : ℝ → (Fin n → ℝ)}
    (hγ :
      IsIntegralCurve γ
        (fun _ z ↦ PolynomialFieldCode.realize P z))
    (τ : ℝ) :
    BaseSpace (layout n) :=
  positiveBasePoint (slowedAffineCurve K P hγ τ)

/-- The positive lift solves the literal polynomial base field emitted by
the compiler, coordinate by coordinate. -/
theorem positiveBaseCurve_isIntegralCurve
    (hP :
      ∀ j,
        MixedCentralPolynomialCode.TermsAffineBlockDegreeLE
          (layout n) (2 * K) (P j))
    {γ : ℝ → (Fin n → ℝ)}
    (hγ :
      IsIntegralCurve γ
        (fun _ z ↦ PolynomialFieldCode.realize P z)) :
    IsIntegralCurve
      (fun τ ↦ (positiveBaseCurve K P hγ τ).1)
      (fun _ y ↦
        PolynomialFieldCode.realize
          (baseFieldCode (layout n) (2 * K) P) y) := by
  let z : ℝ → (Fin n → ℝ) :=
    slowedAffineCurve K P hγ
  have hz :=
    slowedAffineCurve_isIntegralCurve K P hγ
  intro t
  rw [hasDerivAt_pi]
  intro q
  obtain ⟨j | b, rfl⟩ :=
    finSumFinEquiv.surjective q
  · have hlift :=
      positiveCentralChartPoint_x_hasDerivAt
        z (fun s ↦ PolynomialFieldCode.realize P (z s))
        (fun s ↦ affineSpeed K (z s)) t
        (fun i ↦ by
          have hzi :=
            (hasDerivAt_pi.mp (hz t)) i
          simpa only [timeScaledField, Pi.smul_apply,
            smul_eq_mul, z] using hzi)
        j
    have hvelocity :=
      realize_baseFieldCode_positiveBasePoint_x
        K P hP (z t) j
    have hlift' := hlift.congr_deriv hvelocity.symm
    simpa only [positiveBaseCurve, z,
      positiveBasePoint_finSum_inl] using hlift'
  · have hb : b = 0 := Subsingleton.elim _ _
    subst b
    have hlift :=
      positiveCentralChartPoint_w_hasDerivAt
        z (fun s ↦ PolynomialFieldCode.realize P (z s))
        (fun s ↦ affineSpeed K (z s)) t
        (fun i ↦ by
          have hzi :=
            (hasDerivAt_pi.mp (hz t)) i
          simpa only [timeScaledField, Pi.smul_apply,
            smul_eq_mul, z] using hzi)
    have hvelocity :=
      realize_baseFieldCode_positiveBasePoint_w
        K P hP (z t)
    have hlift' := hlift.congr_deriv hvelocity.symm
    simpa only [positiveBaseCurve, z,
      positiveBasePoint_finSum_inr] using hlift'

/-- A complete curve in the compact base that solves the literal base ODE
and starts at `y₀` is the canonical base-flow orbit through `y₀`. -/
theorem integralCurve_eq_baseFlow
    (E : ℕ)
    (hPdegree : ∀ j, PolynomialCode.TermsDegreeLE E (P j))
    (hcompactBase :
      ∀ y : BaseSpace (layout n),
        let x : Fin n → ℝ :=
          fun j ↦ y.1
            (MixedCentralPolynomialCode.xIndex (k := 1) j)
        ∀ c, MixedCentralPolynomialCode.compactBlockDot
          (layout n) x
          (MixedCentralPolynomialCode.clearedSourceVelocity
            (layout n) (2 * K) P y.1) c = 0)
    (η : ℝ → BaseSpace (layout n))
    (hη :
      IsIntegralCurve
        (fun t ↦ (η t).1)
        (fun _ y ↦
          PolynomialFieldCode.realize
            (baseFieldCode (layout n) (2 * K) P) y))
    (t : ℝ) :
    η t =
      baseFlow (layout n) E (2 * K) P t (η 0) := by
  apply Subtype.ext
  let gammaOne : ℝ → Fin (n + 1) → ℝ :=
    fun s ↦ (η s).1
  let gammaTwo : ℝ → Fin (n + 1) → ℝ :=
    fun s ↦
      (baseFlow (layout n) E (2 * K) P s (η 0)).1
  have hgammaOne :
      IsIntegralCurve gammaOne
        (fun _ y ↦
          PolynomialFieldCode.realize
            (baseFieldCode (layout n) (2 * K) P) y) := by
    simpa only [gammaOne] using hη
  have hgammaTwo :
      IsIntegralCurve gammaTwo
        (fun _ y ↦
          PolynomialFieldCode.realize
            (baseFieldCode (layout n) (2 * K) P) y) := by
    simpa only [gammaTwo] using
      baseFlow_integralCurve
        (layout n) E (2 * K) P hPdegree hcompactBase (η 0)
  have hC1 :
      ContDiff ℝ 1
        (PolynomialFieldCode.realize
          (baseFieldCode (layout n) (2 * K) P)) :=
    (UnitSpherePolynomialWrapper.contDiff_realize_sourcePolynomialFieldCode
      (baseFieldCode (layout n) (2 * K) P)).of_le (by norm_num)
  obtain ⟨L, hL⟩ :=
    hC1.contDiffOn.exists_lipschitzOnWith
      one_ne_zero
      (convex_closedBall (0 : Fin (n + 1) → ℝ) 1)
      (isCompact_closedBall (0 : Fin (n + 1) → ℝ) 1)
  have hOneMem :
      ∀ s,
        gammaOne s ∈
          closedBall (0 : Fin (n + 1) → ℝ) 1 := by
    intro s
    have hnorm :=
      UnitSpherePolynomialWrapper.source_norm_le_one_of_onSourceProductSpheres
        (MixedCentralPolynomialCode.targetBlock (layout n))
        (gammaOne s) (η s).property
    simpa only [Metric.mem_closedBall, dist_zero_right]
      using hnorm
  have hTwoMem :
      ∀ s,
        gammaTwo s ∈
          closedBall (0 : Fin (n + 1) → ℝ) 1 := by
    intro s
    have hnorm :=
      UnitSpherePolynomialWrapper.source_norm_le_one_of_onSourceProductSpheres
        (MixedCentralPolynomialCode.targetBlock (layout n))
        (gammaTwo s)
        (baseFlow (layout n) E (2 * K) P s (η 0)).property
    simpa only [Metric.mem_closedBall, dist_zero_right]
      using hnorm
  have heq : gammaOne = gammaTwo := by
    apply ODE_solution_unique_univ
      (v := fun _ : ℝ ↦
        PolynomialFieldCode.realize
          (baseFieldCode (layout n) (2 * K) P))
      (s := fun _ ↦
        closedBall (0 : Fin (n + 1) → ℝ) 1)
      (K := L) (t₀ := 0)
    · intro _
      exact hL
    · intro s
      exact ⟨hgammaOne s, hOneMem s⟩
    · intro s
      exact ⟨hgammaTwo s, hTwoMem s⟩
    · simp [gammaOne, gammaTwo, Flow.map_zero_apply]
  exact congrFun heq t

/-- The explicitly time-changed positive lift is exactly the canonical
compact base-flow trajectory. -/
theorem positiveBaseCurve_eq_baseFlow
    (hP :
      ∀ j,
        MixedCentralPolynomialCode.TermsAffineBlockDegreeLE
          (layout n) (2 * K) (P j))
    (E : ℕ)
    (hPdegree : ∀ j, PolynomialCode.TermsDegreeLE E (P j))
    (hcompactBase :
      ∀ y : BaseSpace (layout n),
        let x : Fin n → ℝ :=
          fun j ↦ y.1
            (MixedCentralPolynomialCode.xIndex (k := 1) j)
        ∀ c, MixedCentralPolynomialCode.compactBlockDot
          (layout n) x
          (MixedCentralPolynomialCode.clearedSourceVelocity
            (layout n) (2 * K) P y.1) c = 0)
    {γ : ℝ → (Fin n → ℝ)}
    (hγ :
      IsIntegralCurve γ
        (fun _ z ↦ PolynomialFieldCode.realize P z))
    (t : ℝ) :
    positiveBaseCurve K P hγ t =
      baseFlow (layout n) E (2 * K) P t
        (positiveBasePoint (γ 0)) := by
  calc
    positiveBaseCurve K P hγ t =
        baseFlow (layout n) E (2 * K) P t
          (positiveBaseCurve K P hγ 0) :=
      integralCurve_eq_baseFlow
        K P E hPdegree hcompactBase
        (positiveBaseCurve K P hγ)
        (positiveBaseCurve_isIntegralCurve K P hP hγ) t
    _ =
        baseFlow (layout n) E (2 * K) P t
          (positiveBasePoint (γ 0)) := by
      congr 2
      simp [positiveBaseCurve, slowedAffineCurve]

end AllAffinePositiveCentralTrajectory

end CompactAccumulatorPipelineCode

end

end HGAS
