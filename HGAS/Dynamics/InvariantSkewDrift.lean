import HGAS.Dynamics.InvariantProbability
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic

/-!
# Invariant probabilities annihilate bounded affine increments

Suppose a continuous flow carries a continuous real coordinate `z` whose
time-one increment

```
                    z(ϕ₁ x) - z(x) = δ(x)
```

is bounded and continuous.  Every invariant probability has zero mean
increment:

```
                         ∫ δ dμ = 0.
```

The coordinate itself need not be bounded or integrable.  To avoid that
false requirement, clip it to `[-R,R]`.  Invariance annihilates the
integral of each clipped coboundary.  As `R → ∞`, the clipped differences
converge pointwise to `δ` and are dominated by `|δ|`, because interval
projection is one-Lipschitz.  Dominated convergence gives the result.

This elementary stationary-cocycle lemma replaces a pointwise-ergodic
argument in the accumulator construction.  It is useful whenever a finite
affine chart of a compactified skew product is invariant.
-/

noncomputable section

open Filter Function MeasureTheory Set Topology
open scoped BoundedContinuousFunction

namespace HGAS.Dynamics

variable {X : Type*} [TopologicalSpace X]

/-- The symmetric clipping interval has correctly ordered endpoints. -/
theorem neg_natSucc_le_natSucc (n : ℕ) :
    -(n + 1 : ℝ) ≤ (n + 1 : ℝ) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- The real coordinate clipped to the symmetric interval
`[-(n+1), n+1]`. -/
def clippedRealCoordinate
    (z : X → ℝ) (hz : Continuous z) (n : ℕ) :
    X →ᵇ ℝ := by
  let R : ℝ := n + 1
  have hR : -R ≤ R := by
    simpa only [R] using neg_natSucc_le_natSucc n
  let f : C(X, ℝ) :=
    ⟨fun x ↦
      (projIcc (-R) R hR (z x) : ℝ),
      continuous_subtype_val.comp
        (continuous_projIcc.comp hz)⟩
  exact BoundedContinuousFunction.mkOfBound f (2 * R) (by
    intro x y
    rw [Real.dist_eq]
    have hx :
        -R ≤ f x ∧ f x ≤ R :=
      (projIcc (-R) R hR (z x)).property
    have hy :
        -R ≤ f y ∧ f y ≤ R :=
      (projIcc (-R) R hR (z y)).property
    rw [abs_le]
    constructor <;> linarith)

@[simp]
theorem clippedRealCoordinate_apply
    (z : X → ℝ) (hz : Continuous z) (n : ℕ) (x : X) :
    clippedRealCoordinate z hz n x =
      (projIcc (-(n + 1 : ℝ)) (n + 1 : ℝ)
        (neg_natSucc_le_natSucc n) (z x) : ℝ) :=
  rfl

/-- For fixed real numbers, symmetric clipping eventually leaves both
numbers unchanged. -/
theorem tendsto_clippedDifference
    (a b : ℝ) :
    Tendsto
      (fun n : ℕ ↦
        (projIcc (-(n + 1 : ℝ)) (n + 1 : ℝ)
            (neg_natSucc_le_natSucc n) a : ℝ) -
          (projIcc (-(n + 1 : ℝ)) (n + 1 : ℝ)
            (neg_natSucc_le_natSucc n) b : ℝ))
      atTop (𝓝 (a - b)) := by
  obtain ⟨N : ℕ, hN : max |a| |b| < N⟩ :=
    exists_nat_gt (max |a| |b|)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  have haAbs : |a| < (n + 1 : ℝ) := by
    calc
      |a| ≤ max |a| |b| := le_max_left _ _
      _ < N := hN
      _ ≤ n := by exact_mod_cast hn
      _ < n + 1 := by norm_num
  have hbAbs : |b| < (n + 1 : ℝ) := by
    calc
      |b| ≤ max |a| |b| := le_max_right _ _
      _ < N := hN
      _ ≤ n := by exact_mod_cast hn
      _ < n + 1 := by norm_num
  have haMem :
      a ∈ Set.Icc (-(n + 1 : ℝ)) (n + 1 : ℝ) := by
    rw [abs_lt] at haAbs
    exact ⟨haAbs.1.le, haAbs.2.le⟩
  have hbMem :
      b ∈ Set.Icc (-(n + 1 : ℝ)) (n + 1 : ℝ) := by
    rw [abs_lt] at hbAbs
    exact ⟨hbAbs.1.le, hbAbs.2.le⟩
  rw [projIcc_of_mem (neg_natSucc_le_natSucc n) haMem,
    projIcc_of_mem (neg_natSucc_le_natSucc n) hbMem]

/-- Symmetric clipping cannot enlarge the difference of two real
numbers. -/
theorem abs_clippedDifference_le
    (n : ℕ) (a b : ℝ) :
    |(projIcc (-(n + 1 : ℝ)) (n + 1 : ℝ)
          (neg_natSucc_le_natSucc n) a : ℝ) -
        (projIcc (-(n + 1 : ℝ)) (n + 1 : ℝ)
          (neg_natSucc_le_natSucc n) b : ℝ)| ≤ |a - b| := by
  exact
    Set.abs_projIcc_sub_projIcc
      (neg_natSucc_le_natSucc n)

/-- **Invariant affine-increment lemma.**

An invariant probability gives mean zero to every bounded continuous
time-one increment of a possibly unbounded continuous coordinate. -/
theorem InvariantProbabilityMeasure.observableAverage_increment_eq_zero
    [MeasurableSpace X] [BorelSpace X]
    {ϕ : Flow ℝ X}
    (μ : InvariantProbabilityMeasure ϕ)
    (z : X → ℝ) (hz : Continuous z)
    (δ : X →ᵇ ℝ)
    (hincrement : ∀ x, z (ϕ 1 x) - z x = δ x) :
    (∫ x, δ x ∂(μ.measure : Measure X)) = 0 := by
  let F : ℕ → X → ℝ :=
    fun n x ↦
      clippedRealCoordinate z hz n (ϕ 1 x) -
        clippedRealCoordinate z hz n x
  have hFIntegralZero :
      ∀ n, (∫ x, F n x ∂(μ.measure : Measure X)) = 0 := by
    intro n
    let w : X →ᵇ ℝ :=
      clippedRealCoordinate z hz n
    have hcomp :
        (∫ x, w (ϕ 1 x) ∂(μ.measure : Measure X)) =
          ∫ x, w x ∂(μ.measure : Measure X) :=
      μ.integral_comp_time 1 w
    have hwcomp :
        Integrable (fun x ↦ w (ϕ 1 x))
          (μ.measure : Measure X) :=
      μ.integrable_comp_time 1 w
    have hw :
        Integrable (fun x ↦ w x)
          (μ.measure : Measure X) :=
      w.integrable _
    change
      (∫ x, w (ϕ 1 x) - w x
        ∂(μ.measure : Measure X)) = 0
    rw [integral_sub hwcomp hw, hcomp, sub_self]
  have hmeas :
      ∀ n,
        AEStronglyMeasurable (F n)
          (μ.measure : Measure X) := by
    intro n
    apply
      ((clippedRealCoordinate z hz n).continuous.comp
        (ϕ.continuous_toFun 1)).sub
          (clippedRealCoordinate z hz n).continuous
      |>.aestronglyMeasurable
  have hbound :
      ∀ n, ∀ᵐ x ∂(μ.measure : Measure X),
        ‖F n x‖ ≤ ‖δ x‖ := by
    intro n
    filter_upwards [] with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact (abs_clippedDifference_le n
      (z (ϕ 1 x)) (z x)).trans_eq
        (congrArg abs (hincrement x))
  have hlimit :
      ∀ᵐ x ∂(μ.measure : Measure X),
        Tendsto (fun n ↦ F n x) atTop (𝓝 (δ x)) := by
    filter_upwards [] with x
    simpa only [F, clippedRealCoordinate_apply,
      hincrement x] using
        tendsto_clippedDifference (z (ϕ 1 x)) (z x)
  have htendsto :
      Tendsto
        (fun n ↦ ∫ x, F n x ∂(μ.measure : Measure X))
        atTop
        (𝓝 (∫ x, δ x ∂(μ.measure : Measure X))) :=
    tendsto_integral_of_dominated_convergence
      (fun x ↦ ‖δ x‖) hmeas
      (δ.integrable _).norm hbound hlimit
  have hzero :
      Tendsto
        (fun _ : ℕ ↦ (0 : ℝ))
        atTop
        (𝓝 (∫ x, δ x ∂(μ.measure : Measure X))) := by
    simpa only [hFIntegralZero] using htendsto
  have hintegral :
      (∫ x, δ x ∂(μ.measure : Measure X)) = 0 :=
    tendsto_nhds_unique hzero tendsto_const_nhds
  exact hintegral

/-- Coordinatewise form of the invariant affine-increment lemma.

This is the form used by a finite-dimensional accumulator.  It deliberately
states the conclusion coordinatewise: downstream arguments can select only
the accumulator coordinate they need, while the proof remains independent
of any chosen Euclidean norm on the finite product. -/
theorem InvariantProbabilityMeasure.coordinateAverage_increment_eq_zero
    [MeasurableSpace X] [BorelSpace X]
    {m : ℕ} {ϕ : Flow ℝ X}
    (μ : InvariantProbabilityMeasure ϕ)
    (z : X → (Fin m → ℝ)) (hz : Continuous z)
    (δ : X →ᵇ (Fin m → ℝ))
    (hincrement : ∀ x, z (ϕ 1 x) - z x = δ x) :
    ∀ i : Fin m,
      (∫ x, δ x i ∂(μ.measure : Measure X)) = 0 := by
  intro i
  let δi : X →ᵇ ℝ :=
    (ContinuousLinearMap.proj i :
      (Fin m → ℝ) →L[ℝ] ℝ).compLeftContinuousBounded X δ
  apply μ.observableAverage_increment_eq_zero
    (fun x ↦ z x i) ((continuous_apply i).comp hz) δi
  intro x
  change z (ϕ 1 x) i - z x i = δ x i
  exact congrFun (hincrement x) i

end HGAS.Dynamics

end
