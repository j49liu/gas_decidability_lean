import HGAS.Modular.JacobiResidualDynamics
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

/-!
# Bloch-gauge covariance of the elliptic Jacobi field

The four theta coordinates admit a common Bloch multiplier.  If a
canonical theta state is `z`, a nonzero common scale `S` and a logarithmic
slope `L` produce the transformed reciprocal-chart state

```text
  Tⱼ ↦ S Tⱼ,      Δ ↦ S (Δ + L T₁),      U ↦ U / S.
```

The formula for `Δ` is forced by differentiation: `Δ` is the first theta
derivative divided by `π`, while the normalized derivative of the common
factor is `L S`.

This module proves, by exact field algebra, that this transformation
conjugates the elliptic Jacobi dynamics on the reciprocal locus
`U T₁ = 1`.  The result is deliberately independent of theta functions
and of the analytic trajectory used later.  It can therefore be reused
for any solution of the rational Jacobi chart.
-/

namespace HGAS.Modular

noncomputable section

namespace JacobiState

variable {R : Type*} [Field R] [CharZero R]

/-- Common Bloch rescaling of a reciprocal Jacobi-chart state. -/
def blochGauge (S L : R) (z : JacobiState R) : JacobiState R where
  p2 := z.p2
  p3 := z.p3
  p4 := z.p4
  H := z.H
  T1 := S * z.T1
  T2 := S * z.T2
  T3 := S * z.T3
  T4 := S * z.T4
  Delta := S * (z.Delta + L * z.T1)
  U := z.U / S

/-- The normalized derivative of `blochGauge S L z` when
`z' / π = ellipticVectorField z`, `S' / π = L S`, and `L` is constant.

It is written out independently of the vector field so that the
covariance theorem below is an honest algebraic identity. -/
def blochGaugeEllipticTangent
    (S L : R) (z : JacobiState R) : JacobiState R :=
  let Z := ellipticVectorField z
  { p2 := 0
    p3 := 0
    p4 := 0
    H := 0
    T1 := S * (Z.T1 + L * z.T1)
    T2 := S * (Z.T2 + L * z.T2)
    T3 := S * (Z.T3 + L * z.T3)
    T4 := S * (Z.T4 + L * z.T4)
    Delta :=
      S * (Z.Delta + L * Z.T1 +
        L * (z.Delta + L * z.T1))
    U := (Z.U - L * z.U) / S }

omit [CharZero R] in
@[simp]
theorem blochGauge_residualR0
    (S L : R) (z : JacobiState R) :
    residualR0 (blochGauge S L z) = residualR0 z := by
  rfl

omit [CharZero R] in
theorem blochGauge_residualR1
    (S L : R) (z : JacobiState R) :
    residualR1 (blochGauge S L z) =
      S ^ 2 * residualR1 z := by
  simp only [residualR1, blochGauge]
  ring

omit [CharZero R] in
theorem blochGauge_residualR2
    (S L : R) (z : JacobiState R) :
    residualR2 (blochGauge S L z) =
      S ^ 2 * residualR2 z := by
  simp only [residualR2, blochGauge]
  ring

omit [CharZero R] in
theorem blochGauge_residualRU
    (S L : R) (z : JacobiState R)
    (hS : S ≠ 0) :
    residualRU (blochGauge S L z) =
      residualRU z := by
  simp only [residualRU, blochGauge]
  field_simp

/-- **Elliptic Bloch-gauge covariance.**

On the reciprocal chart, the normalized derivative obtained by the
ordinary product rule is exactly the elliptic Jacobi vector field at the
Bloch-transformed state. -/
theorem blochGaugeEllipticTangent_eq
    (S L : R) (z : JacobiState R)
    (hS : S ≠ 0)
    (hreciprocal : z.U * z.T1 = 1) :
    blochGaugeEllipticTangent S L z =
      ellipticVectorField (blochGauge S L z) := by
  ext <;>
    simp only [blochGaugeEllipticTangent, ellipticVectorField,
      blochGauge, K]
  · field_simp [hS]
    linear_combination
      (-L * z.T2) * hreciprocal
  · field_simp [hS]
    linear_combination
      (-L * z.T3) * hreciprocal
  · field_simp [hS]
    linear_combination
      (-L * z.T4) * hreciprocal
  · field_simp [hS]
    linear_combination
      (-12 *
        (2 * L * z.Delta + L ^ 2 * z.T1)) *
          hreciprocal
  · field_simp [hS]
    linear_combination
      L * z.U * hreciprocal

/-! ## Simultaneous elliptic--modular covariance -/

/-- Parameter drift of the common Bloch multiplier for target clocks
`κZ, κPhi` and constant logarithmic elliptic slope `L`. -/
def blochGaugeLogarithmicDrift
    (κZ κPhi L : R) : R :=
  κZ * L - κPhi * L ^ 2 / 4

/-- The ordinary product-rule tangent of a Bloch-transformed solution
whose underlying canonical state has the shifted elliptic clock
`κZ - κPhi*L/2` and the same modular clock `κPhi`.

This is the algebraic form of the Galilean symmetry of the heat
equation. -/
def blochGaugeCombinedTangent
    (κZ κPhi S L : R) (z : JacobiState R) :
    JacobiState R :=
  let W :=
    combinedVectorField
      (κZ - κPhi * L / 2) κPhi z
  let g := blochGaugeLogarithmicDrift κZ κPhi L
  { p2 := W.p2
    p3 := W.p3
    p4 := W.p4
    H := W.H
    T1 := S * (W.T1 + g * z.T1)
    T2 := S * (W.T2 + g * z.T2)
    T3 := S * (W.T3 + g * z.T3)
    T4 := S * (W.T4 + g * z.T4)
    Delta :=
      S * (W.Delta +
        g * (z.Delta + L * z.T1) +
        L * W.T1)
    U := (W.U - g * z.U) / S }

/-- **Simultaneous Bloch covariance.**

The heat-equation Galilean transformation conjugates the shifted
elliptic/modular flow to the target combined flow. -/
theorem blochGaugeCombinedTangent_eq
    (κZ κPhi S L : R) (z : JacobiState R)
    (hS : S ≠ 0)
    (hreciprocal : z.U * z.T1 = 1) :
    blochGaugeCombinedTangent κZ κPhi S L z =
      combinedVectorField κZ κPhi
        (blochGauge S L z) := by
  have hT1 : z.T1 ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hreciprocal
    exact one_ne_zero hreciprocal.symm
  have hU : z.U = z.T1⁻¹ := by
    calc
      z.U = z.U * 1 := (mul_one z.U).symm
      _ = z.U * (z.T1 * z.T1⁻¹) := by
        rw [mul_inv_cancel₀ hT1]
      _ = (z.U * z.T1) * z.T1⁻¹ := by ring
      _ = z.T1⁻¹ := by rw [hreciprocal, one_mul]
  ext <;>
    simp only [blochGaugeCombinedTangent,
      blochGaugeLogarithmicDrift,
      combinedVectorField, ellipticVectorField,
      modularVectorField, blochGauge, K]
  all_goals
    try rw [hU]
    field_simp [hS, hT1]
    ring

end JacobiState

/-! ## Trajectory-level conjugacy -/

/-- Pointwise Bloch transformation of a Jacobi trajectory. -/
def jacobiBlochGaugePath
    (S : ℝ → ℂ) (L : ℂ)
    (z : ℝ → JacobiState ℂ) (t : ℝ) :
    JacobiState ℂ :=
  JacobiState.blochGauge (S t) L (z t)

/-- A shifted canonical trajectory and a nonvanishing solution of the
scalar Bloch-factor equation produce an exact trajectory with the target
combined clocks. -/
theorem jacobiBlochGaugePath_isScaledTrajectory
    {κZ κPhi L : ℂ}
    {S : ℝ → ℂ} {z : ℝ → JacobiState ℂ}
    (hz :
      IsScaledJacobiTrajectory
        (κZ - κPhi * L / 2) κPhi z)
    (hS :
      ∀ t,
        HasDerivAt S
          (JacobiState.blochGaugeLogarithmicDrift
            κZ κPhi L * S t) t)
    (hSzero : ∀ t, S t ≠ 0)
    (hreciprocal : ∀ t, (z t).U * (z t).T1 = 1) :
    IsScaledJacobiTrajectory
      κZ κPhi (jacobiBlochGaugePath S L z) := by
  let g : ℂ :=
    JacobiState.blochGaugeLogarithmicDrift
      κZ κPhi L
  have hcov :
      ∀ t,
        JacobiState.blochGaugeCombinedTangent
            κZ κPhi (S t) L (z t) =
          JacobiState.combinedVectorField κZ κPhi
            (JacobiState.blochGauge (S t) L (z t)) :=
    fun t =>
      JacobiState.blochGaugeCombinedTangent_eq
        κZ κPhi (S t) L (z t)
          (hSzero t) (hreciprocal t)
  refine
    {
      p2 := ?_
      p3 := ?_
      p4 := ?_
      H := ?_
      T1 := ?_
      T2 := ?_
      T3 := ?_
      T4 := ?_
      Delta := ?_
      U := ?_
    }
  · intro t
    have hraw := hz.p2 t
    have htangent :
        HasDerivAt
          (fun s ↦
            (jacobiBlochGaugePath S L z s).p2)
          (JacobiState.blochGaugeCombinedTangent
            κZ κPhi (S t) L (z t)).p2 t := by
      simpa [jacobiBlochGaugePath,
        JacobiState.blochGaugeCombinedTangent] using hraw
    rw [hcov t] at htangent
    exact htangent
  · intro t
    have hraw := hz.p3 t
    have htangent :
        HasDerivAt
          (fun s ↦
            (jacobiBlochGaugePath S L z s).p3)
          (JacobiState.blochGaugeCombinedTangent
            κZ κPhi (S t) L (z t)).p3 t := by
      simpa [jacobiBlochGaugePath,
        JacobiState.blochGaugeCombinedTangent] using hraw
    rw [hcov t] at htangent
    exact htangent
  · intro t
    have hraw := hz.p4 t
    have htangent :
        HasDerivAt
          (fun s ↦
            (jacobiBlochGaugePath S L z s).p4)
          (JacobiState.blochGaugeCombinedTangent
            κZ κPhi (S t) L (z t)).p4 t := by
      simpa [jacobiBlochGaugePath,
        JacobiState.blochGaugeCombinedTangent] using hraw
    rw [hcov t] at htangent
    exact htangent
  · intro t
    have hraw := hz.H t
    have htangent :
        HasDerivAt
          (fun s ↦
            (jacobiBlochGaugePath S L z s).H)
          (JacobiState.blochGaugeCombinedTangent
            κZ κPhi (S t) L (z t)).H t := by
      simpa [jacobiBlochGaugePath,
        JacobiState.blochGaugeCombinedTangent] using hraw
    rw [hcov t] at htangent
    exact htangent
  · intro t
    have hraw := (hS t).mul (hz.T1 t)
    have htangent :
        HasDerivAt
          (fun s ↦
            (jacobiBlochGaugePath S L z s).T1)
          (JacobiState.blochGaugeCombinedTangent
            κZ κPhi (S t) L (z t)).T1 t := by
      change
        HasDerivAt
          (fun s ↦ S s * (z s).T1)
          _ t
      convert hraw using 1
      simp only [
        JacobiState.blochGaugeCombinedTangent]
      ring
    rw [hcov t] at htangent
    exact htangent
  · intro t
    have hraw := (hS t).mul (hz.T2 t)
    have htangent :
        HasDerivAt
          (fun s ↦
            (jacobiBlochGaugePath S L z s).T2)
          (JacobiState.blochGaugeCombinedTangent
            κZ κPhi (S t) L (z t)).T2 t := by
      change
        HasDerivAt
          (fun s ↦ S s * (z s).T2)
          _ t
      convert hraw using 1
      simp only [
        JacobiState.blochGaugeCombinedTangent]
      ring
    rw [hcov t] at htangent
    exact htangent
  · intro t
    have hraw := (hS t).mul (hz.T3 t)
    have htangent :
        HasDerivAt
          (fun s ↦
            (jacobiBlochGaugePath S L z s).T3)
          (JacobiState.blochGaugeCombinedTangent
            κZ κPhi (S t) L (z t)).T3 t := by
      change
        HasDerivAt
          (fun s ↦ S s * (z s).T3)
          _ t
      convert hraw using 1
      simp only [
        JacobiState.blochGaugeCombinedTangent]
      ring
    rw [hcov t] at htangent
    exact htangent
  · intro t
    have hraw := (hS t).mul (hz.T4 t)
    have htangent :
        HasDerivAt
          (fun s ↦
            (jacobiBlochGaugePath S L z s).T4)
          (JacobiState.blochGaugeCombinedTangent
            κZ κPhi (S t) L (z t)).T4 t := by
      change
        HasDerivAt
          (fun s ↦ S s * (z s).T4)
          _ t
      convert hraw using 1
      simp only [
        JacobiState.blochGaugeCombinedTangent]
      ring
    rw [hcov t] at htangent
    exact htangent
  · intro t
    have hinside :=
      (hz.Delta t).add
        (HasDerivAt.const_mul L (hz.T1 t))
    have hraw := (hS t).mul hinside
    have hraw' :
        HasDerivAt
          (fun s ↦
            S s * ((z s).Delta + L * (z s).T1))
          (g * S t *
              ((z t).Delta + L * (z t).T1) +
            S t *
              ((JacobiState.combinedVectorField
                (κZ - κPhi * L / 2) κPhi
                  (z t)).Delta +
                L *
                  (JacobiState.combinedVectorField
                    (κZ - κPhi * L / 2) κPhi
                      (z t)).T1)) t := by
      simpa only [Pi.add_apply, g] using hraw
    have htangent :
        HasDerivAt
          (fun s ↦
            (jacobiBlochGaugePath S L z s).Delta)
          (JacobiState.blochGaugeCombinedTangent
            κZ κPhi (S t) L (z t)).Delta t := by
      change
        HasDerivAt
          (fun s ↦
            S s * ((z s).Delta + L * (z s).T1))
          _ t
      convert hraw' using 1
      simp only [
        JacobiState.blochGaugeCombinedTangent, g]
      ring
    rw [hcov t] at htangent
    exact htangent
  · intro t
    have hinv :=
      (hasDerivAt_inv (hSzero t)).scomp t (hS t)
    have hraw := (hz.U t).mul hinv
    have htangent :
        HasDerivAt
          (fun s ↦
            (jacobiBlochGaugePath S L z s).U)
          (JacobiState.blochGaugeCombinedTangent
            κZ κPhi (S t) L (z t)).U t := by
      change
        HasDerivAt
          (fun s ↦ (z s).U * (S s)⁻¹)
          _ t
      convert hraw using 1
      simp only [
        JacobiState.blochGaugeCombinedTangent,
        Function.comp_apply, smul_eq_mul]
      field_simp [hSzero t]
      ring
    rw [hcov t] at htangent
    exact htangent

end

end HGAS.Modular
