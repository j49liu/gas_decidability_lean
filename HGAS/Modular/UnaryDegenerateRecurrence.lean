import HGAS.Modular.RiccatiRecurrence
import HGAS.Modular.UnaryDynamics
import Mathlib.Tactic

/-!
# Recurrent states on the degenerate unary modular divisors

The generic modular classification is needed only away from

```
                         A C (A + C) = 0.
```

On each of these three divisors, an elementary Riccati coordinate remains.
This file combines:

* trajectory-level invariance of the divisors;
* the algebraic Riccati identities from `UnaryAlgebra`; and
* the recurrence obstruction from `RiccatiRecurrence`;

to prove that every recurrent point on a degenerate divisor is an
equilibrium.  This is precisely the elementary divisor paragraph in the
paper's modular invariant-probability classification.

Because `UnaryModularState` is deliberately a lightweight algebraic
structure rather than a bundled product topological space, recurrence is
spelled out coordinatewise below.  One common sequence of late return times
must return all four complex coordinates.
-/

namespace HGAS.Modular

open Filter Topology
open HGAS

noncomputable section

/-- Coordinatewise forward recurrence of a unary modular trajectory, using
one common sequence of return times. -/
structure ForwardRecurrentUnaryModularAt
    (z : ℝ → UnaryModularState ℂ) (t₀ : ℝ) where
  times : ℕ → ℝ
  times_tendsto : Tendsto times atTop atTop
  A_tendsto :
    Tendsto (fun n ↦ (z (times n)).A)
      atTop (𝓝 (z t₀).A)
  C_tendsto :
    Tendsto (fun n ↦ (z (times n)).C)
      atTop (𝓝 (z t₀).C)
  E_tendsto :
    Tendsto (fun n ↦ (z (times n)).E)
      atTop (𝓝 (z t₀).E)
  Y_tendsto :
    Tendsto (fun n ↦ (z (times n)).Y)
      atTop (𝓝 (z t₀).Y)

namespace ForwardRecurrentUnaryModularAt

variable {z : ℝ → UnaryModularState ℂ} {t₀ : ℝ}

/-- The Riccati coordinate `E-C` inherits recurrence. -/
theorem E_sub_C (h : ForwardRecurrentUnaryModularAt z t₀) :
    ForwardRecurrentAt (fun t ↦ (z t).E - (z t).C) t₀ := by
  exact
    ⟨h.times, h.times_tendsto,
      h.E_tendsto.sub h.C_tendsto⟩

/-- The Riccati coordinate `E+A` inherits recurrence. -/
theorem E_add_A (h : ForwardRecurrentUnaryModularAt z t₀) :
    ForwardRecurrentAt (fun t ↦ (z t).E + (z t).A) t₀ := by
  exact
    ⟨h.times, h.times_tendsto,
      h.E_tendsto.add h.A_tendsto⟩

end ForwardRecurrentUnaryModularAt

namespace IsScaledUnaryModularTrajectory

variable {κ : ℂ} {z : ℝ → UnaryModularState ℂ} {t₀ : ℝ}

/-- On `A=0`, the recurrent Riccati coordinate `E-C` vanishes. -/
theorem E_sub_C_eq_zero_of_A_eq_zero_of_recurrent
    (hz : IsScaledUnaryModularTrajectory κ z)
    (hκ : κ ≠ 0)
    (hrec : ForwardRecurrentUnaryModularAt z t₀)
    (hA : (z t₀).A = 0) :
    (z t₀).E - (z t₀).C = 0 := by
  have hAall := hz.A_eq_zero hA
  let q : ℝ → ℂ := fun t ↦ (z t).E - (z t).C
  have hq :
      ∀ t : ℝ,
        HasDerivAt q ((κ / 6) * q t ^ 2) t := by
    intro t
    have hdiff := (hz.E t).sub (hz.C t)
    convert hdiff using 1
    change
      κ / 6 * ((z t).E - (z t).C) ^ 2 =
        κ * (UnaryModularState.vectorField (z t)).E -
          κ * (UnaryModularState.vectorField (z t)).C
    rw [← mul_sub,
      UnaryModularState.riccati_E_sub_C_of_A_eq_zero
        (z t) (hAall t)]
    ring
  apply complexRiccati_eq_zero_of_forwardRecurrent
    (κ / 6) (div_ne_zero hκ (by norm_num)) q hq
  exact hrec.E_sub_C

/-- A recurrent state on `A=0` is an equilibrium of the formal modular
vector field. -/
theorem vectorField_eq_zero_of_A_eq_zero_of_recurrent
    (hz : IsScaledUnaryModularTrajectory κ z)
    (hκ : κ ≠ 0)
    (hrec : ForwardRecurrentUnaryModularAt z t₀)
    (hA : (z t₀).A = 0) :
    UnaryModularState.vectorField (z t₀) = 0 := by
  have hq :=
    hz.E_sub_C_eq_zero_of_A_eq_zero_of_recurrent
      hκ hrec hA
  have hEC : (z t₀).E = (z t₀).C :=
    sub_eq_zero.mp hq
  apply UnaryModularState.ext
  · simp [UnaryModularState.vectorField, hA]
  · simp [UnaryModularState.vectorField, hA, hEC]
  · simp [UnaryModularState.vectorField, hA, hEC]
  · simp [UnaryModularState.vectorField, hA, hEC]

/-- On `C=0`, the recurrent Riccati coordinate `E+A` vanishes. -/
theorem E_add_A_eq_zero_of_C_eq_zero_of_recurrent
    (hz : IsScaledUnaryModularTrajectory κ z)
    (hκ : κ ≠ 0)
    (hrec : ForwardRecurrentUnaryModularAt z t₀)
    (hC : (z t₀).C = 0) :
    (z t₀).E + (z t₀).A = 0 := by
  have hCall := hz.C_eq_zero hC
  let q : ℝ → ℂ := fun t ↦ (z t).E + (z t).A
  have hq :
      ∀ t : ℝ,
        HasDerivAt q ((κ / 6) * q t ^ 2) t := by
    intro t
    have hsum := (hz.E t).add (hz.A t)
    convert hsum using 1
    change
      κ / 6 * ((z t).E + (z t).A) ^ 2 =
        κ * (UnaryModularState.vectorField (z t)).E +
          κ * (UnaryModularState.vectorField (z t)).A
    rw [← mul_add,
      UnaryModularState.riccati_E_add_A_of_C_eq_zero
        (z t) (hCall t)]
    ring
  apply complexRiccati_eq_zero_of_forwardRecurrent
    (κ / 6) (div_ne_zero hκ (by norm_num)) q hq
  exact hrec.E_add_A

/-- A recurrent state on `C=0` is an equilibrium. -/
theorem vectorField_eq_zero_of_C_eq_zero_of_recurrent
    (hz : IsScaledUnaryModularTrajectory κ z)
    (hκ : κ ≠ 0)
    (hrec : ForwardRecurrentUnaryModularAt z t₀)
    (hC : (z t₀).C = 0) :
    UnaryModularState.vectorField (z t₀) = 0 := by
  have hq :=
    hz.E_add_A_eq_zero_of_C_eq_zero_of_recurrent
      hκ hrec hC
  have hEA : (z t₀).E = -(z t₀).A :=
    eq_neg_of_add_eq_zero_left hq
  apply UnaryModularState.ext
  · simp [UnaryModularState.vectorField, hC, hEA]
  · simp [UnaryModularState.vectorField, hC]
  · simp [UnaryModularState.vectorField, hC, hEA]
  · simp [UnaryModularState.vectorField, hC, hEA]

/-- On `A+C=0`, the remaining recurrent Riccati coordinate is `E+C`. -/
theorem E_add_C_eq_zero_of_B_eq_zero_of_recurrent
    (hz : IsScaledUnaryModularTrajectory κ z)
    (hκ : κ ≠ 0)
    (hrec : ForwardRecurrentUnaryModularAt z t₀)
    (hB : UnaryModularState.B (z t₀) = 0) :
    (z t₀).E + (z t₀).C = 0 := by
  have hBall := hz.B_eq_zero hB
  let q : ℝ → ℂ := fun t ↦ (z t).E + (z t).C
  have hq :
      ∀ t : ℝ,
        HasDerivAt q ((κ / 6) * q t ^ 2) t := by
    intro t
    have hsum := (hz.E t).add (hz.C t)
    convert hsum using 1
    have hAC : (z t).A = -(z t).C := by
      exact eq_neg_of_add_eq_zero_left (by
        simpa only [UnaryModularState.B] using hBall t)
    change
      κ / 6 * ((z t).E + (z t).C) ^ 2 =
        κ * (UnaryModularState.vectorField (z t)).E +
          κ * (UnaryModularState.vectorField (z t)).C
    simp only [UnaryModularState.vectorField]
    rw [hAC]
    ring
  apply complexRiccati_eq_zero_of_forwardRecurrent
    (κ / 6) (div_ne_zero hκ (by norm_num)) q hq
  exact
    ⟨hrec.times, hrec.times_tendsto,
      hrec.E_tendsto.add hrec.C_tendsto⟩

/-- On the Jacobi residual locus, a recurrent state on `A+C=0` is an
equilibrium. -/
theorem vectorField_eq_zero_of_B_eq_zero_of_recurrent
    (hz : IsScaledUnaryModularTrajectory κ z)
    (hκ : κ ≠ 0)
    (hrec : ForwardRecurrentUnaryModularAt z t₀)
    (hB : UnaryModularState.B (z t₀) = 0)
    (hJacobi :
      UnaryModularState.jacobiResidual (z t₀) = 0) :
    UnaryModularState.vectorField (z t₀) = 0 := by
  have hq :=
    hz.E_add_C_eq_zero_of_B_eq_zero_of_recurrent
      hκ hrec hB
  have hACsum : (z t₀).A + (z t₀).C = 0 := by
    simpa only [UnaryModularState.B] using hB
  have hAC : (z t₀).A = -(z t₀).C :=
    eq_neg_of_add_eq_zero_left hACsum
  have hEC : (z t₀).E = -(z t₀).C :=
    eq_neg_of_add_eq_zero_left hq
  have hYpow : (z t₀).Y ^ 4 = 0 := by
    simp only [UnaryModularState.jacobiResidual] at hJacobi
    calc
      (z t₀).Y ^ 4 = (z t₀).A + (z t₀).C := by
        linear_combination hJacobi
      _ = 0 := hACsum
  have hY : (z t₀).Y = 0 :=
    (pow_eq_zero_iff (by norm_num : (4 : ℕ) ≠ 0)).mp hYpow
  apply UnaryModularState.ext
  · simp only [UnaryModularState.vectorField,
      UnaryModularState.zero_A]
    rw [hAC, hEC]
    ring
  · simp only [UnaryModularState.vectorField,
      UnaryModularState.zero_C]
    rw [hAC, hEC]
    ring
  · simp only [UnaryModularState.vectorField,
      UnaryModularState.zero_E]
    rw [hAC, hEC]
    ring
  · simp [UnaryModularState.vectorField, hY]

end IsScaledUnaryModularTrajectory

end

end HGAS.Modular
