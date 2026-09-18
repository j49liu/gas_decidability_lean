import HGAS.Compiler.PolynomialExtensionTrajectoryReverseCrosswalk
import Mathlib.Tactic

/-!
# Pointwise reverse crosswalks for polynomial extensions

The global reverse crosswalks require an `IsIntegralCurve` on the whole
real line.  A forward trajectory only has an ODE derivative on
`Set.Ici 0`, and its values at negative times are deliberately
irrelevant.  This file records the local form of the same coordinate
argument.

At one time `t`, a derivative of the flattened compiled point determines
the derivative of its source block and of every adjoined scalar.  These
lemmas are the reusable bridge from strict-positive derivatives of a
forward trajectory to the semantic compiler equations.
-/

namespace HGAS

noncomputable section

namespace ComplexGaugeFamilyPolynomialCode

variable {n b : ℕ}

/-- At a fixed time, the source derivative is the projection of the
flattened gauge-family derivative. -/
theorem base_hasDerivAt_of_pointAt
    (F : PolynomialFieldCode n)
    (frequency : Fin b → PolynomialCode n)
    (z : ℝ → State n b)
    (t : ℝ)
    (h :
      HasDerivAt
        (fun s => point (z s))
        (PolynomialFieldCode.realize
          (fieldCode F frequency) (point (z t))) t) :
    HasDerivAt
      (fun s => (z s).1)
      (PolynomialFieldCode.realize F (z t).1) t := by
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi] at h
  have hi := h (baseEmbedding (b := b) i)
  change
    HasDerivAt
      (fun s => point (z s) (baseEmbedding i))
      (PolynomialFieldCode.realize
        (fieldCode F frequency) (point (z t))
        (baseEmbedding i)) t at hi
  rw [realize_fieldCode] at hi
  simpa only [point_baseEmbedding, vectorField] using hi

/-- At a fixed time, the two real gauge coordinates reassemble to the
semantic complex gauge derivative. -/
theorem gauge_hasDerivAt_of_pointAt
    (F : PolynomialFieldCode n)
    (frequency : Fin b → PolynomialCode n)
    (z : ℝ → State n b)
    (t : ℝ)
    (h :
      HasDerivAt
        (fun s => point (z s))
        (PolynomialFieldCode.realize
          (fieldCode F frequency) (point (z t))) t)
    (a : Fin b) :
    HasDerivAt
      (fun s => (z s).2 a)
      (gaugeVelocity frequency (z t) a) t := by
  rw [hasDerivAt_pi] at h
  have hre := h (gaugeEmbedding (n := n) a (0 : Fin 2))
  have him := h (gaugeEmbedding (n := n) a (1 : Fin 2))
  change
    HasDerivAt
      (fun s => point (z s) (gaugeEmbedding a 0))
      (PolynomialFieldCode.realize
        (fieldCode F frequency) (point (z t))
        (gaugeEmbedding a 0)) t at hre
  change
    HasDerivAt
      (fun s => point (z s) (gaugeEmbedding a 1))
      (PolynomialFieldCode.realize
        (fieldCode F frequency) (point (z t))
        (gaugeEmbedding a 1)) t at him
  rw [realize_fieldCode] at hre him
  apply HasDerivAt.complex_of_re_im
  · simpa only [point_gaugeEmbedding, vectorField,
      Matrix.cons_val_zero] using hre
  · simpa only [point_gaugeEmbedding, vectorField,
      Matrix.cons_val_one, Matrix.cons_val_zero] using him

end ComplexGaugeFamilyPolynomialCode

namespace ComplexReciprocalFamilyPolynomialCode

variable {n b : ℕ}

/-- At a fixed time, the source derivative is the projection of the
flattened reciprocal-family derivative. -/
theorem base_hasDerivAt_of_pointAt
    (F : PolynomialFieldCode n)
    (η : Fin b → RationalCode)
    (wdot : ObservableFamily n b)
    (z : ℝ → State n b)
    (t : ℝ)
    (h :
      HasDerivAt
        (fun s => point (z s))
        (PolynomialFieldCode.realize
          (fieldCode F η wdot) (point (z t))) t) :
    HasDerivAt
      (fun s => (z s).1)
      (PolynomialFieldCode.realize F (z t).1) t := by
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi] at h
  have hi := h (baseEmbedding (b := b) i)
  change
    HasDerivAt
      (fun s => point (z s) (baseEmbedding i))
      (PolynomialFieldCode.realize
        (fieldCode F η wdot) (point (z t))
        (baseEmbedding i)) t at hi
  rw [realize_fieldCode] at hi
  simpa only [point_baseEmbedding, vectorField] using hi

/-- At a fixed time, the two real reciprocal coordinates reassemble to
the semantic complex Riccati derivative. -/
theorem reciprocal_hasDerivAt_of_pointAt
    (F : PolynomialFieldCode n)
    (η : Fin b → RationalCode)
    (wdot : ObservableFamily n b)
    (z : ℝ → State n b)
    (t : ℝ)
    (h :
      HasDerivAt
        (fun s => point (z s))
        (PolynomialFieldCode.realize
          (fieldCode F η wdot) (point (z t))) t)
    (a : Fin b) :
    HasDerivAt
      (fun s => (z s).2 a)
      (reciprocalVelocity
        ((RationalCode.decode (η a) : ℝ) : ℂ)
        (evalObservable (wdot a) (z t).1)
        ((z t).2 a)) t := by
  rw [hasDerivAt_pi] at h
  have hre := h (reciprocalEmbedding (n := n) a (0 : Fin 2))
  have him := h (reciprocalEmbedding (n := n) a (1 : Fin 2))
  change
    HasDerivAt
      (fun s => point (z s) (reciprocalEmbedding a 0))
      (PolynomialFieldCode.realize
        (fieldCode F η wdot) (point (z t))
        (reciprocalEmbedding a 0)) t at hre
  change
    HasDerivAt
      (fun s => point (z s) (reciprocalEmbedding a 1))
      (PolynomialFieldCode.realize
        (fieldCode F η wdot) (point (z t))
        (reciprocalEmbedding a 1)) t at him
  rw [realize_fieldCode] at hre him
  apply HasDerivAt.complex_of_re_im
  · simpa only [point_reciprocalEmbedding, vectorField,
      Matrix.cons_val_zero] using hre
  · simpa only [point_reciprocalEmbedding, vectorField,
      Matrix.cons_val_one, Matrix.cons_val_zero] using him

end ComplexReciprocalFamilyPolynomialCode

namespace Clocks.RHSOscillatorPolynomialCode

variable {n q : ℕ}

/-- At a fixed time, the base derivative is the projection of the
flattened oscillator-extension derivative. -/
theorem base_hasDerivAt_of_combinedPointAt
    (F : PolynomialFieldCode n)
    (a : Fin q → RationalCode)
    (ν : Fin q → PolynomialCode n)
    (x : ℝ → Fin n → ℝ)
    (z : ℝ → Clocks.Controller.PhaseState ℝ)
    (t : ℝ)
    (h :
      HasDerivAt
        (fun s => combinedPoint (x s) (z s))
        (PolynomialFieldCode.realize
          (fieldCode F a ν) (combinedPoint (x t) (z t))) t) :
    HasDerivAt
      x (PolynomialFieldCode.realize F (x t)) t := by
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi] at h
  have hi := h (PolynomialBlockCode.leftEmbedding (p := 2) i)
  change
    HasDerivAt
      (fun s =>
        combinedPoint (x s) (z s)
          (PolynomialBlockCode.leftEmbedding i))
      (PolynomialFieldCode.realize
        (fieldCode F a ν) (combinedPoint (x t) (z t))
        (PolynomialBlockCode.leftEmbedding i)) t at hi
  rw [realize_fieldCode] at hi
  simpa only [combinedPoint_base] using hi

/-- The cosine-like coordinate satisfies its oscillator equation at one
fixed time. -/
theorem c_hasDerivAt_of_combinedPointAt
    (F : PolynomialFieldCode n)
    (a : Fin q → RationalCode)
    (ν : Fin q → PolynomialCode n)
    (x : ℝ → Fin n → ℝ)
    (z : ℝ → Clocks.Controller.PhaseState ℝ)
    (t : ℝ)
    (h :
      HasDerivAt
        (fun s => combinedPoint (x s) (z s))
        (PolynomialFieldCode.realize
          (fieldCode F a ν) (combinedPoint (x t) (z t))) t) :
    HasDerivAt
      (fun s => (z s).c)
      (oscillatorField a ν (x t) (z t)).c t := by
  rw [hasDerivAt_pi] at h
  have hc := h (xIndex n)
  change
    HasDerivAt
      (fun s => combinedPoint (x s) (z s) (xIndex n))
      (PolynomialFieldCode.realize
        (fieldCode F a ν) (combinedPoint (x t) (z t))
        (xIndex n)) t at hc
  rw [realize_fieldCode] at hc
  simpa only [combinedPoint_x] using hc

/-- The sine-like coordinate satisfies its oscillator equation at one
fixed time. -/
theorem d_hasDerivAt_of_combinedPointAt
    (F : PolynomialFieldCode n)
    (a : Fin q → RationalCode)
    (ν : Fin q → PolynomialCode n)
    (x : ℝ → Fin n → ℝ)
    (z : ℝ → Clocks.Controller.PhaseState ℝ)
    (t : ℝ)
    (h :
      HasDerivAt
        (fun s => combinedPoint (x s) (z s))
        (PolynomialFieldCode.realize
          (fieldCode F a ν) (combinedPoint (x t) (z t))) t) :
    HasDerivAt
      (fun s => (z s).d)
      (oscillatorField a ν (x t) (z t)).d t := by
  rw [hasDerivAt_pi] at h
  have hd := h (yIndex n)
  change
    HasDerivAt
      (fun s => combinedPoint (x s) (z s) (yIndex n))
      (PolynomialFieldCode.realize
        (fieldCode F a ν) (combinedPoint (x t) (z t))
        (yIndex n)) t at hd
  rw [realize_fieldCode] at hd
  simpa only [combinedPoint_y] using hd

end Clocks.RHSOscillatorPolynomialCode

end

end HGAS
