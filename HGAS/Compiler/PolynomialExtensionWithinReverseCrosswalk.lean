import HGAS.Compiler.PolynomialExtensionPointwiseReverseCrosswalk
import Mathlib.Tactic

/-!
# One-sided reverse crosswalks for polynomial extensions

These are the `HasDerivWithinAt` versions of the pointwise reverse
crosswalk.  They retain the right derivative at the boundary of a
forward-time domain such as `Set.Ici 0`, which is needed when applying
forward ODE uniqueness from the initial time.
-/

namespace HGAS

noncomputable section

/-- A complex within-derivative is determined by its real and imaginary
within-derivatives. -/
theorem HasDerivWithinAt.complex_of_re_im
    {f : ℝ → ℂ} {f' : ℂ} {s : Set ℝ} {t : ℝ}
    (hre : HasDerivWithinAt (fun u => (f u).re) f'.re s t)
    (him : HasDerivWithinAt (fun u => (f u).im) f'.im s t) :
    HasDerivWithinAt f f' s t := by
  have hre' :
      HasDerivWithinAt
        (fun u => ((f u).re : ℂ))
        ((f'.re : ℝ) : ℂ) s t :=
    hre.ofReal_comp
  have him' :
      HasDerivWithinAt
        (fun u => Complex.I * ((f u).im : ℂ))
        (Complex.I * ((f'.im : ℝ) : ℂ)) s t :=
    him.ofReal_comp.const_mul Complex.I
  convert hre'.add him' using 1
  · funext u
    apply Complex.ext <;> simp
  · apply Complex.ext <;> simp

namespace ComplexGaugeFamilyPolynomialCode

variable {n b : ℕ}

theorem base_hasDerivWithinAt_of_point
    (F : PolynomialFieldCode n)
    (frequency : Fin b → PolynomialCode n)
    (z : ℝ → State n b)
    (s : Set ℝ) (t : ℝ)
    (h :
      HasDerivWithinAt
        (fun u => point (z u))
        (PolynomialFieldCode.realize
          (fieldCode F frequency) (point (z t))) s t) :
    HasDerivWithinAt
      (fun u => (z u).1)
      (PolynomialFieldCode.realize F (z t).1) s t := by
  rw [hasDerivWithinAt_pi]
  intro i
  rw [hasDerivWithinAt_pi] at h
  have hi := h (baseEmbedding (b := b) i)
  change
    HasDerivWithinAt
      (fun u => point (z u) (baseEmbedding i))
      (PolynomialFieldCode.realize
        (fieldCode F frequency) (point (z t))
        (baseEmbedding i)) s t at hi
  rw [realize_fieldCode] at hi
  simpa only [point_baseEmbedding, vectorField] using hi

theorem gauge_hasDerivWithinAt_of_point
    (F : PolynomialFieldCode n)
    (frequency : Fin b → PolynomialCode n)
    (z : ℝ → State n b)
    (s : Set ℝ) (t : ℝ)
    (h :
      HasDerivWithinAt
        (fun u => point (z u))
        (PolynomialFieldCode.realize
          (fieldCode F frequency) (point (z t))) s t)
    (a : Fin b) :
    HasDerivWithinAt
      (fun u => (z u).2 a)
      (gaugeVelocity frequency (z t) a) s t := by
  rw [hasDerivWithinAt_pi] at h
  have hre := h (gaugeEmbedding (n := n) a (0 : Fin 2))
  have him := h (gaugeEmbedding (n := n) a (1 : Fin 2))
  change
    HasDerivWithinAt
      (fun u => point (z u) (gaugeEmbedding a 0))
      (PolynomialFieldCode.realize
        (fieldCode F frequency) (point (z t))
        (gaugeEmbedding a 0)) s t at hre
  change
    HasDerivWithinAt
      (fun u => point (z u) (gaugeEmbedding a 1))
      (PolynomialFieldCode.realize
        (fieldCode F frequency) (point (z t))
        (gaugeEmbedding a 1)) s t at him
  rw [realize_fieldCode] at hre him
  apply HasDerivWithinAt.complex_of_re_im
  · simpa only [point_gaugeEmbedding, vectorField,
      Matrix.cons_val_zero] using hre
  · simpa only [point_gaugeEmbedding, vectorField,
      Matrix.cons_val_one, Matrix.cons_val_zero] using him

end ComplexGaugeFamilyPolynomialCode

namespace ComplexReciprocalFamilyPolynomialCode

variable {n b : ℕ}

theorem base_hasDerivWithinAt_of_point
    (F : PolynomialFieldCode n)
    (η : Fin b → RationalCode)
    (wdot : ObservableFamily n b)
    (z : ℝ → State n b)
    (s : Set ℝ) (t : ℝ)
    (h :
      HasDerivWithinAt
        (fun u => point (z u))
        (PolynomialFieldCode.realize
          (fieldCode F η wdot) (point (z t))) s t) :
    HasDerivWithinAt
      (fun u => (z u).1)
      (PolynomialFieldCode.realize F (z t).1) s t := by
  rw [hasDerivWithinAt_pi]
  intro i
  rw [hasDerivWithinAt_pi] at h
  have hi := h (baseEmbedding (b := b) i)
  change
    HasDerivWithinAt
      (fun u => point (z u) (baseEmbedding i))
      (PolynomialFieldCode.realize
        (fieldCode F η wdot) (point (z t))
        (baseEmbedding i)) s t at hi
  rw [realize_fieldCode] at hi
  simpa only [point_baseEmbedding, vectorField] using hi

end ComplexReciprocalFamilyPolynomialCode

namespace Clocks.RHSOscillatorPolynomialCode

variable {n q : ℕ}

theorem base_hasDerivWithinAt_of_combinedPoint
    (F : PolynomialFieldCode n)
    (a : Fin q → RationalCode)
    (ν : Fin q → PolynomialCode n)
    (x : ℝ → Fin n → ℝ)
    (z : ℝ → Clocks.Controller.PhaseState ℝ)
    (s : Set ℝ) (t : ℝ)
    (h :
      HasDerivWithinAt
        (fun u => combinedPoint (x u) (z u))
        (PolynomialFieldCode.realize
          (fieldCode F a ν) (combinedPoint (x t) (z t))) s t) :
    HasDerivWithinAt
      x (PolynomialFieldCode.realize F (x t)) s t := by
  rw [hasDerivWithinAt_pi]
  intro i
  rw [hasDerivWithinAt_pi] at h
  have hi := h (PolynomialBlockCode.leftEmbedding (p := 2) i)
  change
    HasDerivWithinAt
      (fun u =>
        combinedPoint (x u) (z u)
          (PolynomialBlockCode.leftEmbedding i))
      (PolynomialFieldCode.realize
        (fieldCode F a ν) (combinedPoint (x t) (z t))
        (PolynomialBlockCode.leftEmbedding i)) s t at hi
  rw [realize_fieldCode] at hi
  simpa only [combinedPoint_base] using hi

end Clocks.RHSOscillatorPolynomialCode

end

end HGAS
