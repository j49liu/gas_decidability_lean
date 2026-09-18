import HGAS.Analysis.ComplexRealTimeDerivative
import HGAS.Compiler.ComplexGaugeFamilyPolynomialCode
import HGAS.Compiler.ComplexReciprocalFamilyPolynomialCode
import HGAS.Clocks.RHSOscillatorPolynomialCode
import Mathlib.Tactic

/-!
# Integral curves of reusable polynomial extensions

Several stages of the detector compiler have the same logical shape.
Starting from a real polynomial source trajectory, they adjoin either

* finitely many complex fourth-root gauges;
* finitely many complex reciprocal coordinates; or
* one two-real-coordinate phase oscillator.

The compiler files prove exact *pointwise* semantics for their polynomial
fields.  This file supplies the corresponding *trajectory* interface.
It is deliberately independent of the Jacobi application: clients only
need to prove the source integral-curve equation and the scalar ODEs for
the newly adjoined coordinates.
-/

namespace HGAS

noncomputable section

/-! ## Complex gauge families -/

namespace ComplexGaugeFamilyPolynomialCode

variable {n b : ℕ}

/-- If the base path follows `F` and each complex gauge follows its
compiled scalar ODE, the flattened real path follows the complete
gauge-family polynomial field. -/
theorem point_isIntegralCurve
    (F : PolynomialFieldCode n)
    (frequency : Fin b → PolynomialCode n)
    (z : ℝ → State n b)
    (hbase :
      IsIntegralCurve
        (fun t => (z t).1)
        (fun _ x => PolynomialFieldCode.realize F x))
    (hgauge :
      ∀ a t,
        HasDerivAt
          (fun s => (z s).2 a)
          (gaugeVelocity frequency (z t) a) t) :
    IsIntegralCurve
      (fun t => point (z t))
      (fun _ x =>
        PolynomialFieldCode.realize
          (fieldCode F frequency) x) := by
  intro t
  rw [hasDerivAt_pi]
  intro k
  change
    HasDerivAt
      (fun s => point (z s) k)
      (PolynomialFieldCode.realize
        (fieldCode F frequency) (point (z t)) k) t
  rw [realize_fieldCode]
  obtain ⟨i | r, rfl⟩ :=
    finSumFinEquiv.surjective k
  · rw [show
      finSumFinEquiv (Sum.inl i) =
        baseEmbedding (b := b) i by rfl]
    have hb := hbase t
    rw [hasDerivAt_pi] at hb
    simpa only [point_baseEmbedding, vectorField] using hb i
  · obtain ⟨⟨a, j⟩, rfl⟩ :=
      finProdFinEquiv.surjective r
    have hj :
        HasDerivAt
          (fun s =>
            ![((z s).2 a).re, ((z s).2 a).im] j)
          (![(gaugeVelocity frequency (z t) a).re,
            (gaugeVelocity frequency (z t) a).im] j) t := by
      change Fin 2 at j
      fin_cases j
      · simpa using
          HGAS.HasDerivAt.complex_re (hgauge a t)
      · simpa using
          HGAS.HasDerivAt.complex_im (hgauge a t)
    rw [show
      finSumFinEquiv
          (Sum.inr (finProdFinEquiv (a, j)) :
            Fin n ⊕ Fin (gaugeDimension b)) =
        gaugeEmbedding a j by rfl]
    simpa only [point_gaugeEmbedding, vectorField] using hj

end ComplexGaugeFamilyPolynomialCode

/-! ## Complex reciprocal families -/

namespace ComplexReciprocalFamilyPolynomialCode

variable {n b : ℕ}

/-- If the base path follows `F` and every reciprocal follows the
velocity emitted by the reciprocal-family compiler, the flattened
real path is an integral curve of the complete extension. -/
theorem point_isIntegralCurve
    (F : PolynomialFieldCode n)
    (η : Fin b → RationalCode)
    (wdot : ObservableFamily n b)
    (z : ℝ → State n b)
    (hbase :
      IsIntegralCurve
        (fun t => (z t).1)
        (fun _ x => PolynomialFieldCode.realize F x))
    (hreciprocal :
      ∀ a t,
        HasDerivAt
          (fun s => (z s).2 a)
          (reciprocalVelocity
            ((RationalCode.decode (η a) : ℝ) : ℂ)
            (evalObservable (wdot a) (z t).1)
            ((z t).2 a)) t) :
    IsIntegralCurve
      (fun t => point (z t))
      (fun _ x =>
        PolynomialFieldCode.realize
          (fieldCode F η wdot) x) := by
  intro t
  rw [hasDerivAt_pi]
  intro k
  change
    HasDerivAt
      (fun s => point (z s) k)
      (PolynomialFieldCode.realize
        (fieldCode F η wdot) (point (z t)) k) t
  rw [realize_fieldCode]
  obtain ⟨i | r, rfl⟩ :=
    finSumFinEquiv.surjective k
  · rw [show
      finSumFinEquiv (Sum.inl i) =
        baseEmbedding (b := b) i by rfl]
    have hb := hbase t
    rw [hasDerivAt_pi] at hb
    simpa only [point_baseEmbedding, vectorField] using hb i
  · obtain ⟨⟨a, j⟩, rfl⟩ :=
      finProdFinEquiv.surjective r
    have hj :
        HasDerivAt
          (fun s =>
            ![((z s).2 a).re, ((z s).2 a).im] j)
          (![(reciprocalVelocity
              ((RationalCode.decode (η a) : ℝ) : ℂ)
              (evalObservable (wdot a) (z t).1)
              ((z t).2 a)).re,
            (reciprocalVelocity
              ((RationalCode.decode (η a) : ℝ) : ℂ)
              (evalObservable (wdot a) (z t).1)
              ((z t).2 a)).im] j) t := by
      change Fin 2 at j
      fin_cases j
      · simpa using
          HGAS.HasDerivAt.complex_re (hreciprocal a t)
      · simpa using
          HGAS.HasDerivAt.complex_im (hreciprocal a t)
    rw [show
      finSumFinEquiv
          (Sum.inr (finProdFinEquiv (a, j)) :
            Fin n ⊕ Fin (reciprocalDimension b)) =
        reciprocalEmbedding a j by rfl]
    simpa only [point_reciprocalEmbedding, vectorField] using hj

end ComplexReciprocalFamilyPolynomialCode

/-! ## The right-hand-side oscillator -/

namespace Clocks.RHSOscillatorPolynomialCode

variable {n q : ℕ}

/-- Coordinatewise trajectory interface for the real two-dimensional
oscillator appended by `RHSOscillatorPolynomialCode`. -/
structure IsOscillatorTrajectory
    (a : Fin q → RationalCode)
    (ν : Fin q → PolynomialCode n)
    (x : ℝ → Fin n → ℝ)
    (z : ℝ → Clocks.Controller.PhaseState ℝ) : Prop where
  c :
    ∀ t,
      HasDerivAt
        (fun s => (z s).c)
        (oscillatorField a ν (x t) (z t)).c t
  d :
    ∀ t,
      HasDerivAt
        (fun s => (z s).d)
        (oscillatorField a ν (x t) (z t)).d t

/-- A base integral curve and a solution of the appended oscillator
equations combine into an integral curve of the literal augmented
polynomial field. -/
theorem combinedPoint_isIntegralCurve
    (F : PolynomialFieldCode n)
    (a : Fin q → RationalCode)
    (ν : Fin q → PolynomialCode n)
    (x : ℝ → Fin n → ℝ)
    (z : ℝ → Clocks.Controller.PhaseState ℝ)
    (hbase :
      IsIntegralCurve
        x (fun _ y => PolynomialFieldCode.realize F y))
    (hoscillator :
      IsOscillatorTrajectory a ν x z) :
    IsIntegralCurve
      (fun t => combinedPoint (x t) (z t))
      (fun _ y =>
        PolynomialFieldCode.realize
          (fieldCode F a ν) y) := by
  intro t
  rw [hasDerivAt_pi]
  intro k
  change
    HasDerivAt
      (fun s => combinedPoint (x s) (z s) k)
      (PolynomialFieldCode.realize
        (fieldCode F a ν)
        (combinedPoint (x t) (z t)) k) t
  rw [realize_fieldCode]
  obtain ⟨i | j, rfl⟩ :=
    finSumFinEquiv.surjective k
  · rw [show
      finSumFinEquiv (Sum.inl i) =
        PolynomialBlockCode.leftEmbedding
          (p := 2) i by rfl]
    have hb := hbase t
    rw [hasDerivAt_pi] at hb
    simpa [combinedPoint] using hb i
  · have hj :
        HasDerivAt
          (fun s => ![(z s).c, (z s).d] j)
          (![(oscillatorField a ν (x t) (z t)).c,
            (oscillatorField a ν (x t) (z t)).d] j) t := by
      fin_cases j
      · simpa using hoscillator.c t
      · simpa using hoscillator.d t
    rw [show
      finSumFinEquiv
          (Sum.inr j : Fin n ⊕ Fin 2) =
        PolynomialBlockCode.rightEmbedding
          (m := n) j by rfl]
    simpa only [combinedPoint,
      PolynomialBlockCode.point_rightEmbedding] using hj

end Clocks.RHSOscillatorPolynomialCode

end

end HGAS
