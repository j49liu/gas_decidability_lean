import HGAS.Compiler.PolynomialExtensionTrajectoryCrosswalk
import Mathlib.Tactic

/-!
# Recovering structured trajectories from polynomial extensions

`PolynomialExtensionTrajectoryCrosswalk` proves the forward direction:
solutions of the source equation together with the adjoined scalar
equations flatten to a solution of the compiled real polynomial field.

This file proves the converse.  It is useful whenever a trajectory is
obtained abstractly in the final Euclidean coordinate space (for example,
after compactification and a change to physical time).  The coordinate
projections of that trajectory then recover:

* the source integral curve;
* each complex fourth-root gauge equation;
* each complex reciprocal equation; and
* the two real equations of the final phase oscillator.

No invariant-circle, graph-residual, or nonvanishing assumption is used.
The results are therefore exact ambient statements about the emitted
polynomial fields.
-/

namespace HGAS

noncomputable section

/-! ## Reassembling a complex derivative from its two real coordinates -/

/-- A complex-valued real-time derivative is determined by the
derivatives of its real and imaginary parts. -/
theorem HasDerivAt.complex_of_re_im
    {f : ℝ → ℂ} {f' : ℂ} {t : ℝ}
    (hre : HasDerivAt (fun s => (f s).re) f'.re t)
    (him : HasDerivAt (fun s => (f s).im) f'.im t) :
    HasDerivAt f f' t := by
  have hre' :
      HasDerivAt
        (fun s => ((f s).re : ℂ))
        ((f'.re : ℝ) : ℂ) t :=
    hre.ofReal_comp
  have him' :
      HasDerivAt
        (fun s => Complex.I * ((f s).im : ℂ))
        (Complex.I * ((f'.im : ℝ) : ℂ)) t :=
    him.ofReal_comp.const_mul Complex.I
  convert hre'.add him' using 1
  · funext s
    apply Complex.ext <;> simp
  · apply Complex.ext <;> simp

/-! ## Complex gauge families -/

namespace ComplexGaugeFamilyPolynomialCode

variable {n b : ℕ}

/-- Projecting a compiled gauge-family trajectory to its source
coordinates recovers an integral curve of the original source field. -/
theorem base_isIntegralCurve_of_point
    (F : PolynomialFieldCode n)
    (frequency : Fin b → PolynomialCode n)
    (z : ℝ → State n b)
    (h :
      IsIntegralCurve
        (fun t => point (z t))
        (fun _ x =>
          PolynomialFieldCode.realize
            (fieldCode F frequency) x)) :
    IsIntegralCurve
      (fun t => (z t).1)
      (fun _ x => PolynomialFieldCode.realize F x) := by
  intro t
  rw [hasDerivAt_pi]
  intro i
  have ht := h t
  rw [hasDerivAt_pi] at ht
  have hi := ht (baseEmbedding (b := b) i)
  change
    HasDerivAt
      (fun s => point (z s) (baseEmbedding i))
      (PolynomialFieldCode.realize
        (fieldCode F frequency) (point (z t))
        (baseEmbedding i)) t at hi
  rw [realize_fieldCode] at hi
  simpa only [point_baseEmbedding, vectorField] using hi

/-- Each complex coordinate of a compiled gauge-family trajectory
satisfies the semantic fourth-root gauge equation. -/
theorem gauge_hasDerivAt_of_point
    (F : PolynomialFieldCode n)
    (frequency : Fin b → PolynomialCode n)
    (z : ℝ → State n b)
    (h :
      IsIntegralCurve
        (fun t => point (z t))
        (fun _ x =>
          PolynomialFieldCode.realize
            (fieldCode F frequency) x))
    (a : Fin b) (t : ℝ) :
    HasDerivAt
      (fun s => (z s).2 a)
      (gaugeVelocity frequency (z t) a) t := by
  have ht := h t
  rw [hasDerivAt_pi] at ht
  have hre := ht (gaugeEmbedding (n := n) a (0 : Fin 2))
  have him := ht (gaugeEmbedding (n := n) a (1 : Fin 2))
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

/-- Exact trajectory semantics of the gauge-family compiler. -/
theorem point_isIntegralCurve_iff
    (F : PolynomialFieldCode n)
    (frequency : Fin b → PolynomialCode n)
    (z : ℝ → State n b) :
    IsIntegralCurve
        (fun t => point (z t))
        (fun _ x =>
          PolynomialFieldCode.realize
            (fieldCode F frequency) x) ↔
      IsIntegralCurve
          (fun t => (z t).1)
          (fun _ x => PolynomialFieldCode.realize F x) ∧
        ∀ a t,
          HasDerivAt
            (fun s => (z s).2 a)
            (gaugeVelocity frequency (z t) a) t := by
  constructor
  · intro h
    exact
      ⟨base_isIntegralCurve_of_point F frequency z h,
        fun a t => gauge_hasDerivAt_of_point F frequency z h a t⟩
  · rintro ⟨hbase, hgauge⟩
    exact point_isIntegralCurve F frequency z hbase hgauge

end ComplexGaugeFamilyPolynomialCode

/-! ## Complex reciprocal families -/

namespace ComplexReciprocalFamilyPolynomialCode

variable {n b : ℕ}

/-- Projecting a compiled reciprocal-family trajectory to its source
coordinates recovers the source integral curve. -/
theorem base_isIntegralCurve_of_point
    (F : PolynomialFieldCode n)
    (η : Fin b → RationalCode)
    (wdot : ObservableFamily n b)
    (z : ℝ → State n b)
    (h :
      IsIntegralCurve
        (fun t => point (z t))
        (fun _ x =>
          PolynomialFieldCode.realize
            (fieldCode F η wdot) x)) :
    IsIntegralCurve
      (fun t => (z t).1)
      (fun _ x => PolynomialFieldCode.realize F x) := by
  intro t
  rw [hasDerivAt_pi]
  intro i
  have ht := h t
  rw [hasDerivAt_pi] at ht
  have hi := ht (baseEmbedding (b := b) i)
  change
    HasDerivAt
      (fun s => point (z s) (baseEmbedding i))
      (PolynomialFieldCode.realize
        (fieldCode F η wdot) (point (z t))
        (baseEmbedding i)) t at hi
  rw [realize_fieldCode] at hi
  simpa only [point_baseEmbedding, vectorField] using hi

/-- Each complex reciprocal coordinate of a compiled trajectory
satisfies the semantic Riccati equation. -/
theorem reciprocal_hasDerivAt_of_point
    (F : PolynomialFieldCode n)
    (η : Fin b → RationalCode)
    (wdot : ObservableFamily n b)
    (z : ℝ → State n b)
    (h :
      IsIntegralCurve
        (fun t => point (z t))
        (fun _ x =>
          PolynomialFieldCode.realize
            (fieldCode F η wdot) x))
    (a : Fin b) (t : ℝ) :
    HasDerivAt
      (fun s => (z s).2 a)
      (reciprocalVelocity
        ((RationalCode.decode (η a) : ℝ) : ℂ)
        (evalObservable (wdot a) (z t).1)
        ((z t).2 a)) t := by
  have ht := h t
  rw [hasDerivAt_pi] at ht
  have hre :=
    ht (reciprocalEmbedding (n := n) a (0 : Fin 2))
  have him :=
    ht (reciprocalEmbedding (n := n) a (1 : Fin 2))
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

/-- Exact trajectory semantics of the reciprocal-family compiler. -/
theorem point_isIntegralCurve_iff
    (F : PolynomialFieldCode n)
    (η : Fin b → RationalCode)
    (wdot : ObservableFamily n b)
    (z : ℝ → State n b) :
    IsIntegralCurve
        (fun t => point (z t))
        (fun _ x =>
          PolynomialFieldCode.realize
            (fieldCode F η wdot) x) ↔
      IsIntegralCurve
          (fun t => (z t).1)
          (fun _ x => PolynomialFieldCode.realize F x) ∧
        ∀ a t,
          HasDerivAt
            (fun s => (z s).2 a)
            (reciprocalVelocity
              ((RationalCode.decode (η a) : ℝ) : ℂ)
              (evalObservable (wdot a) (z t).1)
              ((z t).2 a)) t := by
  constructor
  · intro h
    exact
      ⟨base_isIntegralCurve_of_point F η wdot z h,
        fun a t =>
          reciprocal_hasDerivAt_of_point F η wdot z h a t⟩
  · rintro ⟨hbase, hreciprocal⟩
    exact point_isIntegralCurve F η wdot z hbase hreciprocal

end ComplexReciprocalFamilyPolynomialCode

/-! ## Right-hand-side oscillator -/

namespace Clocks.RHSOscillatorPolynomialCode

variable {n q : ℕ}

/-- Projecting a compiled oscillator extension to its base block recovers
the base integral curve. -/
theorem base_isIntegralCurve_of_combinedPoint
    (F : PolynomialFieldCode n)
    (a : Fin q → RationalCode)
    (ν : Fin q → PolynomialCode n)
    (x : ℝ → Fin n → ℝ)
    (z : ℝ → Clocks.Controller.PhaseState ℝ)
    (h :
      IsIntegralCurve
        (fun t => combinedPoint (x t) (z t))
        (fun _ y =>
          PolynomialFieldCode.realize
            (fieldCode F a ν) y)) :
    IsIntegralCurve
      x (fun _ y => PolynomialFieldCode.realize F y) := by
  intro t
  rw [hasDerivAt_pi]
  intro i
  have ht := h t
  rw [hasDerivAt_pi] at ht
  have hi :=
    ht (PolynomialBlockCode.leftEmbedding (p := 2) i)
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

/-- Projecting the two final real coordinates recovers the oscillator
trajectory equations. -/
theorem isOscillatorTrajectory_of_combinedPoint
    (F : PolynomialFieldCode n)
    (a : Fin q → RationalCode)
    (ν : Fin q → PolynomialCode n)
    (x : ℝ → Fin n → ℝ)
    (z : ℝ → Clocks.Controller.PhaseState ℝ)
    (h :
      IsIntegralCurve
        (fun t => combinedPoint (x t) (z t))
        (fun _ y =>
          PolynomialFieldCode.realize
            (fieldCode F a ν) y)) :
    IsOscillatorTrajectory a ν x z where
  c := by
    intro t
    have ht := h t
    rw [hasDerivAt_pi] at ht
    have hc := ht (xIndex n)
    change
      HasDerivAt
        (fun s => combinedPoint (x s) (z s) (xIndex n))
        (PolynomialFieldCode.realize
          (fieldCode F a ν) (combinedPoint (x t) (z t))
          (xIndex n)) t at hc
    rw [realize_fieldCode] at hc
    simpa only [combinedPoint_x] using hc
  d := by
    intro t
    have ht := h t
    rw [hasDerivAt_pi] at ht
    have hd := ht (yIndex n)
    change
      HasDerivAt
        (fun s => combinedPoint (x s) (z s) (yIndex n))
        (PolynomialFieldCode.realize
          (fieldCode F a ν) (combinedPoint (x t) (z t))
          (yIndex n)) t at hd
    rw [realize_fieldCode] at hd
    simpa only [combinedPoint_y] using hd

/-- Exact trajectory semantics of the oscillator extension. -/
theorem combinedPoint_isIntegralCurve_iff
    (F : PolynomialFieldCode n)
    (a : Fin q → RationalCode)
    (ν : Fin q → PolynomialCode n)
    (x : ℝ → Fin n → ℝ)
    (z : ℝ → Clocks.Controller.PhaseState ℝ) :
    IsIntegralCurve
        (fun t => combinedPoint (x t) (z t))
        (fun _ y =>
          PolynomialFieldCode.realize
            (fieldCode F a ν) y) ↔
      IsIntegralCurve
          x (fun _ y => PolynomialFieldCode.realize F y) ∧
        IsOscillatorTrajectory a ν x z := by
  constructor
  · intro h
    exact
      ⟨base_isIntegralCurve_of_combinedPoint F a ν x z h,
        isOscillatorTrajectory_of_combinedPoint F a ν x z h⟩
  · rintro ⟨hbase, hoscillator⟩
    exact
      combinedPoint_isIntegralCurve
        F a ν x z hbase hoscillator

end Clocks.RHSOscillatorPolynomialCode

end

end HGAS
