import HGAS.Analysis.ComplexMatrixLinearODE
import HGAS.Modular.HorizontalTrajectory
import HGAS.Modular.UnaryRootNormalizedSolution
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Trajectory-level invariance of the unary root links

The root extension carries four polynomial residuals

```
L₂ = p₂²-A,   L₄ = p₄²-C,   L_H = 12H-E,
S₃ = p₃-Y².
```

The first three residuals form a coupled homogeneous linear system along
every trajectory of the extended polynomial vector field.  We display
its full `3×3` coefficient matrix and use the reusable finite-dimensional
matrix ODE uniqueness theorem to prove that simultaneous vanishing at one
time propagates for all time.

Once `L₂=L₄=L_H=0`, the signed residual `S₃` satisfies a scalar
homogeneous linear equation, so its vanishing propagates as well.  The
clock multiplier `κ : ℂ` is arbitrary throughout.
-/

namespace HGAS.Modular

open Complex

noncomputable section

/-- A real-time trajectory of the eight-coordinate unary root system,
with a constant complex clock multiplier `κ`. -/
structure IsScaledUnaryRootTrajectory
    (κ : ℂ) (z : ℝ → UnaryRootState ℂ) : Prop where
  base : IsScaledUnaryModularTrajectory κ
    (fun t ↦ (z t).toUnaryModularState)
  p2 : ∀ t : ℝ,
    HasDerivAt (fun s ↦ (z s).p2)
      (κ * (UnaryRootState.vectorField (z t)).p2) t
  p3 : ∀ t : ℝ,
    HasDerivAt (fun s ↦ (z s).p3)
      (κ * (UnaryRootState.vectorField (z t)).p3) t
  p4 : ∀ t : ℝ,
    HasDerivAt (fun s ↦ (z s).p4)
      (κ * (UnaryRootState.vectorField (z t)).p4) t
  H : ∀ t : ℝ,
    HasDerivAt (fun s ↦ (z s).H)
      (κ * (UnaryRootState.vectorField (z t)).H) t

namespace IsScaledUnaryRootTrajectory

variable {κ : ℂ} {z : ℝ → UnaryRootState ℂ}

/-! ## Coordinate continuity -/

theorem continuous_p2
    (hz : IsScaledUnaryRootTrajectory κ z) :
    Continuous (fun t ↦ (z t).p2) :=
  continuous_iff_continuousAt.mpr
    fun t ↦ (hz.p2 t).continuousAt

theorem continuous_p3
    (hz : IsScaledUnaryRootTrajectory κ z) :
    Continuous (fun t ↦ (z t).p3) :=
  continuous_iff_continuousAt.mpr
    fun t ↦ (hz.p3 t).continuousAt

theorem continuous_p4
    (hz : IsScaledUnaryRootTrajectory κ z) :
    Continuous (fun t ↦ (z t).p4) :=
  continuous_iff_continuousAt.mpr
    fun t ↦ (hz.p4 t).continuousAt

theorem continuous_H
    (hz : IsScaledUnaryRootTrajectory κ z) :
    Continuous (fun t ↦ (z t).H) :=
  continuous_iff_continuousAt.mpr
    fun t ↦ (hz.H t).continuousAt

/-! ## Exact residual derivatives -/

/-- The derivative of `L₂` is `κ` times its formal Lie derivative. -/
theorem link2_hasDerivAt_lie
    (hz : IsScaledUnaryRootTrajectory κ z)
    (t : ℝ) :
    HasDerivAt
      (fun s ↦ UnaryRootState.link2 (z s))
      (κ * UnaryRootState.link2Lie (z t)) t := by
  have hraw :=
    ((hz.p2 t).fun_pow 2).sub (hz.base.A t)
  convert hraw using 1
  simp only [UnaryRootState.link2Lie]
  ring_nf
  rfl

/-- The derivative of `L₄` is `κ` times its formal Lie derivative. -/
theorem link4_hasDerivAt_lie
    (hz : IsScaledUnaryRootTrajectory κ z)
    (t : ℝ) :
    HasDerivAt
      (fun s ↦ UnaryRootState.link4 (z s))
      (κ * UnaryRootState.link4Lie (z t)) t := by
  have hraw :=
    ((hz.p4 t).fun_pow 2).sub (hz.base.C t)
  convert hraw using 1
  simp only [UnaryRootState.link4Lie]
  ring_nf
  rfl

/-- The derivative of `L_H` is `κ` times its formal Lie derivative. -/
theorem linkH_hasDerivAt_lie
    (hz : IsScaledUnaryRootTrajectory κ z)
    (t : ℝ) :
    HasDerivAt
      (fun s ↦ UnaryRootState.linkH (z s))
      (κ * UnaryRootState.linkHLie (z t)) t := by
  have hraw :=
    (HasDerivAt.const_mul (12 : ℂ) (hz.H t)).sub
      (hz.base.E t)
  convert hraw using 1
  simp only [UnaryRootState.linkHLie]
  ring_nf
  rfl

/-- Explicit coupled derivative equation for `L₂`. -/
theorem link2_hasDerivAt
    (hz : IsScaledUnaryRootTrajectory κ z)
    (t : ℝ) :
    HasDerivAt
      (fun s ↦ UnaryRootState.link2 (z s))
      (κ *
        ((1 / 3 : ℂ) *
            (12 * (z t).H + (z t).p2 ^ 2 +
              2 * (z t).p4 ^ 2) *
              UnaryRootState.link2 (z t) +
          (1 / 3 : ℂ) * (z t).A *
            (UnaryRootState.linkH (z t) +
              UnaryRootState.link2 (z t) +
              2 * UnaryRootState.link4 (z t)))) t := by
  convert link2_hasDerivAt_lie hz t using 1
  rw [UnaryRootState.link2Lie_eq]

/-- Explicit coupled derivative equation for `L₄`. -/
theorem link4_hasDerivAt
    (hz : IsScaledUnaryRootTrajectory κ z)
    (t : ℝ) :
    HasDerivAt
      (fun s ↦ UnaryRootState.link4 (z s))
      (κ *
        ((1 / 3 : ℂ) *
            (12 * (z t).H - 2 * (z t).p2 ^ 2 -
              (z t).p4 ^ 2) *
              UnaryRootState.link4 (z t) +
          (1 / 3 : ℂ) * (z t).C *
            (UnaryRootState.linkH (z t) -
              2 * UnaryRootState.link2 (z t) -
              UnaryRootState.link4 (z t)))) t := by
  convert link4_hasDerivAt_lie hz t using 1
  rw [UnaryRootState.link4Lie_eq]

/-- Explicit coupled derivative equation for `L_H`. -/
theorem linkH_hasDerivAt
    (hz : IsScaledUnaryRootTrajectory κ z)
    (t : ℝ) :
    HasDerivAt
      (fun s ↦ UnaryRootState.linkH (z s))
      (κ *
        ((1 / 6 : ℂ) *
            (12 * (z t).H + (z t).E) *
              UnaryRootState.linkH (z t) -
          (1 / 6 : ℂ) *
            ((z t).p2 ^ 2 + (z t).A + (z t).C) *
              UnaryRootState.link2 (z t) -
          (1 / 6 : ℂ) *
            ((z t).p2 ^ 2 + (z t).p4 ^ 2 +
              (z t).C) *
              UnaryRootState.link4 (z t))) t := by
  convert linkH_hasDerivAt_lie hz t using 1
  rw [UnaryRootState.linkHLie_eq]

/-! ## The coupled `3×3` unsigned-link system -/

/-- Residual vector ordered as `(L₂,L₄,L_H)`. -/
def unsignedLinkVector
    (z : ℝ → UnaryRootState ℂ) (t : ℝ) :
    Fin 3 → ℂ :=
  ![UnaryRootState.link2 (z t),
    UnaryRootState.link4 (z t),
    UnaryRootState.linkH (z t)]

/-- Coefficient matrix for the coupled unsigned-link equation
`L'(t)=M(t)L(t)`.

Rows and columns are ordered as `(L₂,L₄,L_H)`.  The clock multiplier
`κ` is included in every entry, so the matrix theorem can be applied
without a subsequent rescaling. -/
def unsignedLinkMatrix
    (κ : ℂ) (z : ℝ → UnaryRootState ℂ) (t : ℝ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  !![
    κ * ((1 / 3 : ℂ) *
      (12 * (z t).H + (z t).p2 ^ 2 +
        2 * (z t).p4 ^ 2) +
      (1 / 3 : ℂ) * (z t).A),
    κ * ((2 / 3 : ℂ) * (z t).A),
    κ * ((1 / 3 : ℂ) * (z t).A);
    κ * (-(2 / 3 : ℂ) * (z t).C),
    κ * ((1 / 3 : ℂ) *
      (12 * (z t).H - 2 * (z t).p2 ^ 2 -
        (z t).p4 ^ 2) -
      (1 / 3 : ℂ) * (z t).C),
    κ * ((1 / 3 : ℂ) * (z t).C);
    κ * (-(1 / 6 : ℂ) *
      ((z t).p2 ^ 2 + (z t).A + (z t).C)),
    κ * (-(1 / 6 : ℂ) *
      ((z t).p2 ^ 2 + (z t).p4 ^ 2 +
        (z t).C)),
    κ * ((1 / 6 : ℂ) *
      (12 * (z t).H + (z t).E))
  ]

/-- The coefficient matrix varies continuously along every root
trajectory. -/
theorem continuous_unsignedLinkMatrix
    (hz : IsScaledUnaryRootTrajectory κ z) :
    Continuous (unsignedLinkMatrix κ z) := by
  have hA := hz.base.continuous_A
  have hC := hz.base.continuous_C
  have hE := hz.base.continuous_E
  have hp2 := continuous_p2 hz
  have hp4 := continuous_p4 hz
  have hH := continuous_H hz
  unfold unsignedLinkMatrix
  fun_prop

/-- The residual vector satisfies the displayed matrix ODE. -/
theorem unsignedLinkVector_hasDerivAt
    (hz : IsScaledUnaryRootTrajectory κ z)
    (t : ℝ) :
    HasDerivAt
      (unsignedLinkVector z)
      (fun i ↦
        ∑ j,
          unsignedLinkMatrix κ z t i j *
            unsignedLinkVector z t j) t := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · convert link2_hasDerivAt hz t using 1
    simp [unsignedLinkVector, unsignedLinkMatrix,
      Fin.sum_univ_succ]
    ring
  · convert link4_hasDerivAt hz t using 1
    simp [unsignedLinkVector, unsignedLinkMatrix,
      Fin.sum_univ_succ]
    ring
  · convert linkH_hasDerivAt hz t using 1
    simp [unsignedLinkVector, unsignedLinkMatrix,
      Fin.sum_univ_succ]
    ring

/-! ## Simultaneous zero propagation -/

/-- All three unsigned root links vanish at a state. -/
def UnsignedLinksZero (w : UnaryRootState ℂ) : Prop :=
  UnaryRootState.link2 w = 0 ∧
    UnaryRootState.link4 w = 0 ∧
      UnaryRootState.linkH w = 0

/-- If the three unsigned links vanish simultaneously at one time, they
vanish simultaneously for the entire trajectory. -/
theorem unsignedLinks_eq_zero
    (hz : IsScaledUnaryRootTrajectory κ z)
    {t₀ : ℝ}
    (hzero : UnsignedLinksZero (z t₀)) :
    ∀ t : ℝ, UnsignedLinksZero (z t) := by
  rcases hzero with ⟨h2, h4, hH⟩
  have hinitial :
      unsignedLinkVector z t₀ = 0 := by
    funext i
    fin_cases i <;>
      simp [unsignedLinkVector, h2, h4, hH]
  have hident :=
    HGAS.complexMatrixODE_eq_zero
      (unsignedLinkMatrix κ z)
      (unsignedLinkVector z)
      (continuous_unsignedLinkMatrix hz)
      (unsignedLinkVector_hasDerivAt hz)
      hinitial
  intro t
  have ht :
      unsignedLinkVector z t = 0 :=
    congrFun hident t
  refine ⟨?_, ?_, ?_⟩
  · simpa [unsignedLinkVector] using
      congrFun ht (0 : Fin 3)
  · simpa [unsignedLinkVector] using
      congrFun ht (1 : Fin 3)
  · simpa [unsignedLinkVector] using
      congrFun ht (2 : Fin 3)

/-! ## The signed link -/

/-- The derivative of `S₃=p₃-Y²` is `κ` times its formal Lie
derivative. -/
theorem signedLink3_hasDerivAt_lie
    (hz : IsScaledUnaryRootTrajectory κ z)
    (t : ℝ) :
    HasDerivAt
      (fun s ↦ UnaryRootState.signedLink3 (z s))
      (κ * UnaryRootState.signedLink3Lie (z t)) t := by
  have hraw :=
    (hz.p3 t).sub ((hz.base.Y t).fun_pow 2)
  convert hraw using 1
  simp only [UnaryRootState.signedLink3Lie]
  ring_nf
  rfl

/-- Exact signed-link derivative, including its forcing by the three
unsigned links. -/
theorem signedLink3_hasDerivAt
    (hz : IsScaledUnaryRootTrajectory κ z)
    (t : ℝ) :
    HasDerivAt
      (fun s ↦ UnaryRootState.signedLink3 (z s))
      (κ *
        ((1 / 6 : ℂ) *
            (12 * (z t).H + (z t).p2 ^ 2 -
              (z t).p4 ^ 2) *
              UnaryRootState.signedLink3 (z t) +
          (1 / 6 : ℂ) *
            (UnaryRootState.linkH (z t) +
              UnaryRootState.link2 (z t) -
              UnaryRootState.link4 (z t)) *
                (z t).Y ^ 2)) t := by
  convert signedLink3_hasDerivAt_lie hz t using 1
  rw [UnaryRootState.signedLink3Lie_eq]

/-- Scalar coefficient governing `S₃` once the unsigned links vanish. -/
def signedLink3Coefficient
    (κ : ℂ) (z : ℝ → UnaryRootState ℂ)
    (t : ℝ) : ℂ :=
  κ * ((1 / 6 : ℂ) *
    (12 * (z t).H + (z t).p2 ^ 2 -
      (z t).p4 ^ 2))

theorem continuous_signedLink3Coefficient
    (hz : IsScaledUnaryRootTrajectory κ z) :
    Continuous (signedLink3Coefficient κ z) := by
  have hp2 := continuous_p2 hz
  have hp4 := continuous_p4 hz
  have hH := continuous_H hz
  unfold signedLink3Coefficient
  fun_prop

/-- If all unsigned links and the signed link vanish at one time, then
the signed link vanishes for all time. -/
theorem signedLink3_eq_zero
    (hz : IsScaledUnaryRootTrajectory κ z)
    {t₀ : ℝ}
    (hunsigned : UnsignedLinksZero (z t₀))
    (hsigned :
      UnaryRootState.signedLink3 (z t₀) = 0) :
    ∀ t : ℝ,
      UnaryRootState.signedLink3 (z t) = 0 := by
  have hlinks :=
    unsignedLinks_eq_zero hz hunsigned
  have hderiv :
      ∀ t : ℝ,
        HasDerivAt
          (fun s ↦
            UnaryRootState.signedLink3 (z s))
          (signedLink3Coefficient κ z t *
            UnaryRootState.signedLink3 (z t)) t := by
    intro t
    rcases hlinks t with ⟨h2, h4, hH⟩
    convert signedLink3_hasDerivAt hz t using 1
    simp only [signedLink3Coefficient]
    rw [h2, h4, hH]
    ring
  have hident :=
    HGAS.complex_eq_zero_of_hasDerivAt_eq_mul
      (signedLink3Coefficient κ z)
      (fun t ↦ UnaryRootState.signedLink3 (z t))
      (continuous_signedLink3Coefficient hz)
      hderiv hsigned
  intro t
  exact congrFun hident t

/-- Combined propagation theorem for all four root links. -/
theorem allLinks_eq_zero
    (hz : IsScaledUnaryRootTrajectory κ z)
    {t₀ : ℝ}
    (hunsigned : UnsignedLinksZero (z t₀))
    (hsigned :
      UnaryRootState.signedLink3 (z t₀) = 0) :
    ∀ t : ℝ,
      UnsignedLinksZero (z t) ∧
        UnaryRootState.signedLink3 (z t) = 0 := by
  intro t
  exact
    ⟨unsignedLinks_eq_zero hz hunsigned t,
      signedLink3_eq_zero hz hunsigned hsigned t⟩

end IsScaledUnaryRootTrajectory

end

end HGAS.Modular
