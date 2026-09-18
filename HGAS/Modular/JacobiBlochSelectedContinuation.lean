import HGAS.Modular.JacobiBlochRegularContinuation
import HGAS.Modular.JacobiPointwiseSaturationUnconditional

/-!
# Selecting and continuing affine Jacobi--Bloch initial data

This module connects the explicit inverse parameters from
`JacobiBlochInitialData` with the global continuation theorem.

Given a modulus `τ`, a displayed base point `w`, speeds `ν,κ`, and
prescribed theta data `(S,ξ,L)` at time `t₀`, the structure
`selectedAffineBlochParameters` chooses the constants

```text
  u₀ = Re τ - κt₀,       w₀ = w - νt₀,
  a₀ = L/(2i),           b₀ = ξ-w-a₀τ,
  c₀ = S exp(-πia₀(2w+a₀τ)).
```

The following lemmas verify that the resulting affine path has exactly
the requested modulus, elliptic coordinate, scale, and Bloch slope at
`t₀`.  The final theorem feeds that initial equality into the
closed-and-open reciprocal continuation theorem.
-/

namespace HGAS.Modular

open Complex Real
open UpperHalfPlane hiding I

noncomputable section

/-- Explicit affine Bloch parameters selected from data prescribed at an
arbitrary real time `t₀`. -/
def selectedAffineBlochParameters
    (τ : ℍ) (w : ℂ) (ν κ : ℝ)
    (S ξ L : ℂ) (t₀ : ℝ) :
    AffineBlochParameters where
  u0 := τ.re - κ * t₀
  gamma := τ.im
  kappa := κ
  gamma_pos := τ.im_pos
  w0 := w - ((ν * t₀ : ℝ) : ℂ)
  nu := ν
  a0 := jacobiBlochParameterA L
  b0 := jacobiBlochParameterB ξ w (τ : ℂ) L
  c0 := jacobiBlochParameterC S w (τ : ℂ) L

namespace selectedAffineBlochParameters

variable (τ : ℍ) (w : ℂ) (ν κ : ℝ)
  (S ξ L : ℂ) (t₀ : ℝ)

@[simp]
theorem tauComplex_at :
    (selectedAffineBlochParameters
      τ w ν κ S ξ L t₀).tauComplex t₀ =
      (τ : ℂ) := by
  apply Complex.ext
  · simp [selectedAffineBlochParameters,
      AffineBlochParameters.tauComplex,
      AffineBlochParameters.tau0,
      affineHorizontalComplexLine]
  · simp [selectedAffineBlochParameters,
      AffineBlochParameters.tauComplex,
      AffineBlochParameters.tau0,
      affineHorizontalComplexLine]

@[simp]
theorem tau_at :
    (selectedAffineBlochParameters
      τ w ν κ S ξ L t₀).tau t₀ = τ := by
  apply UpperHalfPlane.ext
  exact tauComplex_at τ w ν κ S ξ L t₀

@[simp]
theorem w_at :
    (selectedAffineBlochParameters
      τ w ν κ S ξ L t₀).w t₀ = w := by
  simp [selectedAffineBlochParameters,
    AffineBlochParameters.w,
    affineHorizontalComplexLine]

@[simp]
theorem xi_at :
    (selectedAffineBlochParameters
      τ w ν κ S ξ L t₀).xi t₀ = ξ := by
  rw [AffineBlochParameters.xi,
    tauComplex_at, w_at]
  change
    jacobiBlochArgument
        (jacobiBlochParameterA L)
        (jacobiBlochParameterB ξ w (τ : ℂ) L)
        (τ : ℂ) w =
      ξ
  exact jacobiBlochArgument_selected ξ w (τ : ℂ) L

@[simp]
theorem commonScale_at :
    (selectedAffineBlochParameters
      τ w ν κ S ξ L t₀).commonScale t₀ = S := by
  rw [AffineBlochParameters.commonScale,
    tauComplex_at, w_at]
  change
    jacobiBlochScale
        (jacobiBlochParameterC S w (τ : ℂ) L)
        (jacobiBlochParameterA L)
        (τ : ℂ) w =
      S
  exact jacobiBlochScale_selected S w (τ : ℂ) L

@[simp]
theorem jacobiSlope_eq :
    (selectedAffineBlochParameters
      τ w ν κ S ξ L t₀).jacobiSlope = L := by
  simp only [AffineBlochParameters.jacobiSlope,
    selectedAffineBlochParameters,
    jacobiBlochParameterA]
  field_simp

theorem c0_ne_zero
    (hS : S ≠ 0) :
    (selectedAffineBlochParameters
      τ w ν κ S ξ L t₀).c0 ≠ 0 := by
  exact
    mul_ne_zero hS
      (Complex.exp_ne_zero
        (-jacobiBlochExponent
          (jacobiBlochParameterA L) (τ : ℂ) w))

/-- At the selected time, the nine regular coordinates are exactly the
Bloch gauge of the canonical theta state. -/
theorem corePoint_at :
    jacobiCorePoint
        ((selectedAffineBlochParameters
          τ w ν κ S ξ L t₀).jacobiBlochPath t₀) =
      jacobiCorePoint
        (JacobiState.blochGauge S L
          (canonicalJacobiThetaState ξ τ)) := by
  funext i
  fin_cases i <;>
    simp [jacobiCorePoint,
      AffineBlochParameters.jacobiBlochPath,
      jacobiBlochGaugePath,
      AffineBlochParameters.canonicalJacobiPath,
      canonicalJacobiThetaMovingPath,
      tau_at, xi_at, commonScale_at, jacobiSlope_eq]

end selectedAffineBlochParameters

/-! ## From the canonical residual locus to matched initial data -/

/-- A regular point of the two canonical Jacobi quadrics is the core of
one Bloch-gauged canonical theta state.

This is the state-level form of pointwise theta saturation: it includes
the four coefficient coordinates and the normalized derivative, not only
the projective theta vector. -/
theorem exists_blochGauge_core_eq_of_canonical_residual
    (τ : ℍ) (q : JacobiState ℂ) (w : ℂ)
    (hp2 : q.p2 = (canonicalUnaryRoots τ).p2)
    (hp3 : q.p3 = (canonicalUnaryRoots τ).p3)
    (hp4 : q.p4 = (canonicalUnaryRoots τ).p4)
    (hH : q.H = (canonicalUnaryRoots τ).H)
    (hR1 : JacobiState.residualR1 q = 0)
    (hR2 : JacobiState.residualR2 q = 0)
    (hRU : q.U * q.T1 = 1) :
    ∃ S ξ L : ℂ,
      S ≠ 0 ∧
      jacobiCorePoint q =
        jacobiCorePoint
          (JacobiState.blochGauge S L
            (canonicalJacobiThetaState ξ τ)) := by
  let X : Fin 4 → ℂ :=
    jacobiResidualProjectiveCoordinates q
  have hX1 : X 0 ≠ 0 := by
    simpa only [X, jacobiResidualProjectiveCoordinates,
      Matrix.cons_val_zero] using
      right_ne_zero_of_mul_eq_one hRU
  have hX : X ≠ 0 := by
    intro hzero
    exact hX1 (congrFun hzero 0)
  have hQ1 :
      jacobiResidualQ1
          (canonicalUnaryRoots τ).p2
          (canonicalUnaryRoots τ).p3
          (canonicalUnaryRoots τ).p4 X = 0 := by
    rw [← hp2, ← hp3, ← hp4]
    simpa only [X,
      jacobiResidualQ1_projectiveCoordinates] using hR1
  have hQ2 :
      jacobiResidualQ2
          (canonicalUnaryRoots τ).p2
          (canonicalUnaryRoots τ).p3
          (canonicalUnaryRoots τ).p4 X = 0 := by
    rw [← hp2, ← hp3, ← hp4]
    simpa only [X,
      jacobiResidualQ2_projectiveCoordinates] using hR2
  obtain
      ⟨S, ξ, L, hS, hscale, hinitial,
        _hvalue, _hfirstDerivative⟩ :=
    pointwiseJacobiBlochSaturation
      τ X q.Delta w hX hX1 hQ1 hQ2
  have hDeltaRaw := congrArg Prod.snd hinitial
  have hDelta :
      S *
          (jacobiThetaVectorPrime ξ (τ : ℂ) 0 / π +
            L * jacobiThetaVector ξ (τ : ℂ) 0) =
        q.Delta := by
    simpa only [jacobiInitialValueMap,
      jacobiThetaNormalizedPrime1] using hDeltaRaw
  refine ⟨S, ξ, L, hS, ?_⟩
  funext i
  fin_cases i
  · simpa only [jacobiCorePoint, JacobiState.blochGauge,
      canonicalJacobiThetaState] using hp2
  · simpa only [jacobiCorePoint, JacobiState.blochGauge,
      canonicalJacobiThetaState] using hp3
  · simpa only [jacobiCorePoint, JacobiState.blochGauge,
      canonicalJacobiThetaState] using hp4
  · simpa only [jacobiCorePoint, JacobiState.blochGauge,
      canonicalJacobiThetaState] using hH
  · have h := congrFun hscale (0 : Fin 4)
    simpa only [X, jacobiResidualProjectiveCoordinates,
      Matrix.cons_val_zero, Pi.smul_apply, smul_eq_mul,
      jacobiCorePoint, JacobiState.blochGauge,
      canonicalJacobiThetaState] using h
  · have h := congrFun hscale (1 : Fin 4)
    simpa only [X, jacobiResidualProjectiveCoordinates,
      Matrix.cons_val_one, Matrix.cons_val_zero,
      Pi.smul_apply, smul_eq_mul,
      jacobiCorePoint, JacobiState.blochGauge,
      canonicalJacobiThetaState] using h
  · have h := congrFun hscale (2 : Fin 4)
    simpa only [X, jacobiResidualProjectiveCoordinates,
      Matrix.cons_val_one, Matrix.cons_val_zero,
      Pi.smul_apply, smul_eq_mul,
      jacobiCorePoint, JacobiState.blochGauge,
      canonicalJacobiThetaState] using h
  · have h := congrFun hscale (3 : Fin 4)
    simpa only [X, jacobiResidualProjectiveCoordinates,
      Matrix.cons_val_one, Matrix.cons_val_zero,
      Pi.smul_apply, smul_eq_mul,
      jacobiCorePoint, JacobiState.blochGauge,
      canonicalJacobiThetaState] using h
  · simpa only [jacobiCorePoint, JacobiState.blochGauge,
      canonicalJacobiThetaState] using hDelta.symm

/-- A matched Bloch-gauged canonical state at one time extends uniquely
to the complete affine theta formula. -/
theorem exists_affineBlochParameters_eq_of_core_eq_at
    (τ : ℍ) (w : ℂ) (ν κ : ℝ)
    (S ξ L : ℂ) (t₀ : ℝ)
    {z : ℝ → JacobiState ℂ}
    (hz :
      IsScaledJacobiTrajectory
        ((π : ℂ) * (ν : ℂ))
        ((π : ℂ) * I * (κ : ℂ)) z)
    (hS : S ≠ 0)
    (hreciprocal :
      ∀ t, (z t).U * (z t).T1 = 1)
    (hinitial :
      jacobiCorePoint (z t₀) =
        jacobiCorePoint
          (JacobiState.blochGauge S L
            (canonicalJacobiThetaState ξ τ))) :
    ∃ p : AffineBlochParameters,
      p.nu = ν ∧
      p.kappa = κ ∧
      p.tau t₀ = τ ∧
      p.w t₀ = w ∧
      p.xi t₀ = ξ ∧
      p.commonScale t₀ = S ∧
      p.jacobiSlope = L ∧
      (∀ t,
        jacobiTheta1 (p.xi t) (p.tau t : ℂ) ≠ 0) ∧
      z = p.jacobiBlochPath := by
  let p :=
    selectedAffineBlochParameters
      τ w ν κ S ξ L t₀
  have hp0 :
      jacobiCorePoint (z t₀) =
        jacobiCorePoint (p.jacobiBlochPath t₀) := by
    rw [selectedAffineBlochParameters.corePoint_at]
    exact hinitial
  have hcontinue :=
    p.regular_and_eq_jacobiBlochPath_of_core_eq_at
      hz
      (selectedAffineBlochParameters.c0_ne_zero
        τ w ν κ S ξ L t₀ hS)
      hreciprocal hp0
  refine ⟨p, rfl, rfl, ?_, ?_, ?_, ?_, ?_, hcontinue⟩
  · exact selectedAffineBlochParameters.tau_at
      τ w ν κ S ξ L t₀
  · exact selectedAffineBlochParameters.w_at
      τ w ν κ S ξ L t₀
  · exact selectedAffineBlochParameters.xi_at
      τ w ν κ S ξ L t₀
  · exact selectedAffineBlochParameters.commonScale_at
      τ w ν κ S ξ L t₀
  · exact selectedAffineBlochParameters.jacobiSlope_eq
      τ w ν κ S ξ L t₀

/-- **Canonical residual trajectory classification.**

A complete Jacobi trajectory whose state at `t₀` lies on the canonical
coefficient branch and on the two theta quadrics is one globally regular
affine Jacobi--Bloch solution. -/
theorem exists_affineBlochParameters_eq_of_canonical_residual_at
    (τ : ℍ) (w : ℂ) (ν κ : ℝ) (t₀ : ℝ)
    {z : ℝ → JacobiState ℂ}
    (hz :
      IsScaledJacobiTrajectory
        ((π : ℂ) * (ν : ℂ))
        ((π : ℂ) * I * (κ : ℂ)) z)
    (hp2 : (z t₀).p2 = (canonicalUnaryRoots τ).p2)
    (hp3 : (z t₀).p3 = (canonicalUnaryRoots τ).p3)
    (hp4 : (z t₀).p4 = (canonicalUnaryRoots τ).p4)
    (hH : (z t₀).H = (canonicalUnaryRoots τ).H)
    (hR1 : JacobiState.residualR1 (z t₀) = 0)
    (hR2 : JacobiState.residualR2 (z t₀) = 0)
    (hreciprocal :
      ∀ t, (z t).U * (z t).T1 = 1) :
    ∃ p : AffineBlochParameters,
      p.nu = ν ∧
      p.kappa = κ ∧
      p.tau t₀ = τ ∧
      p.w t₀ = w ∧
      (∀ t,
        jacobiTheta1 (p.xi t) (p.tau t : ℂ) ≠ 0) ∧
      z = p.jacobiBlochPath := by
  obtain ⟨S, ξ, L, hS, hcore⟩ :=
    exists_blochGauge_core_eq_of_canonical_residual
      τ (z t₀) w hp2 hp3 hp4 hH hR1 hR2
        (hreciprocal t₀)
  obtain
      ⟨p, hpnu, hpkappa, hptau, hpw, _hpxi,
        _hpscale, _hpslope, hpregular, hpeq⟩ :=
    exists_affineBlochParameters_eq_of_core_eq_at
      τ w ν κ S ξ L t₀ hz hS hreciprocal hcore
  exact
    ⟨p, hpnu, hpkappa, hptau, hpw,
      hpregular, hpeq⟩

end

end HGAS.Modular
