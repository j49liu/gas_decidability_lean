import HGAS.Modular.ClosedHorocycleUnaryProjectiveBranches
import HGAS.Modular.ThetaQuarticVelocityCancellation
import HGAS.Modular.UnaryComparisonReconstruction

/-!
# Exact unary amplitude in a horizontal cusp chart

The lambda coordinate alone determines the unary quartics only
projectively.  Along a differentiable lift the missing scale is its
relative weight-two velocity.  Moving the lift by an integral modular
matrix and using weight-two theta automorphy converts that velocity into
the constant speed of the resulting horizontal line.

For the three normalized `Γ(2)` cusps the exact amplitudes are

```text
  infinity :   q =  s,   (A,B,C) = q ( H₂,H₃,H₄),
  zero     :   q = -s,   (A,B,C) = q ( H₄,H₃,H₂),
  one      :   q = -s,   (A,B,C) = q (-H₄,H₂,H₃).
```

The signs are forced by the complete signed theta transformation table;
they are not conventions.  This upgrades the projective branch theorem to
the literal normalization consumed by the Fourier moment selector.
-/

namespace HGAS.Modular

open Complex
open UpperHalfPlane hiding I

noncomputable section

/-- Exact common quartic amplitude attached to a signed horizontal speed. -/
def cuspQuarticAmplitude
    (cusp : GammaTwoCuspLabel) (s : ℝ) : ℂ :=
  match cusp with
  | .infinity => (s : ℂ)
  | .zero => -(s : ℂ)
  | .one => -(s : ℂ)

/-- A branch with its common amplitude exposed rather than existentially
quantified. -/
def HasCuspQuarticAmplitude
    (cusp : GammaTwoCuspLabel)
    (z : UnaryModularState ℂ)
    (τ : UpperHalfPlane) (q : ℂ) : Prop :=
  q ≠ 0 ∧
    match cusp with
    | .infinity =>
        z.A = q * H₂ τ ∧
        UnaryModularState.B z = q * H₃ τ ∧
        z.C = q * H₄ τ
    | .zero =>
        z.A = q * H₄ τ ∧
        UnaryModularState.B z = q * H₃ τ ∧
        z.C = q * H₂ τ
    | .one =>
        z.A = -(q * H₄ τ) ∧
        UnaryModularState.B z = q * H₂ τ ∧
        z.C = q * H₃ τ

/-- Forgetting the displayed amplitude recovers the projective branch. -/
theorem HasCuspQuarticAmplitude.isCuspQuarticBranch
    {cusp : GammaTwoCuspLabel}
    {z : UnaryModularState ℂ}
    {τ : UpperHalfPlane} {q : ℂ}
    (h : HasCuspQuarticAmplitude cusp z τ q) :
    IsCuspQuarticBranch cusp z τ :=
  ⟨q, h⟩

/-- The exact amplitude in a normalized horizontal cusp chart is the
signed horizontal speed shown in the table above. -/
theorem hasCuspQuarticAmplitude_of_horizontalized_comparison
    (cusp : GammaTwoCuspLabel)
    (γ : IntegralModularGroup)
    (hred :
      reduceModTwo γ =
        reduceModTwo (cuspRepresentative cusp))
    (z : ℝ → UnaryModularState ℂ)
    (T : ℝ → UpperHalfPlane)
    (hBz : ∀ t, UnaryModularState.B (z t) ≠ 0)
    (hlambda :
      ∀ t,
        UnaryModularState.lambdaCoordinate (z t) =
          canonicalLambda (T t))
    (x y s : ℝ) (hy : 0 < y) (hs : s ≠ 0)
    (hline :
      ∀ t,
        γ • T t = horizontalLine x y s hy t)
    (t : ℝ)
    (hT :
      HasDerivAt
        (fun u : ℝ ↦ (T u : ℂ))
        (unaryComparisonV z
          (fun u ↦ canonicalUnaryTheta (T u)) t) t) :
    HasCuspQuarticAmplitude cusp (z t) (γ • T t)
      (cuspQuarticAmplitude cusp s) := by
  let r : ℝ → UnaryModularState ℂ :=
    fun u ↦ canonicalUnaryTheta (T u)
  let v : ℂ := unaryComparisonV z r t
  have hBr_eq :
      UnaryModularState.B (r t) = H₃ (T t) := by
    have hJacobi :
        H₂ (T t) + H₄ (T t) = H₃ (T t) := by
      simpa only [Pi.add_apply] using
        congrFun jacobi_quartic_identity (T t)
    simpa only [r, UnaryModularState.B,
      canonicalUnaryTheta_A, canonicalUnaryTheta_C] using hJacobi
  have hBr :
      UnaryModularState.B (r t) ≠ 0 := by
    rw [hBr_eq]
    exact H₃_ne_zero (T t)
  have hlambda_r :
      UnaryModularState.lambdaCoordinate (z t) =
        UnaryModularState.lambdaCoordinate (r t) := by
    rw [hlambda t]
    exact (canonicalUnaryTheta_lambdaCoordinate (T t)).symm
  have hA :
      (z t).A = v * H₂ (T t) := by
    simpa only [v, r, canonicalUnaryTheta_A] using
      unaryComparison_A_eq z r t (hBz t) hBr hlambda_r
  have hB :
      UnaryModularState.B (z t) = v * H₃ (T t) := by
    rw [show H₃ (T t) = UnaryModularState.B (r t) by
      exact hBr_eq.symm]
    exact unaryComparison_B_eq z r t hBr
  have hC :
      (z t).C = v * H₄ (T t) := by
    simpa only [v, r, canonicalUnaryTheta_C] using
      unaryComparison_C_eq z r t (hBz t) hBr hlambda_r
  have hvelocity (i : Fin 3) :
      v *
          thetaEvenQuartic
            (thetaSquareIndex (reduceModTwo γ) i) (T t) =
        (thetaQuarticSign (reduceModTwo γ) i : ℂ) *
          (s : ℂ) *
            thetaEvenQuartic i (γ • T t) := by
    exact
      velocity_mul_thetaQuartic_index_eq
        γ T x y s hy hline t (by simpa only [v, r] using hT) i
  cases cusp with
  | infinity =>
      have hred' : reduceModTwo γ = 1 := by
        simpa [cuspRepresentative] using hred
      rw [hred'] at hvelocity
      refine
        ⟨Complex.ofReal_ne_zero.mpr hs, ?_, ?_, ?_⟩
      · rw [hA]
        have hv := hvelocity (0 : Fin 3)
        rw [thetaSquareIndex_one, thetaQuarticSign_one] at hv
        simpa [thetaEvenQuartic, cuspQuarticAmplitude] using hv
      · rw [hB]
        have hv := hvelocity (1 : Fin 3)
        rw [thetaSquareIndex_one, thetaQuarticSign_one] at hv
        simpa [thetaEvenQuartic, cuspQuarticAmplitude] using hv
      · rw [hC]
        have hv := hvelocity (2 : Fin 3)
        rw [thetaSquareIndex_one, thetaQuarticSign_one] at hv
        simpa [thetaEvenQuartic, cuspQuarticAmplitude] using hv
  | zero =>
      have hred' :
          reduceModTwo γ = reduceModTwo ModularGroup.S := by
        simpa [cuspRepresentative] using hred
      rw [hred'] at hvelocity
      refine
        ⟨neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hs),
          ?_, ?_, ?_⟩
      · rw [hA]
        have hv := hvelocity (2 : Fin 3)
        rw [thetaSquareIndex_S, thetaQuarticSign_S] at hv
        convert hv using 1
        all_goals simp [thetaEvenQuartic, cuspQuarticAmplitude]
      · rw [hB]
        have hv := hvelocity (1 : Fin 3)
        rw [thetaSquareIndex_S, thetaQuarticSign_S] at hv
        convert hv using 1
        all_goals simp [thetaEvenQuartic, cuspQuarticAmplitude]
      · rw [hC]
        have hv := hvelocity (0 : Fin 3)
        rw [thetaSquareIndex_S, thetaQuarticSign_S] at hv
        convert hv using 1
        all_goals simp [thetaEvenQuartic, cuspQuarticAmplitude]
  | one =>
      have hred' :
          reduceModTwo γ =
            reduceModTwo (ModularGroup.S * ModularGroup.T) := by
        simpa [cuspRepresentative] using hred
      rw [hred'] at hvelocity
      refine
        ⟨neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hs),
          ?_, ?_, ?_⟩
      · rw [hA]
        have hv := hvelocity (2 : Fin 3)
        rw [thetaSquareIndex_ST, thetaQuarticSign_ST] at hv
        convert hv using 1
        all_goals simp [thetaEvenQuartic, cuspQuarticAmplitude]
      · rw [hB]
        have hv := hvelocity (0 : Fin 3)
        rw [thetaSquareIndex_ST, thetaQuarticSign_ST] at hv
        convert hv using 1
        all_goals simp [thetaEvenQuartic, cuspQuarticAmplitude]
      · rw [hC]
        have hv := hvelocity (1 : Fin 3)
        rw [thetaSquareIndex_ST, thetaQuarticSign_ST] at hv
        convert hv using 1
        all_goals simp [thetaEvenQuartic, cuspQuarticAmplitude]

end

end HGAS.Modular
