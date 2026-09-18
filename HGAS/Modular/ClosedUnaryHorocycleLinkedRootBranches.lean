import HGAS.Modular.ClosedUnaryHorocycleExactAmplitude
import HGAS.Modular.JacobiCoefficientLinkDynamics
import HGAS.Modular.JacobiResidualEnergy
import HGAS.Modular.ThetaZeroFree
import HGAS.Topology.ContinuousConstantRootMultiple
import Mathlib.Tactic

/-!
# Coherent root branches in an exact unary cusp chart

The exact cusp-amplitude theorem identifies the unary quartics with one
fixed nonzero multiple of a permuted triple of theta fourth powers.
The linked Jacobi residuals then say

```text
  Y⁴ = A + C,       p₂² = A,       p₄² = C.
```

Pointwise these equations leave fourth- and square-root ambiguities.  Along
a complete trajectory the relevant coordinates are continuous, and none of
the theta constants vanishes on the upper half-plane.  Since the real time
axis is connected, each ambiguity is therefore one *constant* nonzero
complex scalar, rather than a sign or phase which can change with time.

The resulting reference table is

```text
 cusp       Y reference     p₂ reference     p₄ reference
 ---------------------------------------------------------
 infinity      θ₃               θ₂²               θ₄²
 zero          θ₃               θ₄²               θ₂²
 one           θ₂               θ₄²               θ₃² .
```

At the one cusp the exact amplitude gives `A = -q H₄`; the minus sign is
absorbed into the constant `p₂` scale.  No logarithm and no choice of a
time-dependent complex root is used.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I

noncomputable section

/-! ## Uniform cusp reference functions -/

/-- The theta constant whose fourth power is the unary `Y⁴` coordinate
in the indicated exact cusp branch. -/
def cuspYRoot
    (cusp : GammaTwoCuspLabel) (τ : UpperHalfPlane) : ℂ :=
  match cusp with
  | .infinity => theta₃ τ
  | .zero => theta₃ τ
  | .one => theta₂ τ

/-- The theta square whose square is the linked `p₂²` coordinate, up to
one fixed nonzero scalar. -/
def cuspP2Root
    (cusp : GammaTwoCuspLabel) (τ : UpperHalfPlane) : ℂ :=
  match cusp with
  | .infinity => theta₂ τ ^ 2
  | .zero => theta₄ τ ^ 2
  | .one => theta₄ τ ^ 2

/-- The theta square whose square is the linked `p₄²` coordinate, up to
one fixed nonzero scalar. -/
def cuspP4Root
    (cusp : GammaTwoCuspLabel) (τ : UpperHalfPlane) : ℂ :=
  match cusp with
  | .infinity => theta₄ τ ^ 2
  | .zero => theta₂ τ ^ 2
  | .one => theta₃ τ ^ 2

/-- Pointwise zero-freeness of `θ₂`, extracted from that of `H₂=θ₂⁴`. -/
theorem theta₂_ne_zero (τ : UpperHalfPlane) :
    theta₂ τ ≠ 0 := by
  intro hzero
  apply H₂_ne_zero τ
  simp [H₂, hzero]

/-- Pointwise zero-freeness of `θ₃`, extracted from that of `H₃=θ₃⁴`. -/
theorem theta₃_ne_zero (τ : UpperHalfPlane) :
    theta₃ τ ≠ 0 := by
  intro hzero
  apply H₃_ne_zero τ
  simp [H₃, hzero]

/-- Pointwise zero-freeness of `θ₄`, extracted from that of `H₄=θ₄⁴`. -/
theorem theta₄_ne_zero (τ : UpperHalfPlane) :
    theta₄ τ ≠ 0 := by
  intro hzero
  apply H₄_ne_zero τ
  simp [H₄, hzero]

/-- The three globally coherent root choices supplied by connectedness.
All three scales are nonzero and independent of time. -/
structure CuspLinkedRootBranches
    (cusp : GammaTwoCuspLabel)
    (z : ℝ → LinkedJacobiState ℂ)
    (τ : ℝ → UpperHalfPlane) where
  yScale : ℂ
  p2Scale : ℂ
  p4Scale : ℂ
  yScale_ne_zero : yScale ≠ 0
  p2Scale_ne_zero : p2Scale ≠ 0
  p4Scale_ne_zero : p4Scale ≠ 0
  y_eq : ∀ t, (z t).unary.Y = yScale * cuspYRoot cusp (τ t)
  p2_eq : ∀ t, (z t).jacobi.p2 = p2Scale * cuspP2Root cusp (τ t)
  p4_eq : ∀ t, (z t).jacobi.p4 = p4Scale * cuspP4Root cusp (τ t)

/-! ## The connected-path root theorem -/

/-- Exact cusp amplitude plus the three displayed linked residuals gives
one global nonzero scalar for each root coordinate.

The modulus path is allowed to be any continuous upper-half-plane path.
The horizontal-line specialization below is the form used by the closed
horocycle selector. -/
theorem exists_cuspLinkedRootBranches_of_continuous
    {κZ κPhi : ℂ}
    (cusp : GammaTwoCuspLabel)
    (z : ℝ → LinkedJacobiState ℂ)
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z)
    (τ : ℝ → UpperHalfPlane)
    (hτ : Continuous τ)
    (q : ℂ) (hq : q ≠ 0)
    (hamplitude :
      ∀ t, HasCuspQuarticAmplitude cusp (z t).unary (τ t) q)
    (hresidual :
      ∀ t (r : LinkedJacobiResidualIndex),
        linkedJacobiResidual r (z t) = 0) :
    Nonempty (CuspLinkedRootBranches cusp z τ) := by
  have htheta₂ :
      Continuous (fun t ↦ theta₂ (τ t)) :=
    theta₂_mdifferentiable.continuous.comp hτ
  have htheta₃ :
      Continuous (fun t ↦ theta₃ (τ t)) :=
    theta₃_mdifferentiable.continuous.comp hτ
  have htheta₄ :
      Continuous (fun t ↦ theta₄ (τ t)) :=
    theta₄_mdifferentiable.continuous.comp hτ
  cases cusp with
  | infinity =>
      have hYfourth :
          ∀ t, (z t).unary.Y ^ 4 =
            q * (theta₃ (τ t)) ^ 4 := by
        intro t
        have hJacobi :
            H₂ (τ t) + H₄ (τ t) = H₃ (τ t) := by
          simpa only [Pi.add_apply] using
            congrFun jacobi_quartic_identity (τ t)
        have hA := (hamplitude t).2.1
        have hC := (hamplitude t).2.2.2
        have hR := hresidual t .unaryJacobi
        change
          (z t).unary.Y ^ 4 -
              (z t).unary.A - (z t).unary.C = 0 at hR
        rw [hA, hC] at hR
        rw [H₃] at hJacobi
        linear_combination hR + q * hJacobi
      have hp2square :
          ∀ t, (z t).jacobi.p2 ^ 2 =
            q * (theta₂ (τ t) ^ 2) ^ 2 := by
        intro t
        have hA := (hamplitude t).2.1
        have hR := hresidual t .coefficientLinkTwo
        change
          (z t).jacobi.p2 ^ 2 - (z t).unary.A = 0 at hR
        rw [hA] at hR
        calc
          (z t).jacobi.p2 ^ 2 = q * H₂ (τ t) :=
            sub_eq_zero.mp hR
          _ = q * (theta₂ (τ t) ^ 2) ^ 2 := by
            simp only [H₂]
            ring
      have hp4square :
          ∀ t, (z t).jacobi.p4 ^ 2 =
            q * (theta₄ (τ t) ^ 2) ^ 2 := by
        intro t
        have hC := (hamplitude t).2.2.2
        have hR := hresidual t .coefficientLinkFour
        change
          (z t).jacobi.p4 ^ 2 - (z t).unary.C = 0 at hR
        rw [hC] at hR
        calc
          (z t).jacobi.p4 ^ 2 = q * H₄ (τ t) :=
            sub_eq_zero.mp hR
          _ = q * (theta₄ (τ t) ^ 2) ^ 2 := by
            simp only [H₄]
            ring
      obtain ⟨yScale, hyScale, hy⟩ :=
        HGAS.Topology.exists_constant_complex_multiple_of_fourth_eq
          (fun t ↦ (z t).unary.Y)
          (fun t ↦ theta₃ (τ t))
          hz.unary.continuous_Y htheta₃ hYfourth
          (fun t ↦ theta₃_ne_zero (τ t)) hq
      obtain ⟨p2Scale, hp2Scale, hp2⟩ :=
        HGAS.Topology.exists_constant_complex_multiple_of_sq_eq
          (fun t ↦ (z t).jacobi.p2)
          (fun t ↦ theta₂ (τ t) ^ 2)
          hz.jacobi.continuous_p2 (htheta₂.pow 2) hp2square
          (fun t ↦ pow_ne_zero 2 (theta₂_ne_zero (τ t))) hq
      obtain ⟨p4Scale, hp4Scale, hp4⟩ :=
        HGAS.Topology.exists_constant_complex_multiple_of_sq_eq
          (fun t ↦ (z t).jacobi.p4)
          (fun t ↦ theta₄ (τ t) ^ 2)
          hz.jacobi.continuous_p4 (htheta₄.pow 2) hp4square
          (fun t ↦ pow_ne_zero 2 (theta₄_ne_zero (τ t))) hq
      exact
        ⟨{
          yScale := yScale
          p2Scale := p2Scale
          p4Scale := p4Scale
          yScale_ne_zero := hyScale
          p2Scale_ne_zero := hp2Scale
          p4Scale_ne_zero := hp4Scale
          y_eq := by
            simpa only [cuspYRoot] using hy
          p2_eq := by
            simpa only [cuspP2Root] using hp2
          p4_eq := by
            simpa only [cuspP4Root] using hp4
        }⟩
  | zero =>
      have hYfourth :
          ∀ t, (z t).unary.Y ^ 4 =
            q * (theta₃ (τ t)) ^ 4 := by
        intro t
        have hJacobi :
            H₂ (τ t) + H₄ (τ t) = H₃ (τ t) := by
          simpa only [Pi.add_apply] using
            congrFun jacobi_quartic_identity (τ t)
        have hA := (hamplitude t).2.1
        have hC := (hamplitude t).2.2.2
        have hR := hresidual t .unaryJacobi
        change
          (z t).unary.Y ^ 4 -
              (z t).unary.A - (z t).unary.C = 0 at hR
        rw [hA, hC] at hR
        rw [H₃] at hJacobi
        linear_combination hR + q * hJacobi
      have hp2square :
          ∀ t, (z t).jacobi.p2 ^ 2 =
            q * (theta₄ (τ t) ^ 2) ^ 2 := by
        intro t
        have hA := (hamplitude t).2.1
        have hR := hresidual t .coefficientLinkTwo
        change
          (z t).jacobi.p2 ^ 2 - (z t).unary.A = 0 at hR
        rw [hA] at hR
        calc
          (z t).jacobi.p2 ^ 2 = q * H₄ (τ t) :=
            sub_eq_zero.mp hR
          _ = q * (theta₄ (τ t) ^ 2) ^ 2 := by
            simp only [H₄]
            ring
      have hp4square :
          ∀ t, (z t).jacobi.p4 ^ 2 =
            q * (theta₂ (τ t) ^ 2) ^ 2 := by
        intro t
        have hC := (hamplitude t).2.2.2
        have hR := hresidual t .coefficientLinkFour
        change
          (z t).jacobi.p4 ^ 2 - (z t).unary.C = 0 at hR
        rw [hC] at hR
        calc
          (z t).jacobi.p4 ^ 2 = q * H₂ (τ t) :=
            sub_eq_zero.mp hR
          _ = q * (theta₂ (τ t) ^ 2) ^ 2 := by
            simp only [H₂]
            ring
      obtain ⟨yScale, hyScale, hy⟩ :=
        HGAS.Topology.exists_constant_complex_multiple_of_fourth_eq
          (fun t ↦ (z t).unary.Y)
          (fun t ↦ theta₃ (τ t))
          hz.unary.continuous_Y htheta₃ hYfourth
          (fun t ↦ theta₃_ne_zero (τ t)) hq
      obtain ⟨p2Scale, hp2Scale, hp2⟩ :=
        HGAS.Topology.exists_constant_complex_multiple_of_sq_eq
          (fun t ↦ (z t).jacobi.p2)
          (fun t ↦ theta₄ (τ t) ^ 2)
          hz.jacobi.continuous_p2 (htheta₄.pow 2) hp2square
          (fun t ↦ pow_ne_zero 2 (theta₄_ne_zero (τ t))) hq
      obtain ⟨p4Scale, hp4Scale, hp4⟩ :=
        HGAS.Topology.exists_constant_complex_multiple_of_sq_eq
          (fun t ↦ (z t).jacobi.p4)
          (fun t ↦ theta₂ (τ t) ^ 2)
          hz.jacobi.continuous_p4 (htheta₂.pow 2) hp4square
          (fun t ↦ pow_ne_zero 2 (theta₂_ne_zero (τ t))) hq
      exact
        ⟨{
          yScale := yScale
          p2Scale := p2Scale
          p4Scale := p4Scale
          yScale_ne_zero := hyScale
          p2Scale_ne_zero := hp2Scale
          p4Scale_ne_zero := hp4Scale
          y_eq := by
            simpa only [cuspYRoot] using hy
          p2_eq := by
            simpa only [cuspP2Root] using hp2
          p4_eq := by
            simpa only [cuspP4Root] using hp4
        }⟩
  | one =>
      have hYfourth :
          ∀ t, (z t).unary.Y ^ 4 =
            q * (theta₂ (τ t)) ^ 4 := by
        intro t
        have hJacobi :
            H₂ (τ t) + H₄ (τ t) = H₃ (τ t) := by
          simpa only [Pi.add_apply] using
            congrFun jacobi_quartic_identity (τ t)
        have hA := (hamplitude t).2.1
        have hC := (hamplitude t).2.2.2
        have hR := hresidual t .unaryJacobi
        change
          (z t).unary.Y ^ 4 -
              (z t).unary.A - (z t).unary.C = 0 at hR
        rw [hA, hC] at hR
        rw [H₂] at hJacobi
        linear_combination hR - q * hJacobi
      have hp2square :
          ∀ t, (z t).jacobi.p2 ^ 2 =
            (-q) * (theta₄ (τ t) ^ 2) ^ 2 := by
        intro t
        have hA := (hamplitude t).2.1
        have hR := hresidual t .coefficientLinkTwo
        change
          (z t).jacobi.p2 ^ 2 - (z t).unary.A = 0 at hR
        rw [hA] at hR
        calc
          (z t).jacobi.p2 ^ 2 = -(q * H₄ (τ t)) :=
            sub_eq_zero.mp hR
          _ = (-q) * (theta₄ (τ t) ^ 2) ^ 2 := by
            simp only [H₄]
            ring
      have hp4square :
          ∀ t, (z t).jacobi.p4 ^ 2 =
            q * (theta₃ (τ t) ^ 2) ^ 2 := by
        intro t
        have hC := (hamplitude t).2.2.2
        have hR := hresidual t .coefficientLinkFour
        change
          (z t).jacobi.p4 ^ 2 - (z t).unary.C = 0 at hR
        rw [hC] at hR
        calc
          (z t).jacobi.p4 ^ 2 = q * H₃ (τ t) :=
            sub_eq_zero.mp hR
          _ = q * (theta₃ (τ t) ^ 2) ^ 2 := by
            simp only [H₃]
            ring
      obtain ⟨yScale, hyScale, hy⟩ :=
        HGAS.Topology.exists_constant_complex_multiple_of_fourth_eq
          (fun t ↦ (z t).unary.Y)
          (fun t ↦ theta₂ (τ t))
          hz.unary.continuous_Y htheta₂ hYfourth
          (fun t ↦ theta₂_ne_zero (τ t)) hq
      obtain ⟨p2Scale, hp2Scale, hp2⟩ :=
        HGAS.Topology.exists_constant_complex_multiple_of_sq_eq
          (fun t ↦ (z t).jacobi.p2)
          (fun t ↦ theta₄ (τ t) ^ 2)
          hz.jacobi.continuous_p2 (htheta₄.pow 2) hp2square
          (fun t ↦ pow_ne_zero 2 (theta₄_ne_zero (τ t)))
          (neg_ne_zero.mpr hq)
      obtain ⟨p4Scale, hp4Scale, hp4⟩ :=
        HGAS.Topology.exists_constant_complex_multiple_of_sq_eq
          (fun t ↦ (z t).jacobi.p4)
          (fun t ↦ theta₃ (τ t) ^ 2)
          hz.jacobi.continuous_p4 (htheta₃.pow 2) hp4square
          (fun t ↦ pow_ne_zero 2 (theta₃_ne_zero (τ t))) hq
      exact
        ⟨{
          yScale := yScale
          p2Scale := p2Scale
          p4Scale := p4Scale
          yScale_ne_zero := hyScale
          p2Scale_ne_zero := hp2Scale
          p4Scale_ne_zero := hp4Scale
          y_eq := by
            simpa only [cuspYRoot] using hy
          p2_eq := by
            simpa only [cuspP2Root] using hp2
          p4_eq := by
            simpa only [cuspP4Root] using hp4
        }⟩

/-! ## Horizontal-line specialization -/

/-- Root-branch coherence along a literal horizontal modulus
`τ(t)=x+s t+i y`. -/
theorem exists_cuspLinkedRootBranches_horizontalLine
    {κZ κPhi : ℂ}
    (cusp : GammaTwoCuspLabel)
    (z : ℝ → LinkedJacobiState ℂ)
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z)
    (x y s : ℝ) (hy : 0 < y)
    (q : ℂ) (hq : q ≠ 0)
    (hamplitude :
      ∀ t,
        HasCuspQuarticAmplitude cusp (z t).unary
          (horizontalLine x y s hy t) q)
    (hresidual :
      ∀ t (r : LinkedJacobiResidualIndex),
        linkedJacobiResidual r (z t) = 0) :
    Nonempty
      (CuspLinkedRootBranches cusp z
        (fun t ↦ horizontalLine x y s hy t)) := by
  apply
    exists_cuspLinkedRootBranches_of_continuous
      cusp z hz (fun t ↦ horizontalLine x y s hy t)
        _ q hq hamplitude hresidual
  rw [continuous_induced_rng]
  change
    Continuous
      (fun t : ℝ ↦
        (horizontalLine x y s hy t : ℂ))
  rw [show
    (fun t : ℝ ↦ (horizontalLine x y s hy t : ℂ)) =
      fun t : ℝ ↦
        (x + s * t : ℂ) + (y : ℂ) * Complex.I by
    funext t
    apply Complex.ext <;> simp]
  fun_prop

end

end HGAS.Modular
