import HGAS.Analysis.MvPolynomialCalculus
import HGAS.Dynamics.LyapunovDirect
import HGAS.Lyapunov.RationalCertificateAlgebra
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic

/-!
# Analytic soundness of rational Lyapunov certificates

The algebraic certificate module defines

```
V(x) = p(x) / ρ(x)^r,
q(x) = -ρ(x) (∇p(x) · F(x)) + 2r p(x) (x · F(x)),
ρ(x) = ∑ i, xᵢ².
```

This file proves the missing analytic bridge.  Away from the origin,

```
d/dt V(x(t)) = -q(x(t)) / ρ(x(t))^(r+1)
```

along solutions of `x' = F(x)`.  The sign is worth emphasizing:
`rationalLyapunovNumerator` represents `-V̇`, not `V̇`.

The final theorem is a soundness theorem, not a converse theorem.  It turns
explicit continuity, comparison, and decay hypotheses for this rational
function into global asymptotic stability.  No rational converse Lyapunov
result is asserted or imported.
-/

namespace HGAS

open Set MvPolynomial
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-- The rational Lyapunov candidate `p / ρ^r`, interpreted as a real-valued
function.  Lean's field convention assigns a value also at `ρ = 0`; all
quotient differentiation theorems below explicitly assume a nonzero state. -/
def rationalLyapunovValue
    (p : MvPolynomial (Fin n) ℚ) (r : ℕ) (x : Fin n → ℝ) : ℝ :=
  ratMvPolynomialEval p x / normSq x ^ r

/-- The nonnegative quantity intended to equal `-V̇`: evaluation of the
polynomial numerator divided by `ρ^(r+1)`. -/
def rationalLyapunovDecay
    (F : PolynomialField n) (p : MvPolynomial (Fin n) ℚ)
    (r : ℕ) (x : Fin n → ℝ) : ℝ :=
  ratMvPolynomialEval (rationalLyapunovNumerator F p r) x /
    normSq x ^ (r + 1)

/-- The rational-polynomial evaluation wrapper is definitionally the usual
`eval₂Hom` after rewriting through `MvPolynomial.eval_map`. -/
theorem ratMvPolynomialEval_eq_eval₂Hom
    (p : MvPolynomial (Fin n) ℚ) (x : Fin n → ℝ) :
    ratMvPolynomialEval p x =
      eval₂Hom (algebraMap ℚ ℝ) x p := by
  simp [ratMvPolynomialEval]

/-- Real evaluation of `rhoPolynomial` is the algebraic squared Euclidean
norm. -/
@[simp]
theorem ratMvPolynomialEval_rhoPolynomial (x : Fin n → ℝ) :
    ratMvPolynomialEval (rhoPolynomial (n := n)) x = normSq x := by
  rw [ratMvPolynomialEval_eq_eval₂Hom]
  exact eval₂Hom_rhoPolynomial x

/-- Real evaluation of the formal numerator, in the form used by the
quotient derivative calculation. -/
theorem ratMvPolynomialEval_rationalLyapunovNumerator
    (F : PolynomialField n) (p : MvPolynomial (Fin n) ℚ)
    (r : ℕ) (x : Fin n → ℝ) :
    ratMvPolynomialEval (rationalLyapunovNumerator F p r) x =
      -normSq x *
          (∑ i, eval₂Hom (algebraMap ℚ ℝ) x (pderiv i p) *
            evalPolynomialField F x i) +
        (2 * (r : ℝ)) * ratMvPolynomialEval p x *
          dot x (evalPolynomialField F x) := by
  rw [ratMvPolynomialEval_eq_eval₂Hom,
    eval₂Hom_rationalLyapunovNumerator]
  rw [ratMvPolynomialEval_eq_eval₂Hom]

/-- A nonzero real coordinate vector has strictly positive algebraic squared
Euclidean norm. -/
theorem normSq_pos_of_ne_zero
    {x : Fin n → ℝ} (hx : x ≠ 0) :
    0 < normSq x := by
  have hexists : ∃ i : Fin n, x i ≠ 0 := by
    by_contra h
    apply hx
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hexists
  simp only [normSq, dot]
  exact Finset.sum_pos' (fun j _ ↦ mul_self_nonneg (x j))
    ⟨i, by simp [hi]⟩

/-- Chain rule for the algebraic squared Euclidean norm. -/
theorem hasDerivAt_normSq
    {γ : ℝ → (Fin n → ℝ)} {v : Fin n → ℝ} {t : ℝ}
    (hγ : HasDerivAt γ v t) :
    HasDerivAt (fun s ↦ normSq (γ s))
      (2 * dot (γ t) v) t := by
  have hsum :
      HasDerivAt
        (fun s ↦ ∑ i : Fin n, γ s i * γ s i)
        (∑ i : Fin n, (v i * γ t i + γ t i * v i)) t := by
    apply HasDerivAt.fun_sum
    intro i hi
    exact (hasDerivAt_pi.mp hγ i).mul (hasDerivAt_pi.mp hγ i)
  convert hsum using 1
  simp only [dot, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Scalar algebra behind the quotient rule for `P / ρ^r`. -/
private theorem quotient_pow_derivative_identity
    {ρ P A B : ℝ} (hρ : ρ ≠ 0) (r : ℕ) :
    (A * ρ ^ r - P * ((r : ℝ) * ρ ^ (r - 1) * B)) /
        (ρ ^ r) ^ 2 =
      (ρ * A - (r : ℝ) * P * B) / ρ ^ (r + 1) := by
  cases r with
  | zero =>
      simp [hρ]
  | succ k =>
      simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
      field_simp [pow_succ, hρ]
      ring

/-- Derivative of `p(γ(t))/ρ(γ(t))^r` along an arbitrary differentiable
curve, at a time when the curve is away from the origin.

The displayed numerator is the ordinary quotient-rule numerator before
specializing the velocity to a polynomial vector field. -/
theorem hasDerivAt_rationalLyapunovValue
    {γ : ℝ → (Fin n → ℝ)} {v : Fin n → ℝ} {t : ℝ}
    (hγ : HasDerivAt γ v t)
    (p : MvPolynomial (Fin n) ℚ) (r : ℕ)
    (hx : γ t ≠ 0) :
    HasDerivAt (fun s ↦ rationalLyapunovValue p r (γ s))
      ((normSq (γ t) *
            (∑ i : Fin n,
              eval₂Hom (algebraMap ℚ ℝ) (γ t) (pderiv i p) * v i) -
          (2 * (r : ℝ)) * ratMvPolynomialEval p (γ t) *
            dot (γ t) v) /
        normSq (γ t) ^ (r + 1)) t := by
  have hp := HasDerivAt.ratMvPolynomialEval hγ p
  have hρ := hasDerivAt_normSq hγ
  have hρpos : 0 < normSq (γ t) :=
    normSq_pos_of_ne_zero hx
  have hden := hρ.pow r
  have hquot :
      HasDerivAt (fun s ↦ rationalLyapunovValue p r (γ s))
        (((∑ i : Fin n,
              MvPolynomial.eval (γ t)
                (MvPolynomial.map (algebraMap ℚ ℝ) (pderiv i p)) * v i) *
              normSq (γ t) ^ r -
            ratMvPolynomialEval p (γ t) *
              ((r : ℝ) * normSq (γ t) ^ (r - 1) *
                (2 * dot (γ t) v))) /
          (normSq (γ t) ^ r) ^ 2) t := by
    simpa only [rationalLyapunovValue, Pi.pow_apply] using
      hp.fun_div hden (pow_ne_zero r hρpos.ne')
  apply hquot.congr_deriv
  rw [quotient_pow_derivative_identity hρpos.ne' r]
  simp only [MvPolynomial.eval_map, MvPolynomial.coe_eval₂Hom]
  ring

/-- Along the real vector field denoted by `F`, the formal numerator has
exactly the advertised sign: `V̇ = -q/ρ^(r+1)`. -/
theorem hasDerivAt_rationalLyapunovValue_along_field
    {γ : ℝ → (Fin n → ℝ)} {t : ℝ}
    (F : PolynomialField n) (p : MvPolynomial (Fin n) ℚ) (r : ℕ)
    (hγ : HasDerivAt γ (evalPolynomialField F (γ t)) t)
    (hx : γ t ≠ 0) :
    HasDerivAt (fun s ↦ rationalLyapunovValue p r (γ s))
      (-rationalLyapunovDecay F p r (γ t)) t := by
  have hquot := hasDerivAt_rationalLyapunovValue hγ p r hx
  convert hquot using 1
  rw [rationalLyapunovDecay,
    ratMvPolynomialEval_rationalLyapunovNumerator]
  ring

/-- Positive evaluation of the polynomial numerator implies nonnegativity
of the analytic decay quotient. -/
theorem rationalLyapunovDecay_nonneg
    (F : PolynomialField n) (p : MvPolynomial (Fin n) ℚ) (r : ℕ)
    (x : Fin n → ℝ)
    (hq : 0 ≤ ratMvPolynomialEval
      (rationalLyapunovNumerator F p r) x) :
    0 ≤ rationalLyapunovDecay F p r x := by
  exact div_nonneg hq (pow_nonneg (normSq_nonneg x) _)

@[simp]
theorem rationalLyapunovDecay_zero
    (F : PolynomialField n) (p : MvPolynomial (Fin n) ℚ) (r : ℕ) :
    rationalLyapunovDecay F p r 0 = 0 := by
  simp [rationalLyapunovDecay]

/-! ## A reusable direct-method soundness theorem -/

/-- A continuous Lyapunov function with quadratic comparison bounds and a
quantified positive decay rate proves global asymptotic stability.

The hypothesis `hdecay_level` is the precise uniformity needed by the
finite-entry argument: on every positive Lyapunov superlevel, the decay is
bounded below by some positive constant.  Compactness and homogeneity are
typical ways to establish this hypothesis, but they are deliberately kept
outside this analytic theorem. -/
theorem globallyAsymptoticallyStable_of_lyapunov_decay
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → E) (xEq : E) (V decay : E → ℝ)
    (hequilibrium : F xEq = 0)
    (hcomplete : ForwardComplete F)
    {b c : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hVcontinuous : Continuous V)
    (hstableLower : ∀ x : E, dist x xEq ^ 2 ≤ b * V x)
    (hupper : ∀ x : E, V x ≤ b * dist x xEq ^ 2)
    (hattractLower : ∀ x : E, c * dist x xEq ^ 2 ≤ V x)
    (hdecay_nonneg : ∀ x : E, 0 ≤ decay x)
    (hdecay_level : ∀ η : ℝ, 0 < η →
      ∃ d : ℝ, 0 < d ∧ ∀ x : E, η ≤ V x → d ≤ decay x)
    (hderiv : ∀ {x₀ : E} {γ : ℝ → E} {t : ℝ},
      IsForwardTrajectory F γ x₀ → 0 < t →
        HasDerivAt (fun s ↦ V (γ s)) (-decay (γ t)) t) :
    GloballyAsymptoticallyStable F xEq := by
  have hcontinuousAlong :
      ∀ {x₀ : E} {γ : ℝ → E}, IsForwardTrajectory F γ x₀ →
        ContinuousOn (fun t ↦ V (γ t)) (Ici 0) := by
    intro x₀ γ hγ
    have hγcontinuous : ContinuousOn γ (Ici 0) :=
      fun t ht ↦ (hγ.2 t ht).continuousWithinAt
    exact hVcontinuous.comp_continuousOn hγcontinuous
  have hantitone :
      ∀ {x₀ : E} {γ : ℝ → E}, IsForwardTrajectory F γ x₀ →
        AntitoneOn (fun t ↦ V (γ t)) (Ici 0) := by
    intro x₀ γ hγ
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (hcontinuousAlong hγ)
    · intro t ht
      have htpos : 0 < t := by
        simpa only [interior_Ici, mem_Ioi] using ht
      exact (hderiv hγ htpos).differentiableAt.differentiableWithinAt
    · intro t ht
      have htpos : 0 < t := by
        simpa only [interior_Ici, mem_Ioi] using ht
      rw [(hderiv hγ htpos).deriv]
      exact neg_nonpos.mpr (hdecay_nonneg (γ t))
  have hVnonneg : ∀ x : E, 0 ≤ V x := by
    intro x
    exact le_trans
      (mul_nonneg hc.le (sq_nonneg (dist x xEq)))
      (hattractLower x)
  have heventually :
      ∀ {x₀ : E} {γ : ℝ → E}, IsForwardTrajectory F γ x₀ →
        ∀ η : ℝ, 0 < η →
          ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → V (γ t) < η := by
    intro x₀ γ hγ η hη
    obtain ⟨d, hd, hdlevel⟩ := hdecay_level η hη
    apply eventually_lt_of_antitoneOn_of_hasDerivAt_le
      (h := fun t ↦ V (γ t)) (d := d)
    · exact hcontinuousAlong hγ
    · exact hantitone hγ
    · intro t ht
      exact hVnonneg (γ t)
    · exact hd
    · intro t ht hlevel
      refine ⟨-decay (γ t), hderiv hγ ht, ?_⟩
      exact neg_le_neg (hdlevel (γ t) hlevel)
  exact
    { equilibrium := hequilibrium
      forwardComplete := hcomplete
      stable := lyapunovStable_of_quadratic_bounds
        F xEq V hb hstableLower hupper hantitone
      attractive :=
        globallyAttractive_of_lower_quadratic_of_eventually_lt
          F xEq V hc hattractLower heventually }

/-! ## Soundness of the rational polynomial certificate -/

/-- Explicit soundness theorem for the rational certificate
`V = p / ρ^r`.

The assumptions fall into four transparent groups:

* equilibrium and forward completeness of the polynomial vector field;
* continuity of the quotient at the origin and quadratic comparison bounds;
* nonnegativity of the polynomial numerator;
* a positive lower bound for the numerator after multiplication by the
  denominator on every positive `V`-superlevel.

The additional `hzeroDerivative` hypothesis isolates the only point not
covered by quotient differentiation.  It says that the extended quotient
has derivative zero along a solution when that solution is at the origin.
For a concrete homogeneous certificate this can be discharged from the
extension's quadratic behavior together with the equilibrium dynamics; no
converse Lyapunov theorem is used here. -/
theorem rationalCertificate_gas
    (F : PolynomialField n) (p : MvPolynomial (Fin n) ℚ) (r : ℕ)
    (hequilibrium :
      (evalPolynomialField F : (Fin n → ℝ) → (Fin n → ℝ)) 0 = 0)
    (hcomplete :
      ForwardComplete
        (evalPolynomialField F : (Fin n → ℝ) → (Fin n → ℝ)))
    {b c : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hVcontinuous : Continuous (rationalLyapunovValue p r))
    (hstableLower : ∀ x : Fin n → ℝ,
      dist x 0 ^ 2 ≤ b * rationalLyapunovValue p r x)
    (hupper : ∀ x : Fin n → ℝ,
      rationalLyapunovValue p r x ≤ b * dist x 0 ^ 2)
    (hattractLower : ∀ x : Fin n → ℝ,
      c * dist x 0 ^ 2 ≤ rationalLyapunovValue p r x)
    (hnumerator_nonneg : ∀ x : Fin n → ℝ,
      0 ≤ ratMvPolynomialEval
        (rationalLyapunovNumerator F p r) x)
    (hnumerator_level : ∀ η : ℝ, 0 < η →
      ∃ d : ℝ, 0 < d ∧ ∀ x : Fin n → ℝ,
        η ≤ rationalLyapunovValue p r x →
          d * normSq x ^ (r + 1) ≤
            ratMvPolynomialEval
              (rationalLyapunovNumerator F p r) x)
    (hzeroDerivative :
      ∀ {x₀ : Fin n → ℝ} {γ : ℝ → (Fin n → ℝ)} {t : ℝ},
        IsForwardTrajectory
          (evalPolynomialField F : (Fin n → ℝ) → (Fin n → ℝ))
          γ x₀ →
        0 < t → γ t = 0 →
        HasDerivAt
          (fun s ↦ rationalLyapunovValue p r (γ s)) 0 t) :
    GloballyAsymptoticallyStable
      (evalPolynomialField F : (Fin n → ℝ) → (Fin n → ℝ)) 0 := by
  apply globallyAsymptoticallyStable_of_lyapunov_decay
    (evalPolynomialField F : (Fin n → ℝ) → (Fin n → ℝ))
    0 (rationalLyapunovValue p r) (rationalLyapunovDecay F p r)
    hequilibrium hcomplete hb hc hVcontinuous hstableLower hupper
    hattractLower
  · intro x
    exact rationalLyapunovDecay_nonneg F p r x
      (hnumerator_nonneg x)
  · intro η hη
    obtain ⟨d, hd, hdlevel⟩ := hnumerator_level η hη
    refine ⟨d, hd, ?_⟩
    intro x hVlevel
    have hx : x ≠ 0 := by
      intro hx
      subst x
      have hVzero : rationalLyapunovValue p r 0 ≤ 0 := by
        simpa using hupper 0
      linarith
    have hdenpos : 0 < normSq x ^ (r + 1) :=
      pow_pos (normSq_pos_of_ne_zero hx) _
    exact (le_div_iff₀ hdenpos).mpr (hdlevel x hVlevel)
  · intro x₀ γ t hγ ht
    by_cases hx : γ t = 0
    · have hz := hzeroDerivative hγ ht hx
      simpa [hx] using hz
    · have hγt :
          HasDerivAt γ (evalPolynomialField F (γ t)) t :=
        (hγ.2 t ht.le).hasDerivAt (Ici_mem_nhds ht)
      exact hasDerivAt_rationalLyapunovValue_along_field
        F p r hγt hx

end

end HGAS
