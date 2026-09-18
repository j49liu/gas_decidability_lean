import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Tactic

/-!
# Differential calculus for real multivariate polynomials

Mathlib provides the algebraic partial derivatives of a multivariate
polynomial, but does not currently package their evaluation as the Fréchet
derivative of the polynomial function.  This file supplies that bridge for
polynomials in finitely many real variables.

For `p : MvPolynomial (Fin n) ℝ`, the continuous linear differential at `x`
is the functional

```
v ↦ ∑ i, pderiv i p evaluated at x * v i.
```

The proof follows the algebraic induction principle for multivariate
polynomials: constants, sums, and multiplication by a variable.  The final
chain-rule lemmas are stated in both unrestricted and within-set forms so
that later ODE modules can differentiate polynomial certificates along
trajectories without reopening the polynomial induction.
-/

namespace HGAS

open scoped BigOperators

noncomputable section

open MvPolynomial

/-- The Fréchet differential predicted by the formal partial derivatives of
a real multivariate polynomial. -/
def mvPolynomialDifferential {n : ℕ}
    (p : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ i : Fin n,
    (MvPolynomial.eval x (MvPolynomial.pderiv i p)) •
      ContinuousLinearMap.proj i

/-- Evaluation of `mvPolynomialDifferential` is the familiar directional
derivative, namely the dot product of the formal gradient with `v`. -/
@[simp]
theorem mvPolynomialDifferential_apply {n : ℕ}
    (p : MvPolynomial (Fin n) ℝ) (x v : Fin n → ℝ) :
    mvPolynomialDifferential p x v =
      ∑ i : Fin n,
        MvPolynomial.eval x (MvPolynomial.pderiv i p) * v i := by
  simp [mvPolynomialDifferential]

/-- Applying the polynomial differential to a standard coordinate vector
recovers the corresponding evaluated formal partial derivative. -/
theorem mvPolynomialDifferential_piSingle_one {n : ℕ}
    (p : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ)
    (i : Fin n) :
    mvPolynomialDifferential p x (Pi.single i 1) =
      MvPolynomial.eval x (MvPolynomial.pderiv i p) := by
  classical
  rw [mvPolynomialDifferential_apply, Finset.sum_eq_single i]
  · simp
  · intro j _hj hji
    simp [hji]
  · simp

@[simp]
theorem mvPolynomialDifferential_C {n : ℕ}
    (a : ℝ) (x : Fin n → ℝ) :
    mvPolynomialDifferential (MvPolynomial.C a) x = 0 := by
  ext v
  simp

@[simp]
theorem mvPolynomialDifferential_add {n : ℕ}
    (p q : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    mvPolynomialDifferential (p + q) x =
      mvPolynomialDifferential p x + mvPolynomialDifferential q x := by
  ext v
  simp [Finset.sum_add_distrib, add_mul]

@[simp]
theorem mvPolynomialDifferential_X {n : ℕ}
    (j : Fin n) (x : Fin n → ℝ) :
    mvPolynomialDifferential (MvPolynomial.X j) x =
      ContinuousLinearMap.proj j := by
  ext v
  classical
  rw [mvPolynomialDifferential_apply, Finset.sum_eq_single j]
  · simp
  · intro i hi hij
    simp [MvPolynomial.pderiv_X_of_ne hij.symm]
  · simp

/-- Product rule for the formal differential.  Its order agrees with
Mathlib's Fréchet product rule for scalar-valued functions. -/
theorem mvPolynomialDifferential_mul {n : ℕ}
    (p q : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    mvPolynomialDifferential (p * q) x =
      MvPolynomial.eval x p • mvPolynomialDifferential q x +
        MvPolynomial.eval x q • mvPolynomialDifferential p x := by
  ext v
  classical
  simp only [mvPolynomialDifferential_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, MvPolynomial.pderiv_mul, MvPolynomial.eval_add,
    MvPolynomial.eval_mul]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  calc
    (∑ i : Fin n,
        MvPolynomial.eval x (MvPolynomial.pderiv i p) *
            MvPolynomial.eval x q * v i) +
        ∑ i : Fin n,
          MvPolynomial.eval x p *
              MvPolynomial.eval x (MvPolynomial.pderiv i q) * v i =
      MvPolynomial.eval x q *
          ∑ i : Fin n,
            MvPolynomial.eval x (MvPolynomial.pderiv i p) * v i +
        MvPolynomial.eval x p *
          ∑ i : Fin n,
            MvPolynomial.eval x (MvPolynomial.pderiv i q) * v i := by
        apply congrArg₂ (· + ·)
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = MvPolynomial.eval x p *
          ∑ i : Fin n,
            MvPolynomial.eval x (MvPolynomial.pderiv i q) * v i +
        MvPolynomial.eval x q *
          ∑ i : Fin n,
            MvPolynomial.eval x (MvPolynomial.pderiv i p) * v i := by
      ac_rfl

/-- A real multivariate polynomial evaluates to a smooth function of all
orders on its finite-dimensional coordinate space. -/
theorem contDiff_mvPolynomial_eval {n : ℕ}
    (p : MvPolynomial (Fin n) ℝ) :
    ContDiff ℝ ⊤ (fun x : Fin n → ℝ ↦ MvPolynomial.eval x p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      simpa using
        (contDiff_const : ContDiff ℝ ⊤
          (fun _ : Fin n → ℝ ↦ a))
  | add p q hp hq =>
      simpa only [MvPolynomial.eval_add] using hp.add hq
  | mul_X p j hp =>
      have hj : ContDiff ℝ ⊤ (fun x : Fin n → ℝ ↦ x j) :=
        (ContinuousLinearMap.proj j :
          (Fin n → ℝ) →L[ℝ] ℝ).contDiff
      simpa only [MvPolynomial.eval_mul, MvPolynomial.eval_X] using hp.mul hj

/-- In particular, evaluation of a real multivariate polynomial is
continuous. -/
theorem continuous_mvPolynomial_eval {n : ℕ}
    (p : MvPolynomial (Fin n) ℝ) :
    Continuous (fun x : Fin n → ℝ ↦ MvPolynomial.eval x p) :=
  (contDiff_mvPolynomial_eval p).continuous

/-- The exact Fréchet derivative of polynomial evaluation is the continuous
linear functional assembled from the evaluated formal partial derivatives. -/
theorem hasFDerivAt_mvPolynomial_eval {n : ℕ}
    (p : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    HasFDerivAt (fun y : Fin n → ℝ ↦ MvPolynomial.eval y p)
      (mvPolynomialDifferential p x) x := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      simpa using
        (hasFDerivAt_const a x :
          HasFDerivAt (fun _ : Fin n → ℝ ↦ a) 0 x)
  | add p q hp hq =>
      simpa only [MvPolynomial.eval_add, mvPolynomialDifferential_add]
        using hp.add hq
  | mul_X p j hp =>
      have hj :
          HasFDerivAt (fun y : Fin n → ℝ ↦ MvPolynomial.eval y (X j))
            (mvPolynomialDifferential (X j) x) x := by
        simpa only [MvPolynomial.eval_X, mvPolynomialDifferential_X] using
          (ContinuousLinearMap.proj j :
            (Fin n → ℝ) →L[ℝ] ℝ).hasFDerivAt
      simpa only [MvPolynomial.eval_mul, mvPolynomialDifferential_mul]
        using hp.mul hj

/-- Within-set version of the exact polynomial Fréchet derivative. -/
theorem hasFDerivWithinAt_mvPolynomial_eval {n : ℕ}
    (p : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ)
    (s : Set (Fin n → ℝ)) :
    HasFDerivWithinAt (fun y : Fin n → ℝ ↦ MvPolynomial.eval y p)
      (mvPolynomialDifferential p x) s x :=
  (hasFDerivAt_mvPolynomial_eval p x).hasFDerivWithinAt

/-- Fréchet derivative written as an exact action formula, without exposing
the bundled continuous linear map. -/
theorem fderiv_mvPolynomial_eval_apply {n : ℕ}
    (p : MvPolynomial (Fin n) ℝ) (x v : Fin n → ℝ) :
    fderiv ℝ (fun y : Fin n → ℝ ↦ MvPolynomial.eval y p) x v =
      ∑ i : Fin n,
        MvPolynomial.eval x (MvPolynomial.pderiv i p) * v i := by
  rw [(hasFDerivAt_mvPolynomial_eval p x).fderiv]
  exact mvPolynomialDifferential_apply p x v

/-- Chain rule for evaluating a multivariate polynomial along a
differentiable curve. -/
theorem HasDerivAt.mvPolynomial_eval {n : ℕ}
    {γ : ℝ → (Fin n → ℝ)} {v : Fin n → ℝ} {t : ℝ}
    (hγ : HasDerivAt γ v t) (p : MvPolynomial (Fin n) ℝ) :
    HasDerivAt (fun s ↦ MvPolynomial.eval (γ s) p)
      (∑ i : Fin n,
        MvPolynomial.eval (γ t) (MvPolynomial.pderiv i p) * v i) t := by
  simpa only [mvPolynomialDifferential_apply] using
    (hasFDerivAt_mvPolynomial_eval p (γ t)).comp_hasDerivAt t hγ

/-- Within-set chain rule for evaluating a multivariate polynomial along a
curve whose derivative is known relative to a time set. -/
theorem HasDerivWithinAt.mvPolynomial_eval {n : ℕ}
    {γ : ℝ → (Fin n → ℝ)} {v : Fin n → ℝ}
    {t : ℝ} {s : Set ℝ}
    (hγ : HasDerivWithinAt γ v s t) (p : MvPolynomial (Fin n) ℝ) :
    HasDerivWithinAt (fun u ↦ MvPolynomial.eval (γ u) p)
      (∑ i : Fin n,
        MvPolynomial.eval (γ t) (MvPolynomial.pderiv i p) * v i) s t := by
  simpa only [mvPolynomialDifferential_apply] using
    (hasFDerivAt_mvPolynomial_eval p (γ t)).comp_hasDerivWithinAt t hγ

/-! ## Rational polynomials interpreted over the reals -/

/-- Evaluation of a rational-coefficient multivariate polynomial after the
canonical coefficient embedding `ℚ → ℝ`. -/
def ratMvPolynomialEval {n : ℕ}
    (p : MvPolynomial (Fin n) ℚ) (x : Fin n → ℝ) : ℝ :=
  MvPolynomial.eval x (MvPolynomial.map (algebraMap ℚ ℝ) p)

/-- The real differential of a rational-coefficient polynomial. -/
def ratMvPolynomialDifferential {n : ℕ}
    (p : MvPolynomial (Fin n) ℚ) (x : Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] ℝ :=
  mvPolynomialDifferential (MvPolynomial.map (algebraMap ℚ ℝ) p) x

/-- Directional derivative formula for a rational polynomial interpreted
over the reals.  Algebraic partial differentiation commutes with the
coefficient embedding. -/
@[simp]
theorem ratMvPolynomialDifferential_apply {n : ℕ}
    (p : MvPolynomial (Fin n) ℚ) (x v : Fin n → ℝ) :
    ratMvPolynomialDifferential p x v =
      ∑ i : Fin n,
        MvPolynomial.eval x
          (MvPolynomial.map (algebraMap ℚ ℝ) (MvPolynomial.pderiv i p)) *
            v i := by
  simp [ratMvPolynomialDifferential, MvPolynomial.pderiv_map]

/-- A rational-coefficient polynomial defines a smooth real-valued
function. -/
theorem contDiff_ratMvPolynomialEval {n : ℕ}
    (p : MvPolynomial (Fin n) ℚ) :
    ContDiff ℝ ⊤ (ratMvPolynomialEval p) :=
  contDiff_mvPolynomial_eval (MvPolynomial.map (algebraMap ℚ ℝ) p)

/-- Exact Fréchet derivative of a rational polynomial interpreted over the
reals. -/
theorem hasFDerivAt_ratMvPolynomialEval {n : ℕ}
    (p : MvPolynomial (Fin n) ℚ) (x : Fin n → ℝ) :
    HasFDerivAt (ratMvPolynomialEval p)
      (ratMvPolynomialDifferential p x) x :=
  hasFDerivAt_mvPolynomial_eval
    (MvPolynomial.map (algebraMap ℚ ℝ) p) x

/-- Chain rule for a rational polynomial, with its formal rational partial
derivatives embedded into `ℝ` only at evaluation time. -/
theorem HasDerivAt.ratMvPolynomialEval {n : ℕ}
    {γ : ℝ → (Fin n → ℝ)} {v : Fin n → ℝ} {t : ℝ}
    (hγ : HasDerivAt γ v t) (p : MvPolynomial (Fin n) ℚ) :
    HasDerivAt (fun s ↦ ratMvPolynomialEval p (γ s))
      (∑ i : Fin n,
        MvPolynomial.eval (γ t)
          (MvPolynomial.map (algebraMap ℚ ℝ) (MvPolynomial.pderiv i p)) *
            v i) t := by
  simpa only [ratMvPolynomialDifferential_apply] using
    (hasFDerivAt_ratMvPolynomialEval p (γ t)).comp_hasDerivAt t hγ

/-- Within-set chain rule for a rational polynomial interpreted over
`ℝ`. -/
theorem HasDerivWithinAt.ratMvPolynomialEval {n : ℕ}
    {γ : ℝ → (Fin n → ℝ)} {v : Fin n → ℝ}
    {t : ℝ} {s : Set ℝ}
    (hγ : HasDerivWithinAt γ v s t)
    (p : MvPolynomial (Fin n) ℚ) :
    HasDerivWithinAt (fun u ↦ ratMvPolynomialEval p (γ u))
      (∑ i : Fin n,
        MvPolynomial.eval (γ t)
          (MvPolynomial.map (algebraMap ℚ ℝ) (MvPolynomial.pderiv i p)) *
            v i) s t := by
  simpa only [ratMvPolynomialDifferential_apply] using
    (hasFDerivAt_ratMvPolynomialEval p (γ t)).comp_hasDerivWithinAt t hγ

end

end HGAS
