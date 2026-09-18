import HGAS.Analysis.MvPolynomialCalculus
import HGAS.Dynamics.LinearConjugacyRegularity
import HGAS.Lyapunov.EuclideanAngularConverse
import HGAS.Lyapunov.EuclideanSphereC1PolynomialApproximation
import HGAS.Lyapunov.GridRationalCertificateCompleteness
import HGAS.Lyapunov.HomogeneousConverseC1
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# The unconditional rational homogeneous converse

This file closes the analytic completeness argument for the exact
rational Lyapunov-certificate search.

Let `F` be a rational polynomial vector field, homogeneous of odd positive
degree `d`, and suppose that the origin of its real realization is globally
asymptotically stable.  The proof is constructive at the level needed for
semidecidability:

1. polynomial evaluation is `C∞` and has the expected scaling law;
2. the angular-flow construction gives a strict degree-two homogeneous
   `C¹` Lyapunov function;
3. antipodal averaging makes that Lyapunov function even;
4. multivariate Bernstein polynomials approximate both its value and first
   derivatives on the Euclidean unit sphere;
5. homogenization and rational coefficient perturbation produce a finite
   exact-grid certificate.

The final theorem says that, for every fixed dimension and every fixed odd
degree, rational homogeneous GAS is recursively enumerable.  No analytic
converse theorem remains as a hypothesis.
-/

namespace HGAS

open _root_.MvPolynomial

noncomputable section

variable {n d : ℕ}

/-- Evaluation of a real polynomial vector field is smooth of every
finite order. -/
theorem contDiff_realPolynomialFieldEval
    (F : RealPolynomialField n) :
    ContDiff ℝ ⊤ (realPolynomialFieldEval F) := by
  rw [contDiff_pi]
  intro i
  exact contDiff_mvPolynomial_eval (F i)

/-- The real realization of a rational homogeneous polynomial field has
the semantic scaling law used by the angular converse theorem. -/
theorem scalesAsDegree_realPolynomialFieldEval_of_rational
    (F : PolynomialField n)
    (hF : IsHomogeneousOfDegree d F) :
    ScalesAsDegree ℝ d
      (realPolynomialFieldEval
        (realPolynomialFieldOfRational F)) := by
  intro c x
  rw [realPolynomialFieldEval_realPolynomialFieldOfRational,
    realPolynomialFieldEval_realPolynomialFieldOfRational]
  exact evalPolynomialField_smul F hF c x

/-- A GAS rational polynomial field of odd homogeneous degree has the real
rational Lyapunov witness required by the exact finite checker. -/
theorem realRationalLyapunovWitness_of_GAS_oddDegree
    (F : PolynomialField n)
    (hF : IsHomogeneousOfDegree d F)
    (hd : Odd d)
    (hgas :
      GloballyAsymptoticallyStable
        (realPolynomialFieldEval
          (realPolynomialFieldOfRational F)) 0) :
    Nonempty (RealRationalLyapunovWitness F) := by
  have hdpos : 0 < d := hd.pos
  have hdegree : d - 1 + 1 = d :=
    Nat.sub_add_cancel hdpos
  have hscale :
      ScalesAsDegree ℝ (d - 1 + 1)
        (realPolynomialFieldEval
          (realPolynomialFieldOfRational F)) := by
    simpa only [hdegree] using
      scalesAsDegree_realPolynomialFieldEval_of_rational F hF
  have hsmooth :
      ContDiff ℝ 2
        (realPolynomialFieldEval
          (realPolynomialFieldOfRational F)) :=
    (contDiff_realPolynomialFieldEval
      (realPolynomialFieldOfRational F)).of_le le_top
  let e :
      (Fin n → ℝ) ≃L[ℝ]
        EuclideanSpace ℝ (Fin n) :=
    (EuclideanSpace.equiv (Fin n) ℝ).symm
  have hgasEuclidean :
      GloballyAsymptoticallyStable
        (conjugateField e
          (realPolynomialFieldEval
            (realPolynomialFieldOfRational F))) 0 :=
    hgas.conjugateField e
  have hscaleEuclidean :
      ScalesAsDegree ℝ (d - 1 + 1)
        (conjugateField e
          (realPolynomialFieldEval
            (realPolynomialFieldOfRational F))) :=
    scalesAsDegree_conjugateField e hscale
  have hsmoothEuclidean :
      ContDiff ℝ 2
        (conjugateField e
          (realPolynomialFieldEval
            (realPolynomialFieldOfRational F))) :=
    ContDiff.conjugateField e hsmooth
  let LEuclidean :
      StrictHomogeneousC1Lyapunov
        (conjugateField e
          (realPolynomialFieldEval
            (realPolynomialFieldOfRational F))) 2 :=
    hgasEuclidean.strictHomogeneousC1Lyapunov
      hscaleEuclidean hsmoothEuclidean
  let L :
      StrictHomogeneousC1Lyapunov
        (realPolynomialFieldEval
          (realPolynomialFieldOfRational F)) 2 :=
    LEuclidean.pullback_conjugateField e
  let hodd :=
    realPolynomialFieldEval_neg_of_odd F hF hd
  apply
    realRationalLyapunovWitness_of_oddDegree_C1_approximation
      F hF hd L
  exact
    HGAS.ContDiff.hasC1MvPolynomialApproximationOn_euclideanUnitSphere
      (L.evenized hodd).V
      (L.evenized hodd).contDiff

/-- Odd degree discharges the analytic hypothesis in
`HasRealRationalHomogeneousConverse`. -/
theorem hasRealRationalHomogeneousConverse_of_odd
    (hd : Odd d) :
    HasRealRationalHomogeneousConverse n d := by
  intro F hvalid hgas
  have hF :
      IsHomogeneousOfDegree d
        (PolynomialFieldCode.decode F) :=
    (PolynomialFieldCode.homogeneous_eq_true_iff d F).mp hvalid
  have hrealize :
      realPolynomialFieldEval
          (realPolynomialFieldOfRational
            (PolynomialFieldCode.decode F)) =
        PolynomialFieldCode.realize F := by
    funext x
    exact
      realPolynomialFieldEval_realPolynomialFieldOfRational
        (PolynomialFieldCode.decode F) x
  apply
    realRationalLyapunovWitness_of_GAS_oddDegree
      (PolynomialFieldCode.decode F) hF hd
  rw [hrealize]
  exact hgas

/-- For every fixed dimension and fixed odd degree, the exact rational
homogeneous GAS language is recursively enumerable. -/
theorem hgasQ_re_of_oddDegree
    (n d : ℕ) (hd : Odd d) :
    REPred (HGASQ n d) :=
  hgasQ_re_of_realRationalHomogeneousConverse
    n d hd.pos
    (hasRealRationalHomogeneousConverse_of_odd hd)

end

end HGAS
