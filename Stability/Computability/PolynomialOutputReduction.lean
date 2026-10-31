import Stability.Computability.PolynomialCodeTrim
import Stability.Simulation.ProjectivePolynomialComputability
import Stability.Simulation.ProjectiveStabilityCriterion

/-!
# A fixed-degree code reduction from bounded polynomial output

First remove canceled exponent groups, then homogenize with the fixed odd
parameter `2d+3`. A decoded degree bound `d` for both field and output
therefore yields the strict raw bounds needed at the equator. The target
has dimension `n+1` and degree `2d+5`, independently of all coefficients.
-/

namespace Stability.PolynomialOutputReduction

open HGAS PolynomialCodeOperations ProjectivePolynomialCode

variable {n : ℕ}

def compile (d : ℕ) (data : PolynomialFieldCode n × PolynomialCode n) :
    PolynomialFieldCode (n + 1) :=
  fieldCode (2 * d + 3) (fun i ↦ trim (data.1 i)) (trim data.2)

theorem trimField_primrec :
    Primrec (fun P : PolynomialFieldCode n ↦ fun i ↦ trim (P i)) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro i
  exact trim_primrec.comp (Primrec.fin_app.comp Primrec.id (Primrec.const i))

theorem compile_primrec (d : ℕ) :
    Primrec (compile (n := n) d) :=
  (fieldCode_primrec (2 * d + 3)).comp
    (Primrec.pair (trimField_primrec.comp Primrec.fst) (trim_primrec.comp Primrec.snd))

private theorem strict_degree_field (d : ℕ) (P : PolynomialFieldCode n)
    (hP : ∀ i, (PolynomialCode.decode (P i)).totalDegree ≤ d) :
    ∀ i t, t ∈ trim (P i) → ExponentCode.totalDegree t.1 < 2 * d + 3 := by
  intro i t ht
  have h := termsDegreeLE_trim_of_totalDegree_le (P i) (hP i) t ht
  omega

private theorem strict_degree_output (d : ℕ) (b : PolynomialCode n)
    (hb : (PolynomialCode.decode b).totalDegree ≤ d) :
    ∀ t ∈ trim b, ExponentCode.totalDegree t.1 < (2 * d + 3) - 1 := by
  intro t ht
  have h := termsDegreeLE_trim_of_totalDegree_le b hb t ht
  omega

theorem homogeneous_compile (d : ℕ) (P : PolynomialFieldCode n) (b : PolynomialCode n)
    (hP : ∀ i, (PolynomialCode.decode (P i)).totalDegree ≤ d)
    (hb : (PolynomialCode.decode b).totalDegree ≤ d) :
    PolynomialFieldCode.homogeneous (2 * d + 5) (compile d (P, b)) = true := by
  apply (PolynomialFieldCode.homogeneous_eq_true_iff _ _).mpr
  have hh := isHomogeneous_fieldCode (2 * d + 3) (by omega)
    (fun i ↦ trim (P i)) (trim b)
    (fun i t ht ↦ (strict_degree_field d P hP i t ht).le)
    (fun t ht ↦ (strict_degree_output d b hb t ht).le)
  exact hh

theorem hlsQ_compile_iff (d : ℕ) (P : PolynomialFieldCode n) (b : PolynomialCode n)
    (hP : ∀ i, (PolynomialCode.decode (P i)).totalDegree ≤ d)
    (hb : (PolynomialCode.decode b).totalDegree ≤ d) :
    HGAS.HLSQ (n + 1) (2 * d + 5) (compile d (P, b)) ↔
      HasBoundedFiniteOutput (PolynomialFieldCode.realize P)
        (fun x ↦ MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x (PolynomialCode.decode b)) := by
  rw [HGAS.hlsQ_iff_of_homogeneous _ (homogeneous_compile d P b hP hb)]
  have h := lyapunovStable_fieldCode_iff_boundedFiniteOutput (2 * d + 3)
    (by exact ⟨d + 1, by omega⟩) (fun i ↦ trim (P i)) (trim b)
    (strict_degree_field d P hP) (strict_degree_output d b hb)
  have hrealize : PolynomialFieldCode.realize (fun i ↦ trim (P i)) =
      PolynomialFieldCode.realize P := by
    funext x i
    simp only [PolynomialFieldCode.realize_apply, decode_trim]
  simpa only [hrealize, decode_trim] using h

end Stability.PolynomialOutputReduction
