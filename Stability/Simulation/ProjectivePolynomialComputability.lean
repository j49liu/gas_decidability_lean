import Stability.Simulation.ProjectivePolynomialCode

/-!
# Effectivity of the sparse projective construction

For fixed dimension and homogenizing degree, the construction uses only
primitive-recursive sparse polynomial operations. No semantic polynomial
encoder or real-number operation appears in the compiled code.
-/

namespace Stability.ProjectivePolynomialCode

open HGAS

variable {n : ℕ}

theorem augmentedFieldCode_at_primrec (ell : ℕ) (i : Fin (n + 1)) :
    Primrec (fun P : PolynomialFieldCode n ↦ augmentedFieldCode ell P i) := by
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · exact (Primrec.const PolynomialCode.zero).of_eq (fun P ↦ by simp)
  · exact ((homogenize_primrec ell).comp
      (Primrec.fin_app.comp Primrec.id (Primrec.const j))).of_eq (fun P ↦ by simp)

theorem augmentedFieldCode_primrec (ell : ℕ) :
    Primrec (augmentedFieldCode ell : PolynomialFieldCode n → PolynomialFieldCode (n + 1)) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  exact augmentedFieldCode_at_primrec ell

theorem radialRateCode_primrec (ell : ℕ) :
    Primrec (radialRateCode ell : PolynomialCode n → PolynomialCode (n + 1)) :=
  homogenize_primrec (ell - 1)

theorem radialDotCode_primrec (ell : ℕ) :
    Primrec (radialDotCode ell : PolynomialFieldCode n → PolynomialCode (n + 1)) := by
  apply PolynomialCode.sumCodes_primrec.comp
  apply Primrec.list_ofFn
  intro i
  exact PolynomialCode.mul_primrec.comp (Primrec.const (PolynomialCode.varCode i))
    (augmentedFieldCode_at_primrec ell i)

theorem fieldCode_at_primrec (ell : ℕ) (i : Fin (n + 1)) :
    Primrec (fun data : PolynomialFieldCode n × PolynomialCode n ↦
      fieldCode ell data.1 data.2 i) := by
  exact PolynomialCode.add_primrec.comp
    (PolynomialCode.sub_primrec.comp
      (PolynomialCode.mul_primrec.comp (Primrec.const (normSqCode (n + 1)))
        ((augmentedFieldCode_at_primrec ell i).comp Primrec.fst))
      (PolynomialCode.mul_primrec.comp ((radialDotCode_primrec ell).comp Primrec.fst)
        (Primrec.const (PolynomialCode.varCode i))))
    (PolynomialCode.mul_primrec.comp
      (PolynomialCode.mul_primrec.comp (Primrec.const (normSqCode (n + 1)))
        ((radialRateCode_primrec ell).comp Primrec.snd))
      (Primrec.const (PolynomialCode.varCode i)))

/-- The full raw projective field compiler is primitive recursive in the
source field and output codes, for fixed dimension and degree. -/
theorem fieldCode_primrec (ell : ℕ) :
    Primrec (fun data : PolynomialFieldCode n × PolynomialCode n ↦
      fieldCode ell data.1 data.2) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  exact fieldCode_at_primrec ell

theorem fieldCode_computable (ell : ℕ) :
    Computable (fun data : PolynomialFieldCode n × PolynomialCode n ↦
      fieldCode ell data.1 data.2) :=
  (fieldCode_primrec ell).to_comp

end Stability.ProjectivePolynomialCode
