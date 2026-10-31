import Stability.Computability.RawPolynomialStatistics
import HGAS.Wrapper.TwoSheetPolynomialCode

/-!
# Removing canceled exponent groups from sparse codes

The filter removes every term whose exponent has zero collected
coefficient. It need not combine the remaining duplicate terms: every
retained exponent already lies in the decoded support. Consequently any
semantic degree bound becomes a raw term-degree bound, as required by
the executable projective homogenizer.
-/

namespace Stability.PolynomialCodeOperations

open HGAS

variable {n : ℕ}

/-- Delete canceled exponent groups, retaining the order of other terms. -/
def trim (p : PolynomialCode n) : PolynomialCode n :=
  p.filter fun t ↦ !(RationalCode.equal (p.coefficient t.1) RationalCode.zero)

private theorem coeff_decode_filter (b : ExponentCode n → Bool)
    (p : PolynomialCode n) (e : ExponentCode n) :
    MvPolynomial.coeff (ExponentCode.decode e)
        (PolynomialCode.decode (p.filter fun t ↦ b t.1)) =
      if b e then MvPolynomial.coeff (ExponentCode.decode e) (PolynomialCode.decode p)
      else 0 := by
  induction p with
  | nil => simp
  | cons t p ih =>
    by_cases he : t.1 = e
    · simp only [List.filter_cons, PolynomialCode.decode_cons]
      rw [he]
      cases hb : b e <;> simp [hb, PolynomialCode.decode_cons,
        PolynomialCode.decodeTerm, he, ih]
    · have hdecode := ExponentCode.decode_injective.ne he
      cases hb : b t.1 <;> simp [hb, PolynomialCode.decode_cons,
        PolynomialCode.decodeTerm, hdecode, ih]

/-- Filtering an entire zero-coefficient group preserves the polynomial. -/
@[simp]
theorem decode_trim (p : PolynomialCode n) :
    PolynomialCode.decode (trim p) = PolynomialCode.decode p := by
  apply MvPolynomial.ext
  intro e
  rw [← ExponentCode.decode_encode e]
  let a := ExponentCode.encode e
  have ha : ExponentCode.decode a = e := ExponentCode.decode_encode e
  change (PolynomialCode.decode (trim p)).coeff (ExponentCode.decode a) = _
  rw [trim, coeff_decode_filter
    (fun b ↦ !(RationalCode.equal (p.coefficient b) RationalCode.zero)) p a]
  by_cases hz : RationalCode.equal (p.coefficient a) RationalCode.zero = true
  · have hzero : (PolynomialCode.decode p).coeff (ExponentCode.decode a) = 0 := by
      simpa only [RationalCode.equal_eq_true_iff, PolynomialCode.decode_coefficient,
        RationalCode.decode_zero] using hz
    rw [ha] at hzero
    simp [hz, hzero]
  · simp [hz, ha]

/-- Every retained raw term has degree at most the decoded total degree. -/
theorem termsDegreeLE_trim (p : PolynomialCode n) :
    PolynomialCode.TermsDegreeLE (PolynomialCode.decode p).totalDegree (trim p) := by
  intro t ht
  have hn := (List.mem_filter.mp ht).2
  have hn' : RationalCode.equal (p.coefficient t.1) RationalCode.zero ≠ true := by
    intro hz
    simp [hz] at hn
  have hcoeff : (PolynomialCode.decode p).coeff (ExponentCode.decode t.1) ≠ 0 := by
    simpa only [ne_eq, RationalCode.equal_eq_true_iff,
      PolynomialCode.decode_coefficient, RationalCode.decode_zero] using hn'
  rw [← ExponentCode.degree_decode]
  simpa [Finsupp.degree] using
    MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hcoeff)

theorem termsDegreeLE_trim_of_totalDegree_le (p : PolynomialCode n) {d : ℕ}
    (hp : (PolynomialCode.decode p).totalDegree ≤ d) :
    PolynomialCode.TermsDegreeLE d (trim p) :=
  fun t ht ↦ (termsDegreeLE_trim p t ht).trans hp

/-- The support-aware filter uses only exact rational comparisons and
the existing primitive-recursive coefficient accumulator. -/
theorem trim_primrec : Primrec (trim : PolynomialCode n → PolynomialCode n) := by
  have hr : PrimrecRel (fun (t : ExponentCode n × RationalCode) (p : PolynomialCode n) ↦
      RationalCode.equal (p.coefficient t.1) RationalCode.zero ≠ true) :=
    (Primrec.eq.comp (RationalCode.equal_primrec.comp
      (PolynomialCode.coefficient_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
      (Primrec.const RationalCode.zero)) (Primrec.const true)).not
  exact ((PrimrecRel.listFilter hr).comp Primrec.id Primrec.id).of_eq fun p ↦ by
    apply List.filter_congr
    intro t _
    dsimp only [id]
    simp only [decide_not, Bool.decide_eq_true]

end Stability.PolynomialCodeOperations
