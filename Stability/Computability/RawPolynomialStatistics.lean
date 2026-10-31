import Stability.Computability.RawGridComputability
import Stability.Simulation.PolynomialEnvelope

/-!
# Exact effective statistics of decoded sparse polynomials

The coefficient mass reuses the existing collected-coefficient algorithm.
The degree is the maximum degree of a syntactic exponent whose collected
coefficient is nonzero. Thus repeated terms, cancellation, and the zero
polynomial agree with the actual `MvPolynomial` statistics used by the
monitor's majorants and defect weights.
-/

namespace Stability

open HGAS

namespace RawPolynomialCode

/-- Decoded degree, computed without a semantic support enumeration. -/
def totalDegree (p : RawPolynomialCode) : ℕ :=
  ((p.map Prod.fst).map fun e ↦
    if RationalCode.equal (coefficient e p) RationalCode.zero then 0 else e.sum).foldr max 0

private theorem totalDegree_ofFixed_formula {n : ℕ} (p : PolynomialCode n) :
    totalDegree (ofFixed p) =
      (p.exponents.map fun e ↦
        if RationalCode.equal (p.coefficient e) RationalCode.zero then 0
        else ExponentCode.totalDegree e).foldr max 0 := by
  unfold totalDegree
  rw [show (ofFixed p).map Prod.fst = p.exponents.map RawExponentCode.ofFixed by
    simp [ofFixed, PolynomialCode.exponents, List.map_map]]
  simp only [List.map_map, Function.comp_def, coefficient_ofFixed]
  rfl

private theorem foldMax_le (l : List ℕ) (b : ℕ) (h : ∀ a ∈ l, a ≤ b) :
    l.foldr max 0 ≤ b := by
  induction l with
  | nil => simp
  | cons a l ih =>
    exact max_le (h a (by simp)) (ih (fun c hc ↦ h c (List.mem_cons_of_mem _ hc)))

private theorem le_foldMax (l : List ℕ) {a : ℕ} (ha : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact le_max_left _ _
    · exact (ih ha).trans (le_max_right _ _)

private theorem encode_mem_exponents_of_mem_support {n : ℕ} (p : PolynomialCode n)
    {e : Fin n →₀ ℕ} (he : e ∈ (PolynomialCode.decode p).support) :
    ExponentCode.encode e ∈ p.exponents := by
  by_contra hnot
  have hzero := PolynomialCode.coefficient_eq_zero_of_not_mem (ExponentCode.encode e) p hnot
  have hdecode := PolynomialCode.decode_coefficient (ExponentCode.encode e) p
  rw [hzero, RationalCode.decode_zero, ExponentCode.decode_encode] at hdecode
  exact (MvPolynomial.mem_support_iff.mp he) hdecode.symm

/-- The executable maximum is the actual decoded polynomial degree. -/
theorem totalDegree_ofFixed {n : ℕ} (p : PolynomialCode n) :
    totalDegree (ofFixed p) = (PolynomialCode.decode p).totalDegree := by
  rw [totalDegree_ofFixed_formula]
  apply le_antisymm
  · apply foldMax_le
    intro a ha
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp ha
    by_cases hz : RationalCode.equal (p.coefficient e) RationalCode.zero = true
    · simp [hz]
    · simp only [hz, Bool.false_eq_true, ↓reduceIte]
      have he : (PolynomialCode.decode p).coeff (ExponentCode.decode e) ≠ 0 := by
        simpa only [RationalCode.equal_eq_true_iff, PolynomialCode.decode_coefficient,
          RationalCode.decode_zero] using hz
      rw [← ExponentCode.degree_decode]
      simpa [Finsupp.degree] using
        MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr he)
  · apply Finset.sup_le
    intro e he
    have hmem := encode_mem_exponents_of_mem_support p he
    have hne : RationalCode.equal (p.coefficient (ExponentCode.encode e))
        RationalCode.zero ≠ true := by
      simpa only [ne_eq, RationalCode.equal_eq_true_iff, PolynomialCode.decode_coefficient,
        ExponentCode.decode_encode, RationalCode.decode_zero] using
          (MvPolynomial.mem_support_iff.mp he)
    have h := le_foldMax (p.exponents.map fun a ↦
      if RationalCode.equal (p.coefficient a) RationalCode.zero then 0
      else ExponentCode.totalDegree a)
      (List.mem_map.mpr ⟨ExponentCode.encode e, hmem, rfl⟩)
    simp only [hne, Bool.false_eq_true, ↓reduceIte] at h
    simpa only [← ExponentCode.degree_decode, ExponentCode.decode_encode,
      Finsupp.degree] using h

/-- A raw list must have the declared exponent lengths before its
syntactic exponents are identified with the fixed-dimensional decoder. -/
theorem totalDegree_eq_decode {n : ℕ} (p : RawPolynomialCode)
    (hp : wellFormed n p = true) :
    totalDegree p = (PolynomialCode.decode (toFixed n p)).totalDegree := by
  exact (congrArg totalDegree (ofFixed_toFixed p hp)).symm.trans (totalDegree_ofFixed _)

/-- The old exact cube bound is precisely the rational coefficient mass
used by the actual polynomial-envelope construction. -/
theorem cubeAbsBoundCode_eq_coefficientMass {n : ℕ} (p : PolynomialCode n) :
    RationalCode.decode (cubeAbsBoundCode (ofFixed p)) =
      Simulation.AbsFormula.coefficientMass (PolynomialCode.decode p) := by
  rw [cubeAbsBoundCode_ofFixed]
  have h := PolynomialCode.cubeAbsBoundCode_eq_polynomialCubeAbsBound p
  have hcast : (Simulation.AbsFormula.coefficientMass (PolynomialCode.decode p) : ℝ) =
      polynomialCubeAbsBound (PolynomialCode.decode p) := by
    simp [Simulation.AbsFormula.coefficientMass, polynomialCubeAbsBound]
  apply Rat.cast_injective (α := ℝ)
  exact h.trans hcast.symm

open RawCodePrimrec

attribute [local fun_prop] Primrec Primrec.id Primrec.const Primrec.fst Primrec.snd
attribute [local fun_prop] Primrec.comp Primrec.pair ratEqual coefficient_primrec listSum

private theorem natMax_primrec : Primrec (fun q : ℕ × ℕ ↦ max q.1 q.2) := by
  exact (Primrec.nat_add.comp Primrec.fst
    (Primrec.nat_sub.comp Primrec.snd Primrec.fst)).of_eq fun q ↦ by omega

attribute [local fun_prop] natMax_primrec

/-- Degree computation is primitive recursive even before shape validation. -/
theorem totalDegree_primrec : Primrec totalDegree := by
  unfold totalDegree
  apply listFoldr (h := fun _ t ↦ max t.1 t.2)
  · apply listMap
    · apply listMap <;> fun_prop
    · apply Primrec.ite
        (Primrec.eq.comp (by fun_prop) (Primrec.const true)) <;> fun_prop
  · fun_prop
  · fun_prop

end RawPolynomialCode

end Stability
