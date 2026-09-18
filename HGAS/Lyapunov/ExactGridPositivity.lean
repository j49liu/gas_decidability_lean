import HGAS.Analysis.PolynomialCubeBounds
import HGAS.Analysis.StrictPolynomialPositivity
import HGAS.Algebra.HomogeneousEvaluation
import HGAS.Foundation.PolynomialDifferentiationCode
import Mathlib.Data.List.GetD
import Mathlib.Tactic

/-!
# Exact finite-grid certificates for strict polynomial positivity

This file implements the finite arithmetic part of a grid certificate for
strict positivity on the sup-norm unit sphere.

For a resolution `m > 0`, a grid coordinate is indexed by
`k ∈ {0, ..., 2m}` and denotes the rational number

```
                    (k - m) / m.
```

Thus the endpoints `k = 0` and `k = 2m` denote `-1` and `1`.  A grid point
lies on the sup-sphere boundary precisely when at least one coordinate is
an endpoint.  We generate all length-`n` index lists recursively, so the
checker is visibly finite and executable.

Polynomial values and the Lipschitz margin are computed entirely with
`RationalCode`.  The margin is

```
        coefficientGradientBound(p) / m,
```

where repeated monomials are first combined exactly, and
`coefficientGradientBound` sums the absolute semantic coefficients in the
coded formal partial derivatives.  The bridge theorem below proves that
this rational code decodes exactly to the coefficient-gradient bound from
`HGAS.Analysis.PolynomialCubeBounds`.

The file deliberately separates:

* exact arithmetic and finite-grid checking;
* semantic interpretation of an accepted grid certificate;
* geometric approximation from arbitrary points of the sup-sphere to the
  grid;
* compactness-based completeness of the certificate.

This separation keeps the checker reusable and makes clear which portion
is computational.  Primitive-recursiveness and the resulting `REPred`
theorem are proved in
`HGAS.Lyapunov.ExactGridPositivityComputability`.
-/

namespace HGAS

open MvPolynomial
open scoped BigOperators

/-! ## Exact rational-code utilities -/

namespace RationalCode

/-- Absolute value without changing the positive denominator. -/
def abs (q : RationalCode) : RationalCode :=
  ((false, q.1.2), q.2)

/-- Subtraction of rational codes. -/
def sub (a b : RationalCode) : RationalCode :=
  add a (neg b)

/-- Natural powers of a rational code. -/
def pow (q : RationalCode) : ℕ → RationalCode
  | 0 => one
  | k + 1 => mul q (pow q k)

/-- The code of `1 / m` when `m > 0`.  At `m = 0` it harmlessly denotes
`1`; the top-level checker rejects that resolution before using it as a
certificate. -/
def unitFraction (m : ℕ) : RationalCode :=
  ((false, 1), m - 1)

@[simp]
theorem decode_sub (a b : RationalCode) :
    decode (sub a b) = decode a - decode b := by
  simp [sub, sub_eq_add_neg]

@[simp]
theorem decode_pow (q : RationalCode) (k : ℕ) :
    decode (pow q k) = decode q ^ k := by
  induction k with
  | zero => simp [pow]
  | succ k ih => simp [pow, ih, pow_succ, mul_comm]

@[simp]
theorem decode_unitFraction {m : ℕ} (hm : 0 < m) :
    decode (unitFraction m) = 1 / (m : ℚ) := by
  rw [decode, unitFraction]
  simp only [SignedMagnitudeCode.decode, Bool.false_eq_true,
    ↓reduceIte]
  rw [Nat.sub_add_cancel hm]
  simp [Rat.divInt_eq_div]

@[simp]
theorem decode_abs (q : RationalCode) :
    decode (abs q) = |decode q| := by
  rcases q with ⟨⟨s, a⟩, b⟩
  cases s
  · simp [abs, decode, SignedMagnitudeCode.decode,
      Rat.divInt_eq_div, abs_div,
      abs_of_nonneg (show (0 : ℚ) ≤ b + 1 by positivity)]
  · simp [abs, decode, SignedMagnitudeCode.decode,
      Rat.divInt_eq_div, abs_div,
      abs_of_nonneg (show (0 : ℚ) ≤ b + 1 by positivity)]

/-- Exact strict comparison of two rational codes. -/
def lt (a b : RationalCode) : Bool :=
  positive (sub b a)

@[simp]
theorem lt_eq_true_iff (a b : RationalCode) :
    lt a b = true ↔ decode a < decode b := by
  simp [lt, sub_pos]

end RationalCode

/-! ## Exact evaluation of a sparse polynomial code -/

namespace PolynomialCode

variable {n : ℕ}

/-- Evaluate one coded monomial at a vector of coded rationals. -/
def evalMonomialCode
    (e : ExponentCode n) (x : Fin n → RationalCode) : RationalCode :=
  (List.ofFn fun i : Fin n ↦ RationalCode.pow (x i) (e i)).foldr
    RationalCode.mul RationalCode.one

/-- Evaluate a raw sparse polynomial code at coded rational coordinates. -/
def evalCode
    (p : PolynomialCode n) (x : Fin n → RationalCode) : RationalCode :=
  match p with
  | [] => RationalCode.zero
  | t :: tail =>
      RationalCode.add
        (RationalCode.mul t.2 (evalMonomialCode t.1 x))
        (evalCode tail x)

/-- Sum of the absolute values of the coefficients as they occur in a raw
code.  Repeated monomials are intentionally not combined; hence this is an
upper bound after decoding. -/
def rawAbsBoundCode (p : PolynomialCode n) : RationalCode :=
  match p with
  | [] => RationalCode.zero
  | t :: tail =>
      RationalCode.add (RationalCode.abs t.2)
        (rawAbsBoundCode tail)

/-- Exact coefficient `ℓ¹` bound after combining duplicate exponents.
The deduplicated syntactic exponent list contains the semantic support;
cancelled coefficients simply contribute zero. -/
def cubeAbsBoundCode (p : PolynomialCode n) : RationalCode :=
  (p.exponents.dedup.map fun e ↦
      RationalCode.abs (p.coefficient e)).foldr
    RationalCode.add RationalCode.zero

/-- Exact rational coefficient-gradient bound on the unit cube. -/
def cubeGradientBoundCode (p : PolynomialCode n) : RationalCode :=
  (List.ofFn fun i : Fin n ↦ cubeAbsBoundCode (pderiv i p)).foldr
    RationalCode.add RationalCode.zero

private theorem decode_foldr_mul
    (l : List RationalCode) :
    RationalCode.decode
        (l.foldr RationalCode.mul RationalCode.one) =
      (l.map RationalCode.decode).prod := by
  induction l with
  | nil => simp
  | cons q l ih => simp [ih]

private theorem decode_foldr_add
    (l : List RationalCode) :
    RationalCode.decode
        (l.foldr RationalCode.add RationalCode.zero) =
      (l.map RationalCode.decode).sum := by
  induction l with
  | nil => simp
  | cons q l ih => simp [ih]

@[simp]
theorem decode_evalMonomialCode
  (e : ExponentCode n) (x : Fin n → RationalCode) :
    RationalCode.decode (evalMonomialCode e x) =
      ∏ i : Fin n, RationalCode.decode (x i) ^ e i := by
  unfold evalMonomialCode
  rw [decode_foldr_mul]
  simp [List.prod_ofFn]

@[simp]
theorem decode_evalCode
    (p : PolynomialCode n) (x : Fin n → RationalCode) :
    RationalCode.decode (evalCode p x) =
      MvPolynomial.eval₂ (algebraMap ℚ ℚ)
        (fun i ↦ RationalCode.decode (x i))
        (decode p) := by
  induction p with
  | nil =>
      simp [evalCode]
  | cons t p ih =>
      simp only [evalCode, RationalCode.decode_add,
        RationalCode.decode_mul, decode_cons, MvPolynomial.eval₂_add, ih,
        decodeTerm, MvPolynomial.eval₂_monomial,
        decode_evalMonomialCode]
      simp [ExponentCode.decode]

@[simp]
theorem decode_rawAbsBoundCode
    (p : PolynomialCode n) :
    RationalCode.decode (rawAbsBoundCode p) =
      (p.map fun t ↦ |RationalCode.decode t.2|).sum := by
  induction p with
  | nil => simp [rawAbsBoundCode]
  | cons t p ih =>
      simp [rawAbsBoundCode, ih]

@[simp]
theorem decode_cubeAbsBoundCode
    (p : PolynomialCode n) :
    RationalCode.decode (cubeAbsBoundCode p) =
      (p.exponents.dedup.map fun e ↦
        |RationalCode.decode (p.coefficient e)|).sum := by
  unfold cubeAbsBoundCode
  rw [decode_foldr_add]
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro e he
  simp

@[simp]
theorem decode_cubeGradientBoundCode
    (p : PolynomialCode n) :
    RationalCode.decode (cubeGradientBoundCode p) =
      ∑ i : Fin n,
        RationalCode.decode (cubeAbsBoundCode (pderiv i p)) := by
  unfold cubeGradientBoundCode
  rw [decode_foldr_add]
  simp [List.sum_ofFn]

/-- The executable coefficient bound is exactly the semantic coefficient
`ℓ¹` bound used by `PolynomialCubeBounds`. -/
theorem cubeAbsBoundCode_eq_polynomialCubeAbsBound
    (p : PolynomialCode n) :
    algebraMap ℚ ℝ
        (RationalCode.decode (cubeAbsBoundCode p)) =
      polynomialCubeAbsBound (decode p) := by
  let l : List (Fin n →₀ ℕ) :=
    p.exponents.dedup.map ExponentCode.decode
  let S : Finset (Fin n →₀ ℕ) := l.toFinset
  have hlNodup : l.Nodup := by
    exact (List.nodup_dedup p.exponents).map
      ExponentCode.decode_injective
  have hsupport : (decode p).support ⊆ S := by
    intro e he
    have hencode : ExponentCode.encode e ∈ p.exponents := by
      by_contra hnot
      have hcode :=
        coefficient_eq_zero_of_not_mem
          (ExponentCode.encode e) p hnot
      have hdecode :=
        decode_coefficient (ExponentCode.encode e) p
      rw [hcode, RationalCode.decode_zero] at hdecode
      simp only [ExponentCode.decode_encode] at hdecode
      exact (MvPolynomial.mem_support_iff.mp he) hdecode.symm
    change e ∈ l.toFinset
    rw [List.mem_toFinset]
    apply List.mem_map.mpr
    exact ⟨ExponentCode.encode e,
      List.mem_dedup.mpr hencode, ExponentCode.decode_encode e⟩
  have hextend :
      (∑ e ∈ (decode p).support,
          |algebraMap ℚ ℝ ((decode p).coeff e)|) =
        ∑ e ∈ S,
          |algebraMap ℚ ℝ ((decode p).coeff e)| := by
    apply Finset.sum_subset hsupport
    intro e heS hnot
    have hzero : (decode p).coeff e = 0 := by
      simpa only [MvPolynomial.mem_support_iff, not_not] using hnot
    simp [hzero]
  rw [polynomialCubeAbsBound, hextend]
  rw [show
      (∑ e ∈ S,
          |algebraMap ℚ ℝ ((decode p).coeff e)|) =
        (l.map fun e ↦
          |algebraMap ℚ ℝ ((decode p).coeff e)|).sum by
      exact List.sum_toFinset _ hlNodup]
  rw [decode_cubeAbsBoundCode]
  rw [map_list_sum]
  unfold l
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro e he
  simp only [Function.comp_apply]
  rw [decode_coefficient]
  exact Rat.cast_abs _

/-- Consequently the coded gradient bound is exactly the semantic
coefficient-gradient bound. -/
theorem cubeGradientBoundCode_eq_polynomialCubeGradientBound
    (p : PolynomialCode n) :
    algebraMap ℚ ℝ
        (RationalCode.decode (cubeGradientBoundCode p)) =
      polynomialCubeGradientBound (decode p) := by
  rw [decode_cubeGradientBoundCode,
    polynomialCubeGradientBound, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [cubeAbsBoundCode_eq_polynomialCubeAbsBound,
    decode_pderiv]

end PolynomialCode

/-! ## The canonical finite sup-sphere grid -/

namespace ExactGridPositivity

/-- Cartesian words of length `n` over a finite alphabet. -/
def cartesianWords {α : Type*} (alphabet : List α) : ℕ → List (List α)
  | 0 => [[]]
  | n + 1 =>
      alphabet.flatMap fun a ↦
        (cartesianWords alphabet n).map fun tail ↦ a :: tail

/-- All length-`n` lists with entries in `{0, ..., 2m}`. -/
def gridIndexPoints (n m : ℕ) : List (List ℕ) :=
  cartesianWords (List.range (2 * m + 1)) n

/-- Exact rational coordinate represented by an index `k`. -/
def gridCoordinate (m k : ℕ) : ℚ :=
  ((k : ℚ) - m) / m

/-- The same coordinate interpreted in `ℝ`. -/
noncomputable def gridCoordinateReal (m k : ℕ) : ℝ :=
  ((k : ℝ) - m) / m

/-- Signed numerator `k - m`, represented using only natural-number
subtraction and a sign bit. -/
def centeredNumeratorCode (m k : ℕ) : SignedMagnitudeCode :=
  if k < m then (true, m - k) else (false, k - m)

/-- Coded version of `gridCoordinate`.

For positive `m` this is the direct signed numerator/shifted-denominator
code for `(k-m)/m`.  The separate zero branch preserves total semantic
correctness at the rejected resolution `m = 0`, while keeping the function
primitive-recursive. -/
def gridCoordinateCode (m k : ℕ) : RationalCode :=
  if m = 0 then RationalCode.zero
  else (centeredNumeratorCode m k, m - 1)

/-- Turn an index list into a coded rational vector.  Generated grid
points always have length `n`; `getD` makes the operation total on arbitrary
lists as well. -/
def gridPointCode (n m : ℕ) (point : List ℕ) :
    Fin n → RationalCode :=
  fun i ↦ gridCoordinateCode m (point.getD i 0)

/-- Real vector represented by an index word. -/
noncomputable def gridPointReal (n m : ℕ) (point : List ℕ) :
    Fin n → ℝ :=
  fun i ↦ gridCoordinateReal m (point.getD i 0)

/-- An index list is on the boundary when one coordinate is an endpoint. -/
def isBoundaryIndexPoint (m : ℕ) (point : List ℕ) : Bool :=
  point.any fun k ↦ (k == 0) || (k == 2 * m)

/-- Mathematical form of the boundary test. -/
def IsBoundaryIndexPoint (m : ℕ) (point : List ℕ) : Prop :=
  ∃ k ∈ point, k = 0 ∨ k = 2 * m

/-- Exact rational Lipschitz margin used at resolution `m`. -/
def marginCode {n : ℕ} (p : PolynomialCode n) (m : ℕ) :
    RationalCode :=
  RationalCode.mul (PolynomialCode.cubeGradientBoundCode p)
    (RationalCode.unitFraction m)

/-- Check one grid word.  Interior words are ignored; boundary words must
have polynomial value strictly greater than the exact margin. -/
def checkGridPoint {n : ℕ}
    (p : PolynomialCode n) (m : ℕ) (point : List ℕ) : Bool :=
  !isBoundaryIndexPoint m point ||
    RationalCode.lt (marginCode p m)
      (PolynomialCode.evalCode p (gridPointCode n m point))

/-- The complete finite checker. -/
def checkStrictPositiveOnSupSphere {n : ℕ}
    (p : PolynomialCode n) (m : ℕ) : Bool :=
  decide (0 < m) &&
    (gridIndexPoints n m).all (checkGridPoint p m)

@[simp]
theorem decode_centeredNumeratorCode (m k : ℕ) :
    SignedMagnitudeCode.decode (centeredNumeratorCode m k) =
      (k : ℤ) - (m : ℤ) := by
  by_cases hk : k < m
  · simp only [centeredNumeratorCode, hk, ↓reduceIte,
      SignedMagnitudeCode.decode, ↓reduceIte]
    omega
  · simp only [centeredNumeratorCode, hk, ↓reduceIte,
      SignedMagnitudeCode.decode, Bool.false_eq_true,
      ↓reduceIte]
    omega

@[simp]
theorem decode_gridCoordinateCode (m k : ℕ) :
    RationalCode.decode (gridCoordinateCode m k) =
      gridCoordinate m k := by
  by_cases hm : m = 0
  · simp [gridCoordinateCode, gridCoordinate, hm]
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    rw [gridCoordinateCode, if_neg hm, RationalCode.decode,
      decode_centeredNumeratorCode, Nat.sub_add_cancel hmpos]
    simp [gridCoordinate, Rat.divInt_eq_div]

theorem gridCoordinate_cast (m k : ℕ) :
    ((gridCoordinate m k : ℚ) : ℝ) =
      gridCoordinateReal m k := by
  norm_num [gridCoordinate, gridCoordinateReal]

/-- Characterization of the recursively generated Cartesian words. -/
theorem mem_cartesianWords_iff {α : Type*}
    (alphabet : List α) (n : ℕ) (point : List α) :
    point ∈ cartesianWords alphabet n ↔
      point.length = n ∧ ∀ a ∈ point, a ∈ alphabet := by
  induction n generalizing point with
  | zero =>
      cases point <;> simp [cartesianWords]
  | succ n ih =>
      constructor
      · intro h
        simp only [cartesianWords, List.mem_flatMap,
          List.mem_map] at h
        obtain ⟨a, ha, tail, htail, rfl⟩ := h
        have htail' := (ih tail).1 htail
        constructor
        · simp [htail'.1]
        · intro b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · exact ha
          · exact htail'.2 b hb
      · rintro ⟨hlength, hall⟩
        cases point with
        | nil => simp at hlength
        | cons a tail =>
            simp only [List.length_cons, Nat.succ.injEq] at hlength
            have ha : a ∈ alphabet :=
              hall a (List.mem_cons_self)
            have htailAll :
                ∀ b ∈ tail, b ∈ alphabet := by
              intro b hb
              exact hall b (List.mem_cons_of_mem a hb)
            have htail :
                tail ∈ cartesianWords alphabet n :=
              (ih tail).2 ⟨hlength, htailAll⟩
            simp only [cartesianWords, List.mem_flatMap,
              List.mem_map]
            exact ⟨a, ha, tail, htail, rfl⟩

theorem mem_gridIndexPoints_iff
    (n m : ℕ) (point : List ℕ) :
    point ∈ gridIndexPoints n m ↔
      point.length = n ∧
        ∀ k ∈ point, k < 2 * m + 1 := by
  rw [gridIndexPoints, mem_cartesianWords_iff]
  simp only [List.mem_range]

/-- Every generated coordinate lies in the real unit interval. -/
theorem abs_gridCoordinateReal_le_one
    {m k : ℕ} (hm : 0 < m) (hk : k < 2 * m + 1) :
    |gridCoordinateReal m k| ≤ 1 := by
  have hk' : k ≤ 2 * m := by omega
  have hmReal : (0 : ℝ) < m := by exact_mod_cast hm
  have hkNonnegReal : (0 : ℝ) ≤ k := by positivity
  have hkLeReal : (k : ℝ) ≤ 2 * (m : ℝ) := by
    exact_mod_cast hk'
  unfold gridCoordinateReal
  rw [abs_le]
  constructor
  · apply (le_div_iff₀ hmReal).2
    nlinarith
  · apply (div_le_iff₀ hmReal).2
    nlinarith

/-- One-dimensional floor approximation.  The endpoint clauses ensure
that a sup-sphere point is sent to a boundary grid word. -/
theorem exists_gridIndex_approx
    {m : ℕ} (hm : 0 < m) {x : ℝ} (hx : |x| ≤ 1) :
    ∃ k : ℕ,
      k < 2 * m + 1 ∧
      |gridCoordinateReal m k - x| < 1 / (m : ℝ) ∧
      (x = -1 → k = 0) ∧
      (x = 1 → k = 2 * m) := by
  let z : ℤ := ⌊(m : ℝ) * x⌋
  let k : ℕ := (z + (m : ℤ)).toNat
  have hmReal : (0 : ℝ) < m := by exact_mod_cast hm
  have hxBounds : -1 ≤ x ∧ x ≤ 1 := (abs_le.mp hx)
  have hzLower : -(m : ℤ) ≤ z := by
    rw [Int.le_floor]
    have hmul :=
      mul_le_mul_of_nonneg_left hxBounds.1
        (show (0 : ℝ) ≤ m by positivity)
    norm_num at hmul ⊢
    exact hmul
  have hzUpper : z ≤ (m : ℤ) := by
    have hfloor := Int.floor_le ((m : ℝ) * x)
    have hmul :
        (m : ℝ) * x ≤ (m : ℝ) :=
      mul_le_of_le_one_right (by positivity) hxBounds.2
    exact_mod_cast hfloor.trans hmul
  have hnonneg : 0 ≤ z + (m : ℤ) := by omega
  have hkCast : (k : ℤ) = z + (m : ℤ) := by
    exact Int.toNat_of_nonneg hnonneg
  have hkLe : k ≤ 2 * m := by
    have hkLeInt : (k : ℤ) ≤ (2 * m : ℕ) := by
      rw [hkCast]
      norm_num
      omega
    exact_mod_cast hkLeInt
  have hfloorLower :
      (z : ℝ) ≤ (m : ℝ) * x := by
    exact Int.floor_le ((m : ℝ) * x)
  have hfloorUpper :
      (m : ℝ) * x < (z : ℝ) + 1 := by
    exact Int.lt_floor_add_one ((m : ℝ) * x)
  have hcoordinate :
      gridCoordinateReal m k = (z : ℝ) / (m : ℝ) := by
    unfold gridCoordinateReal
    have hkReal :
        (k : ℝ) = (z : ℝ) + (m : ℝ) := by
      exact_mod_cast hkCast
    rw [hkReal]
    ring
  have hcoordLe :
      gridCoordinateReal m k ≤ x := by
    rw [hcoordinate]
    exact (div_le_iff₀ hmReal).2 (by
      simpa only [mul_comm] using hfloorLower)
  have herror :
      x - gridCoordinateReal m k < 1 / (m : ℝ) := by
    rw [hcoordinate]
    have hxlt :
        x < ((z : ℝ) + 1) / (m : ℝ) := by
      exact (lt_div_iff₀ hmReal).2 (by
        simpa only [mul_comm] using hfloorUpper)
    calc
      x - (z : ℝ) / (m : ℝ) <
          ((z : ℝ) + 1) / (m : ℝ) -
            (z : ℝ) / (m : ℝ) :=
        sub_lt_sub_right hxlt _
      _ = 1 / (m : ℝ) := by ring
  refine ⟨k, by omega, ?_, ?_, ?_⟩
  · rw [abs_of_nonpos (sub_nonpos.mpr hcoordLe)]
    simpa only [neg_sub] using herror
  · intro hxneg
    have hzEq : z = -(m : ℤ) := by
      unfold z
      rw [hxneg]
      convert Int.floor_intCast (R := ℝ) (-(m : ℤ)) using 1
      norm_num
    have hkZero : (k : ℤ) = 0 := by
      rw [hkCast, hzEq]
      ring
    exact_mod_cast hkZero
  · intro hxone
    have hzEq : z = (m : ℤ) := by
      unfold z
      rw [hxone]
      norm_num
    have hkTwo : (k : ℤ) = (2 * m : ℕ) := by
      rw [hkCast, hzEq]
      norm_num
      ring
    exact_mod_cast hkTwo

/-- Every point of the real sup-sphere has a boundary grid point within
strict sup-distance `1/m`. -/
theorem exists_boundary_gridPoint_near
    {n m : ℕ} (hm : 0 < m) (x : Fin n → ℝ)
    (hxnorm : ‖x‖ = 1) :
    ∃ point : List ℕ,
      point ∈ gridIndexPoints n m ∧
      IsBoundaryIndexPoint m point ∧
      ‖gridPointReal n m point - x‖ < 1 / (m : ℝ) := by
  have hmReal : (0 : ℝ) < m := by exact_mod_cast hm
  have hxCoordinate :
      ∀ i : Fin n, |x i| ≤ 1 := by
    intro i
    have hi := norm_le_pi_norm x i
    simpa only [Real.norm_eq_abs, hxnorm] using hi
  have happ :
      ∀ i : Fin n,
        ∃ k : ℕ,
          k < 2 * m + 1 ∧
          |gridCoordinateReal m k - x i| < 1 / (m : ℝ) ∧
          (x i = -1 → k = 0) ∧
          (x i = 1 → k = 2 * m) :=
    fun i ↦ exists_gridIndex_approx hm (hxCoordinate i)
  choose k hkRange hkApprox hkNeg hkPos using happ
  let point : List ℕ := List.ofFn k
  have hpoint : point ∈ gridIndexPoints n m := by
    apply (mem_gridIndexPoints_iff n m point).2
    constructor
    · simp [point]
    · intro q hq
      simp only [point] at hq
      rw [List.mem_ofFn', Set.mem_range] at hq
      obtain ⟨i, rfl⟩ := hq
      exact hkRange i
  have hboundaryCoordinate :
      ∃ i : Fin n, |x i| = 1 := by
    by_contra hnone
    have hall :
        ∀ i : Fin n, |x i| < 1 := by
      intro i
      exact lt_of_le_of_ne (hxCoordinate i)
        (fun heq ↦ hnone ⟨i, heq⟩)
    have hnormLt : ‖x‖ < 1 := by
      apply (pi_norm_lt_iff zero_lt_one).2
      intro i
      simpa only [Real.norm_eq_abs] using hall i
    rw [hxnorm] at hnormLt
    exact (lt_irrefl 1 hnormLt)
  obtain ⟨i, hi⟩ := hboundaryCoordinate
  have hboundary :
      IsBoundaryIndexPoint m point := by
    rcases (abs_eq (show (0 : ℝ) ≤ 1 by norm_num)).1 hi with
      hpos | hneg
    · refine ⟨k i, ?_, Or.inr (hkPos i hpos)⟩
      exact List.mem_ofFn.mpr ⟨i, rfl⟩
    · refine ⟨k i, ?_, Or.inl (hkNeg i hneg)⟩
      exact List.mem_ofFn.mpr ⟨i, rfl⟩
  have hdistance :
      ‖gridPointReal n m point - x‖ < 1 / (m : ℝ) := by
    have hmarginPos : (0 : ℝ) < 1 / (m : ℝ) := by positivity
    apply (pi_norm_lt_iff hmarginPos).2
    intro i
    rw [Real.norm_eq_abs]
    change
      |gridCoordinateReal m (point.getD i 0) - x i| <
        1 / (m : ℝ)
    have hget : point.getD i 0 = k i := by
      simp [point, List.getD_eq_getElem?_getD, i.isLt]
    rw [hget]
    exact hkApprox i
  exact ⟨point, hpoint, hboundary, hdistance⟩

@[simp]
theorem isBoundaryIndexPoint_eq_true_iff
    (m : ℕ) (point : List ℕ) :
    isBoundaryIndexPoint m point = true ↔
      IsBoundaryIndexPoint m point := by
  simp [isBoundaryIndexPoint, IsBoundaryIndexPoint]

@[simp]
theorem decode_marginCode {n : ℕ}
    (p : PolynomialCode n) {m : ℕ} (hm : 0 < m) :
    RationalCode.decode (marginCode p m) =
      RationalCode.decode (PolynomialCode.cubeGradientBoundCode p) /
        (m : ℚ) := by
  simp [marginCode, hm, div_eq_mul_inv]

/-- Exact coded evaluation agrees with real evaluation of the decoded
polynomial at the corresponding grid point. -/
theorem ratMvPolynomialEval_gridPointReal
    {n : ℕ} (p : PolynomialCode n) (m : ℕ) (point : List ℕ) :
    ratMvPolynomialEval (PolynomialCode.decode p)
        (gridPointReal n m point) =
      algebraMap ℚ ℝ
        (RationalCode.decode
          (PolynomialCode.evalCode p (gridPointCode n m point))) := by
  let q : Fin n → ℚ :=
    fun i ↦ RationalCode.decode (gridPointCode n m point i)
  have hcoordinate :
      ∀ i : Fin n,
        algebraMap ℚ ℝ (q i) =
          gridPointReal n m point i := by
    intro i
    simp [q, gridPointCode, gridPointReal,
      gridCoordinate_cast]
  rw [PolynomialCode.decode_evalCode]
  unfold ratMvPolynomialEval
  rw [← MvPolynomial.eval₂_eq_eval_map]
  have hmap :=
    MvPolynomial.map_eval₂Hom
      (algebraMap ℚ ℚ) q (algebraMap ℚ ℝ)
        (PolynomialCode.decode p)
  simpa only [MvPolynomial.coe_eval₂Hom, q, hcoordinate] using
    hmap.symm

/-- Exact semantic meaning of the one-point Boolean test. -/
theorem checkGridPoint_eq_true_iff {n : ℕ}
    (p : PolynomialCode n) {m : ℕ} (hm : 0 < m)
    (point : List ℕ) :
    checkGridPoint p m point = true ↔
      IsBoundaryIndexPoint m point →
        RationalCode.decode (PolynomialCode.evalCode p
            (gridPointCode n m point)) >
          RationalCode.decode
              (PolynomialCode.cubeGradientBoundCode p) /
            (m : ℚ) := by
  unfold checkGridPoint
  rw [Bool.or_eq_true, RationalCode.lt_eq_true_iff,
    decode_marginCode p hm]
  constructor
  · rintro (hinterior | hmargin)
    · intro hboundary
      have htrue :
          isBoundaryIndexPoint m point = true :=
        (isBoundaryIndexPoint_eq_true_iff m point).2 hboundary
      simp [htrue] at hinterior
    · intro _
      exact hmargin
  · intro h
    by_cases hboundary : IsBoundaryIndexPoint m point
    · exact Or.inr (h hboundary)
    · left
      have hfalse :
          isBoundaryIndexPoint m point = false := by
        apply Bool.eq_false_iff.mpr
        intro htrue
        exact hboundary
          ((isBoundaryIndexPoint_eq_true_iff m point).1 htrue)
      simp [hfalse]

/-- Exact semantic specification of the complete checker. -/
theorem checkStrictPositiveOnSupSphere_eq_true_iff {n : ℕ}
    (p : PolynomialCode n) (m : ℕ) :
    checkStrictPositiveOnSupSphere p m = true ↔
      0 < m ∧
      ∀ point ∈ gridIndexPoints n m,
        IsBoundaryIndexPoint m point →
          RationalCode.decode (PolynomialCode.evalCode p
              (gridPointCode n m point)) >
            RationalCode.decode
                (PolynomialCode.cubeGradientBoundCode p) /
              (m : ℚ) := by
  by_cases hm : 0 < m
  · simp [checkStrictPositiveOnSupSphere, hm,
      checkGridPoint_eq_true_iff p hm]
  · simp [checkStrictPositiveOnSupSphere, hm]

/-- A generated grid word represents a point of the closed unit
sup-ball. -/
theorem gridPointReal_mem_closedUnitBall
    {n m : ℕ} (hm : 0 < m) {point : List ℕ}
    (hpoint : point ∈ gridIndexPoints n m) :
    gridPointReal n m point ∈
      Metric.closedBall (0 : Fin n → ℝ) 1 := by
  have hdescription :=
    (mem_gridIndexPoints_iff n m point).1 hpoint
  have hnorm : ‖gridPointReal n m point‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).2
    intro i
    rw [Real.norm_eq_abs]
    have hiLt : i.val < point.length := by
      simpa only [hdescription.1] using i.isLt
    have himem : point.getD i 0 ∈ point := by
      rw [List.getD_eq_getElem point 0 hiLt]
      exact List.getElem_mem hiLt
    exact abs_gridCoordinateReal_le_one hm
      (hdescription.2 (point.getD i 0) himem)
  simpa [Metric.mem_closedBall, dist_zero_right] using hnorm

/-- A generated boundary word represents a point whose sup norm is
exactly one.  This is the converse geometric fact to
`gridPointReal_mem_closedUnitBall`: the endpoint in the boundary witness
supplies a coordinate of absolute value one. -/
theorem norm_gridPointReal_eq_one_of_boundary
    {n m : ℕ} (hm : 0 < m) {point : List ℕ}
    (hpoint : point ∈ gridIndexPoints n m)
    (hboundary : IsBoundaryIndexPoint m point) :
    ‖gridPointReal n m point‖ = 1 := by
  have hdescription :=
    (mem_gridIndexPoints_iff n m point).1 hpoint
  have hupper : ‖gridPointReal n m point‖ ≤ 1 := by
    have hball :=
      gridPointReal_mem_closedUnitBall hm hpoint
    simpa [Metric.mem_closedBall, dist_zero_right] using hball
  obtain ⟨k, hkmem, hk⟩ := hboundary
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hkmem
  let j : Fin n :=
    ⟨i.val, by simpa only [hdescription.1] using i.isLt⟩
  have hgetD : point.getD j 0 = k := by
    change point.getD i.val 0 = k
    rw [List.getD_eq_get point 0 i, hi]
  have hcoordinate :
      |gridCoordinateReal m k| = 1 := by
    rcases hk with rfl | rfl
    · have hm0 : (m : ℝ) ≠ 0 := by positivity
      rw [show gridCoordinateReal m 0 = -1 by
        unfold gridCoordinateReal
        field_simp
        ring]
      norm_num
    · have hm0 : (m : ℝ) ≠ 0 := by positivity
      rw [show gridCoordinateReal m (2 * m) = 1 by
        unfold gridCoordinateReal
        push_cast
        field_simp
        ring]
      norm_num
  have hlower : 1 ≤ ‖gridPointReal n m point‖ := by
    calc
      1 = ‖gridPointReal n m point j‖ := by
        rw [Real.norm_eq_abs]
        change 1 =
          |gridCoordinateReal m (point.getD j 0)|
        rw [hgetD, hcoordinate]
      _ ≤ ‖gridPointReal n m point‖ :=
        norm_le_pi_norm (gridPointReal n m point) j
  exact le_antisymm hupper hlower

/-- Semantic strict positivity on the real sup-sphere. -/
def StrictlyPositiveOnSupSphere {n : ℕ}
    (p : MvPolynomial (Fin n) ℚ) : Prop :=
  ∀ x : Fin n → ℝ, ‖x‖ = 1 → 0 < ratMvPolynomialEval p x

/-- Soundness of the exact finite checker. -/
theorem checkStrictPositiveOnSupSphere_sound
    {n : ℕ} (p : PolynomialCode n) (m : ℕ)
    (hcheck : checkStrictPositiveOnSupSphere p m = true) :
    StrictlyPositiveOnSupSphere (PolynomialCode.decode p) := by
  have hspec :=
    (checkStrictPositiveOnSupSphere_eq_true_iff p m).1 hcheck
  have hm := hspec.1
  intro x hxnorm
  obtain ⟨point, hpoint, hboundary, hdistance⟩ :=
    exists_boundary_gridPoint_near hm x hxnorm
  let y : Fin n → ℝ := gridPointReal n m point
  have hyBall :
      y ∈ Metric.closedBall (0 : Fin n → ℝ) 1 :=
    gridPointReal_mem_closedUnitBall hm hpoint
  have hxBall :
      x ∈ Metric.closedBall (0 : Fin n → ℝ) 1 := by
    simp [Metric.mem_closedBall, dist_zero_right, hxnorm]
  have hgridRat := hspec.2 point hpoint hboundary
  have hgrid :
      polynomialCubeGradientBound (PolynomialCode.decode p) /
          (m : ℝ) <
        ratMvPolynomialEval (PolynomialCode.decode p) y := by
    have hcast :
        ((RationalCode.decode
                (PolynomialCode.cubeGradientBoundCode p) /
              (m : ℚ) : ℚ) : ℝ) <
          ((RationalCode.decode
              (PolynomialCode.evalCode p
                (gridPointCode n m point)) : ℚ) : ℝ) := by
      exact_mod_cast hgridRat
    rw [Rat.cast_div] at hcast
    have hgradientCode :=
      PolynomialCode.cubeGradientBoundCode_eq_polynomialCubeGradientBound
        p
    change
      ((RationalCode.decode
        (PolynomialCode.cubeGradientBoundCode p) : ℚ) : ℝ) =
          polynomialCubeGradientBound (PolynomialCode.decode p)
      at hgradientCode
    rw [hgradientCode] at hcast
    have hevaluation :=
      ratMvPolynomialEval_gridPointReal p m point
    change
      ratMvPolynomialEval (PolynomialCode.decode p)
          (gridPointReal n m point) =
        ((RationalCode.decode
          (PolynomialCode.evalCode p
            (gridPointCode n m point)) : ℚ) : ℝ)
      at hevaluation
    rw [← hevaluation] at hcast
    exact hcast
  have hLipschitz :=
    abs_ratMvPolynomialEval_sub_le_cubeGradientBound
      (PolynomialCode.decode p) hxBall hyBall
  have hgradient :
      0 ≤ polynomialCubeGradientBound
        (PolynomialCode.decode p) :=
    polynomialCubeGradientBound_nonneg _
  have hdistanceLe :
      ‖y - x‖ ≤ 1 / (m : ℝ) :=
    hdistance.le
  have herror :
      |ratMvPolynomialEval (PolynomialCode.decode p) y -
          ratMvPolynomialEval (PolynomialCode.decode p) x| ≤
        polynomialCubeGradientBound (PolynomialCode.decode p) /
          (m : ℝ) := by
    calc
      |ratMvPolynomialEval (PolynomialCode.decode p) y -
          ratMvPolynomialEval (PolynomialCode.decode p) x| ≤
          polynomialCubeGradientBound (PolynomialCode.decode p) *
            ‖y - x‖ :=
        hLipschitz
      _ ≤ polynomialCubeGradientBound (PolynomialCode.decode p) *
            (1 / (m : ℝ)) :=
        mul_le_mul_of_nonneg_left hdistanceLe hgradient
      _ = polynomialCubeGradientBound (PolynomialCode.decode p) /
            (m : ℝ) := by ring
  have hplain :
      ratMvPolynomialEval (PolynomialCode.decode p) y -
          ratMvPolynomialEval (PolynomialCode.decode p) x ≤
        polynomialCubeGradientBound (PolynomialCode.decode p) /
          (m : ℝ) :=
    (le_abs_self _).trans herror
  linarith

/-- Completeness of the exact checker: every polynomial which is strictly
positive on the sup-sphere is accepted at some finite resolution.

The compact sphere supplies a uniform positive lower bound `ε`.  Choosing
`m` so large that the coefficient-gradient margin `L / m` is below `ε`
makes every boundary grid inequality pass. -/
theorem checkStrictPositiveOnSupSphere_complete
    {n : ℕ} (p : PolynomialCode n)
    (hpos :
      StrictlyPositiveOnSupSphere (PolynomialCode.decode p)) :
    ∃ m : ℕ, checkStrictPositiveOnSupSphere p m = true := by
  obtain ⟨ε, hε, hεbound⟩ :=
    exists_pos_lower_bound_ratMvPolynomialEval_on_unitSphere
      (PolynomialCode.decode p) hpos
  let L : ℝ :=
    polynomialCubeGradientBound (PolynomialCode.decode p)
  have hL : 0 ≤ L :=
    polynomialCubeGradientBound_nonneg _
  obtain ⟨m, hmLarge⟩ := exists_nat_gt (L / ε)
  have hratio : 0 ≤ L / ε :=
    div_nonneg hL hε.le
  have hmReal : (0 : ℝ) < m :=
    lt_of_le_of_lt hratio hmLarge
  have hm : 0 < m := by
    exact_mod_cast hmReal
  have hmarginSmall : L / (m : ℝ) < ε := by
    apply (div_lt_iff₀ hmReal).2
    have hcross : L < (m : ℝ) * ε :=
      (div_lt_iff₀ hε).1 hmLarge
    simpa only [mul_comm] using hcross
  refine ⟨m,
    (checkStrictPositiveOnSupSphere_eq_true_iff p m).2
      ⟨hm, ?_⟩⟩
  intro point hpoint hboundary
  have hnorm :
      ‖gridPointReal n m point‖ = 1 :=
    norm_gridPointReal_eq_one_of_boundary
      hm hpoint hboundary
  have hvalue :
      L / (m : ℝ) <
        ratMvPolynomialEval (PolynomialCode.decode p)
          (gridPointReal n m point) :=
    hmarginSmall.trans_le
      (hεbound (gridPointReal n m point) hnorm)
  have hgradientCode :=
    PolynomialCode.cubeGradientBoundCode_eq_polynomialCubeGradientBound
      p
  change
    ((RationalCode.decode
      (PolynomialCode.cubeGradientBoundCode p) : ℚ) : ℝ) =
        polynomialCubeGradientBound (PolynomialCode.decode p)
    at hgradientCode
  have hevaluation :=
    ratMvPolynomialEval_gridPointReal p m point
  change
    ratMvPolynomialEval (PolynomialCode.decode p)
        (gridPointReal n m point) =
      ((RationalCode.decode
        (PolynomialCode.evalCode p
          (gridPointCode n m point)) : ℚ) : ℝ)
    at hevaluation
  have hcast :
      ((RationalCode.decode
              (PolynomialCode.cubeGradientBoundCode p) /
            (m : ℚ) : ℚ) : ℝ) <
        ((RationalCode.decode
            (PolynomialCode.evalCode p
              (gridPointCode n m point)) : ℚ) : ℝ) := by
    rw [Rat.cast_div, hgradientCode, ← hevaluation]
    exact hvalue
  exact_mod_cast hcast

/-- The existential finite-grid certificate is equivalent to strict
positivity on the real sup-sphere. -/
theorem exists_checked_iff_strictlyPositiveOnSupSphere
    {n : ℕ} (p : PolynomialCode n) :
    (∃ m : ℕ, checkStrictPositiveOnSupSphere p m = true) ↔
      StrictlyPositiveOnSupSphere (PolynomialCode.decode p) := by
  constructor
  · rintro ⟨m, hm⟩
    exact checkStrictPositiveOnSupSphere_sound p m hm
  · exact checkStrictPositiveOnSupSphere_complete p

/-- For a homogeneous form, sphere positivity propagates to every nonzero
point by radial scaling. -/
theorem checkStrictPositiveOnSupSphere_sound_nonzero
    {n d : ℕ} (p : PolynomialCode n) (m : ℕ)
    (hp : (PolynomialCode.decode p).IsHomogeneous d)
    (hcheck : checkStrictPositiveOnSupSphere p m = true) :
    ∀ x : Fin n → ℝ, x ≠ 0 →
      0 < ratMvPolynomialEval (PolynomialCode.decode p) x := by
  have hsphere :=
    checkStrictPositiveOnSupSphere_sound p m hcheck
  intro x hx
  let c : ℝ := ‖x‖
  let y : Fin n → ℝ := c⁻¹ • x
  have hc : 0 < c := by
    exact norm_pos_iff.mpr hx
  have hynorm : ‖y‖ = 1 := by
    simp [y, c, norm_smul, hc.ne']
  have hypos :
      0 < ratMvPolynomialEval (PolynomialCode.decode p) y :=
    hsphere y hynorm
  have hxy : c • y = x := by
    simp [y, smul_smul, hc.ne']
  have hscale :
      ratMvPolynomialEval (PolynomialCode.decode p) x =
        c ^ d *
          ratMvPolynomialEval (PolynomialCode.decode p) y := by
    rw [← hxy]
    simpa only [ratMvPolynomialEval,
      ← MvPolynomial.eval₂_eq_eval_map] using
      MvPolynomial.IsHomogeneous.eval₂Hom_smul
        hp (algebraMap ℚ ℝ) y c
  rw [hscale]
  exact mul_pos (pow_pos hc d) hypos

/-- For a homogeneous rational form, existence of an accepted finite grid
is equivalent to positivity at every nonzero real point. -/
theorem exists_checked_iff_positive_nonzero
    {n d : ℕ} (p : PolynomialCode n)
    (hp : (PolynomialCode.decode p).IsHomogeneous d) :
    (∃ m : ℕ, checkStrictPositiveOnSupSphere p m = true) ↔
      ∀ x : Fin n → ℝ, x ≠ 0 →
        0 < ratMvPolynomialEval (PolynomialCode.decode p) x := by
  constructor
  · rintro ⟨m, hm⟩
    exact checkStrictPositiveOnSupSphere_sound_nonzero p m hp hm
  · intro hnonzero
    apply checkStrictPositiveOnSupSphere_complete p
    intro x hxnorm
    apply hnonzero x
    intro hxzero
    subst x
    simp at hxnorm

end ExactGridPositivity

end HGAS
