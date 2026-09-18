import Mathlib.Tactic

/-!
# Quadratic--geometric sequences are determined by two neighbours

The coefficient sequences occurring in a one-dimensional Jacobi theta
trace have the form

```text
                         R^(k²) S^k,       k ∈ ℤ.
```

The two coefficients at `k = 1` and `k = -1` determine the entire
sequence.  There is a harmless simultaneous sign ambiguity
`(R,S) ↦ (-R,-S)`, but it disappears because `k²+k` is always even.

This elementary lemma is useful whenever two first moments determine a
complete quadratic Fourier trace.  It is deliberately independent of
theta functions and dynamical systems.
-/

noncomputable section

namespace HGAS.Modular

/-- A normalized quadratic--geometric sequence on the integer lattice. -/
def quadraticGeometricSequence
    (R S : ℂ) (k : ℤ) : ℂ :=
  R ^ (k ^ 2) * S ^ k

@[simp]
theorem quadraticGeometricSequence_zero
    (R S : ℂ) :
    quadraticGeometricSequence R S 0 = 1 := by
  simp [quadraticGeometricSequence]

@[simp]
theorem quadraticGeometricSequence_one
    (R S : ℂ) :
    quadraticGeometricSequence R S 1 = R * S := by
  simp [quadraticGeometricSequence]

@[simp]
theorem quadraticGeometricSequence_neg_one
    (R S : ℂ) :
    quadraticGeometricSequence R S (-1) = R * S⁻¹ := by
  simp [quadraticGeometricSequence]

/-- Two nonzero quadratic--geometric sequences which agree at the two
neighbouring indices `1` and `-1` agree everywhere. -/
theorem quadraticGeometricSequence_eq_of_neighbors
    (R S R' S' : ℂ)
    (hR : R ≠ 0) (hS : S ≠ 0)
    (hS' : S' ≠ 0)
    (hone :
      quadraticGeometricSequence R S 1 =
        quadraticGeometricSequence R' S' 1)
    (hneg :
      quadraticGeometricSequence R S (-1) =
        quadraticGeometricSequence R' S' (-1)) :
    ∀ k : ℤ,
      quadraticGeometricSequence R S k =
        quadraticGeometricSequence R' S' k := by
  simp only [quadraticGeometricSequence_one] at hone
  simp only [quadraticGeometricSequence_neg_one] at hneg
  have hRsq : R ^ 2 = R' ^ 2 := by
    calc
      R ^ 2 =
          (R * S) * (R * S⁻¹) := by
            calc
              R ^ 2 =
                  R ^ 2 * (S * S⁻¹) := by
                    rw [mul_inv_cancel₀ hS, mul_one]
              _ = (R * S) * (R * S⁻¹) := by ring
      _ = (R' * S') * (R' * S'⁻¹) := by rw [hone, hneg]
      _ = R' ^ 2 := by
            calc
              (R' * S') * (R' * S'⁻¹) =
                  R' ^ 2 * (S' * S'⁻¹) := by ring
              _ = R' ^ 2 := by
                    rw [mul_inv_cancel₀ hS', mul_one]
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hRsq) with hsame | hsign
  · have hSsame : S = S' := by
      apply mul_left_cancel₀ hR
      rw [hone, hsame]
    intro k
    rw [hsame, hSsame]
  · have hSsign : S = -S' := by
      apply mul_left_cancel₀ hR
      rw [hone, hsign]
      ring
    intro k
    unfold quadraticGeometricSequence
    rw [hsign, hSsign]
    rcases Int.even_or_odd k with hk | hk
    · have hksq : Even (k ^ 2) := by
        simpa only [pow_two] using hk.mul_right k
      rw [hksq.neg_zpow, hk.neg_zpow]
    · have hksq : Odd (k ^ 2) := by
        exact hk.pow
      rw [hksq.neg_zpow, hk.neg_zpow]
      ring

end HGAS.Modular
