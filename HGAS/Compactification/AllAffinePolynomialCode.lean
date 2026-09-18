import HGAS.Accumulator.PolynomialDegrees
import HGAS.Compactification.MixedCentralPolynomialCode
import Mathlib.Tactic

/-!
# The one-block all-affine mixed-central layout

Many polynomial sources begin in an ordinary affine space, with no
coordinates already constrained to compact sphere blocks.  They fit the
mixed-central compiler by using one affine block and zero compact blocks:

```
             Fin n → Fin 1 ⊕ Fin 0,   j ↦ Sum.inl 0.
```

For this layout, affine-block degree is exactly total monomial degree.
Consequently every ordinary raw degree bound supplies the
denominator-clearing bound expected by the mixed-central compiler.  The
compact-block tangency obligation is vacuous because `Fin 0` is empty.

These elementary facts are packaged here so concrete source compilers do
not repeatedly prove them.
-/

namespace HGAS

namespace MixedCentralPolynomialCode

/-- Put every source coordinate in one affine block and use no pre-existing
compact block. -/
def oneBlockAllAffineLayout (n : ℕ) :
    Fin n → Fin 1 ⊕ Fin 0 :=
  fun _ ↦ Sum.inl 0

@[simp]
theorem oneBlockAllAffineLayout_apply
    {n : ℕ} (j : Fin n) :
    oneBlockAllAffineLayout n j = Sum.inl 0 :=
  rfl

/-- In the unique affine block, block degree is total degree. -/
theorem affineBlockDegree_oneBlockAllAffineLayout
    {n : ℕ} (e : ExponentCode n) (b : Fin 1) :
    affineBlockDegree (oneBlockAllAffineLayout n) e b =
      ExponentCode.totalDegree e := by
  have hb : b = 0 := Subsingleton.elim _ _
  subst b
  simp [affineBlockDegree, oneBlockAllAffineLayout,
    ExponentCode.totalDegree, List.sum_ofFn]

/-- An ordinary raw degree bound supplies the exact all-affine
denominator-clearing premise. -/
theorem termsAffineBlockDegreeLE_oneBlockAllAffineLayout
    {n M : ℕ} {p : PolynomialCode n}
    (hp : PolynomialCode.TermsDegreeLE M p) :
    TermsAffineBlockDegreeLE
      (oneBlockAllAffineLayout n) M p := by
  intro t ht b
  rw [affineBlockDegree_oneBlockAllAffineLayout]
  exact hp t ht

/-- Fieldwise version of the preceding conversion. -/
theorem field_termsAffineBlockDegreeLE_oneBlockAllAffineLayout
    {n M : ℕ} {P : PolynomialFieldCode n}
    (hP : ∀ j, PolynomialCode.TermsDegreeLE M (P j)) :
    ∀ j,
      TermsAffineBlockDegreeLE
        (oneBlockAllAffineLayout n) M (P j) :=
  fun j ↦
    termsAffineBlockDegreeLE_oneBlockAllAffineLayout (hP j)

end MixedCentralPolynomialCode

end HGAS
