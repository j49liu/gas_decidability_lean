import Stability.Computability.PolynomialLAS

/-!
# Exact-degree polynomial stability languages

The bounded-degree languages `PGASQ` and `PLASQ` are preserved. The languages
below additionally require that at least one decoded coordinate attain the
degree bound. Degree is measured after cancellation of duplicate monomials,
so it depends on the polynomial and not on its sparse representation.
-/

namespace Stability

open HGAS

/-- A polynomial vector field has exact degree `d` when every coordinate
has degree at most `d` and one coordinate has degree equal to `d`. -/
def PolynomialFieldExactDegree (n d : ℕ) (F : PolynomialFieldCode n) : Prop :=
  (∀ i : Fin n, (PolynomialCode.decode (F i)).totalDegree ≤ d) ∧
    ∃ i : Fin n, (PolynomialCode.decode (F i)).totalDegree = d

/-- GAS of rational polynomial vector fields of exact decoded degree `d`. -/
def PGASExactQ (n d : ℕ) (F : PolynomialFieldCode n) : Prop :=
  PolynomialFieldExactDegree n d F ∧
    PolynomialFieldCode.realize F 0 = 0 ∧
    GloballyAsymptoticallyStable (PolynomialFieldCode.realize F) 0

/-- LAS of rational polynomial vector fields of exact decoded degree `d`. -/
def PLASExactQ (n d : ℕ) (F : PolynomialFieldCode n) : Prop :=
  PolynomialFieldExactDegree n d F ∧
    PolynomialFieldCode.realize F 0 = 0 ∧
    LocallyAsymptoticallyStable (PolynomialFieldCode.realize F) 0

theorem polynomialFieldExactDegree_iff_of_decode_eq
    {n d : ℕ} {F G : PolynomialFieldCode n}
    (h : ∀ i, PolynomialCode.decode (F i) = PolynomialCode.decode (G i)) :
    PolynomialFieldExactDegree n d F ↔ PolynomialFieldExactDegree n d G := by
  simp only [PolynomialFieldExactDegree, h]

theorem pgasExactQ_iff_of_decode_eq
    {n d : ℕ} {F G : PolynomialFieldCode n}
    (h : ∀ i, PolynomialCode.decode (F i) = PolynomialCode.decode (G i)) :
    PGASExactQ n d F ↔ PGASExactQ n d G := by
  have hrealize : PolynomialFieldCode.realize F = PolynomialFieldCode.realize G := by
    funext x i
    simp only [PolynomialFieldCode.realize_apply, h]
  simp only [PGASExactQ, polynomialFieldExactDegree_iff_of_decode_eq h, hrealize]

theorem plasExactQ_iff_of_decode_eq
    {n d : ℕ} {F G : PolynomialFieldCode n}
    (h : ∀ i, PolynomialCode.decode (F i) = PolynomialCode.decode (G i)) :
    PLASExactQ n d F ↔ PLASExactQ n d G := by
  have hrealize : PolynomialFieldCode.realize F = PolynomialFieldCode.realize G := by
    funext x i
    simp only [PolynomialFieldCode.realize_apply, h]
  simp only [PLASExactQ, polynomialFieldExactDegree_iff_of_decode_eq h, hrealize]

theorem pgasQ_of_pgasExactQ {n d : ℕ} {F : PolynomialFieldCode n}
    (h : PGASExactQ n d F) : PGASQ n d F :=
  ⟨h.1.1, h.2⟩

theorem plasQ_of_plasExactQ {n d : ℕ} {F : PolynomialFieldCode n}
    (h : PLASExactQ n d F) : PLASQ n d F :=
  ⟨h.1.1, h.2⟩

end Stability
