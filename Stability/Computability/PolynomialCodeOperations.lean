import HGAS.Foundation.PolynomialDifferentiationCode
import Mathlib.Algebra.MvPolynomial.Monad

/-!
# Effective substitution of rational sparse polynomials

Each input monomial is expanded using the actual coded substitution
polynomials. Decoding commutes with `MvPolynomial.bind₁`, including
noninjective substitutions, zero-dimensional spaces, and cancellation.
-/

namespace Stability.PolynomialCodeOperations

open HGAS

variable {n m : ℕ}

def product (ps : List (PolynomialCode n)) : PolynomialCode n :=
  ps.foldr PolynomialCode.mul PolynomialCode.one

@[simp]
theorem decode_product (ps : List (PolynomialCode n)) :
    PolynomialCode.decode (product ps) = (ps.map PolynomialCode.decode).prod := by
  induction ps with
  | nil => simp [product]
  | cons p ps ih =>
    change PolynomialCode.decode (PolynomialCode.mul p (product ps)) = _
    rw [PolynomialCode.decode_mul_code, ih]
    rfl

def substituteTerm (q : Fin n → PolynomialCode m)
    (t : ExponentCode n × RationalCode) : PolynomialCode m :=
  PolynomialCode.mul (PolynomialCode.constant t.2)
    (product (List.ofFn fun i ↦ PolynomialCode.pow (q i) (t.1 i)))

def substitute (q : Fin n → PolynomialCode m) (p : PolynomialCode n) : PolynomialCode m :=
  PolynomialCode.sumCodes (p.map (substituteTerm q))

@[simp]
theorem decode_substituteTerm (q : Fin n → PolynomialCode m)
    (t : ExponentCode n × RationalCode) :
    PolynomialCode.decode (substituteTerm q t) =
      MvPolynomial.bind₁ (fun i ↦ PolynomialCode.decode (q i)) (PolynomialCode.decodeTerm t) := by
  simp only [substituteTerm, PolynomialCode.decode_mul_code, PolynomialCode.decode_constant,
    decode_product, List.map_ofFn, List.prod_ofFn, Function.comp_apply,
    PolynomialCode.decode_pow_code,
    PolynomialCode.decodeTerm, MvPolynomial.bind₁_monomial]
  congr 1
  symm
  change (∏ i ∈ (ExponentCode.decode t.1).support,
    PolynomialCode.decode (q i) ^ ExponentCode.decode t.1 i) =
      ∏ i, PolynomialCode.decode (q i) ^ ExponentCode.decode t.1 i
  apply Finset.prod_subset (Finset.subset_univ _)
  intro i _ hi
  have hz : ExponentCode.decode t.1 i = 0 := Finsupp.notMem_support_iff.mp hi
  rw [hz, pow_zero]

/-- This equality identifies the executable substitution with the
actual polynomial algebra homomorphism, not only its evaluations. -/
@[simp]
theorem decode_substitute (q : Fin n → PolynomialCode m) (p : PolynomialCode n) :
    PolynomialCode.decode (substitute q p) =
      MvPolynomial.bind₁ (fun i ↦ PolynomialCode.decode (q i)) (PolynomialCode.decode p) := by
  induction p with
  | nil => simp [substitute, PolynomialCode.sumCodes]
  | cons t p ih =>
    change PolynomialCode.decode (PolynomialCode.add (substituteTerm q t) (substitute q p)) = _
    rw [PolynomialCode.decode_add_code, decode_substituteTerm, ih,
      PolynomialCode.decode_cons, map_add]

def rename (r : Fin n → Fin m) (p : PolynomialCode n) : PolynomialCode m :=
  substitute (fun i ↦ PolynomialCode.varCode (r i)) p

@[simp]
theorem decode_rename (r : Fin n → Fin m) (p : PolynomialCode n) :
    PolynomialCode.decode (rename r p) = MvPolynomial.rename r (PolynomialCode.decode p) := by
  simp only [rename, decode_substitute, PolynomialCode.decode_varCode]
  change MvPolynomial.bind₁ (MvPolynomial.X ∘ r) (PolynomialCode.decode p) = _
  rw [← MvPolynomial.bind₁_rename MvPolynomial.X r, MvPolynomial.bind₁_X_left]
  rfl

theorem product_primrec : Primrec (product : List (PolynomialCode n) → PolynomialCode n) :=
  Primrec.list_foldr Primrec.id (Primrec.const PolynomialCode.one)
    (PolynomialCode.mul_primrec.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂

theorem substituteTerm_primrec :
    Primrec₂ (substituteTerm : (Fin n → PolynomialCode m) →
      (ExponentCode n × RationalCode) → PolynomialCode m) := by
  apply PolynomialCode.mul_primrec.comp
    (PolynomialCode.constant_primrec.comp (Primrec.snd.comp Primrec.snd))
  apply product_primrec.comp
  apply Primrec.list_ofFn
  intro i
  exact PolynomialCode.pow_primrec.comp
    (Primrec.fin_app.comp Primrec.fst (Primrec.const i))
    (Primrec.fin_app.comp (Primrec.fst.comp Primrec.snd) (Primrec.const i))

theorem substitute_primrec :
    Primrec₂ (substitute : (Fin n → PolynomialCode m) → PolynomialCode n → PolynomialCode m) := by
  apply PolynomialCode.sumCodes_primrec.comp
  exact Primrec.list_map Primrec.snd
    (substituteTerm_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)

/-- A fixed coordinate map is a constant of the compiler; it need not
be supplied as an input or selected from the input polynomial. -/
theorem rename_primrec (r : Fin n → Fin m) : Primrec (rename r) :=
  substitute_primrec.comp (Primrec.const (fun i ↦ PolynomialCode.varCode (r i))) Primrec.id

end Stability.PolynomialCodeOperations
