import HGAS.Lyapunov.ExactGridPositivityComputability

/-!
# Dimension-independent sparse polynomial syntax

Exponent vectors and vector fields are lists. The dimension is explicit
data, and shape validation requires exactly that many coordinates.
Decoding pads missing entries with zero only to remain total; malformed
inputs will be rejected by the language checker. Repeated monomials and
cancelling rational coefficients retain the existing polynomial semantics.
-/

namespace Stability

open HGAS

abbrev RawExponentCode := List ℕ
abbrev RawPolynomialCode := List (RawExponentCode × RationalCode)
abbrev RawPolynomialFieldCode := List RawPolynomialCode

namespace RawExponentCode

def toFixed (n : ℕ) (e : RawExponentCode) : ExponentCode n := fun i ↦ e.getD i 0

def ofFixed {n : ℕ} (e : ExponentCode n) : RawExponentCode := List.ofFn e

@[simp]
theorem getD_ofFixed {n : ℕ} (e : ExponentCode n) (i : Fin n) :
    (ofFixed e).getD i 0 = e i := by
  simp [ofFixed, List.getD_eq_getElem?_getD, i.isLt]

@[simp]
theorem toFixed_ofFixed {n : ℕ} (e : ExponentCode n) : toFixed n (ofFixed e) = e := by
  funext i
  simp [toFixed, ofFixed, List.getD_eq_getElem?_getD, i.isLt]

theorem ofFixed_injective {n : ℕ} : Function.Injective (ofFixed : ExponentCode n → _) :=
  List.ofFn_injective

theorem ofFixed_toFixed {n : ℕ} (e : RawExponentCode) (he : e.length = n) :
    ofFixed (toFixed n e) = e := by
  subst n
  apply List.ext_getElem
  · simp [ofFixed]
  · intro i hi hj
    simp [ofFixed, toFixed, List.getD_eq_getElem?_getD, hj]

end RawExponentCode

namespace RawPolynomialCode

def toFixed (n : ℕ) (p : RawPolynomialCode) : PolynomialCode n :=
  p.map fun t ↦ (RawExponentCode.toFixed n t.1, t.2)

def ofFixed {n : ℕ} (p : PolynomialCode n) : RawPolynomialCode :=
  p.map fun t ↦ (RawExponentCode.ofFixed t.1, t.2)

/-- Syntactic dimension validation; no coefficient or degree restriction
is imposed, so zero coefficients and duplicate cancellation remain valid. -/
def wellFormed (n : ℕ) (p : RawPolynomialCode) : Bool :=
  p.all fun t ↦ t.1.length == n

@[simp]
theorem toFixed_ofFixed {n : ℕ} (p : PolynomialCode n) : toFixed n (ofFixed p) = p := by
  simp [toFixed, ofFixed, List.map_map, Function.comp_def]

@[simp]
theorem wellFormed_ofFixed {n : ℕ} (p : PolynomialCode n) : wellFormed n (ofFixed p) = true := by
  simp [wellFormed, ofFixed, RawExponentCode.ofFixed]

theorem ofFixed_toFixed {n : ℕ} (p : RawPolynomialCode) (hp : wellFormed n p = true) :
    ofFixed (toFixed n p) = p := by
  simp only [wellFormed, List.all_eq_true, beq_iff_eq] at hp
  rw [ofFixed, toFixed, List.map_map]
  induction p with
  | nil => rfl
  | cons t p ih =>
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨Prod.ext (RawExponentCode.ofFixed_toFixed t.1
        (hp t (List.mem_cons_self))) rfl,
        ih (fun u hu ↦ hp u (List.mem_cons_of_mem _ hu))⟩

/-- Collect the coefficient of an entire raw exponent list, so duplicate
terms may cancel before homogeneity is tested. -/
def coefficient (e : RawExponentCode) (p : RawPolynomialCode) : RationalCode :=
  p.foldr (fun t acc ↦ if t.1 = e then RationalCode.add t.2 acc else acc) RationalCode.zero

def homogeneous (d : ℕ) (p : RawPolynomialCode) : Bool :=
  (p.map Prod.fst).all fun e ↦
    RationalCode.equal (coefficient e p) RationalCode.zero || decide (e.sum = d)

@[simp]
theorem coefficient_ofFixed {n : ℕ} (e : ExponentCode n) (p : PolynomialCode n) :
    coefficient (RawExponentCode.ofFixed e) (ofFixed p) = PolynomialCode.coefficient e p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
      simp only [coefficient, ofFixed, List.map_cons, List.foldr_cons] at ih ⊢
      simp only [RawExponentCode.ofFixed_injective.eq_iff, ih,
        PolynomialCode.coefficient, List.foldr_cons]

@[simp]
theorem homogeneous_ofFixed {n : ℕ} (d : ℕ) (p : PolynomialCode n) :
    homogeneous d (ofFixed p) = PolynomialCode.homogeneous d p := by
  unfold homogeneous PolynomialCode.homogeneous PolynomialCode.exponents
  rw [show (ofFixed p).map Prod.fst = p.map (fun t ↦ RawExponentCode.ofFixed t.1) by
    simp [ofFixed, List.map_map]]
  simp only [List.all_map, Function.comp_def, coefficient_ofFixed]
  rfl

end RawPolynomialCode

namespace RawPolynomialFieldCode

def toFixed (n : ℕ) (F : RawPolynomialFieldCode) : PolynomialFieldCode n :=
  fun i ↦ RawPolynomialCode.toFixed n (F.getD i [])

def ofFixed {n : ℕ} (F : PolynomialFieldCode n) : RawPolynomialFieldCode :=
  List.ofFn fun i ↦ RawPolynomialCode.ofFixed (F i)

@[simp]
theorem getD_ofFixed {n : ℕ} (F : PolynomialFieldCode n) (i : Fin n) :
    (ofFixed F).getD i [] = RawPolynomialCode.ofFixed (F i) := by
  simp [ofFixed, List.getD_eq_getElem?_getD, i.isLt]

def wellFormed (n : ℕ) (F : RawPolynomialFieldCode) : Bool :=
  (F.length == n) && F.all (RawPolynomialCode.wellFormed n)

@[simp]
theorem toFixed_ofFixed {n : ℕ} (F : PolynomialFieldCode n) : toFixed n (ofFixed F) = F := by
  funext i
  simp [toFixed, ofFixed, List.getD_eq_getElem?_getD, i.isLt]

@[simp]
theorem wellFormed_ofFixed {n : ℕ} (F : PolynomialFieldCode n) :
    wellFormed n (ofFixed F) = true := by
  simp [wellFormed, ofFixed]

theorem ofFixed_toFixed {n : ℕ} (F : RawPolynomialFieldCode)
    (hF : wellFormed n F = true) : ofFixed (toFixed n F) = F := by
  simp only [wellFormed, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hF
  apply List.ext_getElem
  · simp [ofFixed, hF.1]
  · intro i hi hj
    have hin : i < n := by simpa [ofFixed] using hi
    simp only [ofFixed, List.getElem_ofFn, toFixed, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hj, Option.getD_some]
    exact RawPolynomialCode.ofFixed_toFixed (F[i]) (hF.2 _ (List.getElem_mem hj))

end RawPolynomialFieldCode

end Stability
