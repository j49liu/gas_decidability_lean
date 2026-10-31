import Stability.Computability.RawPolynomialCode

/-!
# Sparse arithmetic with dimension as data

All coordinate loops below range over the input natural number. Their
commutation lemmas identify the resulting lists with the existing
fixed-dimension arithmetic, without changing the old polynomial semantics.
-/

namespace Stability

open HGAS

theorem map_range_eq_ofFn {α : Type*} (n : ℕ) (f : ℕ → α) :
    (List.range n).map f = List.ofFn (fun i : Fin n ↦ f i) := by
  apply List.ext_getElem <;> simp

namespace RawExponentCode

def zero (n : ℕ) : RawExponentCode := (List.range n).map fun _ ↦ 0

def add (n : ℕ) (e f : RawExponentCode) : RawExponentCode :=
  (List.range n).map fun i ↦ e.getD i 0 + f.getD i 0

def predAt (n i : ℕ) (e : RawExponentCode) : RawExponentCode :=
  (List.range n).map fun j ↦ if j = i then e.getD j 0 - 1 else e.getD j 0

def variablePower (n i power : ℕ) : RawExponentCode :=
  (List.range n).map fun j ↦ if j = i then power else 0

@[simp]
theorem zero_eq_ofFixed (n : ℕ) : zero n = ofFixed (ExponentCode.zero (n := n)) := by
  rw [zero, map_range_eq_ofFn]
  rfl

@[simp]
theorem add_ofFixed {n : ℕ} (e f : ExponentCode n) :
    add n (ofFixed e) (ofFixed f) = ofFixed (ExponentCode.add e f) := by
  rw [add, map_range_eq_ofFn]
  apply congrArg List.ofFn
  funext i
  simp only [getD_ofFixed, ExponentCode.add]

@[simp]
theorem predAt_ofFixed {n : ℕ} (i : Fin n) (e : ExponentCode n) :
    predAt n i (ofFixed e) = ofFixed (ExponentCode.predAt i e) := by
  rw [predAt, map_range_eq_ofFn]
  apply congrArg List.ofFn
  funext j
  simp only [getD_ofFixed, ExponentCode.predAt, Fin.ext_iff]

@[simp]
theorem variable_one_eq_ofFixed {n : ℕ} (i : Fin n) :
    variablePower n i 1 = ofFixed (ExponentCode.singleVariable i) := by
  rw [variablePower, map_range_eq_ofFn]
  apply congrArg List.ofFn
  funext j
  simp [ExponentCode.singleVariable, Fin.ext_iff]

@[simp]
theorem variable_two_eq_ofFixed {n : ℕ} (i : Fin n) :
    variablePower n i 2 = ofFixed (ExponentCode.squareVariable i) := by
  rw [variablePower, map_range_eq_ofFn]
  apply congrArg List.ofFn
  funext j
  simp [ExponentCode.squareVariable, Fin.ext_iff]

end RawExponentCode

namespace RawPolynomialCode

def constant (n : ℕ) (a : RationalCode) : RawPolynomialCode :=
  [(RawExponentCode.zero n, a)]

def neg (p : RawPolynomialCode) : RawPolynomialCode :=
  p.map fun t ↦ (t.1, RationalCode.neg t.2)

def mulByTerm (n : ℕ) (t : RawExponentCode × RationalCode)
    (p : RawPolynomialCode) : RawPolynomialCode :=
  p.map fun u ↦ (RawExponentCode.add n t.1 u.1, RationalCode.mul t.2 u.2)

def mul (n : ℕ) (p q : RawPolynomialCode) : RawPolynomialCode :=
  p.flatMap fun t ↦ mulByTerm n t q

def pderivTerm (n i : ℕ) (t : RawExponentCode × RationalCode) : RawPolynomialCode :=
  if t.1.getD i 0 = 0 then [] else
    [(RawExponentCode.predAt n i t.1, RationalCode.mul t.2
      (RationalCode.ofNat (t.1.getD i 0)))]

def pderiv (n i : ℕ) (p : RawPolynomialCode) : RawPolynomialCode :=
  p.flatMap (pderivTerm n i)

def rhoCode (n : ℕ) : RawPolynomialCode :=
  (List.range n).map fun i ↦ (RawExponentCode.variablePower n i 2, RationalCode.one)

def varCode (n i : ℕ) : RawPolynomialCode :=
  [(RawExponentCode.variablePower n i 1, RationalCode.one)]

def gradientDotField (n : ℕ) (p : RawPolynomialCode)
    (F : RawPolynomialFieldCode) : RawPolynomialCode :=
  (List.range n).flatMap fun i ↦ mul n (pderiv n i p) (F.getD i [])

def radialDotField (n : ℕ) (F : RawPolynomialFieldCode) : RawPolynomialCode :=
  (List.range n).flatMap fun i ↦ mul n (varCode n i) (F.getD i [])

def rationalLyapunovNumerator (n : ℕ) (F : RawPolynomialFieldCode)
    (p : RawPolynomialCode) (r : ℕ) : RawPolynomialCode :=
  neg (mul n (rhoCode n) (gradientDotField n p F)) ++
    mul n (mul n (constant n (RationalCode.ofNat (2 * r))) p) (radialDotField n F)

@[simp]
theorem ofFixed_append {n : ℕ} (p q : PolynomialCode n) :
    ofFixed (p ++ q) = ofFixed p ++ ofFixed q := List.map_append

@[simp]
theorem constant_eq_ofFixed (n : ℕ) (a : RationalCode) :
    constant n a = ofFixed (PolynomialCode.constant (n := n) a) := by
  simp [constant, PolynomialCode.constant, ofFixed]

@[simp]
theorem neg_ofFixed {n : ℕ} (p : PolynomialCode n) :
    neg (ofFixed p) = ofFixed (PolynomialCode.neg p) := by
  simp [neg, ofFixed, PolynomialCode.neg, List.map_map]

@[simp]
theorem mulByTerm_ofFixed {n : ℕ} (t : ExponentCode n × RationalCode)
    (p : PolynomialCode n) :
    mulByTerm n (RawExponentCode.ofFixed t.1, t.2) (ofFixed p) =
      ofFixed (PolynomialCode.mulByTerm t p) := by
  simp [mulByTerm, ofFixed, PolynomialCode.mulByTerm, PolynomialCode.mulTerm,
    List.map_map]

@[simp]
theorem mul_ofFixed {n : ℕ} (p q : PolynomialCode n) :
    mul n (ofFixed p) (ofFixed q) = ofFixed (PolynomialCode.mul p q) := by
  induction p with
  | nil => rfl
  | cons t p ih =>
      change mulByTerm n (RawExponentCode.ofFixed t.1, t.2) (ofFixed q) ++
        mul n (ofFixed p) (ofFixed q) = ofFixed (PolynomialCode.mul (t :: p) q)
      rw [mulByTerm_ofFixed, ih, PolynomialCode.mul, ofFixed_append]

@[simp]
theorem pderivTerm_ofFixed {n : ℕ} (i : Fin n) (t : ExponentCode n × RationalCode) :
    pderivTerm n i (RawExponentCode.ofFixed t.1, t.2) =
      ofFixed (PolynomialCode.pderivTerm i t) := by
  simp only [pderivTerm, RawExponentCode.getD_ofFixed, PolynomialCode.pderivTerm]
  split <;> simp [ofFixed]

@[simp]
theorem pderiv_ofFixed {n : ℕ} (i : Fin n) (p : PolynomialCode n) :
    pderiv n i (ofFixed p) = ofFixed (PolynomialCode.pderiv i p) := by
  induction p with
  | nil => rfl
  | cons t p ih =>
      change pderivTerm n i (RawExponentCode.ofFixed t.1, t.2) ++
        pderiv n i (ofFixed p) =
          ofFixed (PolynomialCode.pderivTerm i t ++ PolynomialCode.pderiv i p)
      rw [pderivTerm_ofFixed, ih, ofFixed_append]

@[simp]
theorem rhoCode_eq_ofFixed (n : ℕ) : rhoCode n = ofFixed (PolynomialCode.rhoCode n) := by
  rw [rhoCode, map_range_eq_ofFn]
  simp [ofFixed, PolynomialCode.rhoCode, Function.comp_def]

@[simp]
theorem varCode_eq_ofFixed {n : ℕ} (i : Fin n) :
    varCode n i = ofFixed (PolynomialCode.varCode i) := by
  simp [varCode, ofFixed, PolynomialCode.varCode]

private theorem sumCodes_eq_flatten {n : ℕ} (ps : List (PolynomialCode n)) :
    PolynomialCode.sumCodes ps = ps.flatten := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      change p ++ PolynomialCode.sumCodes ps = p ++ ps.flatten
      rw [ih]

@[simp]
theorem gradientDotField_ofFixed {n : ℕ} (p : PolynomialCode n) (F : PolynomialFieldCode n) :
    gradientDotField n (ofFixed p) (RawPolynomialFieldCode.ofFixed F) =
      ofFixed (PolynomialCode.gradientDotField p F) := by
  simp only [gradientDotField, List.flatMap, map_range_eq_ofFn,
    RawPolynomialFieldCode.getD_ofFixed, pderiv_ofFixed, mul_ofFixed,
    PolynomialCode.gradientDotField, sumCodes_eq_flatten]
  simp [ofFixed, List.map_flatten, Function.comp_def]

@[simp]
theorem radialDotField_ofFixed {n : ℕ} (F : PolynomialFieldCode n) :
    radialDotField n (RawPolynomialFieldCode.ofFixed F) =
      ofFixed (PolynomialCode.radialDotField F) := by
  simp only [radialDotField, List.flatMap, map_range_eq_ofFn,
    RawPolynomialFieldCode.getD_ofFixed, varCode_eq_ofFixed, mul_ofFixed,
    PolynomialCode.radialDotField, sumCodes_eq_flatten]
  simp [ofFixed, List.map_flatten, Function.comp_def]

@[simp]
theorem rationalLyapunovNumerator_ofFixed {n : ℕ} (F : PolynomialFieldCode n)
    (p : PolynomialCode n) (r : ℕ) :
    rationalLyapunovNumerator n (RawPolynomialFieldCode.ofFixed F) (ofFixed p) r =
      ofFixed (PolynomialCode.rationalLyapunovNumerator F p r) := by
  simp [rationalLyapunovNumerator, PolynomialCode.rationalLyapunovNumerator,
    PolynomialCode.add]

end RawPolynomialCode

end Stability
