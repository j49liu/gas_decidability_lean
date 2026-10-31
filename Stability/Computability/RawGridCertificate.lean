import Stability.Computability.RawPolynomialArithmetic

/-!
# A dimension-input finite grid test

This is the literal finite rational checker, implemented with list
coordinates and a natural-number dimension. The comparison lemmas below
identify it with the established checker on well-shaped fixed-dimensional
codes; in particular the coefficient bound combines duplicate monomials.
-/

namespace Stability

open HGAS

namespace RawPolynomialCode

def evalMonomialCode (n : ℕ) (e : RawExponentCode) (x : List RationalCode) : RationalCode :=
  ((List.range n).map fun i ↦ RationalCode.pow (x.getD i RationalCode.zero)
    (e.getD i 0)).foldr RationalCode.mul RationalCode.one

def evalCode (n : ℕ) (p : RawPolynomialCode) (x : List RationalCode) : RationalCode :=
  p.foldr (fun t acc ↦ RationalCode.add
    (RationalCode.mul t.2 (evalMonomialCode n t.1 x)) acc) RationalCode.zero

def cubeAbsBoundCode (p : RawPolynomialCode) : RationalCode :=
  ((p.map Prod.fst).dedup.map fun e ↦ RationalCode.abs (coefficient e p)).foldr
    RationalCode.add RationalCode.zero

def cubeGradientBoundCode (n : ℕ) (p : RawPolynomialCode) : RationalCode :=
  ((List.range n).map fun i ↦ cubeAbsBoundCode (pderiv n i p)).foldr
    RationalCode.add RationalCode.zero

@[simp]
theorem evalMonomialCode_ofFixed {n : ℕ} (e : ExponentCode n) (x : Fin n → RationalCode) :
    evalMonomialCode n (RawExponentCode.ofFixed e) (List.ofFn x) =
      PolynomialCode.evalMonomialCode e x := by
  rw [evalMonomialCode, map_range_eq_ofFn]
  simp only [RawExponentCode.ofFixed, List.getD_eq_getElem?_getD,
    List.getElem?_ofFn, Fin.isLt, ↓reduceDIte, Option.getD_some]
  rfl

@[simp]
theorem evalCode_ofFixed {n : ℕ} (p : PolynomialCode n) (x : Fin n → RationalCode) :
    evalCode n (ofFixed p) (List.ofFn x) = PolynomialCode.evalCode p x := by
  induction p with
  | nil => rfl
  | cons t p ih =>
      change RationalCode.add
        (RationalCode.mul t.2 (evalMonomialCode n (RawExponentCode.ofFixed t.1)
          (List.ofFn x))) (evalCode n (ofFixed p) (List.ofFn x)) = _
      rw [evalMonomialCode_ofFixed, ih]
      rfl

@[simp]
theorem cubeAbsBoundCode_ofFixed {n : ℕ} (p : PolynomialCode n) :
    cubeAbsBoundCode (ofFixed p) = PolynomialCode.cubeAbsBoundCode p := by
  have hexp : (ofFixed p).map Prod.fst =
      (p.map Prod.fst).map RawExponentCode.ofFixed := by
    simp [ofFixed, List.map_map]
  rw [cubeAbsBoundCode, hexp,
    List.dedup_map_of_injective RawExponentCode.ofFixed_injective]
  simp only [List.map_map, Function.comp_def, coefficient_ofFixed]
  rfl

@[simp]
theorem cubeGradientBoundCode_ofFixed {n : ℕ} (p : PolynomialCode n) :
    cubeGradientBoundCode n (ofFixed p) = PolynomialCode.cubeGradientBoundCode p := by
  rw [cubeGradientBoundCode, map_range_eq_ofFn]
  simp only [pderiv_ofFixed, cubeAbsBoundCode_ofFixed]
  rfl

end RawPolynomialCode

namespace RawGridCertificate

open ExactGridPositivity

def gridPointCode (n m : ℕ) (point : List ℕ) : List RationalCode :=
  (List.range n).map fun i ↦ ExactGridPositivity.gridCoordinateCode m (point.getD i 0)

def marginCode (n : ℕ) (p : RawPolynomialCode) (m : ℕ) : RationalCode :=
  RationalCode.mul (RawPolynomialCode.cubeGradientBoundCode n p) (RationalCode.unitFraction m)

def checkGridPoint (n : ℕ) (p : RawPolynomialCode) (m : ℕ) (point : List ℕ) : Bool :=
  !isBoundaryIndexPoint m point || RationalCode.lt (marginCode n p m)
    (RawPolynomialCode.evalCode n p (gridPointCode n m point))

def checkStrictPositiveOnSupSphere (n : ℕ) (p : RawPolynomialCode) (m : ℕ) : Bool :=
  decide (0 < m) && (gridIndexPoints n m).all (checkGridPoint n p m)

@[simp]
theorem gridPointCode_eq_ofFn (n m : ℕ) (point : List ℕ) :
    gridPointCode n m point = List.ofFn (ExactGridPositivity.gridPointCode n m point) :=
  map_range_eq_ofFn _ _

@[simp]
theorem marginCode_ofFixed {n : ℕ} (p : PolynomialCode n) (m : ℕ) :
    marginCode n (RawPolynomialCode.ofFixed p) m = ExactGridPositivity.marginCode p m := by
  simp only [marginCode, RawPolynomialCode.cubeGradientBoundCode_ofFixed]
  rfl

@[simp]
theorem checkGridPoint_ofFixed {n : ℕ} (p : PolynomialCode n) (m : ℕ) (point : List ℕ) :
    checkGridPoint n (RawPolynomialCode.ofFixed p) m point =
      ExactGridPositivity.checkGridPoint p m point := by
  simp only [checkGridPoint, marginCode_ofFixed, gridPointCode_eq_ofFn,
    RawPolynomialCode.evalCode_ofFixed]
  rfl

@[simp]
theorem checkStrictPositiveOnSupSphere_ofFixed {n : ℕ} (p : PolynomialCode n) (m : ℕ) :
    checkStrictPositiveOnSupSphere n (RawPolynomialCode.ofFixed p) m =
      ExactGridPositivity.checkStrictPositiveOnSupSphere p m := by
  have hpoint : checkGridPoint n (RawPolynomialCode.ofFixed p) m =
      ExactGridPositivity.checkGridPoint p m :=
    funext fun point ↦ checkGridPoint_ofFixed p m point
  rw [checkStrictPositiveOnSupSphere, hpoint]
  rfl

end RawGridCertificate

end Stability
