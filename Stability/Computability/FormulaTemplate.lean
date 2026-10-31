import Stability.Computability.PolynomialCodeOperations
import HGAS.Lyapunov.ExactGridPositivityComputability
import Stability.Simulation.ClockedMonitorFormula

/-!
# Fixed formula trees with input-dependent rational constants

Only constant leaves vary with the input. This is the shape of the actual
register monitor: loading registers does not change its formula trees.
Primitive recursiveness is required of these explicit constant functions,
not postulated for any polynomial compiler or simulation semantics.
-/

namespace Stability

open HGAS Simulation

/-- A fixed absolute-value syntax tree whose constant leaves read input data. -/
inductive FormulaTemplate (α σ : Type*) where
  | coordinate : σ → FormulaTemplate α σ
  | constant : (α → RationalCode) → FormulaTemplate α σ
  | add : FormulaTemplate α σ → FormulaTemplate α σ → FormulaTemplate α σ
  | mul : FormulaTemplate α σ → FormulaTemplate α σ → FormulaTemplate α σ
  | abs : FormulaTemplate α σ → FormulaTemplate α σ

namespace FormulaTemplate

variable {α σ τ : Type*}

/-- Substitute the input in every rational constant leaf. -/
def instantiate : FormulaTemplate α σ → α → AbsFormula σ
  | .coordinate i, _ => .coordinate i
  | .constant c, x => .constant (RationalCode.decode (c x))
  | .add e f, x => .add (instantiate e x) (instantiate f x)
  | .mul e f, x => .mul (instantiate e x) (instantiate f x)
  | .abs e, x => .abs (instantiate e x)

def ofFormula : AbsFormula σ → FormulaTemplate α σ
  | .coordinate i => .coordinate i
  | .constant c => .constant (fun _ ↦ RationalCode.encode c)
  | .add e f => .add (ofFormula e) (ofFormula f)
  | .mul e f => .mul (ofFormula e) (ofFormula f)
  | .abs e => .abs (ofFormula e)

@[simp]
theorem instantiate_ofFormula (e : AbsFormula σ) (x : α) :
    (ofFormula e).instantiate x = e := by
  induction e <;> simp_all [ofFormula, instantiate]

def mapCoordinates (r : σ → τ) : FormulaTemplate α σ → FormulaTemplate α τ
  | .coordinate i => .coordinate (r i)
  | .constant c => .constant c
  | .add e f => .add (mapCoordinates r e) (mapCoordinates r f)
  | .mul e f => .mul (mapCoordinates r e) (mapCoordinates r f)
  | .abs e => .abs (mapCoordinates r e)

@[simp]
theorem instantiate_mapCoordinates (r : σ → τ) (e : FormulaTemplate α σ) (x : α) :
    (mapCoordinates r e).instantiate x = AbsFormula.mapCoordinates r (e.instantiate x) := by
  induction e <;> simp_all [mapCoordinates, instantiate, AbsFormula.mapCoordinates]

/-- Every absolute-value occurrence allocates one root, independently
of whether some input makes its argument vanish. -/
def rootCount : FormulaTemplate α σ → ℕ
  | .coordinate _ | .constant _ => 0
  | .add e f | .mul e f => rootCount e + rootCount f
  | .abs e => rootCount e + 1

@[simp]
theorem radicalCount_instantiate (e : FormulaTemplate α σ) (x : α) :
    AbsFormula.radicalCount (e.instantiate x) = e.rootCount := by
  induction e <;> simp_all [instantiate, rootCount, AbsFormula.radicalCount]

theorem eraseConstants_instantiate (e : FormulaTemplate α σ) (x y : α) :
    AbsFormula.eraseConstants (e.instantiate x) =
      AbsFormula.eraseConstants (e.instantiate y) := by
  induction e <;> simp_all [instantiate, AbsFormula.eraseConstants]

/-- The only effectivity condition concerns the input functions at
constant leaves. Fixed formulas satisfy it automatically. -/
def PrimitiveConstants [Primcodable α] : FormulaTemplate α σ → Prop
  | .coordinate _ => True
  | .constant c => Primrec c
  | .add e f | .mul e f => PrimitiveConstants e ∧ PrimitiveConstants f
  | .abs e => PrimitiveConstants e

theorem primitiveConstants_ofFormula [Primcodable α] (e : AbsFormula σ) :
    PrimitiveConstants (ofFormula (α := α) e) := by
  induction e <;> simp_all [PrimitiveConstants, ofFormula, Primrec.const]

theorem PrimitiveConstants.mapCoordinates [Primcodable α] {e : FormulaTemplate α σ}
    (he : PrimitiveConstants e) (r : σ → τ) : PrimitiveConstants (e.mapCoordinates r) := by
  induction e <;> simp_all [PrimitiveConstants, FormulaTemplate.mapCoordinates]

def sub (e f : FormulaTemplate α σ) : FormulaTemplate α σ :=
  .add e (.mul (ofFormula (.constant (-1))) f)

def pow (e : FormulaTemplate α σ) : ℕ → FormulaTemplate α σ
  | 0 => ofFormula (.constant 1)
  | n + 1 => .mul (pow e n) e

@[simp]
theorem instantiate_sub (e f : FormulaTemplate α σ) (x : α) :
    (e.sub f).instantiate x = (e.instantiate x).sub (f.instantiate x) := by
  simp [sub, instantiate, AbsFormula.sub]

@[simp]
theorem instantiate_pow (e : FormulaTemplate α σ) (n : ℕ) (x : α) :
    (e.pow n).instantiate x = (e.instantiate x).pow n := by
  induction n <;> simp_all [pow, instantiate, AbsFormula.pow]

theorem PrimitiveConstants.sub [Primcodable α] {e f : FormulaTemplate α σ}
    (he : PrimitiveConstants e) (hf : PrimitiveConstants f) : PrimitiveConstants (e.sub f) :=
  ⟨he, primitiveConstants_ofFormula _, hf⟩

theorem PrimitiveConstants.pow [Primcodable α] {e : FormulaTemplate α σ}
    (he : PrimitiveConstants e) (n : ℕ) : PrimitiveConstants (e.pow n) := by
  induction n with
  | zero => exact primitiveConstants_ofFormula _
  | succ n ih => exact ⟨ih, he⟩

/-- Raw codes for the actual value and error majorants. -/
def majorantsCode {n : ℕ} (r : σ → Fin n) :
    FormulaTemplate α σ → α → PolynomialCode n × PolynomialCode n
  | .coordinate i, _ =>
      (PolynomialCode.add PolynomialCode.one (PolynomialCode.pow (PolynomialCode.varCode (r i)) 2),
        PolynomialCode.zero)
  | .constant c, x =>
      (PolynomialCode.constant (RationalCode.add RationalCode.one (RationalCode.abs (c x))),
        PolynomialCode.zero)
  | .add e f, x =>
      (PolynomialCode.add (majorantsCode r e x).1 (majorantsCode r f x).1,
        PolynomialCode.add (majorantsCode r e x).2 (majorantsCode r f x).2)
  | .mul e f, x =>
      (PolynomialCode.mul (majorantsCode r e x).1 (majorantsCode r f x).1,
        PolynomialCode.add
          (PolynomialCode.mul (majorantsCode r e x).2 (majorantsCode r f x).1)
          (PolynomialCode.mul (majorantsCode r e x).1 (majorantsCode r f x).2))
  | .abs e, x =>
      (PolynomialCode.add (majorantsCode r e x).1 PolynomialCode.one,
        PolynomialCode.add (majorantsCode r e x).2 PolynomialCode.one)

/-- Both stored majorants decode to the existing structural construction. -/
theorem decode_majorantsCode {n : ℕ} (r : σ → Fin n) (e : FormulaTemplate α σ) (x : α) :
    (PolynomialCode.decode (majorantsCode r e x).1,
      PolynomialCode.decode (majorantsCode r e x).2) =
      (MvPolynomial.rename r (AbsFormula.majorants (e.instantiate x)).1,
        MvPolynomial.rename r (AbsFormula.majorants (e.instantiate x)).2) := by
  induction e <;> simp_all [majorantsCode, instantiate, AbsFormula.majorants, Prod.ext_iff]

/-- Structural compilation of a fixed template is primitive recursive
in the input, with the coordinate map fixed as part of the compiler. -/
theorem majorantsCode_primrec [Primcodable α] {n : ℕ} (r : σ → Fin n)
    (e : FormulaTemplate α σ) (he : PrimitiveConstants e) : Primrec (majorantsCode r e) := by
  induction e with
  | coordinate i => exact Primrec.const _
  | constant c =>
    exact Primrec.pair (PolynomialCode.constant_primrec.comp
      (RationalCode.add_primrec.comp (Primrec.const RationalCode.one)
        (RationalCode.abs_primrec.comp he))) (Primrec.const _)
  | add e f ihE ihF =>
    have hE := ihE he.1
    have hF := ihF he.2
    exact Primrec.pair
      (PolynomialCode.add_primrec.comp (Primrec.fst.comp hE) (Primrec.fst.comp hF))
      (PolynomialCode.add_primrec.comp (Primrec.snd.comp hE) (Primrec.snd.comp hF))
  | mul e f ihE ihF =>
    have hE := ihE he.1
    have hF := ihF he.2
    exact Primrec.pair
      (PolynomialCode.mul_primrec.comp (Primrec.fst.comp hE) (Primrec.fst.comp hF))
      (PolynomialCode.add_primrec.comp
        (PolynomialCode.mul_primrec.comp (Primrec.snd.comp hE) (Primrec.fst.comp hF))
        (PolynomialCode.mul_primrec.comp (Primrec.fst.comp hE) (Primrec.snd.comp hF)))
  | abs e ih =>
    exact Primrec.pair
      (PolynomialCode.add_primrec.comp (Primrec.fst.comp (ih he)) (Primrec.const _))
      (PolynomialCode.add_primrec.comp (Primrec.snd.comp (ih he)) (Primrec.const _))

end FormulaTemplate

end Stability
