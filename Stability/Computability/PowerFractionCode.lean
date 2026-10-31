import Stability.Computability.PolynomialCodeOperations
import Stability.Simulation.PowerFraction

/-!
# Sparse codes for common-denominator power fractions

The operations preserve the stored numerator and exponent of the actual
fraction construction. No rational cancellation or semantic normalization
is used.
-/

namespace Stability

open HGAS Simulation

abbrev PowerFractionCode (n : ℕ) := PolynomialCode n × ℕ

namespace PowerFractionCode

variable {n : ℕ}

noncomputable def decode (f : PowerFractionCode n) : PowerFraction (Fin n) :=
  ⟨PolynomialCode.decode f.1, f.2⟩

def ofPolynomial (p : PolynomialCode n) : PowerFractionCode n := (p, 0)

def add (L : PolynomialCode n) (f g : PowerFractionCode n) : PowerFractionCode n :=
  (PolynomialCode.add (PolynomialCode.mul f.1 (PolynomialCode.pow L g.2))
    (PolynomialCode.mul g.1 (PolynomialCode.pow L f.2)), f.2 + g.2)

def mul (f g : PowerFractionCode n) : PowerFractionCode n :=
  (PolynomialCode.mul f.1 g.1, f.2 + g.2)

def smoothingRadicand (L : PolynomialCode n) (f : PowerFractionCode n) : PolynomialCode n :=
  PolynomialCode.add
    (PolynomialCode.mul (PolynomialCode.pow f.1 2) (PolynomialCode.pow L 2))
    (PolynomialCode.pow L (2 * f.2))

@[simp]
theorem decode_ofPolynomial (p : PolynomialCode n) :
    decode (ofPolynomial p) = PowerFraction.ofPolynomial (PolynomialCode.decode p) := rfl

@[simp]
theorem decode_add (L : PolynomialCode n) (f g : PowerFractionCode n) :
    decode (add L f g) = PowerFraction.add (PolynomialCode.decode L) (decode f) (decode g) := by
  simp [decode, add, PowerFraction.add]

@[simp]
theorem decode_mul (f g : PowerFractionCode n) :
    decode (mul f g) = PowerFraction.mul (decode f) (decode g) := by
  simp [decode, mul, PowerFraction.mul]

@[simp]
theorem decode_smoothingRadicand (L : PolynomialCode n) (f : PowerFractionCode n) :
    PolynomialCode.decode (smoothingRadicand L f) =
      PowerFraction.smoothingRadicand (PolynomialCode.decode L) (decode f) := by
  simp [smoothingRadicand, decode, PowerFraction.smoothingRadicand]

attribute [local fun_prop] Primrec Primrec.id Primrec.fst Primrec.snd Primrec.const Primrec.pair
attribute [local fun_prop] Primrec.comp

@[local fun_prop] private theorem polynomialAdd_primrec :
    Primrec (fun q : PolynomialCode n × PolynomialCode n ↦ PolynomialCode.add q.1 q.2) :=
  PolynomialCode.add_primrec

@[local fun_prop] private theorem polynomialMul_primrec :
    Primrec (fun q : PolynomialCode n × PolynomialCode n ↦ PolynomialCode.mul q.1 q.2) :=
  PolynomialCode.mul_primrec

@[local fun_prop] private theorem polynomialPow_primrec :
    Primrec (fun q : PolynomialCode n × ℕ ↦ PolynomialCode.pow q.1 q.2) :=
  PolynomialCode.pow_primrec

theorem ofPolynomial_primrec :
    Primrec (ofPolynomial : PolynomialCode n → PowerFractionCode n) :=
  Primrec.pair Primrec.id (Primrec.const 0)

theorem add_primrec : Primrec
    (fun q : PolynomialCode n × PowerFractionCode n × PowerFractionCode n ↦
      add q.1 q.2.1 q.2.2) := by
  unfold add
  apply Primrec.pair
  · fun_prop
  · exact Primrec.nat_add.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

theorem mul_primrec : Primrec₂ (mul : PowerFractionCode n → _ → _) := by
  apply Primrec.pair
  · exact PolynomialCode.mul_primrec.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)
  · exact Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)

theorem smoothingRadicand_primrec : Primrec₂
    (smoothingRadicand : PolynomialCode n → PowerFractionCode n → PolynomialCode n) := by
  unfold smoothingRadicand
  apply PolynomialCode.add_primrec.comp
  · fun_prop
  · exact PolynomialCode.pow_primrec.comp Primrec.fst
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd))

end PowerFractionCode

end Stability
