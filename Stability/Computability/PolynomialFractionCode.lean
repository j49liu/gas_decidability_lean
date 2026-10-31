import Stability.Computability.PolynomialCodeRealization
import Stability.Computability.PowerFractionCode
import Stability.Simulation.RationalDirectionalDerivative

/-!
# Effective arithmetic of literal polynomial fractions

All numerators and denominators match the actual fraction construction.
Finite directional sums use the same fixed coordinate order, not an
equivalent fraction obtained by cancellation.
-/

namespace Stability

open HGAS Simulation

abbrev PolynomialFractionCode (n : ℕ) := PolynomialCode n × PolynomialCode n

namespace PolynomialFractionCode

variable {n : ℕ} {σ : Type*}

noncomputable def decode (f : PolynomialFractionCode n) : PolynomialFraction (Fin n) :=
  ⟨PolynomialCode.decode f.1, PolynomialCode.decode f.2⟩

noncomputable def rename (e : σ → Fin n) (f : PolynomialFraction σ) : PolynomialFraction (Fin n) :=
  ⟨MvPolynomial.rename e f.numerator, MvPolynomial.rename e f.denominator⟩

def ofPolynomial (p : PolynomialCode n) : PolynomialFractionCode n := (p, PolynomialCode.one)

def ofPowerFraction (L : PolynomialCode n) (f : PowerFractionCode n) : PolynomialFractionCode n :=
  (f.1, PolynomialCode.pow L f.2)

def add (f g : PolynomialFractionCode n) : PolynomialFractionCode n :=
  (PolynomialCode.add (PolynomialCode.mul f.1 g.2) (PolynomialCode.mul g.1 f.2),
    PolynomialCode.mul f.2 g.2)

def mulPolynomial (p : PolynomialCode n) (f : PolynomialFractionCode n) :
    PolynomialFractionCode n :=
  (PolynomialCode.mul p f.1, f.2)

def divPolynomial (f : PolynomialFractionCode n) (p : PolynomialCode n) :
    PolynomialFractionCode n :=
  (f.1, PolynomialCode.mul f.2 p)

def sum : List (PolynomialFractionCode n) → PolynomialFractionCode n
  | [] => ofPolynomial PolynomialCode.zero
  | f :: fs => add f (sum fs)

noncomputable def directional [Fintype σ] (e : σ ≃ Fin n) (p : PolynomialCode n)
    (V : σ → PolynomialFractionCode n) : PolynomialFractionCode n :=
  sum (Finset.univ.toList.map fun i ↦ mulPolynomial (PolynomialCode.pderiv (e i) p) (V i))

@[simp]
theorem decode_ofPolynomial (p : PolynomialCode n) :
    decode (ofPolynomial p) = PolynomialFraction.ofPolynomial (PolynomialCode.decode p) := by
  simp [decode, ofPolynomial, PolynomialFraction.ofPolynomial]

@[simp]
theorem decode_add (f g : PolynomialFractionCode n) :
    decode (add f g) = PolynomialFraction.add (decode f) (decode g) := by
  simp [decode, add, PolynomialFraction.add]

@[simp]
theorem decode_mulPolynomial (p : PolynomialCode n) (f : PolynomialFractionCode n) :
    decode (mulPolynomial p f) = PolynomialFraction.mulPolynomial (PolynomialCode.decode p)
      (decode f) := by
  simp [decode, mulPolynomial, PolynomialFraction.mulPolynomial]

@[simp]
theorem decode_divPolynomial (f : PolynomialFractionCode n) (p : PolynomialCode n) :
    decode (divPolynomial f p) = PolynomialFraction.divPolynomial (decode f)
      (PolynomialCode.decode p) := by
  simp [decode, divPolynomial, PolynomialFraction.divPolynomial]

@[simp]
theorem decode_sum (fs : List (PolynomialFractionCode n)) :
    decode (sum fs) = PolynomialFraction.sum (fs.map decode) := by
  induction fs with
  | nil => simp [sum, PolynomialFraction.sum]
  | cons f fs ih => simp [sum, PolynomialFraction.sum, ih]

@[simp]
theorem rename_ofPolynomial (e : σ → Fin n) (p : MvPolynomial σ ℚ) :
    rename e (PolynomialFraction.ofPolynomial p) =
      PolynomialFraction.ofPolynomial (MvPolynomial.rename e p) := by
  simp [rename, PolynomialFraction.ofPolynomial]

@[simp]
theorem rename_add (e : σ → Fin n) (f g : PolynomialFraction σ) :
    rename e (PolynomialFraction.add f g) =
      PolynomialFraction.add (rename e f) (rename e g) := by
  simp [rename, PolynomialFraction.add]

@[simp]
theorem rename_mulPolynomial (e : σ → Fin n) (p : MvPolynomial σ ℚ)
    (f : PolynomialFraction σ) :
    rename e (PolynomialFraction.mulPolynomial p f) =
      PolynomialFraction.mulPolynomial (MvPolynomial.rename e p) (rename e f) := by
  simp [rename, PolynomialFraction.mulPolynomial]

@[simp]
theorem rename_divPolynomial (e : σ → Fin n) (f : PolynomialFraction σ)
    (p : MvPolynomial σ ℚ) :
    rename e (PolynomialFraction.divPolynomial f p) =
      PolynomialFraction.divPolynomial (rename e f) (MvPolynomial.rename e p) := by
  simp [rename, PolynomialFraction.divPolynomial]

@[simp]
theorem rename_sum (e : σ → Fin n) (fs : List (PolynomialFraction σ)) :
    rename e (PolynomialFraction.sum fs) = PolynomialFraction.sum (fs.map (rename e)) := by
  induction fs with
  | nil => simp [PolynomialFraction.sum]
  | cons f fs ih => simp [PolynomialFraction.sum, ih]

theorem decode_directional [Fintype σ] (e : σ ≃ Fin n) (p : PolynomialCode n)
    (P : MvPolynomial σ ℚ) (hp : PolynomialCode.decode p = MvPolynomial.rename e P)
    (V : σ → PolynomialFractionCode n) (W : σ → PolynomialFraction σ)
    (hV : ∀ i, decode (V i) = rename e (W i)) :
    decode (directional e p V) = rename e (PolynomialFraction.directional P W) := by
  simp only [directional, decode_sum, List.map_map, Function.comp_def,
    decode_mulPolynomial, PolynomialCode.decode_pderiv, hp,
    PolynomialCodeRealization.pderiv_rename_equiv, hV,
    PolynomialFraction.directional, PolynomialFraction.sumOver, rename_sum,
    rename_mulPolynomial]

theorem ofPolynomial_primrec :
    Primrec (ofPolynomial : PolynomialCode n → PolynomialFractionCode n) :=
  Primrec.pair Primrec.id (Primrec.const _)

theorem ofPowerFraction_primrec : Primrec₂
    (ofPowerFraction : PolynomialCode n → PowerFractionCode n → PolynomialFractionCode n) :=
  Primrec.pair (Primrec.fst.comp Primrec.snd)
    (PolynomialCode.pow_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd))

theorem add_primrec : Primrec₂ (add : PolynomialFractionCode n → _ → _) :=
  Primrec.pair
    (PolynomialCode.add_primrec.comp
      (PolynomialCode.mul_primrec.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.snd.comp Primrec.snd))
      (PolynomialCode.mul_primrec.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.fst)))
    (PolynomialCode.mul_primrec.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))

theorem mulPolynomial_primrec : Primrec₂
    (mulPolynomial : PolynomialCode n → PolynomialFractionCode n → PolynomialFractionCode n) :=
  Primrec.pair (PolynomialCode.mul_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
    (Primrec.snd.comp Primrec.snd)

theorem divPolynomial_primrec : Primrec₂
    (divPolynomial : PolynomialFractionCode n → PolynomialCode n → PolynomialFractionCode n) :=
  Primrec.pair (Primrec.fst.comp Primrec.fst)
    (PolynomialCode.mul_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)

theorem sum_map_primrec {α ι : Type*} [Primcodable α] (indices : List ι)
    (F : α → ι → PolynomialFractionCode n) (hF : ∀ i, Primrec (fun a ↦ F a i)) :
    Primrec (fun a ↦ sum (indices.map (F a))) := by
  induction indices with
  | nil => exact Primrec.const _
  | cons i indices ih => exact add_primrec.comp (hF i) ih

theorem directional_primrec {α : Type*} [Primcodable α] [Fintype σ] (e : σ ≃ Fin n)
    (p : α → PolynomialCode n) (V : α → σ → PolynomialFractionCode n)
    (hp : Primrec p) (hV : ∀ i, Primrec (fun a ↦ V a i)) :
    Primrec (fun a ↦ directional e (p a) (V a)) := by
  apply sum_map_primrec
  intro i
  exact mulPolynomial_primrec.comp
    (PolynomialCode.pderiv_primrec.comp (Primrec.const (e i)) hp) (hV i)

end PolynomialFractionCode

end Stability
