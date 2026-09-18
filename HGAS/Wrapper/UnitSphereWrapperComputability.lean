import HGAS.Wrapper.UnitSphereWrapperProperFace
import Mathlib.Computability.Partrec

/-!
# Primitive-recursive compilation of the complete polynomial wrapper

The preceding wrapper files deliberately define every transformation on
raw sparse syntax.  This file proves the promised effectivity statement:
for fixed source and block dimensions, a fixed block layout, and a fixed
chart degree, the map

```
(P,a) ↦ finalFieldCode sourceBlock D P a
```

is primitive recursive, hence computable.

The proof follows the compiler structure.  Every coordinate is assembled
from the previously proved primitive-recursive sparse operations
`add`, `sub`, `mul`, `pow`, `sumCodes`, two-sheet homogenization, and
parity homogenization.  Finite coordinate functions are handled by
`Primrec.fin_curry`; all layout tests involve fixed finite indices and are
therefore resolved while building the corresponding coordinate program.
-/

namespace HGAS

namespace UnitSpherePolynomialWrapper

variable {n k : ℕ}

theorem chartPolynomialCode_primrec (k D : ℕ) :
    Primrec (chartPolynomialCode k D :
      PolynomialCode n → PolynomialCode (n + 1)) := by
  exact
    PolynomialCode.mul_primrec.comp
      (Primrec.const
        (PolynomialCode.constant
          (RationalCode.ofNat (chartScale k D))))
      (PolynomialCode.twoSheetHomogenize_primrec.comp
        (Primrec.const D) Primrec.id)

theorem chartFieldCode_primrec (k D : ℕ) :
    Primrec (chartFieldCode k D :
      PolynomialFieldCode n → PolynomialFieldCode (n + 1)) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro j
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · exact (Primrec.const PolynomialCode.zero).of_eq fun _ ↦ rfl
  · exact
      ((chartPolynomialCode_primrec (n := n) k D).comp
        (Primrec.fin_app.comp Primrec.id
          (Primrec.const i))).of_eq
            fun _ ↦ rfl

theorem chartRewardCode_primrec (k D : ℕ) :
    Primrec (chartRewardCode k D :
      PolynomialCode n → PolynomialCode (n + 1)) := by
  exact
    PolynomialCode.mul_primrec.comp
      (Primrec.const
        (PolynomialCode.constant
          (RationalCode.ofNat (chartScale k D))))
      (PolynomialCode.twoSheetHomogenize_primrec.comp
        (Primrec.const (D - 1)) Primrec.id)

theorem blockDotCode_primrec
    (sourceBlock : Fin n → Fin k) (b : Fin (k + 1)) :
    Primrec (blockDotCode sourceBlock · b :
      PolynomialFieldCode (n + 1) → PolynomialCode (n + 1)) := by
  apply PolynomialCode.sumCodes_primrec.comp
  apply Primrec.list_ofFn
  intro j
  by_cases hj : ambientBlock sourceBlock j = b
  · exact
      (PolynomialCode.mul_primrec.comp
        (Primrec.const (PolynomialCode.varCode j))
        (Primrec.fin_app.comp Primrec.id
          (Primrec.const j))).of_eq
            fun _ ↦ by simp [hj]
  · exact
      (Primrec.const PolynomialCode.zero).of_eq
        fun _ ↦ by simp [hj]

theorem tangentFieldCode_primrec
    (sourceBlock : Fin n → Fin k) :
    Primrec (tangentFieldCode sourceBlock :
      PolynomialFieldCode (n + 1) →
        PolynomialFieldCode (n + 1)) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro j
  let b := ambientBlock sourceBlock j
  have hPi :
      Primrec (fun PiField : PolynomialFieldCode (n + 1) ↦
        PiField j) :=
    Primrec.fin_app.comp Primrec.id (Primrec.const j)
  have hdot :
      Primrec (fun PiField : PolynomialFieldCode (n + 1) ↦
        blockDotCode sourceBlock PiField b) :=
    blockDotCode_primrec sourceBlock b
  exact
    (PolynomialCode.sub_primrec.comp
      (PolynomialCode.mul_primrec.comp
        (Primrec.const (scaledBlockRadiusCode sourceBlock b))
        hPi)
      (PolynomialCode.mul_primrec.comp
        (PolynomialCode.mul_primrec.comp
          (Primrec.const
            (PolynomialCode.constant
              (RationalCode.ofNat (k + 1))))
          hdot)
        (Primrec.const (PolynomialCode.varCode j)))).of_eq
          fun _ ↦ rfl

theorem rawWrapperFieldCode_primrec
    (sourceBlock : Fin n → Fin k) (D : ℕ) :
    Primrec (rawWrapperFieldCode sourceBlock D :
      PolynomialFieldCode n → PolynomialFieldCode (n + 1)) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro j
  have htangentField :
      Primrec
        (fun P : PolynomialFieldCode n ↦
          tangentFieldCode sourceBlock (chartFieldCode k D P)) :=
    (tangentFieldCode_primrec sourceBlock).comp
      (chartFieldCode_primrec k D)
  have htangentCoordinate :
      Primrec
        (fun P : PolynomialFieldCode n ↦
          tangentFieldCode sourceBlock (chartFieldCode k D P) j) :=
    Primrec.fin_app.comp htangentField (Primrec.const j)
  exact
    (PolynomialCode.add_primrec.comp
      htangentCoordinate
      (Primrec.const (cleanupFieldCode sourceBlock j))).of_eq
        fun _ ↦ rfl

theorem rawWrapperRewardCode_primrec
    (sourceBlock : Fin n → Fin k) (D : ℕ) :
    Primrec (rawWrapperRewardCode sourceBlock D :
      PolynomialCode n → PolynomialCode (n + 1)) := by
  let H := blockRadiusProductCode sourceBlock
  exact
    (PolynomialCode.sub_primrec.comp
      (PolynomialCode.mul_primrec.comp
        (Primrec.const H)
        (chartRewardCode_primrec k D))
      (Primrec.const
        (PolynomialCode.sub PolynomialCode.one H))).of_eq
          fun _ ↦ rfl

theorem homogeneousAngularCode_primrec
    (sourceBlock : Fin n → Fin k) (D : ℕ) :
    Primrec (homogeneousAngularCode sourceBlock D :
      PolynomialFieldCode n → PolynomialFieldCode (n + 1)) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro j
  have hrawField :=
    rawWrapperFieldCode_primrec sourceBlock D
  have hrawCoordinate :
      Primrec
        (fun P : PolynomialFieldCode n ↦
          rawWrapperFieldCode sourceBlock D P j) :=
    Primrec.fin_app.comp hrawField (Primrec.const j)
  exact
    (PolynomialCode.parityHomogenizeCode_primrec.comp
      (Primrec.const (targetDegree k D))
      hrawCoordinate).of_eq fun _ ↦ rfl

theorem homogeneousRewardCode_primrec
    (sourceBlock : Fin n → Fin k) (D : ℕ) :
    Primrec (homogeneousRewardCode sourceBlock D :
      PolynomialCode n → PolynomialCode (n + 1)) := by
  exact
    (PolynomialCode.parityHomogenizeCode_primrec.comp
      (Primrec.const (targetDegree k D - 1))
      (rawWrapperRewardCode_primrec sourceBlock D)).of_eq
        fun _ ↦ rfl

/-- **Effective complete wrapper compiler.** -/
theorem finalFieldCode_primrec
    (sourceBlock : Fin n → Fin k) (D : ℕ) :
    Primrec
      (fun input : PolynomialFieldCode n × PolynomialCode n ↦
        finalFieldCode sourceBlock D input.1 input.2) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro j
  have hangularField :
      Primrec
        (fun input : PolynomialFieldCode n × PolynomialCode n ↦
          homogeneousAngularCode sourceBlock D input.1) :=
    (homogeneousAngularCode_primrec sourceBlock D).comp Primrec.fst
  have hangularCoordinate :
      Primrec
        (fun input : PolynomialFieldCode n × PolynomialCode n ↦
          homogeneousAngularCode sourceBlock D input.1 j) :=
    Primrec.fin_app.comp hangularField (Primrec.const j)
  have hreward :
      Primrec
        (fun input : PolynomialFieldCode n × PolynomialCode n ↦
          homogeneousRewardCode sourceBlock D input.2) :=
    (homogeneousRewardCode_primrec sourceBlock D).comp Primrec.snd
  exact
    (PolynomialCode.add_primrec.comp
      hangularCoordinate
      (PolynomialCode.mul_primrec.comp
        hreward
        (Primrec.const (PolynomialCode.varCode j)))).of_eq
          fun _ ↦ rfl

/-- The complete rational sparse-code wrapper is computable. -/
theorem finalFieldCode_computable
    (sourceBlock : Fin n → Fin k) (D : ℕ) :
    Computable
      (fun input : PolynomialFieldCode n × PolynomialCode n ↦
        finalFieldCode sourceBlock D input.1 input.2) :=
  (finalFieldCode_primrec sourceBlock D).to_comp

end UnitSpherePolynomialWrapper

end HGAS
