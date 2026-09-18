import HGAS.Wrapper.SparseDegreeCalculus
import Mathlib.Tactic

/-!
# Automatic degree and parity verification for the wrapper compiler

This file discharges the two syntactic eligibility hypotheses that were
kept explicit in `finalFieldCode_isHomogeneous`.

Assume:

* `D` is odd and at least three;
* every raw source-field monomial has degree at most `D`;
* every raw reward monomial has degree at most `D-1`.

Then:

* the raw wrapper field contains only odd monomials of degree at most
  `E = D + 2(k+1)`;
* the raw wrapper reward contains only even monomials of degree at most
  `E-1`;
* consequently the final compiled field is rational homogeneous of the
  advertised odd degree `E`.

All claims are about raw sparse lists, so they apply before normalization
and are directly compatible with the primitive-recursive compiler.
-/

namespace HGAS

open _root_.MvPolynomial

namespace PolynomialCode

variable {n : ℕ}

theorem termsParityEligible_sumCodes_ofFn
    {m E : ℕ} {p : Fin m → PolynomialCode n}
    (hp : ∀ i, TermsParityEligible E (p i)) :
    TermsParityEligible E (sumCodes (List.ofFn p)) := by
  apply termsParityEligible_sumCodes
  intro q hq
  rw [List.mem_ofFn] at hq
  obtain ⟨i, rfl⟩ := hq
  exact hp i

end PolynomialCode

namespace UnitSpherePolynomialWrapper

variable {n k : ℕ}

theorem rawBlockNormSqCode_termsParityEligible
    (sourceBlock : Fin n → Fin k) (b : Fin (k + 1)) :
    PolynomialCode.TermsParityEligible 2
      (rawBlockNormSqCode sourceBlock b) := by
  apply PolynomialCode.termsParityEligible_sumCodes_ofFn
  intro j
  by_cases hj : ambientBlock sourceBlock j = b
  · simp only [hj, ↓reduceIte]
    simpa using
      PolynomialCode.termsParityEligible_pow
        (PolynomialCode.termsParityEligible_varCode j) 2
  · simp only [hj, ↓reduceIte]
    exact PolynomialCode.termsParityEligible_zero 2

theorem scaledBlockRadiusCode_termsParityEligible
    (sourceBlock : Fin n → Fin k) (b : Fin (k + 1)) :
    PolynomialCode.TermsParityEligible 2
      (scaledBlockRadiusCode sourceBlock b) := by
  simpa [scaledBlockRadiusCode] using
    PolynomialCode.termsParityEligible_mul
      (PolynomialCode.termsParityEligible_constant
        (RationalCode.ofNat (k + 1)))
      (rawBlockNormSqCode_termsParityEligible sourceBlock b)

theorem chartPolynomialCode_termsParityEligible
    (D : ℕ) (p : PolynomialCode n)
    (hp : PolynomialCode.TermsDegreeLE D p) :
    PolynomialCode.TermsParityEligible D
      (chartPolynomialCode k D p) := by
  simpa [chartPolynomialCode] using
    PolynomialCode.termsParityEligible_mul
      (PolynomialCode.termsParityEligible_constant
        (RationalCode.ofNat (chartScale k D)))
      (PolynomialCode.termsParityEligible_twoSheetHomogenize D p hp)

theorem chartFieldCode_termsParityEligible
    (D : ℕ) (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE D (P j)) :
    ∀ j,
      PolynomialCode.TermsParityEligible D
        (chartFieldCode k D P j) := by
  intro j
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · exact PolynomialCode.termsParityEligible_zero D
  · exact chartPolynomialCode_termsParityEligible D (P i) (hP i)

theorem chartRewardCode_termsParityEligible
    (D : ℕ) (a : PolynomialCode n)
    (ha : PolynomialCode.TermsDegreeLE (D - 1) a) :
    PolynomialCode.TermsParityEligible (D - 1)
      (chartRewardCode k D a) := by
  simpa [chartRewardCode] using
    PolynomialCode.termsParityEligible_mul
      (PolynomialCode.termsParityEligible_constant
        (RationalCode.ofNat (chartScale k D)))
      (PolynomialCode.termsParityEligible_twoSheetHomogenize
        (D - 1) a ha)

theorem blockDotCode_termsParityEligible
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (PiField : PolynomialFieldCode (n + 1))
    (hPi : ∀ j,
      PolynomialCode.TermsParityEligible D (PiField j))
    (b : Fin (k + 1)) :
    PolynomialCode.TermsParityEligible (D + 1)
      (blockDotCode sourceBlock PiField b) := by
  apply PolynomialCode.termsParityEligible_sumCodes_ofFn
  intro j
  by_cases hj : ambientBlock sourceBlock j = b
  · simp only [hj, ↓reduceIte]
    simpa [Nat.add_comm] using
      PolynomialCode.termsParityEligible_mul
        (PolynomialCode.termsParityEligible_varCode j)
        (hPi j)
  · simp only [hj, ↓reduceIte]
    exact PolynomialCode.termsParityEligible_zero (D + 1)

theorem tangentFieldCode_termsParityEligible
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (PiField : PolynomialFieldCode (n + 1))
    (hPi : ∀ j,
      PolynomialCode.TermsParityEligible D (PiField j)) :
    ∀ j,
      PolynomialCode.TermsParityEligible (D + 2)
        (tangentFieldCode sourceBlock PiField j) := by
  intro j
  let b := ambientBlock sourceBlock j
  have hfirst :
      PolynomialCode.TermsParityEligible (D + 2)
        (PolynomialCode.mul
          (scaledBlockRadiusCode sourceBlock b) (PiField j)) := by
    simpa [Nat.add_comm] using
      PolynomialCode.termsParityEligible_mul
        (scaledBlockRadiusCode_termsParityEligible sourceBlock b)
        (hPi j)
  have hdot :=
    blockDotCode_termsParityEligible sourceBlock D PiField hPi b
  have hscaledDot :
      PolynomialCode.TermsParityEligible (D + 1)
        (PolynomialCode.mul
          (PolynomialCode.constant
            (RationalCode.ofNat (k + 1)))
          (blockDotCode sourceBlock PiField b)) := by
    simpa using
      PolynomialCode.termsParityEligible_mul
        (PolynomialCode.termsParityEligible_constant
          (RationalCode.ofNat (k + 1))) hdot
  have hsecond :
      PolynomialCode.TermsParityEligible (D + 2)
        (PolynomialCode.mul
          (PolynomialCode.mul
            (PolynomialCode.constant
              (RationalCode.ofNat (k + 1)))
            (blockDotCode sourceBlock PiField b))
          (PolynomialCode.varCode j)) := by
    simpa using
      PolynomialCode.termsParityEligible_mul hscaledDot
        (PolynomialCode.termsParityEligible_varCode j)
  exact PolynomialCode.termsParityEligible_sub hfirst hsecond

theorem radiusAverageCode_termsParityEligible
    (sourceBlock : Fin n → Fin k) :
    PolynomialCode.TermsParityEligible 4
      (radiusAverageCode sourceBlock) := by
  have hsummand :
      ∀ b : Fin (k + 1),
        PolynomialCode.TermsParityEligible 4
          (PolynomialCode.mul
            (scaledBlockRadiusCode sourceBlock b)
            (PolynomialCode.sub PolynomialCode.one
              (scaledBlockRadiusCode sourceBlock b))) := by
    intro b
    have hs := scaledBlockRadiusCode_termsParityEligible sourceBlock b
    have hone2 :=
      (PolynomialCode.termsParityEligible_one (n := n + 1)).promote
        (by omega : 0 ≤ 2) (by decide)
    have hdiff :=
      PolynomialCode.termsParityEligible_sub hone2 hs
    simpa using PolynomialCode.termsParityEligible_mul hs hdiff
  have hsum :
      PolynomialCode.TermsParityEligible 4
        (PolynomialCode.sumCodes
          (List.ofFn fun b : Fin (k + 1) ↦
            PolynomialCode.mul
              (scaledBlockRadiusCode sourceBlock b)
              (PolynomialCode.sub PolynomialCode.one
                (scaledBlockRadiusCode sourceBlock b)))) :=
    PolynomialCode.termsParityEligible_sumCodes_ofFn hsummand
  simpa [radiusAverageCode] using
    PolynomialCode.termsParityEligible_mul
      (PolynomialCode.termsParityEligible_constant
        (((false, 1), k) : RationalCode))
      hsum

theorem radiusDeviationCode_termsParityEligible
    (sourceBlock : Fin n → Fin k) (b : Fin (k + 1)) :
    PolynomialCode.TermsParityEligible 4
      (radiusDeviationCode sourceBlock b) := by
  have hone4 :=
    (PolynomialCode.termsParityEligible_one (n := n + 1)).promote
      (by omega : 0 ≤ 4) (by decide)
  have hs4 :=
    (scaledBlockRadiusCode_termsParityEligible sourceBlock b).promote
      (by omega : 2 ≤ 4) (by decide)
  exact PolynomialCode.termsParityEligible_sub
    (PolynomialCode.termsParityEligible_sub hone4 hs4)
    (radiusAverageCode_termsParityEligible sourceBlock)

theorem cleanupFieldCode_termsParityEligible
    (sourceBlock : Fin n → Fin k) :
    ∀ j,
      PolynomialCode.TermsParityEligible 5
        (cleanupFieldCode sourceBlock j) := by
  intro j
  simpa [cleanupFieldCode] using
    PolynomialCode.termsParityEligible_mul
      (radiusDeviationCode_termsParityEligible sourceBlock
        (ambientBlock sourceBlock j))
      (PolynomialCode.termsParityEligible_varCode j)

/-- Automatic odd parity/degree bound for every raw wrapper component. -/
theorem rawWrapperFieldCode_termsParityEligible
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (hD : 3 ≤ D) (hDodd : D % 2 = 1)
    (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE D (P j)) :
    ∀ j,
      PolynomialCode.TermsParityEligible (targetDegree k D)
        (rawWrapperFieldCode sourceBlock D P j) := by
  have hPi := chartFieldCode_termsParityEligible
    (k := k) D P hP
  have hT := tangentFieldCode_termsParityEligible
    sourceBlock D (chartFieldCode k D P) hPi
  have hN := cleanupFieldCode_termsParityEligible sourceBlock
  intro j
  have hT' :
      PolynomialCode.TermsParityEligible (targetDegree k D)
        (tangentFieldCode sourceBlock (chartFieldCode k D P) j) :=
    (hT j).promote (F := targetDegree k D)
      (by dsimp [targetDegree]; omega)
      (by dsimp [targetDegree]; omega)
  have hN' :
      PolynomialCode.TermsParityEligible (targetDegree k D)
        (cleanupFieldCode sourceBlock j) :=
    (hN j).promote (F := targetDegree k D)
      (by dsimp [targetDegree]; omega)
      (by dsimp [targetDegree]; omega)
  exact PolynomialCode.termsParityEligible_add hT' hN'

theorem blockRadiusProductCode_termsParityEligible
    (sourceBlock : Fin n → Fin k) :
    PolynomialCode.TermsParityEligible (2 * (k + 1))
      (blockRadiusProductCode sourceBlock) := by
  let ps :=
    List.ofFn fun b : Fin (k + 1) ↦
      scaledBlockRadiusCode sourceBlock b
  have hps :
      ∀ p ∈ ps, PolynomialCode.TermsParityEligible 2 p := by
    intro p hp
    simp only [ps, List.mem_ofFn] at hp
    obtain ⟨b, rfl⟩ := hp
    exact scaledBlockRadiusCode_termsParityEligible sourceBlock b
  simpa [blockRadiusProductCode, ps] using
    PolynomialCode.termsParityEligible_foldr_mul ps hps

/-- Automatic even parity/degree bound for the raw wrapper reward. -/
theorem rawWrapperRewardCode_termsParityEligible
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (hD : 3 ≤ D) (hDodd : D % 2 = 1)
    (a : PolynomialCode n)
    (ha : PolynomialCode.TermsDegreeLE (D - 1) a) :
    PolynomialCode.TermsParityEligible (targetDegree k D - 1)
      (rawWrapperRewardCode sourceBlock D a) := by
  let H := blockRadiusProductCode sourceBlock
  have hH :
      PolynomialCode.TermsParityEligible (2 * (k + 1)) H :=
    blockRadiusProductCode_termsParityEligible sourceBlock
  have hAlpha :=
    chartRewardCode_termsParityEligible (k := k) D a ha
  have hproductRaw :=
    PolynomialCode.termsParityEligible_mul hH hAlpha
  have hdegree :
      2 * (k + 1) + (D - 1) = targetDegree k D - 1 := by
    simp [targetDegree]
    omega
  have hproduct :
      PolynomialCode.TermsParityEligible (targetDegree k D - 1)
        (PolynomialCode.mul H (chartRewardCode k D a)) := by
    simpa [hdegree] using hproductRaw
  have hone :
      PolynomialCode.TermsParityEligible (targetDegree k D - 1)
        (PolynomialCode.one : PolynomialCode (n + 1)) :=
    (PolynomialCode.termsParityEligible_one (n := n + 1)).promote
      (F := targetDegree k D - 1)
      (by dsimp [targetDegree]; omega)
      (by dsimp [targetDegree]; omega)
  have hHpromoted :
      PolynomialCode.TermsParityEligible (targetDegree k D - 1) H :=
    hH.promote (F := targetDegree k D - 1)
      (by dsimp [targetDegree]; omega)
      (by dsimp [targetDegree]; omega)
  have hcomplement :=
    PolynomialCode.termsParityEligible_sub hone hHpromoted
  simpa [rawWrapperRewardCode, H] using
    PolynomialCode.termsParityEligible_sub hproduct hcomplement

/-- The compiler output is automatically homogeneous of its advertised
degree under the source bounds and the odd-degree choice. -/
theorem finalFieldCode_isHomogeneous_of_degreeBounds
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (hD : 3 ≤ D) (hDodd : D % 2 = 1)
    (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE D (P j))
    (a : PolynomialCode n)
    (ha : PolynomialCode.TermsDegreeLE (D - 1) a) :
    ∀ j,
      (PolynomialCode.decode
        (finalFieldCode sourceBlock D P a j)).IsHomogeneous
          (targetDegree k D) :=
  finalFieldCode_isHomogeneous sourceBlock D P a
    (rawWrapperFieldCode_termsParityEligible
      sourceBlock D hD hDodd P hP)
    (rawWrapperRewardCode_termsParityEligible
      sourceBlock D hD hDodd a ha)

/-- The advertised target degree is odd. -/
theorem targetDegree_odd
    (D : ℕ) (hDodd : D % 2 = 1) :
    targetDegree k D % 2 = 1 := by
  simp [targetDegree]
  omega

end UnitSpherePolynomialWrapper

end HGAS
