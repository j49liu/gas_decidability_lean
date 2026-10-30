import HGAS.Stability.AngularCongruence
import HGAS.Stability.LinearConjugacyLyapunov
import HGAS.Propagation.DegreePaddingCode
import HGAS.Propagation.DegreePaddingGAS
import HGAS.Veronese.SourceEuclideanConjugacy
import HGAS.Algebra.HomogeneousEvaluation
import HGAS.Lyapunov.CheckedRationalCertificateSoundness
import Mathlib.Tactic

/-!
# Lyapunov stability under degree raising and dimension padding

This is the Lyapunov-stability half of Lemma 6.1 (degree raising and
dimension padding) of the paper.  For a homogeneous cubic `H`, the padded
field

```
(x, z) ↦ (‖x‖² + ‖z‖²)^j (H x, -z₁³, …, -z_p³)
```

is Lyapunov stable (with existence of solutions) exactly when `H` is.  The
product with the cubic sinks is handled directly; the radial factor equals
one on the Euclidean unit sphere, so the angular congruence theorem applies
after passing to Euclidean coordinates.
-/

namespace HGAS

open Set

noncomputable section

/-! ## Products -/

section Product

variable {E H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Lyapunov stability with existence for a product system is equivalent to
Lyapunov stability with existence for both factors. -/
theorem lyapunovStableWithExistence_productField_iff
    (F : E → E) (G : H → H) :
    LyapunovStableWithExistence (productField F G) (0, 0) ↔
      LyapunovStableWithExistence F 0 ∧ LyapunovStableWithExistence G 0 := by
  constructor
  · intro h
    constructor
    · intro ε hε
      obtain ⟨δ, hδ, hball⟩ := h ε hε
      refine ⟨δ, hδ, fun a ha ↦ ?_⟩
      have hpair : dist ((a, 0) : E × H) (0, 0) < δ := by
        simpa [Prod.dist_eq, dist_zero_right] using ha
      obtain ⟨γ, hγ⟩ := (hball (a, 0) hpair).1
      refine ⟨⟨fun t ↦ (γ t).1, hγ.fst_product⟩, ?_⟩
      intro γ' hγ' t ht
      have hpr := hγ'.prodMk hγ.snd_product
      have hb := (hball (a, 0) hpair).2 _ hpr t ht
      rw [Prod.dist_eq] at hb
      exact lt_of_le_of_lt (le_max_left _ _) hb
    · intro ε hε
      obtain ⟨δ, hδ, hball⟩ := h ε hε
      refine ⟨δ, hδ, fun b hb ↦ ?_⟩
      have hpair : dist ((0, b) : E × H) (0, 0) < δ := by
        simpa [Prod.dist_eq, dist_zero_right] using hb
      obtain ⟨γ, hγ⟩ := (hball (0, b) hpair).1
      refine ⟨⟨fun t ↦ (γ t).2, hγ.snd_product⟩, ?_⟩
      intro η hη t ht
      have hpr := hγ.fst_product.prodMk hη
      have hbd := (hball (0, b) hpair).2 _ hpr t ht
      rw [Prod.dist_eq] at hbd
      exact lt_of_le_of_lt (le_max_right _ _) hbd
  · rintro ⟨hF, hG⟩ ε hε
    obtain ⟨δ₁, hδ₁, hb₁⟩ := hF ε hε
    obtain ⟨δ₂, hδ₂, hb₂⟩ := hG ε hε
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
    rintro ⟨a, b⟩ hab
    rw [Prod.dist_eq, max_lt_iff] at hab
    have ha : dist a 0 < δ₁ := lt_of_lt_of_le hab.1 (min_le_left _ _)
    have hb : dist b 0 < δ₂ := lt_of_lt_of_le hab.2 (min_le_right _ _)
    refine ⟨?_, ?_⟩
    · obtain ⟨γ, hγ⟩ := (hb₁ a ha).1
      obtain ⟨η, hη⟩ := (hb₂ b hb).1
      exact ⟨fun t ↦ (γ t, η t), hγ.prodMk hη⟩
    · intro γ hγ t ht
      rw [Prod.dist_eq, max_lt_iff]
      exact ⟨(hb₁ a ha).2 _ hγ.fst_product t ht,
        (hb₂ b hb).2 _ hγ.snd_product t ht⟩

end Product

/-! ## The direct product with cubic sinks -/

variable {m p : ℕ}

/-- Adjoining cubic sinks preserves and reflects Lyapunov stability. -/
theorem directProductCubic_lyapunovStableWithExistence_iff
    (H : FinVector m ℝ → FinVector m ℝ) :
    LyapunovStableWithExistence (directProductCubic (k := p) H) (0, 0) ↔
      LyapunovStableWithExistence H 0 := by
  rw [directProductCubic_eq_productField,
    lyapunovStableWithExistence_productField_iff]
  constructor
  · exact fun h ↦ h.1
  · exact fun h ↦ ⟨h, (finiteCubicSink_gas (k := p)).lyapunovStableWithExistence⟩

/-! ## Euclidean coordinates for the padded space -/

/-- Flat coordinates on `Fin (m+p) → ℝ`, Euclidean normalization. -/
noncomputable def paddedEuclideanEquiv (m p : ℕ) :
    SplitPoint m p ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin (m + p)) :=
  (DegreePaddingCode.splitEquiv m p).symm.trans Veronese.sourceEuclideanEquiv

theorem norm_sq_paddedEuclideanEquiv (q : SplitPoint m p ℝ) :
    ‖paddedEuclideanEquiv m p q‖ ^ 2 = splitNormSq q := by
  rw [paddedEuclideanEquiv, ContinuousLinearEquiv.trans_apply,
    Veronese.norm_sq_sourceEuclideanEquiv, ← Veronese.HGAS.normSq_eq_sourceRadiusSq,
    DegreePaddingCode.normSq_eq_splitNormSq_splitEquiv]
  simp

/-- The padded and unpadded fields agree on the Euclidean unit sphere. -/
theorem conjugate_degreePaddedField_eq_on_sphere
    (H : FinVector m ℝ → FinVector m ℝ) (j : ℕ)
    (v : EuclideanSpace ℝ (Fin (m + p))) (hv : ‖v‖ = 1) :
    conjugateField (paddedEuclideanEquiv m p) (degreePaddedField (k := p) H j) v =
      conjugateField (paddedEuclideanEquiv m p) (directProductCubic (k := p) H) v := by
  have hsq : splitNormSq ((paddedEuclideanEquiv m p).symm v) = 1 := by
    rw [← norm_sq_paddedEuclideanEquiv]
    simp [hv]
  simp only [conjugateField, degreePaddedField, degreePaddingFactor, hsq, one_pow,
    one_smul]

/-- **Lyapunov half of the degree-raising and padding lemma.** -/
theorem degreePaddedField_lyapunovStableWithExistence_iff
    (H : FinVector m ℝ → FinVector m ℝ) (hH : ContDiff ℝ 1 H)
    (hHhom : ScalesAsDegree ℝ 3 H) (j : ℕ) :
    LyapunovStableWithExistence (degreePaddedField (k := p) H j) 0 ↔
      LyapunovStableWithExistence H 0 := by
  let e := paddedEuclideanEquiv m p
  have hP : ContDiff ℝ 1 (degreePaddedField (k := p) H j) := by
    have := (degreePaddingFactor_contDiff (m := m) (k := p) j).smul
      (directProductCubic_contDiff (k := p) hH)
    simpa [degreePaddedField] using this
  have hD : ContDiff ℝ 1 (directProductCubic (k := p) H) :=
    directProductCubic_contDiff hH
  have hPhom : ScalesAsDegree ℝ (3 + 2 * j) (degreePaddedField (k := p) H j) :=
    degreePaddedField_scalesAsDegree H j hHhom
  have hDhom : ScalesAsDegree ℝ 3 (directProductCubic (k := p) H) :=
    directProductCubic_scalesAsDegree H hHhom
  have hP0 : degreePaddedField (k := p) H j 0 = 0 := by
    simpa using hPhom 0 0
  have hD0 : directProductCubic (k := p) H 0 = 0 := by
    simpa using hDhom 0 0
  have hcong :=
    lyapunovStableWithExistence_iff_of_eqOn_sphere
      (conjugateField e (degreePaddedField (k := p) H j))
      (conjugateField e (directProductCubic (k := p) H))
      (ContDiff.conjugateField e hP) (ContDiff.conjugateField e hD)
      (2 + 2 * j) 2
      (by
        have hdeg : 3 + 2 * j = (2 + 2 * j) + 1 := by omega
        rw [← hdeg]
        exact scalesAsDegree_conjugateField e hPhom)
      (by simpa using scalesAsDegree_conjugateField e hDhom)
      (conjugateField_zero e hP0) (conjugateField_zero e hD0)
      (conjugate_degreePaddedField_eq_on_sphere H j)
  rw [lyapunovStableWithExistence_conjugateField_iff,
    lyapunovStableWithExistence_conjugateField_iff] at hcong
  have h00 : (0 : SplitPoint m p ℝ) = (0, 0) := rfl
  rw [hcong, h00, directProductCubic_lyapunovStableWithExistence_iff]

/-! ## The executable padding code -/

namespace DegreePaddingCode

/-- Lyapunov stability is invariant under the executable padding
construction once the source code is a valid cubic field. -/
theorem lyapunovStableWithExistence_realize_degreeDimensionPadCode_iff
    (m p j : ℕ) (H : PolynomialFieldCode m)
    (hH : PolynomialFieldCode.homogeneous 3 H = true) :
    LyapunovStableWithExistence
        (PolynomialFieldCode.realize (degreeDimensionPadCode m p j H)) 0 ↔
      LyapunovStableWithExistence (PolynomialFieldCode.realize H) 0 := by
  have hhom : ∀ i : Fin m, (PolynomialCode.decode (H i)).IsHomogeneous 3 :=
    (PolynomialFieldCode.homogeneous_eq_true_iff 3 H).mp hH
  have hscale : ScalesAsDegree ℝ 3 (PolynomialFieldCode.realize H) :=
    fun c x ↦ evalPolynomialField_smul (PolynomialFieldCode.decode H) hhom c x
  rw [realize_degreeDimensionPadCode, lyapunovStableWithExistence_conjugateField_iff]
  exact degreePaddedField_lyapunovStableWithExistence_iff
    (PolynomialFieldCode.realize H) (contDiff_polynomialFieldCode_realize H) hscale j

/-- **Lemma 6.1 for `HLS`.**  Language-level correctness of degree raising
and dimension padding on valid cubic source codes. -/
theorem degreeDimensionPadCode_hlsQ_iff_of_homogeneous
    (m p j : ℕ) (H : PolynomialFieldCode m)
    (hH : PolynomialFieldCode.homogeneous 3 H = true) :
    HLSQ m 3 H ↔
      HLSQ (m + p) (3 + 2 * j) (degreeDimensionPadCode m p j H) := by
  rw [hlsQ_iff_of_homogeneous H hH,
    hlsQ_iff_of_homogeneous _ (degreeDimensionPadCode_homogeneous m p j H hH)]
  exact (lyapunovStableWithExistence_realize_degreeDimensionPadCode_iff
    m p j H hH).symm

end DegreePaddingCode

end

end HGAS
