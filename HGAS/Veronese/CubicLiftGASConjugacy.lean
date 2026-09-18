import HGAS.Veronese.CubicLiftInvariantAverages
import HGAS.Veronese.SourceEuclideanConjugacy
import HGAS.Veronese.WeightedEuclideanConjugacy
import Mathlib.Tactic

/-!
# GAS preservation by the stabilized cubic Veronese lift

This module assembles the formal development into the dynamical theorem
needed by the cubic-degree reduction.

For a rational polynomial source field `F` homogeneous of degree `2k+1`,
the earlier invariant-measure argument proves that a common negative
radial-cocycle block exists for the source angular flow if and only if it
exists for the stabilized cubic angular flow.  Two normalization modules
then identify those compact-flow blocks with GAS:

* `SourceEuclideanConjugacy` replaces the raw source-coordinate sup norm by
  the genuine Euclidean norm without changing coordinates;
* `WeightedEuclideanConjugacy` applies the diagonal
  `sqrt(multinomialWeight)` transformation, turning `Q` into the ordinary
  Euclidean norm-square.

The Euclidean angular-block characterization supplies the remaining
equivalence between a negative block and GAS.  Chaining the three
equivalences gives the exact result

```
GAS (evaluatedSourceField F) 0
  ↔ GAS (evaluatedStabilizedCubicField b) 0.
```

No converse-Lyapunov theorem, flow-regularity hypothesis, or informal norm
identification remains in this statement.
-/

namespace HGAS.Veronese

open Function
open scoped BoundedContinuousFunction

noncomputable section

variable {n k : ℕ} {F : HGAS.PolynomialField n}

/-! ## Restricted compact-flow cocycles versus ambient sphere cocycles -/

/-- The source cocycle written on the restricted source sphere is exactly
the ambient source cocycle at the underlying point. -/
theorem sourceSubtype_orbitIntegral_eq
    (F : HGAS.PolynomialField n)
    (T : ℝ) (u : sourceUnitSphere n) :
    HGAS.Dynamics.orbitIntegral
        (polynomialSourceAngularFlow F)
        (sourceRadialRewardBCF F) T u =
      ∫ t in (0 : ℝ)..T,
        HGAS.radialReward (evaluatedSourceField F)
          (polynomialSourceAngularAmbientFlow F t u.1) := by
  rfl

/-- Therefore the compact source-flow block predicate is the same as the
ambient algebraic-sphere block predicate used by the Euclidean
normalization theorem. -/
theorem sourceUniformNegativeBlock_iff_sourceAngularBlock
    (F : HGAS.PolynomialField n) :
    HGAS.Dynamics.HasUniformNegativeBlock
        (polynomialSourceAngularFlow F)
        (sourceRadialRewardBCF F) ↔
      HasUniformNegativeSourceAngularBlock
        (evaluatedSourceField F)
        (contDiff_evaluatedSourceField F) := by
  constructor
  · rintro ⟨T, c, hT, hc, hblock⟩
    refine ⟨T, c, hT, hc, ?_⟩
    intro x hx
    have h := hblock (⟨x, hx⟩ : sourceUnitSphere n)
    simpa only [sourceSubtype_orbitIntegral_eq] using h
  · rintro ⟨T, c, hT, hc, hblock⟩
    refine ⟨T, c, hT, hc, ?_⟩
    intro u
    rw [sourceSubtype_orbitIntegral_eq]
    exact hblock u.1 u.2

/-- The stabilized cocycle on the restricted weighted sphere is exactly
the ambient weighted cocycle at the underlying point. -/
theorem stabilizedSubtype_orbitIntegral_eq
    (b : CubicLiftStabilizationBounds F k)
    (T : ℝ) (y : weightedUnitSphere n k) :
    HGAS.Dynamics.orbitIntegral
        (stabilizedCubicAngularFlow b)
        (stabilizedCubicRadialRewardBCF b) T y =
      ∫ t in (0 : ℝ)..T,
        weightedRadialReward
          (evaluatedStabilizedCubicField b)
          (stabilizedCubicAmbientAngularFlow b t y.1) := by
  rfl

/-- Therefore the compact stabilized-flow block predicate is the same as
the ambient `Q=1` block predicate used by weighted Euclidean
normalization. -/
theorem stabilizedUniformNegativeBlock_iff_weightedAngularBlock
    (b : CubicLiftStabilizationBounds F k) :
    HGAS.Dynamics.HasUniformNegativeBlock
        (stabilizedCubicAngularFlow b)
        (stabilizedCubicRadialRewardBCF b) ↔
      HasUniformNegativeWeightedAngularBlock
        (evaluatedStabilizedCubicField b)
        (contDiff_evaluatedStabilizedCubicField b) := by
  constructor
  · rintro ⟨T, c, hT, hc, hblock⟩
    refine ⟨T, c, hT, hc, ?_⟩
    intro y hy
    have h := hblock (⟨y, hy⟩ : weightedUnitSphere n k)
    simpa only [stabilizedSubtype_orbitIntegral_eq] using h
  · rintro ⟨T, c, hT, hc, hblock⟩
    refine ⟨T, c, hT, hc, ?_⟩
    intro y
    rw [stabilizedSubtype_orbitIntegral_eq]
    exact hblock y.1 y.2

/-! ## Smoothness, homogeneity, and equilibria of the two fields -/

/-- The evaluated source polynomial field is `C²` (indeed smooth). -/
theorem contDiff_two_evaluatedSourceField
    (F : HGAS.PolynomialField n) :
    ContDiff ℝ 2 (evaluatedSourceField F) := by
  have htop : ContDiff ℝ ⊤ (evaluatedSourceField F) := by
    rw [contDiff_pi]
    intro i
    exact HGAS.contDiff_eval₂Hom_rational_real_fintype (F i)
  exact htop.of_le (by norm_num)

/-- Syntactic source homogeneity gives semantic homogeneity after real
evaluation. -/
theorem evaluatedSourceField_scalesAsDegree
    (F : HGAS.PolynomialField n) {d : ℕ}
    (hF : HGAS.IsHomogeneousOfDegree d F) :
    HGAS.ScalesAsDegree ℝ d (evaluatedSourceField F) := by
  intro c x
  exact HGAS.evalPolynomialField_smul F hF c x

/-- Every positive-degree evaluated source field vanishes at the origin. -/
theorem evaluatedSourceField_zero
    (F : HGAS.PolynomialField n) {d : ℕ}
    (hF : HGAS.IsHomogeneousOfDegree d F) (hd : 0 < d) :
    evaluatedSourceField F 0 = 0 :=
  HGAS.map_zero_of_scalesAsDegree
    (evaluatedSourceField F) d
    (evaluatedSourceField_scalesAsDegree F hF) hd

/-- The evaluated stabilized cubic field is `C²` (indeed smooth). -/
theorem contDiff_two_evaluatedStabilizedCubicField
    (b : CubicLiftStabilizationBounds F k) :
    ContDiff ℝ 2 (evaluatedStabilizedCubicField b) := by
  exact
    (contDiff_evalCoordinateField_real
      (stabilizedCubicField (k := k) F b.K)).of_le
      (by norm_num)

/-- The stabilized field has semantic cubic homogeneity after real
evaluation. -/
theorem evaluatedStabilizedCubicField_scalesAsDegree
    (b : CubicLiftStabilizationBounds F k) :
    HGAS.ScalesAsDegree ℝ 3
      (evaluatedStabilizedCubicField b) := by
  intro c y
  exact evalCoordinateField_smul
    (stabilizedCubicField_isHomogeneous F b.K) c y

/-- The stabilized cubic field vanishes at the origin. -/
theorem evaluatedStabilizedCubicField_zero
    (b : CubicLiftStabilizationBounds F k) :
    evaluatedStabilizedCubicField b 0 = 0 := by
  have hscale :=
    evaluatedStabilizedCubicField_scalesAsDegree b
      (0 : ℝ) (0 : RealVeroneseSpace n k)
  simpa using hscale

/-! ## GAS versus each compact angular block -/

/-- GAS of the evaluated source field is equivalent to the compact
source-sphere negative-block predicate used by the invariant-measure
argument. -/
theorem sourceGAS_iff_sourceUniformNegativeBlock
    (F : HGAS.PolynomialField n)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F) :
    HGAS.GloballyAsymptoticallyStable
        (evaluatedSourceField F) 0 ↔
      HGAS.Dynamics.HasUniformNegativeBlock
        (polynomialSourceAngularFlow F)
        (sourceRadialRewardBCF F) := by
  have hangular :
      HGAS.GloballyAsymptoticallyStable
          (evaluatedSourceField F) 0 ↔
        HasUniformNegativeSourceAngularBlock
          (evaluatedSourceField F)
          ((contDiff_two_evaluatedSourceField F).of_le
            (by norm_num)) :=
    globallyAsymptoticallyStable_iff_uniformNegativeSourceAngularBlock
      (evaluatedSourceField F) (2 * k)
      (evaluatedSourceField_scalesAsDegree F hF)
      (contDiff_two_evaluatedSourceField F)
      (evaluatedSourceField_zero F hF (by omega))
  exact hangular.trans
    (by
      simpa using
        (sourceUniformNegativeBlock_iff_sourceAngularBlock F).symm)

/-- GAS of the evaluated stabilized cubic field is equivalent to the
compact weighted-sphere negative-block predicate used by the
invariant-measure argument. -/
theorem stabilizedGAS_iff_stabilizedUniformNegativeBlock
    (b : CubicLiftStabilizationBounds F k) :
    HGAS.GloballyAsymptoticallyStable
        (evaluatedStabilizedCubicField b) 0 ↔
      HGAS.Dynamics.HasUniformNegativeBlock
        (stabilizedCubicAngularFlow b)
        (stabilizedCubicRadialRewardBCF b) := by
  have hangular :
      HGAS.GloballyAsymptoticallyStable
          (evaluatedStabilizedCubicField b) 0 ↔
        HasUniformNegativeWeightedAngularBlock
          (evaluatedStabilizedCubicField b)
          ((contDiff_two_evaluatedStabilizedCubicField b).of_le
            (by norm_num)) := by
    apply
      globallyAsymptoticallyStable_iff_uniformNegativeWeightedAngularBlock
        (evaluatedStabilizedCubicField b) 2
        (by
          simpa using
            evaluatedStabilizedCubicField_scalesAsDegree b)
        (contDiff_two_evaluatedStabilizedCubicField b)
        (evaluatedStabilizedCubicField_zero b)
  exact hangular.trans
    (by
      simpa using
        (stabilizedUniformNegativeBlock_iff_weightedAngularBlock b).symm)

/-! ## The stabilized cubic GAS equivalence -/

/-- **The stabilized cubic Veronese lift preserves GAS exactly.**

For every source field homogeneous of degree `2k+1`, with `k ≥ 1`, and
every stabilization package `b`, the source field is globally
asymptotically stable at the origin if and only if the resulting rational
cubic field is.

The `Nonempty` assumption merely records that the source unit sphere has a
point; in the intended reduction this follows from `n ≥ 1`.  It is exactly
the assumption needed by the compact invariant-measure argument that
constructs a stabilized uniform block from a source block. -/
theorem sourceGAS_iff_stabilizedCubicGAS
    [Nonempty (sourceUnitSphere n)]
    (b : CubicLiftStabilizationBounds F k)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F)
    (hk : 1 ≤ k) :
    HGAS.GloballyAsymptoticallyStable
        (evaluatedSourceField F) 0 ↔
      HGAS.GloballyAsymptoticallyStable
        (evaluatedStabilizedCubicField b) 0 := by
  exact
    (sourceGAS_iff_sourceUniformNegativeBlock F hF).trans
      ((source_uniformNegativeBlock_iff_stabilized b hF hk).trans
        (stabilizedGAS_iff_stabilizedUniformNegativeBlock b).symm)

end

end HGAS.Veronese
