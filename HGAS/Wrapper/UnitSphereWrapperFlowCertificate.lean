import HGAS.Wrapper.UnitSphereWrapperDegrees
import HGAS.Wrapper.UnitSphereWrapperProperFace
import HGAS.Wrapper.RadiusInvariantFaces
import HGAS.Wrapper.AngularAverageGAS
import HGAS.Veronese.SourceEuclideanConjugacy
import HGAS.Analysis.MvPolynomialCalculus
import Mathlib.Tactic

/-!
# The concrete radius-cleanup flow certificate

The sparse wrapper is written in raw coordinates `Fin (n+1) → ℝ`.
Mathlib equips that function type with the product sup norm, whereas the
angular GAS theorem uses a genuine inner-product norm.  We therefore use
the coordinate-preserving continuous linear equivalence

```
Fin (n+1) → ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin (n+1))
```

from `SourceEuclideanConjugacy`.  No formula or coefficient changes under
this equivalence.

This file packages the pointwise radius identity from
`UnitSpherePolynomialWrapper` as an actual
`RadiusCleanupFlowCertificate` for the Euclidean unit-angular flow of the
final polynomial field.  In particular, it proves the chain rule along
every orbit and hence discharges the flow-level Lyapunov-coboundary
obligation which was explicit in the semantic wrapper theorem.
-/

namespace HGAS

open Function Metric Set
open scoped BigOperators BoundedContinuousFunction RealInnerProductSpace

noncomputable section

namespace UnitSpherePolynomialWrapper

variable {n k : ℕ}

/-- Raw coordinate space of the wrapper. -/
abbrev RawWrapperSpace (n : ℕ) := Fin (n + 1) → ℝ

/-- Genuine Euclidean coordinate space, with exactly the same coordinates. -/
abbrev EuclideanWrapperSpace (n : ℕ) :=
  EuclideanSpace ℝ (Fin (n + 1))

/-- Coordinate-preserving normalization from raw to Euclidean coordinates. -/
noncomputable def wrapperEuclideanEquiv :
    RawWrapperSpace n ≃L[ℝ] EuclideanWrapperSpace n :=
  Veronese.sourceEuclideanEquiv

@[simp]
theorem wrapperEuclideanEquiv_apply_coord
    (x : RawWrapperSpace n) (i : Fin (n + 1)) :
    wrapperEuclideanEquiv x i = x i :=
  rfl

@[simp]
theorem wrapperEuclideanEquiv_symm_apply_coord
    (u : EuclideanWrapperSpace n) (i : Fin (n + 1)) :
    wrapperEuclideanEquiv.symm u i = u i :=
  rfl

/-- The algebraic norm square is exactly the Euclidean norm square after
coordinate normalization. -/
theorem norm_sq_wrapperEuclideanEquiv
    (x : RawWrapperSpace n) :
    ‖wrapperEuclideanEquiv x‖ ^ 2 = normSq x := by
  change ‖Veronese.sourceEuclideanEquiv x‖ ^ 2 = normSq x
  rw [Veronese.norm_sq_sourceEuclideanEquiv]
  exact Veronese.HGAS.normSq_eq_sourceRadiusSq x |>.symm

/-- Unit algebraic radius is equivalent to Euclidean unit norm. -/
theorem norm_wrapperEuclideanEquiv_eq_one_iff
    (x : RawWrapperSpace n) :
    ‖wrapperEuclideanEquiv x‖ = 1 ↔ normSq x = 1 := by
  constructor
  · intro h
    rw [← norm_sq_wrapperEuclideanEquiv x, h]
    norm_num
  · intro h
    have hsquare : ‖wrapperEuclideanEquiv x‖ ^ 2 = 1 := by
      rw [norm_sq_wrapperEuclideanEquiv, h]
    nlinarith [norm_nonneg (wrapperEuclideanEquiv x)]

/-- Every sparse rational polynomial field realizes to a smooth raw
coordinate field. -/
theorem contDiff_realize_polynomialFieldCode
    (F : PolynomialFieldCode (n + 1)) :
    ContDiff ℝ ⊤ (PolynomialFieldCode.realize F) := by
  rw [contDiff_pi]
  intro i
  have hfun :
      (fun x ↦ PolynomialFieldCode.realize F x i) =
        ratMvPolynomialEval (PolynomialCode.decode (F i)) := by
    funext x
    simp only [PolynomialFieldCode.realize_apply]
    simp [ratMvPolynomialEval, MvPolynomial.eval_map]
  rw [hfun]
  exact contDiff_ratMvPolynomialEval _

/-- The final field transported, without changing coordinates, to the
genuine Euclidean space used by the angular GAS theorem. -/
noncomputable def euclideanFinalField
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n) :
    EuclideanWrapperSpace n → EuclideanWrapperSpace n :=
  conjugateField wrapperEuclideanEquiv
    (PolynomialFieldCode.realize
      (finalFieldCode sourceBlock D P a))

theorem contDiff_euclideanFinalField
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n) :
    ContDiff ℝ ⊤ (euclideanFinalField sourceBlock D P a) :=
  ContDiff.conjugateField wrapperEuclideanEquiv
    (contDiff_realize_polynomialFieldCode
      (finalFieldCode sourceBlock D P a))

/-- On the algebraic unit sphere, the radial part of the final raw field is
exactly the homogeneous reward code. -/
theorem radialReward_finalFieldCode_of_normSq_one
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n)
    (x : RawWrapperSpace n) (hx : normSq x = 1) :
    radialReward
        (PolynomialFieldCode.realize
          (finalFieldCode sourceBlock D P a)) x =
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode
          (homogeneousRewardCode sourceBlock D a)) := by
  rw [radialReward, realize_finalFieldCode]
  rw [realize_homogeneousAngularCode_of_normSq_one
    sourceBlock D P x hx]
  rw [dot_add_right, dot_smul_right,
    dot_rawWrapperFieldCode_eq_zero_of_normSq_one
      sourceBlock D P x hx]
  change
    0 + MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode
          (homogeneousRewardCode sourceBlock D a)) * normSq x =
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode
          (homogeneousRewardCode sourceBlock D a))
  rw [hx]
  ring

/-- On the algebraic unit sphere, taking the angular part of the final raw
field removes precisely the added radial reward and recovers the raw
radius-cleanup field. -/
theorem angularField_finalFieldCode_of_normSq_one
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n)
    (x : RawWrapperSpace n) (hx : normSq x = 1) :
    angularField
        (PolynomialFieldCode.realize
          (finalFieldCode sourceBlock D P a)) x =
      PolynomialFieldCode.realize
        (rawWrapperFieldCode sourceBlock D P) x := by
  unfold angularField
  rw [radialReward_finalFieldCode_of_normSq_one
    sourceBlock D P a x hx, realize_finalFieldCode,
    realize_homogeneousAngularCode_of_normSq_one
      sourceBlock D P x hx]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Each scaled block radius is a continuous polynomial function of the
raw coordinates. -/
theorem continuous_scaledBlockRadius
    (sourceBlock : Fin n → Fin k) (b : Fin (k + 1)) :
    Continuous (fun x : RawWrapperSpace n ↦
      scaledBlockRadius sourceBlock x b) := by
  unfold scaledBlockRadius rawBlockNormSq
  apply continuous_const.mul
  apply continuous_finsetSum
  intro j _
  by_cases hj : ambientBlock sourceBlock j = b
  · simp only [hj, ↓reduceIte]
    fun_prop
  · simpa [hj] using
      (continuous_const :
        Continuous (fun _ : RawWrapperSpace n ↦ (0 : ℝ)))

/-- The scaled squared radius of one block, bundled as a bounded
continuous function on the genuine Euclidean unit sphere. -/
noncomputable def scaledBlockRadiusBCF
    (sourceBlock : Fin n → Fin k) (b : Fin (k + 1)) :
    EuclideanUnitSphere (EuclideanWrapperSpace n) →ᵇ ℝ := by
  exact BoundedContinuousFunction.mkOfCompact
    ⟨fun u ↦
      scaledBlockRadius sourceBlock
        (wrapperEuclideanEquiv.symm u.1) b,
      (continuous_scaledBlockRadius sourceBlock b).comp
        (wrapperEuclideanEquiv.symm.continuous.comp
          continuous_subtype_val)⟩

@[simp]
theorem scaledBlockRadiusBCF_apply
    (sourceBlock : Fin n → Fin k)
    (b : Fin (k + 1))
    (u : EuclideanUnitSphere (EuclideanWrapperSpace n)) :
    scaledBlockRadiusBCF sourceBlock b u =
      scaledBlockRadius sourceBlock
        (wrapperEuclideanEquiv.symm u.1) b :=
  rfl

/-- Radius-cleanup Lyapunov potential
`Σᵢ(sᵢ-sᵢ²/2)` in raw coordinates. -/
def radiusPotentialValue
    (sourceBlock : Fin n → Fin k)
    (x : RawWrapperSpace n) : ℝ :=
  ∑ b : Fin (k + 1),
    let s := scaledBlockRadius sourceBlock x b
    s - s ^ 2 / 2

/-- Radius dissipation in raw coordinates. -/
def radiusDissipationValue
    (sourceBlock : Fin n → Fin k)
    (x : RawWrapperSpace n) : ℝ :=
  radiusDissipation (k + 1 : ℝ)
    (fun b ↦ scaledBlockRadius sourceBlock x b)

/-- The cleanup potential is continuous in raw coordinates. -/
theorem continuous_radiusPotentialValue
    (sourceBlock : Fin n → Fin k) :
    Continuous (radiusPotentialValue sourceBlock) := by
  unfold radiusPotentialValue
  apply continuous_finsetSum
  intro b _
  let hs := continuous_scaledBlockRadius sourceBlock b
  exact hs.sub ((hs.pow 2).div_const 2)

/-- The radius dissipation is continuous in raw coordinates. -/
theorem continuous_radiusDissipationValue
    (sourceBlock : Fin n → Fin k) :
    Continuous (radiusDissipationValue sourceBlock) := by
  let s : RawWrapperSpace n → Fin (k + 1) → ℝ :=
    fun x b ↦ scaledBlockRadius sourceBlock x b
  have hs : ∀ b, Continuous (fun x ↦ s x b) :=
    fun b ↦ continuous_scaledBlockRadius sourceBlock b
  have havg :
      Continuous (fun x ↦ radiusAverage (k + 1 : ℝ) (s x)) := by
    unfold radiusAverage
    apply Continuous.div_const
    apply continuous_finsetSum
    intro b _
    exact (hs b).mul (continuous_const.sub (hs b))
  have hdev :
      ∀ b, Continuous
        (fun x ↦ radiusDeviation (k + 1 : ℝ) (s x) b) := by
    intro b
    unfold radiusDeviation
    exact (continuous_const.sub (hs b)).sub havg
  unfold radiusDissipationValue radiusDissipation
  apply continuous_const.mul
  apply continuous_finsetSum
  intro b _
  exact (hs b).mul ((hdev b).pow 2)

/-- The cleanup potential as a bounded continuous sphere observable. -/
noncomputable def radiusPotentialBCF
    (sourceBlock : Fin n → Fin k) :
    EuclideanUnitSphere (EuclideanWrapperSpace n) →ᵇ ℝ := by
  exact BoundedContinuousFunction.mkOfCompact
    ⟨fun u ↦ radiusPotentialValue sourceBlock
        (wrapperEuclideanEquiv.symm u.1),
      (continuous_radiusPotentialValue sourceBlock).comp
        (wrapperEuclideanEquiv.symm.continuous.comp
          continuous_subtype_val)⟩

/-- The radius dissipation as a bounded continuous sphere observable. -/
noncomputable def radiusDissipationBCF
    (sourceBlock : Fin n → Fin k) :
    EuclideanUnitSphere (EuclideanWrapperSpace n) →ᵇ ℝ := by
  exact BoundedContinuousFunction.mkOfCompact
    ⟨fun u ↦ radiusDissipationValue sourceBlock
        (wrapperEuclideanEquiv.symm u.1),
      (continuous_radiusDissipationValue sourceBlock).comp
        (wrapperEuclideanEquiv.symm.continuous.comp
          continuous_subtype_val)⟩

@[simp]
theorem radiusPotentialBCF_apply
    (sourceBlock : Fin n → Fin k)
    (u : EuclideanUnitSphere (EuclideanWrapperSpace n)) :
    radiusPotentialBCF sourceBlock u =
      radiusPotentialValue sourceBlock
        (wrapperEuclideanEquiv.symm u.1) :=
  rfl

@[simp]
theorem radiusDissipationBCF_apply
    (sourceBlock : Fin n → Fin k)
    (u : EuclideanUnitSphere (EuclideanWrapperSpace n)) :
    radiusDissipationBCF sourceBlock u =
      radiusDissipationValue sourceBlock
        (wrapperEuclideanEquiv.symm u.1) :=
  rfl

/-- Chain rule for one scaled block radius along an arbitrary
differentiable raw-coordinate curve. -/
theorem hasDerivAt_scaledBlockRadius
    (sourceBlock : Fin n → Fin k)
    {γ : ℝ → RawWrapperSpace n}
    {v : RawWrapperSpace n} {t : ℝ}
    (hγ : HasDerivAt γ v t)
    (b : Fin (k + 1)) :
    HasDerivAt
      (fun s ↦ scaledBlockRadius sourceBlock (γ s) b)
      (blockRadiusDirectionalDerivative sourceBlock (γ t) v b) t := by
  have hsum :
      HasDerivAt
        (fun s ↦ ∑ j : Fin (n + 1),
          if ambientBlock sourceBlock j = b then
            γ s j ^ 2
          else 0)
        (∑ j : Fin (n + 1),
          if ambientBlock sourceBlock j = b then
            2 * γ t j * v j
          else 0) t := by
    apply HasDerivAt.fun_sum
    intro j _
    by_cases hj : ambientBlock sourceBlock j = b
    · simp only [hj, ↓reduceIte]
      convert (hasDerivAt_pi.mp hγ j).pow 2 using 1
      ring
    · simpa [hj] using (hasDerivAt_const t (0 : ℝ))
  have hmul := (hasDerivAt_const t (k + 1 : ℝ)).mul hsum
  convert hmul using 1
  simp only [blockRadiusDirectionalDerivative, blockDotValue,
    Finset.mul_sum, zero_mul, Finset.sum_const_zero, zero_add]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : ambientBlock sourceBlock j = b
  · simp [hj]
    ring
  · simp [hj]

/-- Chain rule for the radius potential when the block radii have the
radius-cleanup derivatives. -/
theorem hasDerivAt_radiusPotentialValue
    (sourceBlock : Fin n → Fin k)
    {γ : ℝ → RawWrapperSpace n}
    {v : RawWrapperSpace n} {t : ℝ}
    (hγ : HasDerivAt γ v t)
    (hvelocity :
      ∀ b,
        blockRadiusDirectionalDerivative sourceBlock (γ t) v b =
          radiusRhs (k + 1 : ℝ)
            (fun i ↦ scaledBlockRadius sourceBlock (γ t) i) b) :
    HasDerivAt
      (fun s ↦ radiusPotentialValue sourceBlock (γ s))
      (radiusPhiDerivative (k + 1 : ℝ)
        (fun i ↦ scaledBlockRadius sourceBlock (γ t) i)) t := by
  unfold radiusPotentialValue radiusPhiDerivative
  apply HasDerivAt.fun_sum
  intro b _
  let sb : ℝ → ℝ :=
    fun s ↦ scaledBlockRadius sourceBlock (γ s) b
  have hsb :
      HasDerivAt sb
        (radiusRhs (k + 1 : ℝ)
          (fun i ↦ scaledBlockRadius sourceBlock (γ t) i) b) t := by
    simpa only [sb, hvelocity b] using
      hasDerivAt_scaledBlockRadius sourceBlock hγ b
  convert hsb.sub ((hsb.pow 2).div_const 2) using 1
  ring

/-- The raw wrapper makes the radius potential derivative equal the
nonnegative dissipation at every unit-radius point. -/
theorem hasDerivAt_radiusPotentialValue_rawWrapper
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    {γ : ℝ → RawWrapperSpace n} {t : ℝ}
    (hγ : HasDerivAt γ
      (PolynomialFieldCode.realize
        (rawWrapperFieldCode sourceBlock D P) (γ t)) t)
    (hunit : normSq (γ t) = 1) :
    HasDerivAt
      (fun s ↦ radiusPotentialValue sourceBlock (γ s))
      (radiusDissipationValue sourceBlock (γ t)) t := by
  have hchain :=
    hasDerivAt_radiusPotentialValue sourceBlock hγ
      (fun b ↦ blockRadiusDirectionalDerivative_rawWrapper
        sourceBlock D P (γ t) b)
  apply hchain.congr_deriv
  unfold radiusDissipationValue
  apply radiusPhiDerivative_eq_dissipation
  · positivity
  · rw [sum_scaledBlockRadius, hunit, mul_one]

/-- A Euclidean unit-sphere point has algebraic raw norm square one after
coordinate denormalization. -/
theorem normSq_wrapperEuclideanEquiv_symm_sphere
    (u : EuclideanUnitSphere (EuclideanWrapperSpace n)) :
    normSq (wrapperEuclideanEquiv.symm u.1) = 1 := by
  apply (norm_wrapperEuclideanEquiv_eq_one_iff
    (wrapperEuclideanEquiv.symm u.1)).mp
  simp only [wrapperEuclideanEquiv,
    ContinuousLinearEquiv.apply_symm_apply]
  have hu := u.property
  change dist u.1 0 = 1 at hu
  rw [dist_zero_right] at hu
  exact hu

/-- Exact raw-coordinate integral-curve equation along the Euclidean
unit-angular flow of the final field. -/
theorem euclideanUnitAngularFlow_raw_isIntegralCurve
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n)
    (u : EuclideanUnitSphere (EuclideanWrapperSpace n)) :
    IsIntegralCurve
      (fun t ↦ wrapperEuclideanEquiv.symm
        ((euclideanUnitAngularFlow
          (euclideanFinalField sourceBlock D P a)
          ((contDiff_euclideanFinalField
            sourceBlock D P a).of_le (by norm_num)))
          t u).1)
      (fun _ x ↦ PolynomialFieldCode.realize
        (rawWrapperFieldCode sourceBlock D P) x) := by
  intro t
  let Fraw :=
    PolynomialFieldCode.realize
      (finalFieldCode sourceBlock D P a)
  let F :=
    euclideanFinalField sourceBlock D P a
  let hF : ContDiff ℝ 1 F :=
    (contDiff_euclideanFinalField sourceBlock D P a).of_le
      (by norm_num)
  let γE : ℝ → EuclideanWrapperSpace n :=
    fun s ↦ (euclideanUnitAngularFlow F hF s u).1
  let γ : ℝ → RawWrapperSpace n :=
    fun s ↦ wrapperEuclideanEquiv.symm (γE s)
  have hnorm : ‖u.1‖ = 1 := by
    have hu := u.property
    change dist u.1 0 = 1 at hu
    rw [dist_zero_right] at hu
    exact hu
  have hE :
      HasDerivAt γE (innerAngularField F (γE t)) t := by
    change HasDerivAt
      (fun s ↦ euclideanAngularFlow F hF s u.1)
      (innerAngularField F
        (euclideanAngularFlow F hF t u.1)) t
    exact euclideanAngularFlow_isIntegralCurve F hF u.1 hnorm t
  have hraw := wrapperEuclideanEquiv.symm.hasFDerivAt.comp_hasDerivAt t hE
  have hunit : normSq (γ t) = 1 := by
    apply (norm_wrapperEuclideanEquiv_eq_one_iff (γ t)).mp
    have horbit :
        ‖(euclideanUnitAngularFlow F hF t u).1‖ = 1 := by
      have hu := (euclideanUnitAngularFlow F hF t u).property
      change
        dist (euclideanUnitAngularFlow F hF t u).1 0 = 1 at hu
      rw [dist_zero_right] at hu
      exact hu
    simpa only [γ, γE] using horbit
  have hang :
      angularField Fraw (γ t) =
        PolynomialFieldCode.realize
          (rawWrapperFieldCode sourceBlock D P) (γ t) :=
    angularField_finalFieldCode_of_normSq_one
      sourceBlock D P a (γ t) hunit
  have hconj :
      innerAngularField F (γE t) =
        wrapperEuclideanEquiv (angularField Fraw (γ t)) := by
    simpa only [F, Fraw, euclideanFinalField, γ, γE] using
      Veronese.innerAngularField_conjugateField_sourceEuclideanEquiv
        Fraw (γ t)
  simpa only [γ, γE, hconj, hang] using hraw

/-- The fully concrete radius-cleanup flow certificate for the compiled
Euclidean wrapper field. -/
noncomputable def radiusCleanupFlowCertificate
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n) :
    RadiusCleanupFlowCertificate
      (euclideanUnitAngularFlow
        (euclideanFinalField sourceBlock D P a)
        ((contDiff_euclideanFinalField
          sourceBlock D P a).of_le (by norm_num)))
      (k + 1) :=
  RadiusCleanupFlowCertificate.ofHasDerivAt
    (by omega)
    (scaledBlockRadiusBCF sourceBlock)
    (radiusPotentialBCF sourceBlock)
    (radiusDissipationBCF sourceBlock)
    (by
      intro u b
      simp only [scaledBlockRadiusBCF_apply, scaledBlockRadius,
        rawBlockNormSq]
      positivity)
    (by
      intro u
      simp only [scaledBlockRadiusBCF_apply]
      rw [sum_scaledBlockRadius,
        normSq_wrapperEuclideanEquiv_symm_sphere, mul_one]
      norm_num)
    (by
      intro u
      simp only [radiusDissipationBCF_apply,
        radiusDissipationValue, scaledBlockRadiusBCF_apply]
      norm_num)
    (by
      intro u t
      apply hasDerivAt_radiusPotentialValue_rawWrapper
        sourceBlock D P
      · exact euclideanUnitAngularFlow_raw_isIntegralCurve
          sourceBlock D P a u t
      · exact normSq_wrapperEuclideanEquiv_symm_sphere
          ((euclideanUnitAngularFlow
            (euclideanFinalField sourceBlock D P a)
            ((contDiff_euclideanFinalField
              sourceBlock D P a).of_le (by norm_num)))
            t u))

end UnitSpherePolynomialWrapper

end

end HGAS
