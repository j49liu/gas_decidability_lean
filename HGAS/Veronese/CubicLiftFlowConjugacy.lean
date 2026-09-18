import HGAS.Veronese.CubicLiftAngularFlow
import HGAS.Veronese.CubicLiftInvariantSandwich
import HGAS.Veronese.SourceAngularFlow
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Tactic

/-!
# Flow conjugacy on the signed Veronese core

This file turns the pointwise cubic-lift identities into a statement
about complete angular trajectories.

For a homogeneous source polynomial field `F`, its angular flow on the
ordinary unit sphere is mapped by the Veronese embedding to the
stabilized cubic angular flow on the weighted sphere.  There are two
real sheets, `ν(u)` and `-ν(u)`.  We therefore use the doubled source
space `Bool × sourceUnitSphere n`, with a frozen Boolean sign.

The main result,
`signedSource_to_stabilizedCore_semiconjugacy`, says that the exact
zero-penalty core of the stabilized cubic angular system is a
continuous surjective flow factor of those two signed copies.  This is
the form needed later for invariant-measure arguments.

The trajectory identities are proved directly from ODE uniqueness.
This avoids any informal appeal to uniqueness of a local
parametrization of the real Veronese cone.
-/

namespace HGAS.Veronese

open Set Function Metric
open scoped Topology NNReal

noncomputable section

variable {n k : ℕ} {F : HGAS.PolynomialField n}

def evaluatedSourceField
    (F : HGAS.PolynomialField n) :
    (Fin n → ℝ) → (Fin n → ℝ) :=
  fun u ↦ evalSourceField F u

theorem contDiff_evaluatedSourceField
    (F : HGAS.PolynomialField n) :
    ContDiff ℝ 1 (evaluatedSourceField F) := by
  have htop :
      ContDiff ℝ ⊤ (evaluatedSourceField F) := by
    rw [contDiff_pi]
    intro i
    exact HGAS.contDiff_eval₂Hom_rational_real_fintype (F i)
  exact htop.of_le (by norm_num)

noncomputable def polynomialSourceAngularAmbientFlow
    (F : HGAS.PolynomialField n) :
    Flow ℝ (Fin n → ℝ) :=
  sourceAngularAmbientFlow
    (evaluatedSourceField F)
    (contDiff_evaluatedSourceField F)

noncomputable def polynomialSourceAngularFlow
    (F : HGAS.PolynomialField n) :
    Flow ℝ (sourceUnitSphere n) :=
  sourceAngularFlow
    (evaluatedSourceField F)
    (contDiff_evaluatedSourceField F)

theorem continuous_veroneseMap_real :
    Continuous
      (veroneseMap (k := k) :
        (Fin n → ℝ) → RealVeroneseSpace n k) := by
  apply continuous_pi
  intro a
  unfold veroneseMap monomial
  fun_prop

theorem Q_veroneseMap_eq_one_of_sourceRadiusSq_eq_one
    (u : Fin n → ℝ) (hu : sourceRadiusSq u = 1) :
    Q (veroneseMap (k := k) u) = 1 := by
  rw [Q_veroneseMap]
  rw [show (∑ i, u i ^ 2) = 1 by
    simpa [sourceRadiusSq] using hu]
  simp

theorem Q_neg_veroneseMap_eq_one_of_sourceRadiusSq_eq_one
    (u : Fin n → ℝ) (hu : sourceRadiusSq u = 1) :
    Q (-veroneseMap (k := k) u) = 1 := by
  calc
    Q (-veroneseMap (k := k) u) =
        Q (veroneseMap (k := k) u) := by
      unfold Q
      simp
    _ = 1 :=
      Q_veroneseMap_eq_one_of_sourceRadiusSq_eq_one u hu

def positiveVeroneseSphereMap
    (k : ℕ) :
    sourceUnitSphere n → weightedUnitSphere n k :=
  fun u ↦ ⟨veroneseMap (k := k) u.1, by
    exact Q_veroneseMap_eq_one_of_sourceRadiusSq_eq_one u.1 u.2⟩

def negativeVeroneseSphereMap
    (k : ℕ) :
    sourceUnitSphere n → weightedUnitSphere n k :=
  fun u ↦ ⟨-veroneseMap (k := k) u.1, by
    exact Q_neg_veroneseMap_eq_one_of_sourceRadiusSq_eq_one u.1 u.2⟩

theorem continuous_positiveVeroneseSphereMap :
    Continuous (positiveVeroneseSphereMap (n := n) k) := by
  exact Continuous.subtype_mk
    (continuous_veroneseMap_real.comp continuous_subtype_val) _

theorem continuous_negativeVeroneseSphereMap :
    Continuous (negativeVeroneseSphereMap (n := n) k) := by
  exact Continuous.subtype_mk
    ((continuous_veroneseMap_real.comp continuous_subtype_val).neg) _

theorem weightedAngularField_stabilized_veronese
    (b : CubicLiftStabilizationBounds F k)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F)
    (hk : 1 ≤ k)
    (u : Fin n → ℝ) (hu : sourceRadiusSq u = 1) :
    weightedAngularField
        (evaluatedStabilizedCubicField b)
        (veroneseMap (k := k) u) =
      dVeronese u
        (HGAS.angularField
          (evaluatedSourceField F) u) := by
  have hpoint :
      evaluatedStabilizedCubicField b
          (veroneseMap (k := k) u) =
        evaluatedCubicLift (k := k) F
          (veroneseMap (k := k) u) := by
    exact eval_stabilizedCubicField_of_mem_toricZeroSet
      F b.K (veronese_mem_toricZeroSet u)
  unfold weightedAngularField weightedRadialReward
  rw [hpoint]
  exact weightedAngularField_cubicLiftField_veronese
    F hF hk u hu

theorem weightedAngularField_stabilized_neg_veronese
    (b : CubicLiftStabilizationBounds F k)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F)
    (hk : 1 ≤ k)
    (u : Fin n → ℝ) (hu : sourceRadiusSq u = 1) :
    weightedAngularField
        (evaluatedStabilizedCubicField b)
        (-veroneseMap (k := k) u) =
      -dVeronese u
        (HGAS.angularField
          (evaluatedSourceField F) u) := by
  have hpoint :
      evaluatedStabilizedCubicField b
          (-veroneseMap (k := k) u) =
        evaluatedCubicLift (k := k) F
          (-veroneseMap (k := k) u) := by
    exact eval_stabilizedCubicField_of_mem_toricZeroSet
      F b.K (neg_veronese_mem_toricZeroSet u)
  unfold weightedAngularField weightedRadialReward
  rw [hpoint]
  exact weightedAngularField_cubicLiftField_neg_veronese
    F hF hk u hu

set_option maxHeartbeats 800000 in
-- ODE uniqueness is instantiated on a finite-dimensional closed ball,
-- and elaborating the resulting Lipschitz and subtype obligations
-- benefits from a larger heartbeat budget.
theorem positive_veronese_ambient_flow_conjugacy
    (b : CubicLiftStabilizationBounds F k)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F)
    (hk : 1 ≤ k)
    (u : Fin n → ℝ) (hu : sourceRadiusSq u = 1) :
    ∀ t,
      veroneseMap (k := k)
          (polynomialSourceAngularAmbientFlow F t u) =
        stabilizedCubicAmbientAngularFlow b t
          (veroneseMap (k := k) u) := by
  let Y :=
    weightedAngularField (evaluatedStabilizedCubicField b)
  have hY : ContDiff ℝ 1 Y :=
    contDiff_weightedAngularField
      (contDiff_evaluatedStabilizedCubicField b)
  obtain ⟨K, hK⟩ :=
    hY.contDiffOn.exists_lipschitzOnWith
      one_ne_zero
      (convex_closedBall
        (0 : RealVeroneseSpace n k) 1)
      (isCompact_closedBall
        (0 : RealVeroneseSpace n k) 1)
  let γ₁ : ℝ → RealVeroneseSpace n k :=
    fun t ↦ veroneseMap (k := k)
      (polynomialSourceAngularAmbientFlow F t u)
  let γ₂ : ℝ → RealVeroneseSpace n k :=
    fun t ↦ stabilizedCubicAmbientAngularFlow b t
      (veroneseMap (k := k) u)
  have hsourceR :
      ∀ t, sourceRadiusSq
          (polynomialSourceAngularAmbientFlow F t u) = 1 :=
    sourceAngularAmbientFlow_preserves_radiusSq
      (evaluatedSourceField F)
      (contDiff_evaluatedSourceField F) u hu
  have hγ₁ : IsIntegralCurve γ₁ (fun _ ↦ Y) := by
    intro t
    have hs :=
      sourceAngularAmbientFlow_isIntegralCurve
        (evaluatedSourceField F)
        (contDiff_evaluatedSourceField F) u hu t
    have hv := HasDerivAt.veroneseMap (k := k) hs
    simpa [γ₁, Y,
      weightedAngularField_stabilized_veronese
        b hF hk _ (hsourceR t)] using hv
  have hγ₂ : IsIntegralCurve γ₂ (fun _ ↦ Y) := by
    simpa [γ₂, Y] using
      stabilizedCubicAmbientAngularFlow_isIntegralCurve
        b (veroneseMap (k := k) u)
        (Q_veroneseMap_eq_one_of_sourceRadiusSq_eq_one u hu)
  have hγ₁Q : ∀ t, Q (γ₁ t) = 1 := by
    intro t
    exact
      Q_veroneseMap_eq_one_of_sourceRadiusSq_eq_one
        _ (hsourceR t)
  have hγ₂Q : ∀ t, Q (γ₂ t) = 1 :=
    stabilizedCubicAmbientAngularFlow_preserves_Q
      b (veroneseMap (k := k) u)
      (Q_veroneseMap_eq_one_of_sourceRadiusSq_eq_one u hu)
  have heq : γ₁ = γ₂ := by
    apply ODE_solution_unique_univ
      (v := fun _ : ℝ ↦ Y)
      (s := fun _ ↦ closedBall
        (0 : RealVeroneseSpace n k) 1)
      (K := K) (t₀ := 0)
    · intro _
      exact hK
    · intro t
      exact ⟨hγ₁ t, by
        simpa [Metric.mem_closedBall, dist_zero_right] using
          norm_le_one_of_Q_eq_one (γ₁ t) (hγ₁Q t)⟩
    · intro t
      exact ⟨hγ₂ t, by
        simpa [Metric.mem_closedBall, dist_zero_right] using
          norm_le_one_of_Q_eq_one (γ₂ t) (hγ₂Q t)⟩
    · simp [γ₁, γ₂, Flow.map_zero_apply]
  intro t
  exact congrFun heq t

set_option maxHeartbeats 800000 in
-- This is the signed analogue of the preceding ODE-uniqueness proof;
-- the additional negation in the differentiated curve makes
-- elaboration comparably expensive.
theorem negative_veronese_ambient_flow_conjugacy
    (b : CubicLiftStabilizationBounds F k)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F)
    (hk : 1 ≤ k)
    (u : Fin n → ℝ) (hu : sourceRadiusSq u = 1) :
    ∀ t,
      -veroneseMap (k := k)
          (polynomialSourceAngularAmbientFlow F t u) =
        stabilizedCubicAmbientAngularFlow b t
          (-veroneseMap (k := k) u) := by
  let Y :=
    weightedAngularField (evaluatedStabilizedCubicField b)
  have hY : ContDiff ℝ 1 Y :=
    contDiff_weightedAngularField
      (contDiff_evaluatedStabilizedCubicField b)
  obtain ⟨K, hK⟩ :=
    hY.contDiffOn.exists_lipschitzOnWith
      one_ne_zero
      (convex_closedBall
        (0 : RealVeroneseSpace n k) 1)
      (isCompact_closedBall
        (0 : RealVeroneseSpace n k) 1)
  let γ₁ : ℝ → RealVeroneseSpace n k :=
    fun t ↦ -veroneseMap (k := k)
      (polynomialSourceAngularAmbientFlow F t u)
  let γ₂ : ℝ → RealVeroneseSpace n k :=
    fun t ↦ stabilizedCubicAmbientAngularFlow b t
      (-veroneseMap (k := k) u)
  have hsourceR :
      ∀ t, sourceRadiusSq
          (polynomialSourceAngularAmbientFlow F t u) = 1 :=
    sourceAngularAmbientFlow_preserves_radiusSq
      (evaluatedSourceField F)
      (contDiff_evaluatedSourceField F) u hu
  have hγ₁ : IsIntegralCurve γ₁ (fun _ ↦ Y) := by
    intro t
    have hs :=
      sourceAngularAmbientFlow_isIntegralCurve
        (evaluatedSourceField F)
        (contDiff_evaluatedSourceField F) u hu t
    have hv := (HasDerivAt.veroneseMap (k := k) hs).neg
    simpa [γ₁, Y,
      weightedAngularField_stabilized_neg_veronese
        b hF hk _ (hsourceR t)] using hv
  have hγ₂ : IsIntegralCurve γ₂ (fun _ ↦ Y) := by
    simpa [γ₂, Y] using
      stabilizedCubicAmbientAngularFlow_isIntegralCurve
        b (-veroneseMap (k := k) u)
        (Q_neg_veroneseMap_eq_one_of_sourceRadiusSq_eq_one u hu)
  have hγ₁Q : ∀ t, Q (γ₁ t) = 1 := by
    intro t
    exact
      Q_neg_veroneseMap_eq_one_of_sourceRadiusSq_eq_one
        _ (hsourceR t)
  have hγ₂Q : ∀ t, Q (γ₂ t) = 1 :=
    stabilizedCubicAmbientAngularFlow_preserves_Q
      b (-veroneseMap (k := k) u)
      (Q_neg_veroneseMap_eq_one_of_sourceRadiusSq_eq_one u hu)
  have heq : γ₁ = γ₂ := by
    apply ODE_solution_unique_univ
      (v := fun _ : ℝ ↦ Y)
      (s := fun _ ↦ closedBall
        (0 : RealVeroneseSpace n k) 1)
      (K := K) (t₀ := 0)
    · intro _
      exact hK
    · intro t
      exact ⟨hγ₁ t, by
        simpa [Metric.mem_closedBall, dist_zero_right] using
          norm_le_one_of_Q_eq_one (γ₁ t) (hγ₁Q t)⟩
    · intro t
      exact ⟨hγ₂ t, by
        simpa [Metric.mem_closedBall, dist_zero_right] using
          norm_le_one_of_Q_eq_one (γ₂ t) (hγ₂Q t)⟩
    · simp [γ₁, γ₂, Flow.map_zero_apply]
  intro t
  exact congrFun heq t

theorem positiveVeroneseSphereMap_semiconj
    (b : CubicLiftStabilizationBounds F k)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F)
    (hk : 1 ≤ k)
    (t : ℝ) :
    Function.Semiconj
      (positiveVeroneseSphereMap (n := n) k)
      (polynomialSourceAngularFlow F t)
      (stabilizedCubicAngularFlow b t) := by
  intro u
  apply Subtype.ext
  simpa [positiveVeroneseSphereMap,
    polynomialSourceAngularFlow, sourceAngularFlow,
    stabilizedCubicAngularFlow, weightedUnitSphereFlow] using
    positive_veronese_ambient_flow_conjugacy
      b hF hk u.1 u.2 t

theorem negativeVeroneseSphereMap_semiconj
    (b : CubicLiftStabilizationBounds F k)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F)
    (hk : 1 ≤ k)
    (t : ℝ) :
    Function.Semiconj
      (negativeVeroneseSphereMap (n := n) k)
      (polynomialSourceAngularFlow F t)
      (stabilizedCubicAngularFlow b t) := by
  intro u
  apply Subtype.ext
  simpa [negativeVeroneseSphereMap,
    polynomialSourceAngularFlow, sourceAngularFlow,
    stabilizedCubicAngularFlow, weightedUnitSphereFlow] using
    negative_veronese_ambient_flow_conjugacy
      b hF hk u.1 u.2 t

/-! ## The signed source sphere and the Veronese core -/

/-- Two disjoint copies of the source angular flow.  The Boolean
coordinate records the sign of the Veronese sheet and remains frozen
along the flow. -/
noncomputable def signedSourceAngularFlow
    (F : HGAS.PolynomialField n) :
    Flow ℝ (Bool × sourceUnitSphere n) where
  toFun t x := (x.1, polynomialSourceAngularFlow F t x.2)
  cont' := by
    exact
      continuous_snd.fst.prodMk
        ((polynomialSourceAngularFlow F).cont'.comp
          (continuous_fst.prodMk continuous_snd.snd))
  map_add' t₁ t₂ x := by
    apply Prod.ext
    · rfl
    · change
        polynomialSourceAngularFlow F (t₁ + t₂) x.2 =
          polynomialSourceAngularFlow F t₁
            (polynomialSourceAngularFlow F t₂ x.2)
      exact Flow.map_add _ _ _ _
  map_zero' x := by
    apply Prod.ext
    · rfl
    · change polynomialSourceAngularFlow F 0 x.2 = x.2
      exact Flow.map_zero_apply _ _

/-- The signed Veronese map from the doubled source sphere to the
weighted sphere. -/
def signedVeroneseSphereMap
    (k : ℕ) :
    Bool × sourceUnitSphere n → weightedUnitSphere n k :=
  fun x ↦
    if x.1 then
      positiveVeroneseSphereMap k x.2
    else
      negativeVeroneseSphereMap k x.2

theorem continuous_signedVeroneseSphereMap :
    Continuous (signedVeroneseSphereMap (n := n) k) := by
  rw [continuous_prod_of_discrete_left]
  intro s
  cases s
  · simpa [signedVeroneseSphereMap] using
      (continuous_negativeVeroneseSphereMap (n := n) (k := k) :
        Continuous
          (negativeVeroneseSphereMap (n := n) k))
  · simpa [signedVeroneseSphereMap] using
      (continuous_positiveVeroneseSphereMap (n := n) (k := k) :
        Continuous
          (positiveVeroneseSphereMap (n := n) k))

theorem signedVeroneseSphereMap_mem_core
    (x : Bool × sourceUnitSphere n) :
    signedVeroneseSphereMap (n := n) k x ∈
      stabilizedConeCore n k := by
  cases x with
  | mk s u =>
      cases s <;>
        simp [signedVeroneseSphereMap, stabilizedConeCore,
          positiveVeroneseSphereMap, negativeVeroneseSphereMap,
          completeToricEnergy]

/-- The signed Veronese map with codomain restricted to the exact
zero-penalty core. -/
def signedVeroneseCoreMap
    (k : ℕ) :
    Bool × sourceUnitSphere n → stabilizedConeCore n k :=
  fun x ↦
    ⟨signedVeroneseSphereMap k x,
      signedVeroneseSphereMap_mem_core x⟩

theorem continuous_signedVeroneseCoreMap :
    Continuous (signedVeroneseCoreMap (n := n) k) :=
  Continuous.subtype_mk
    (continuous_signedVeroneseSphereMap (n := n) (k := k)) _

theorem surjective_signedVeroneseCoreMap
    (hk : 1 ≤ k) :
    Function.Surjective (signedVeroneseCoreMap (n := n) k) := by
  intro y
  obtain ⟨u, hu, hy | hy⟩ :=
    (completeToricEnergy_eq_zero_on_weightedUnitSphere_iff
      hk y.1.1 y.1.2).mp y.2
  · refine ⟨(true, ⟨u, hu⟩), ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simpa [signedVeroneseCoreMap, signedVeroneseSphereMap,
      positiveVeroneseSphereMap] using hy.symm
  · refine ⟨(false, ⟨u, hu⟩), ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simpa [signedVeroneseCoreMap, signedVeroneseSphereMap,
      negativeVeroneseSphereMap] using hy.symm

theorem stabilizedConeCore_isInvariant
    (b : CubicLiftStabilizationBounds F k)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F)
    (hk : 1 ≤ k) :
    IsInvariant (stabilizedCubicAngularFlow b)
      (stabilizedConeCore n k) := by
  intro t y hy
  obtain ⟨u, hu, hy' | hy'⟩ :=
    (completeToricEnergy_eq_zero_on_weightedUnitSphere_iff
      hk y.1 y.2).mp hy
  · have hflow :=
      positiveVeroneseSphereMap_semiconj b hF hk t
        (⟨u, hu⟩ : sourceUnitSphere n)
    have hySub :
        y = positiveVeroneseSphereMap k ⟨u, hu⟩ := by
      apply Subtype.ext
      simpa [positiveVeroneseSphereMap] using hy'
    rw [hySub, ← hflow]
    exact signedVeroneseSphereMap_mem_core
      (k := k) (true, polynomialSourceAngularFlow F t ⟨u, hu⟩)
  · have hflow :=
      negativeVeroneseSphereMap_semiconj b hF hk t
        (⟨u, hu⟩ : sourceUnitSphere n)
    have hySub :
        y = negativeVeroneseSphereMap k ⟨u, hu⟩ := by
      apply Subtype.ext
      simpa [negativeVeroneseSphereMap] using hy'
    rw [hySub, ← hflow]
    exact signedVeroneseSphereMap_mem_core
      (k := k) (false, polynomialSourceAngularFlow F t ⟨u, hu⟩)

/-- The stabilized angular flow restricted to its invariant
zero-penalty Veronese core. -/
noncomputable def stabilizedCubicCoreFlow
    (b : CubicLiftStabilizationBounds F k)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F)
    (hk : 1 ≤ k) :
    Flow ℝ (stabilizedConeCore n k) :=
  (stabilizedCubicAngularFlow b).restrict
    (stabilizedConeCore_isInvariant b hF hk)

theorem signedVeroneseCoreMap_semiconj
    (b : CubicLiftStabilizationBounds F k)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F)
    (hk : 1 ≤ k)
    (t : ℝ) :
    Function.Semiconj
      (signedVeroneseCoreMap (n := n) k)
      (signedSourceAngularFlow F t)
      (stabilizedCubicCoreFlow b hF hk t) := by
  intro x
  apply Subtype.ext
  cases x with
  | mk s u =>
      cases s
      · exact negativeVeroneseSphereMap_semiconj b hF hk t u
      · exact positiveVeroneseSphereMap_semiconj b hF hk t u

/-- The exact zero-penalty core is a continuous flow factor of two
signed copies of the source angular system. -/
theorem signedSource_to_stabilizedCore_semiconjugacy
    (b : CubicLiftStabilizationBounds F k)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F)
    (hk : 1 ≤ k) :
    Flow.IsSemiconjugacy
      (signedVeroneseCoreMap (n := n) k)
      (signedSourceAngularFlow F)
      (stabilizedCubicCoreFlow b hF hk) where
  cont := continuous_signedVeroneseCoreMap
  surj := surjective_signedVeroneseCoreMap hk
  semiconj := signedVeroneseCoreMap_semiconj b hF hk

end

end HGAS.Veronese
