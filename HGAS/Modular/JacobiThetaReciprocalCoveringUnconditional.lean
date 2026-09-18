import HGAS.Modular.JacobiThetaProjectiveGram
import HGAS.Modular.LinkedJacobiThetaReciprocalPath
import HGAS.Topology.ProperLocalHomeomorphCovering

/-!
# Unconditional reciprocal theta covering and coherent lift

The fixed-torus reciprocal theta map is both a local homeomorphism and
proper.  It is therefore a genuine covering map.  This closes the
global continuation gap isolated in
`JacobiThetaReciprocalCovering`.

For applications we ultimately want an honest complex elliptic
parameter, not merely a torus class.  A continuous real-line path in
the torus lifts coordinatewise through

```
                         ℝ → AddCircle 2.
```

Combining those two covering lifts with the moving-lattice coordinate
homeomorphism produces an unconditional continuous path in
`JacobiThetaReciprocalDomain`, whose normalized theta vector is the
prescribed residual path.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open Complex Real Set Topology

noncomputable section

local instance reciprocalCoveringLevelTwoPeriodPositive :
    Fact (0 < (2 : ℝ)) :=
  ⟨by norm_num⟩

/-- **Unconditional reciprocal theta covering on the fixed torus.** -/
theorem fixedLevelTwoReciprocalTorusMap_isCoveringMap :
    IsCoveringMap fixedLevelTwoReciprocalTorusMap :=
  HGAS.Topology.IsProperMap.isCoveringMap_of_isLocalHomeomorph
    fixedLevelTwoReciprocalTorusMap_isProperMap
    fixedLevelTwoReciprocalTorusMap_isLocalHomeomorph

/-- Every continuous real path in the reciprocal residual family has a
continuous lift to the fixed reciprocal torus. -/
theorem fixedLevelTwoReciprocalTorusMap_exists_continuous_lift
    (y : C(ℝ, JacobiThetaReciprocalTotal))
    (t₀ : ℝ) :
    ∃ q : C(ℝ, FixedLevelTwoReciprocalTorusDomain),
      fixedLevelTwoReciprocalTorusMap ∘ q = y := by
  obtain ⟨q₀, hq₀⟩ :=
    fixedLevelTwoReciprocalTorusMap_surjective (y t₀)
  obtain ⟨q, hq, -⟩ :=
    fixedLevelTwoReciprocalTorusMap_isCoveringMap
      |>.existsUnique_continuousMap_lifts
        y t₀ q₀ hq₀
  exact ⟨q, hq.2⟩

/-- The quotient `ℝ → AddCircle 2` is surjective. -/
theorem levelTwoAddCircle_coe_surjective :
    Function.Surjective
      (fun x : ℝ => (x : LevelTwoAddCircle)) :=
  (QuotientAddGroup.isOpenQuotientMap_mk :
    IsOpenQuotientMap
      (fun x : ℝ => (x : LevelTwoAddCircle))).surjective

/-- A torus-valued real path lifts to the fixed real elliptic
coordinates, while preserving the reciprocal divisor condition. -/
theorem
    fixedLevelTwoReciprocalRestrictedQuotient_exists_continuous_lift
    (q : C(ℝ, FixedLevelTwoReciprocalTorusDomain))
    (t₀ : ℝ) :
    ∃ r : C(ℝ, FixedLevelTwoReciprocalRealDomain),
      fixedLevelTwoReciprocalRestrictedQuotient ∘ r = q := by
  let qa : C(ℝ, LevelTwoAddCircle) :=
    ⟨fun t => (q t).1.2.1, by
      fun_prop⟩
  let qb : C(ℝ, LevelTwoAddCircle) :=
    ⟨fun t => (q t).1.2.2, by
      fun_prop⟩
  obtain ⟨a₀, ha₀⟩ :=
    levelTwoAddCircle_coe_surjective (qa t₀)
  obtain ⟨b₀, hb₀⟩ :=
    levelTwoAddCircle_coe_surjective (qb t₀)
  obtain ⟨a, ha, -⟩ :=
    (AddCircle.isCoveringMap_coe (2 : ℝ))
      |>.existsUnique_continuousMap_lifts
        qa t₀ a₀ ha₀
  obtain ⟨b, hb, -⟩ :=
    (AddCircle.isCoveringMap_coe (2 : ℝ))
      |>.existsUnique_continuousMap_lifts
        qb t₀ b₀ hb₀
  have ha_value (t : ℝ) :
      (a t : LevelTwoAddCircle) =
        (q t).1.2.1 :=
    congrFun ha.2 t
  have hb_value (t : ℝ) :
      (b t : LevelTwoAddCircle) =
        (q t).1.2.2 :=
    congrFun hb.2 t
  have hquotient (t : ℝ) :
      fixedLevelTwoTorusQuotient
          ((q t).1.1, (a t, b t)) =
        (q t).1 := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · exact ha_value t
      · exact hb_value t
  let r : C(ℝ, FixedLevelTwoReciprocalRealDomain) :=
    ⟨fun t =>
      ⟨((q t).1.1, (a t, b t)), by
        rw [hquotient t]
        exact (q t).2⟩,
      by
        rw [continuous_induced_rng]
        exact
          ((continuous_fst.comp
              (continuous_subtype_val.comp q.continuous)).prodMk
            (a.continuous.prodMk b.continuous))⟩
  refine ⟨r, ?_⟩
  funext t
  apply Subtype.ext
  exact hquotient t

/-- **Unconditional analytic path lift.**

Every continuous real path in the affine reciprocal residual family is
represented by continuously varying `(τ,z)` with `θ₁(z|τ) ≠ 0`. -/
theorem
    jacobiThetaReciprocalTotal_exists_continuous_lift_unconditional
    (y : C(ℝ, JacobiThetaReciprocalTotal))
    (t₀ : ℝ) :
    ∃ p : C(ℝ, JacobiThetaReciprocalDomain),
      jacobiThetaReciprocalTotalMap ∘ p = y := by
  obtain ⟨q, hq⟩ :=
    fixedLevelTwoReciprocalTorusMap_exists_continuous_lift
      y t₀
  obtain ⟨r, hr⟩ :=
    fixedLevelTwoReciprocalRestrictedQuotient_exists_continuous_lift
      q t₀
  let p : C(ℝ, JacobiThetaReciprocalDomain) :=
    ⟨fixedLevelTwoReciprocalAnalyticDomainMap ∘ r,
      continuous_fixedLevelTwoReciprocalAnalyticDomainMap.comp
        r.continuous⟩
  refine ⟨p, ?_⟩
  funext t
  calc
    jacobiThetaReciprocalTotalMap (p t) =
        fixedLevelTwoReciprocalRealMap (r t) :=
      rfl
    _ =
        fixedLevelTwoReciprocalTorusMap
          (fixedLevelTwoReciprocalRestrictedQuotient
            (r t)) :=
      (fixedLevelTwoReciprocalTorusMap_quotient_apply
        (r t)).symm
    _ =
        fixedLevelTwoReciprocalTorusMap (q t) := by
      exact
        congrArg fixedLevelTwoReciprocalTorusMap
          (congrFun hr t)
    _ = y t :=
      congrFun hq t

/-! ## Unconditional coherent Bloch parameter selection -/

/-- The reciprocal covering construction supplies an unconditional
coherent projective theta lift for every linked residual trajectory. -/
theorem exists_coherentJacobiThetaProjectiveLift_unconditional
    {κZ κPhi : ℂ}
    {T : ℝ → ℍ} {z : ℝ → LinkedJacobiState ℂ}
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z)
    {t₀ : ℝ}
    (hB : UnaryModularState.B (z t₀).unary ≠ 0)
    (hresidual :
      ∀ i : LinkedJacobiResidualIndex,
        linkedJacobiResidual i (z t₀) = 0)
    (hT : Continuous T)
    (d : CoherentJacobiCoefficientTwist T z) :
    ∃ ξ : ℝ → ℂ,
      IsCoherentJacobiThetaProjectiveLift T z d ξ := by
  let y :=
    coherentLinkedJacobiReciprocalPath
      hz hB hresidual hT d
  obtain ⟨p, hp⟩ :=
    jacobiThetaReciprocalTotal_exists_continuous_lift_unconditional
      y t₀
  let ξ : ℝ → ℂ := fun t ↦ (p t).parameter
  have hvalue (t : ℝ) :
      jacobiThetaReciprocalTotalMap (p t) = y t :=
    congrFun hp t
  have hmodulus (t : ℝ) :
      (p t).modulus = T t := by
    exact
      congrArg JacobiThetaReciprocalTotal.modulus
        (hvalue t)
  have hcoordinates (t : ℝ) :
      jacobiThetaReciprocalCoordinates
          (p t).modulus (p t).parameter =
        jacobiReciprocalNormalize
          (coherentTwistedJacobiProjectiveCoordinates d t) := by
    exact
      congrArg JacobiThetaReciprocalTotal.coordinates
        (hvalue t)
  refine ⟨ξ, ?_⟩
  constructor
  · exact
      continuous_snd.comp
        (continuous_jacobiThetaReciprocalDomain_toBase.comp
          p.continuous)
  · intro t
    have hpnonzero := (p t).thetaOne_ne_zero
    rw [hmodulus t] at hpnonzero
    simpa only [ξ, jacobiThetaVector,
      Matrix.cons_val_zero] using hpnonzero
  · intro t k
    let X :=
      coherentTwistedJacobiProjectiveCoordinates d t
    have hX0 : X 0 ≠ 0 :=
      coherentTwistedJacobiProjectiveCoordinates_zero_ne_zero
        hz hresidual d t
    have htheta0 :
        jacobiThetaVector (ξ t) (T t : ℂ) 0 ≠ 0 := by
      have hpnonzero := (p t).thetaOne_ne_zero
      rw [hmodulus t] at hpnonzero
      simpa only [ξ, jacobiThetaVector,
        Matrix.cons_val_zero] using hpnonzero
    have hratio (j : Fin 3) :
        jacobiThetaVector (ξ t) (T t : ℂ) j.succ /
              jacobiThetaVector (ξ t) (T t : ℂ) 0 =
            X j.succ / X 0 := by
      have hj := congrFun (hcoordinates t) j
      rw [hmodulus t] at hj
      simpa only [jacobiThetaReciprocalCoordinates,
        jacobiReciprocalNormalize, ξ, X] using hj
    change
      jacobiThetaVector (ξ t) (T t : ℂ) 0 * X k =
        X 0 * jacobiThetaVector (ξ t) (T t : ℂ) k
    fin_cases k
    · change
        jacobiThetaVector (ξ t) (T t : ℂ) 0 * X 0 =
          X 0 * jacobiThetaVector (ξ t) (T t : ℂ) 0
      exact mul_comm _ _
    · have hcross :=
        (div_eq_div_iff htheta0 hX0).mp (hratio 0)
      calc
        jacobiThetaVector (ξ t) (T t : ℂ) 0 * X 1 =
            X 1 *
              jacobiThetaVector (ξ t) (T t : ℂ) 0 := by
          ring
        _ =
            jacobiThetaVector (ξ t) (T t : ℂ) 1 * X 0 :=
          hcross.symm
        _ =
            X 0 *
              jacobiThetaVector (ξ t) (T t : ℂ) 1 := by
          ring
    · have hcross :=
        (div_eq_div_iff htheta0 hX0).mp (hratio 1)
      calc
        jacobiThetaVector (ξ t) (T t : ℂ) 0 * X 2 =
            X 2 *
              jacobiThetaVector (ξ t) (T t : ℂ) 0 := by
          ring
        _ =
            jacobiThetaVector (ξ t) (T t : ℂ) 2 * X 0 :=
          hcross.symm
        _ =
            X 0 *
              jacobiThetaVector (ξ t) (T t : ℂ) 2 := by
          ring
    · have hcross :=
        (div_eq_div_iff htheta0 hX0).mp (hratio 2)
      calc
        jacobiThetaVector (ξ t) (T t : ℂ) 0 * X 3 =
            X 3 *
              jacobiThetaVector (ξ t) (T t : ℂ) 0 := by
          ring
        _ =
            jacobiThetaVector (ξ t) (T t : ℂ) 3 * X 0 :=
          hcross.symm
        _ =
            X 0 *
              jacobiThetaVector (ξ t) (T t : ℂ) 3 := by
          ring

/-- Unconditional end-to-end continuous Bloch seed parameters. -/
theorem
    exists_continuous_twistedBlochSeed_parameters_unconditional
    {κZ κPhi : ℂ}
    {T : ℝ → ℍ} {z : ℝ → LinkedJacobiState ℂ}
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z)
    {t₀ : ℝ}
    (hB : UnaryModularState.B (z t₀).unary ≠ 0)
    (hresidual :
      ∀ i : LinkedJacobiResidualIndex,
        linkedJacobiResidual i (z t₀) = 0)
    (hT : Continuous T)
    (d : CoherentJacobiCoefficientTwist T z)
    (w : ℝ → ℂ) :
    ∃ S ξ L : ℝ → ℂ,
      Continuous S ∧ Continuous ξ ∧ Continuous L ∧
      ∀ t,
        ∃ seed :
            TwistedJacobiBlochSeed (T t) (z t) (w t),
          seed.d₁ = d.d₁ ∧
          seed.d₂ = d.d₂ ∧
          seed.S = S t ∧
          seed.ξ = ξ t ∧
          seed.L = L t := by
  obtain ⟨ξ, hξ⟩ :=
    exists_coherentJacobiThetaProjectiveLift_unconditional
      hz hB hresidual hT d
  obtain ⟨S, L, hS, hξcontinuous, hL, hseed⟩ :=
    exists_continuous_twistedBlochSeed_parameters_of_projectiveLift
      hz hresidual hT d hξ w
  exact
    ⟨S, ξ, L, hS, hξcontinuous, hL, hseed⟩

end

end HGAS.Modular
