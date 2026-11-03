import Stability.Dynamics.LocalAsymptoticStability
import HGAS.Stability.PaddingLyapunov

/-!
# Local asymptotic stability of products and coordinate changes

The exact-degree construction adjoins an independent stable planar system.
These lemmas show that local asymptotic stability is preserved and reflected
by products, and is unchanged by continuous linear coordinate equivalences.
The corresponding GAS and Lyapunov-stability results are already available
in `HGAS`. All statements include the local existence requirements of the
trajectory-based definitions.
-/

namespace Stability

open HGAS

noncomputable section

variable {E H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Independent locally attracting systems have a locally attracting product,
including existence of forward trajectories from nearby initial states. -/
theorem LocallyAttractiveWithExistence.prod
    {F : E → E} {G : H → H}
    (hF : LocallyAttractiveWithExistence F 0)
    (hG : LocallyAttractiveWithExistence G 0) :
    LocallyAttractiveWithExistence (productField F G) (0, 0) := by
  obtain ⟨rF, hrF, hbasinF⟩ := hF
  obtain ⟨rG, hrG, hbasinG⟩ := hG
  refine ⟨min rF rG, lt_min hrF hrG, ?_⟩
  rintro ⟨x₀, y₀⟩ hxy
  rw [Prod.dist_eq, max_lt_iff] at hxy
  have hx : dist x₀ 0 < rF := hxy.1.trans_le (min_le_left _ _)
  have hy : dist y₀ 0 < rG := hxy.2.trans_le (min_le_right _ _)
  refine ⟨?_, ?_⟩
  · obtain ⟨γ, hγ⟩ := (hbasinF x₀ hx).1
    obtain ⟨η, hη⟩ := (hbasinG y₀ hy).1
    exact ⟨fun t ↦ (γ t, η t), hγ.prodMk hη⟩
  · intro γ hγ ε hε
    obtain ⟨TF, hTF, hafterF⟩ := (hbasinF x₀ hx).2 _ hγ.fst_product ε hε
    obtain ⟨TG, hTG, hafterG⟩ := (hbasinG y₀ hy).2 _ hγ.snd_product ε hε
    refine ⟨max TF TG, hTF.trans (le_max_left _ _), ?_⟩
    intro t ht
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨hafterF t ((le_max_left _ _).trans ht),
      hafterG t ((le_max_right _ _).trans ht)⟩

/-- Restriction to the invariant first factor reflects local attraction. -/
theorem LocallyAttractiveWithExistence.fst_of_product
    {F : E → E} {G : H → H}
    (h : LocallyAttractiveWithExistence (productField F G) (0, 0))
    (hG : G 0 = 0) : LocallyAttractiveWithExistence F 0 := by
  obtain ⟨r, hr, hbasin⟩ := h
  refine ⟨r, hr, ?_⟩
  intro x₀ hx
  have hpair : dist (x₀, (0 : H)) (0, 0) < r := by
    simpa [Prod.dist_eq] using hx
  refine ⟨?_, ?_⟩
  · obtain ⟨γ, hγ⟩ := (hbasin (x₀, 0) hpair).1
    exact ⟨fun t ↦ (γ t).1, hγ.fst_product⟩
  · intro γ hγ ε hε
    have hprod := hγ.prodMk (isForwardTrajectory_const_of_equilibrium hG)
    obtain ⟨T, hT, hafter⟩ := (hbasin (x₀, 0) hpair).2 _ hprod ε hε
    exact ⟨T, hT, fun t ht ↦ by simpa [Prod.dist_eq] using hafter t ht⟩

/-- Restriction to the invariant second factor reflects local attraction. -/
theorem LocallyAttractiveWithExistence.snd_of_product
    {F : E → E} {G : H → H}
    (h : LocallyAttractiveWithExistence (productField F G) (0, 0))
    (hF : F 0 = 0) : LocallyAttractiveWithExistence G 0 := by
  obtain ⟨r, hr, hbasin⟩ := h
  refine ⟨r, hr, ?_⟩
  intro y₀ hy
  have hpair : dist ((0 : E), y₀) (0, 0) < r := by
    simpa [Prod.dist_eq] using hy
  refine ⟨?_, ?_⟩
  · obtain ⟨γ, hγ⟩ := (hbasin (0, y₀) hpair).1
    exact ⟨fun t ↦ (γ t).2, hγ.snd_product⟩
  · intro γ hγ ε hε
    have hprod := (isForwardTrajectory_const_of_equilibrium hF).prodMk hγ
    obtain ⟨T, hT, hafter⟩ := (hbasin (0, y₀) hpair).2 _ hprod ε hε
    exact ⟨T, hT, fun t ht ↦ by simpa [Prod.dist_eq] using hafter t ht⟩

/-- Local asymptotic stability of a product is equivalent to local
asymptotic stability of both factors. -/
theorem locallyAsymptoticallyStable_productField_iff
    (F : E → E) (G : H → H) :
    LocallyAsymptoticallyStable (productField F G) (0, 0) ↔
      LocallyAsymptoticallyStable F 0 ∧ LocallyAsymptoticallyStable G 0 := by
  constructor
  · intro h
    have hF : F 0 = 0 := congrArg Prod.fst h.equilibrium
    have hG : G 0 = 0 := congrArg Prod.snd h.equilibrium
    obtain ⟨hsF, hsG⟩ := (lyapunovStableWithExistence_productField_iff F G).mp h.stable
    exact ⟨⟨hF, hsF, h.attractive.fst_of_product hG⟩,
      ⟨hG, hsG, h.attractive.snd_of_product hF⟩⟩
  · rintro ⟨hF, hG⟩
    exact ⟨by simp [productField, hF.equilibrium, hG.equilibrium],
      (lyapunovStableWithExistence_productField_iff F G).mpr ⟨hF.stable, hG.stable⟩,
      hF.attractive.prod hG.attractive⟩

/-- Local attraction with forward existence is preserved by a continuous
linear change of coordinates. -/
theorem LocallyAttractiveWithExistence.conjugateField
    (e : E ≃L[ℝ] H) {F : E → E}
    (h : LocallyAttractiveWithExistence F 0) :
    LocallyAttractiveWithExistence (conjugateField e F) 0 := by
  let C : ℝ := max ‖e.toContinuousLinearMap‖ 1
  let D : ℝ := max ‖e.symm.toContinuousLinearMap‖ 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have heBound : ∀ x : E, ‖e x‖ ≤ C * ‖x‖ := fun x ↦
    (e.toContinuousLinearMap.le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg x))
  have hesymmBound : ∀ y : H, ‖e.symm y‖ ≤ D * ‖y‖ := fun y ↦
    (e.symm.toContinuousLinearMap.le_opNorm y).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg y))
  obtain ⟨r, hr, hbasin⟩ := h
  refine ⟨r / D, div_pos hr hD, ?_⟩
  intro y₀ hy₀
  have hx₀ : dist (e.symm y₀) 0 < r := by
    rw [dist_zero_right]
    rw [dist_zero_right] at hy₀
    calc
      ‖e.symm y₀‖ ≤ D * ‖y₀‖ := hesymmBound y₀
      _ < D * (r / D) := mul_lt_mul_of_pos_left hy₀ hD
      _ = r := by field_simp
  refine ⟨?_, ?_⟩
  · obtain ⟨γ, hγ⟩ := (hbasin (e.symm y₀) hx₀).1
    refine ⟨fun t ↦ e (γ t), ?_⟩
    simpa using hγ.map_continuousLinearEquiv e
  · intro η hη ε hε
    have hγ : IsForwardTrajectory F (fun t ↦ e.symm (η t)) (e.symm y₀) :=
      hη.comap_continuousLinearEquiv e
    obtain ⟨T, hT, hafter⟩ :=
      (hbasin (e.symm y₀) hx₀).2 _ hγ (ε / C) (div_pos hε hC)
    refine ⟨T, hT, ?_⟩
    intro t ht
    have hsmall := hafter t ht
    rw [dist_zero_right] at hsmall ⊢
    calc
      ‖η t‖ = ‖e (e.symm (η t))‖ := by simp
      _ ≤ C * ‖e.symm (η t)‖ := heBound _
      _ < C * (ε / C) := mul_lt_mul_of_pos_left hsmall hC
      _ = ε := by field_simp

/-- Local asymptotic stability is preserved by continuous linear
coordinate equivalences. -/
theorem LocallyAsymptoticallyStable.conjugateField
    (e : E ≃L[ℝ] H) {F : E → E}
    (h : LocallyAsymptoticallyStable F 0) :
    LocallyAsymptoticallyStable (conjugateField e F) 0 :=
  ⟨conjugateField_zero e h.equilibrium,
    h.stable.conjugateField e, h.attractive.conjugateField e⟩

/-- Coordinate-invariant form of local asymptotic stability. -/
theorem locallyAsymptoticallyStable_conjugateField_iff
    (e : E ≃L[ℝ] H) (F : E → E) :
    LocallyAsymptoticallyStable (conjugateField e F) 0 ↔
      LocallyAsymptoticallyStable F 0 := by
  constructor
  · intro h
    have hback := h.conjugateField e.symm
    simpa only [conjugateField_symm_conjugateField] using hback
  · exact fun h ↦ h.conjugateField e

end

end Stability
