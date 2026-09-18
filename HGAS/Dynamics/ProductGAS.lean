import HGAS.Dynamics.LyapunovDirect
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Products of globally asymptotically stable systems

Autonomous systems combine componentwise: the product of `x' = F x` and
`y' = G y` is `(x,y)' = (F x,G y)`.  This file proves the corresponding
trajectory, forward-completeness, and global-asymptotic-stability facts for
the trajectory-based definitions in `HGAS.Dynamics.Stability`.

The standard metric on a product of normed spaces is the maximum of the two
factor distances.  The stability proofs below use this identity explicitly:
the smaller of two stability radii works for the product, and the larger of
two attraction times works for the product.

The final section proves that the scalar cubic sink `z' = -z^3` is globally
asymptotically stable.  Forward completeness is witnessed by its explicit
solution, while stability and attraction are proved from the transparent
Lyapunov function `V z = z^2`.
-/

namespace HGAS

open Set

noncomputable section

variable {E H : Type*}

/-! ## Product trajectories -/

/-- The componentwise product of two autonomous vector fields. -/
def productField (F : E → E) (G : H → H) : E × H → E × H :=
  fun p ↦ (F p.1, G p.2)

@[simp]
theorem productField_apply (F : E → E) (G : H → H) (p : E × H) :
    productField F G p = (F p.1, G p.2) :=
  rfl

variable [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The first projection of a product-system trajectory is a trajectory of
the first factor. -/
theorem IsForwardTrajectory.fst_product
    {F : E → E} {G : H → H} {γ : ℝ → E × H} {x₀ : E} {y₀ : H}
    (hγ : IsForwardTrajectory (productField F G) γ (x₀, y₀)) :
    IsForwardTrajectory F (fun t ↦ (γ t).1) x₀ := by
  refine ⟨congrArg Prod.fst hγ.1, ?_⟩
  intro t ht
  convert (hγ.2 t ht).fst using 1

/-- The second projection of a product-system trajectory is a trajectory of
the second factor. -/
theorem IsForwardTrajectory.snd_product
    {F : E → E} {G : H → H} {γ : ℝ → E × H} {x₀ : E} {y₀ : H}
    (hγ : IsForwardTrajectory (productField F G) γ (x₀, y₀)) :
    IsForwardTrajectory G (fun t ↦ (γ t).2) y₀ := by
  refine ⟨congrArg Prod.snd hγ.1, ?_⟩
  intro t ht
  convert (hγ.2 t ht).snd using 1

/-- Pairing two factor trajectories gives a trajectory of the product
system. -/
theorem IsForwardTrajectory.prodMk
    {F : E → E} {G : H → H}
    {γ : ℝ → E} {η : ℝ → H} {x₀ : E} {y₀ : H}
    (hγ : IsForwardTrajectory F γ x₀)
    (hη : IsForwardTrajectory G η y₀) :
    IsForwardTrajectory (productField F G) (fun t ↦ (γ t, η t)) (x₀, y₀) := by
  refine ⟨?_, ?_⟩
  · change (γ 0, η 0) = (x₀, y₀)
    rw [hγ.1, hη.1]
  intro t ht
  simpa [productField] using (hγ.2 t ht).prodMk (hη.2 t ht)

/-- An equilibrium determines the constant forward trajectory through that
equilibrium. -/
theorem isForwardTrajectory_const_of_equilibrium
    {F : E → E} {xEq : E} (hEq : F xEq = 0) :
    IsForwardTrajectory F (fun _ ↦ xEq) xEq := by
  refine ⟨rfl, ?_⟩
  intro t ht
  simpa [hEq] using
    (hasDerivWithinAt_const (x := t) (c := xEq) (s := Ici (0 : ℝ)))

/-- Forward completeness is preserved by componentwise products. -/
theorem ForwardComplete.prod
    {F : E → E} {G : H → H}
    (hF : ForwardComplete F) (hG : ForwardComplete G) :
    ForwardComplete (productField F G) := by
  rintro ⟨x₀, y₀⟩
  obtain ⟨γ, hγ⟩ := hF x₀
  obtain ⟨η, hη⟩ := hG y₀
  exact ⟨fun t ↦ (γ t, η t), hγ.prodMk hη⟩

/-! ## Global asymptotic stability of products -/

/-- The product of two globally asymptotically stable systems is globally
asymptotically stable at the pair of equilibria. -/
theorem GloballyAsymptoticallyStable.prod
    {F : E → E} {G : H → H} {xEq : E} {yEq : H}
    (hF : GloballyAsymptoticallyStable F xEq)
    (hG : GloballyAsymptoticallyStable G yEq) :
    GloballyAsymptoticallyStable (productField F G) (xEq, yEq) where
  equilibrium := by
    simp [productField, hF.equilibrium, hG.equilibrium]
  forwardComplete := hF.forwardComplete.prod hG.forwardComplete
  stable := by
    intro ε hε
    obtain ⟨δF, hδF, hstableF⟩ := hF.stable ε hε
    obtain ⟨δG, hδG, hstableG⟩ := hG.stable ε hε
    refine ⟨min δF δG, lt_min hδF hδG, ?_⟩
    rintro ⟨x₀, y₀⟩ hxy₀ γ hγ t ht
    have hcomponents : dist x₀ xEq < min δF δG ∧
        dist y₀ yEq < min δF δG := by
      simpa only [Prod.dist_eq, max_lt_iff] using hxy₀
    have hx₀ : dist x₀ xEq < δF :=
      lt_of_lt_of_le hcomponents.1 (min_le_left _ _)
    have hy₀ : dist y₀ yEq < δG :=
      lt_of_lt_of_le hcomponents.2 (min_le_right _ _)
    rw [Prod.dist_eq, max_lt_iff]
    exact
      ⟨hstableF x₀ hx₀ (fun s ↦ (γ s).1) hγ.fst_product t ht,
        hstableG y₀ hy₀ (fun s ↦ (γ s).2) hγ.snd_product t ht⟩
  attractive := by
    rintro ⟨x₀, y₀⟩ γ hγ ε hε
    obtain ⟨TF, hTF, hafterF⟩ :=
      hF.attractive x₀ (fun s ↦ (γ s).1) hγ.fst_product ε hε
    obtain ⟨TG, hTG, hafterG⟩ :=
      hG.attractive y₀ (fun s ↦ (γ s).2) hγ.snd_product ε hε
    refine ⟨max TF TG, le_trans hTF (le_max_left _ _), ?_⟩
    intro t ht
    rw [Prod.dist_eq, max_lt_iff]
    exact
      ⟨hafterF t (le_trans (le_max_left _ _) ht),
        hafterG t (le_trans (le_max_right _ _) ht)⟩

/-- If the second equilibrium gives an invariant constant trajectory, GAS
of the product system implies GAS of the first factor. -/
theorem GloballyAsymptoticallyStable.fst_of_product
    {F : E → E} {G : H → H} {xEq : E} {yEq : H}
    (hprod : GloballyAsymptoticallyStable
      (productField F G) (xEq, yEq))
    (hyEq : G yEq = 0) :
    GloballyAsymptoticallyStable F xEq where
  equilibrium := by
    simpa [productField] using congrArg Prod.fst hprod.equilibrium
  forwardComplete := by
    intro x₀
    obtain ⟨γ, hγ⟩ := hprod.forwardComplete (x₀, yEq)
    exact ⟨fun t ↦ (γ t).1, hγ.fst_product⟩
  stable := by
    intro ε hε
    obtain ⟨δ, hδ, hstable⟩ := hprod.stable ε hε
    refine ⟨δ, hδ, ?_⟩
    intro x₀ hx₀ γ hγ t ht
    have hconst : IsForwardTrajectory G (fun _ ↦ yEq) yEq :=
      isForwardTrajectory_const_of_equilibrium hyEq
    have hpair :
        IsForwardTrajectory (productField F G)
          (fun s ↦ (γ s, yEq)) (x₀, yEq) :=
      hγ.prodMk hconst
    have hinitial : dist (x₀, yEq) (xEq, yEq) < δ := by
      simpa [Prod.dist_eq] using hx₀
    simpa [Prod.dist_eq] using
      hstable (x₀, yEq) hinitial (fun s ↦ (γ s, yEq)) hpair t ht
  attractive := by
    intro x₀ γ hγ ε hε
    have hconst : IsForwardTrajectory G (fun _ ↦ yEq) yEq :=
      isForwardTrajectory_const_of_equilibrium hyEq
    have hpair :
        IsForwardTrajectory (productField F G)
          (fun s ↦ (γ s, yEq)) (x₀, yEq) :=
      hγ.prodMk hconst
    obtain ⟨T, hT, hafter⟩ :=
      hprod.attractive (x₀, yEq) (fun s ↦ (γ s, yEq)) hpair ε hε
    exact ⟨T, hT, fun t ht ↦ by simpa [Prod.dist_eq] using hafter t ht⟩

/-- If the first equilibrium gives an invariant constant trajectory, GAS of
the product system implies GAS of the second factor. -/
theorem GloballyAsymptoticallyStable.snd_of_product
    {F : E → E} {G : H → H} {xEq : E} {yEq : H}
    (hprod : GloballyAsymptoticallyStable
      (productField F G) (xEq, yEq))
    (hxEq : F xEq = 0) :
    GloballyAsymptoticallyStable G yEq where
  equilibrium := by
    simpa [productField] using congrArg Prod.snd hprod.equilibrium
  forwardComplete := by
    intro y₀
    obtain ⟨γ, hγ⟩ := hprod.forwardComplete (xEq, y₀)
    exact ⟨fun t ↦ (γ t).2, hγ.snd_product⟩
  stable := by
    intro ε hε
    obtain ⟨δ, hδ, hstable⟩ := hprod.stable ε hε
    refine ⟨δ, hδ, ?_⟩
    intro y₀ hy₀ η hη t ht
    have hconst : IsForwardTrajectory F (fun _ ↦ xEq) xEq :=
      isForwardTrajectory_const_of_equilibrium hxEq
    have hpair :
        IsForwardTrajectory (productField F G)
          (fun s ↦ (xEq, η s)) (xEq, y₀) :=
      hconst.prodMk hη
    have hinitial : dist (xEq, y₀) (xEq, yEq) < δ := by
      simpa [Prod.dist_eq] using hy₀
    simpa [Prod.dist_eq] using
      hstable (xEq, y₀) hinitial (fun s ↦ (xEq, η s)) hpair t ht
  attractive := by
    intro y₀ η hη ε hε
    have hconst : IsForwardTrajectory F (fun _ ↦ xEq) xEq :=
      isForwardTrajectory_const_of_equilibrium hxEq
    have hpair :
        IsForwardTrajectory (productField F G)
          (fun s ↦ (xEq, η s)) (xEq, y₀) :=
      hconst.prodMk hη
    obtain ⟨T, hT, hafter⟩ :=
      hprod.attractive (xEq, y₀) (fun s ↦ (xEq, η s)) hpair ε hε
    exact ⟨T, hT, fun t ht ↦ by simpa [Prod.dist_eq] using hafter t ht⟩

/-! ## The scalar cubic sink -/

/-- The scalar cubic sink vector field `z ↦ -z^3`. -/
def cubicSink (z : ℝ) : ℝ :=
  -z ^ 3

/-- The explicit forward solution of `z' = -z^3` through `z₀`.

For nonnegative time the denominator is at least one.  The formula is left
unchanged at negative times because `IsForwardTrajectory` places no
conditions there. -/
def cubicSinkTrajectory (z₀ t : ℝ) : ℝ :=
  z₀ / √(1 + 2 * z₀ ^ 2 * t)

@[simp]
theorem cubicSinkTrajectory_zero (z₀ : ℝ) :
    cubicSinkTrajectory z₀ 0 = z₀ := by
  simp [cubicSinkTrajectory]

/-- The radicand in the explicit cubic-sink solution is strictly positive
at every nonnegative time. -/
theorem cubicSinkTrajectory_radicand_pos
    (z₀ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    0 < 1 + 2 * z₀ ^ 2 * t := by
  positivity

/-- On the nonnegative time ray, the explicit formula has derivative
`-γ(t)^3`. -/
theorem cubicSinkTrajectory_hasDerivAt
    (z₀ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (cubicSinkTrajectory z₀)
      (cubicSink (cubicSinkTrajectory z₀ t)) t := by
  let u : ℝ → ℝ := fun s ↦ 1 + 2 * z₀ ^ 2 * s
  have hu : HasDerivAt u (2 * z₀ ^ 2) t := by
    simpa [u] using
      ((hasDerivAt_id t).const_mul (2 * z₀ ^ 2)).const_add 1
  have hut_pos : 0 < u t := by
    simpa [u] using cubicSinkTrajectory_radicand_pos z₀ ht
  have hsqrt : HasDerivAt (fun s ↦ √(u s))
      ((2 * z₀ ^ 2) / (2 * √(u t))) t :=
    hu.sqrt hut_pos.ne'
  have hdiv := (hasDerivAt_const (x := t) (c := z₀)).fun_div hsqrt
    (Real.sqrt_ne_zero'.mpr hut_pos)
  convert hdiv using 1
  simp only [cubicSink, cubicSinkTrajectory, u]
  have hsqrt_ne :
      √(1 + 2 * z₀ ^ 2 * t) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hut_pos
  field_simp
  ring

/-- The explicit cubic-sink formula is a forward trajectory through its
parameter `z₀`. -/
theorem cubicSinkTrajectory_isForwardTrajectory (z₀ : ℝ) :
    IsForwardTrajectory cubicSink (cubicSinkTrajectory z₀) z₀ := by
  refine ⟨cubicSinkTrajectory_zero z₀, ?_⟩
  intro t ht
  exact (cubicSinkTrajectory_hasDerivAt z₀ ht).hasDerivWithinAt

/-- The scalar cubic sink has a forward trajectory through every initial
condition. -/
theorem cubicSink_forwardComplete :
    ForwardComplete cubicSink :=
  fun z₀ ↦ ⟨cubicSinkTrajectory z₀,
    cubicSinkTrajectory_isForwardTrajectory z₀⟩

/-- The quadratic energy used for the scalar cubic sink. -/
def cubicSinkEnergy (z : ℝ) : ℝ :=
  z ^ 2

/-- The cubic-sink energy is nonnegative. -/
theorem cubicSinkEnergy_nonneg (z : ℝ) :
    0 ≤ cubicSinkEnergy z := by
  exact sq_nonneg z

/-- Along any forward cubic-sink trajectory and at every positive time,
the energy derivative is `-2 V^2`. -/
theorem cubicSinkEnergy_comp_hasDerivAt
    {γ : ℝ → ℝ} {z₀ : ℝ}
    (hγ : IsForwardTrajectory cubicSink γ z₀)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s ↦ cubicSinkEnergy (γ s))
      (-2 * cubicSinkEnergy (γ t) ^ 2) t := by
  have hγt : HasDerivAt γ (cubicSink (γ t)) t :=
    (hγ.2 t ht.le).hasDerivAt (Ici_mem_nhds ht)
  convert hγt.pow 2 using 1
  simp only [cubicSinkEnergy, cubicSink]
  ring

/-- The cubic-sink energy is continuous along every forward trajectory. -/
theorem cubicSinkEnergy_comp_continuousOn
    {γ : ℝ → ℝ} {z₀ : ℝ}
    (hγ : IsForwardTrajectory cubicSink γ z₀) :
    ContinuousOn (fun t ↦ cubicSinkEnergy (γ t)) (Ici 0) := by
  intro t ht
  simpa [cubicSinkEnergy] using (hγ.2 t ht).continuousWithinAt.pow 2

/-- The quadratic energy is nonincreasing along every forward trajectory of
the cubic sink.  This conclusion does not rely on uniqueness of solutions. -/
theorem cubicSinkEnergy_comp_antitoneOn
    {γ : ℝ → ℝ} {z₀ : ℝ}
    (hγ : IsForwardTrajectory cubicSink γ z₀) :
    AntitoneOn (fun t ↦ cubicSinkEnergy (γ t)) (Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    (cubicSinkEnergy_comp_continuousOn hγ)
  · intro t ht
    have htpos : 0 < t := by
      simpa only [interior_Ici, mem_Ioi] using ht
    exact
      (cubicSinkEnergy_comp_hasDerivAt hγ htpos).differentiableAt
        |>.differentiableWithinAt
  · intro t ht
    have htpos : 0 < t := by
      simpa only [interior_Ici, mem_Ioi] using ht
    rw [(cubicSinkEnergy_comp_hasDerivAt hγ htpos).deriv]
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num)
      (sq_nonneg (cubicSinkEnergy (γ t)))

/-- Every cubic-sink trajectory eventually enters, and thereafter remains
in, every positive quadratic-energy sublevel.

Above the level `η`, the identity `V' = -2 V^2` gives the uniform estimate
`V' ≤ -2 η^2`; the scalar finite-entry lemma then applies. -/
theorem cubicSinkEnergy_comp_eventually_lt
    {γ : ℝ → ℝ} {z₀ η : ℝ}
    (hγ : IsForwardTrajectory cubicSink γ z₀) (hη : 0 < η) :
    ∃ T : ℝ, 0 ≤ T ∧
      ∀ t : ℝ, T ≤ t → cubicSinkEnergy (γ t) < η := by
  apply eventually_lt_of_antitoneOn_of_hasDerivAt_le
    (h := fun t ↦ cubicSinkEnergy (γ t))
    (d := 2 * η ^ 2)
  · exact cubicSinkEnergy_comp_continuousOn hγ
  · exact cubicSinkEnergy_comp_antitoneOn hγ
  · intro t ht
    exact cubicSinkEnergy_nonneg (γ t)
  · exact mul_pos (by norm_num) (sq_pos_of_pos hη)
  · intro t ht hlevel
    refine ⟨-2 * cubicSinkEnergy (γ t) ^ 2,
      cubicSinkEnergy_comp_hasDerivAt hγ ht, ?_⟩
    have hsquare :
        η ^ 2 ≤ cubicSinkEnergy (γ t) ^ 2 :=
      (sq_le_sq₀ hη.le (cubicSinkEnergy_nonneg (γ t))).mpr hlevel
    nlinarith

/-- The origin is Lyapunov stable for the scalar cubic sink. -/
theorem cubicSink_lyapunovStable :
    LyapunovStable cubicSink 0 := by
  apply lyapunovStable_of_quadratic_bounds
    cubicSink 0 cubicSinkEnergy (b := 1) (by norm_num)
  · intro z
    simp [cubicSinkEnergy]
  · intro z
    simp [cubicSinkEnergy]
  · intro z₀ γ hγ
    exact cubicSinkEnergy_comp_antitoneOn hγ

/-- Every forward trajectory of the scalar cubic sink converges to the
origin. -/
theorem cubicSink_globallyAttractive :
    GloballyAttractive cubicSink 0 := by
  apply globallyAttractive_of_lower_quadratic_of_eventually_lt
    cubicSink 0 cubicSinkEnergy (c := 1) (by norm_num)
  · intro z
    simp [cubicSinkEnergy]
  · intro z₀ γ hγ η hη
    exact cubicSinkEnergy_comp_eventually_lt hγ hη

/-- The scalar cubic sink `z' = -z^3` is globally asymptotically stable at
the origin. -/
theorem cubicSink_gas :
    GloballyAsymptoticallyStable cubicSink 0 where
  equilibrium := by simp [cubicSink]
  forwardComplete := cubicSink_forwardComplete
  stable := cubicSink_lyapunovStable
  attractive := cubicSink_globallyAttractive

end

end HGAS
