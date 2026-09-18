import HGAS.Modular.SerreDerivativeModularity
import HGAS.Modular.EisensteinBounds
import HGAS.Analysis.UpperHalfPlaneRestriction
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.Tactic

/-!
# Ramanujan's differential identities

This file completes the reusable modular-form calculation needed by the
unary HGAS source.  The principal results are

```
D E₂ = (E₂² - E₄) / 12,
D E₄ = (E₂ E₄ - E₆) / 3,
D E₆ = (E₂ E₆ - E₄²) / 2.
```

The proof is conceptual.  The preceding modules show that the Serre
derivative of a weight-`k` level-one modular form is again a level-one
modular form of weight `k+2`.  The relevant spaces in weights `4`, `6`,
and `8` are one-dimensional, so each derivative is a scalar multiple of
the normalized Eisenstein generator.  A Cauchy estimate makes the
ordinary derivative tend to zero at the cusp, and the normalizations
`E₂,E₄,E₆ → 1` determine the three scalars.

The `E₂` case needs one extra calculation because `E₂` itself is only
quasimodular.  Its transformation anomaly is differentiated explicitly;
the quadratic anomaly cancels in `D E₂ - E₂²/12`.

The strategy follows the formal proof in Sphere-Packing-Lean, but all
statements here use Mathlib 4.30's native derivative and modular-form API
and have no external dependency.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open Complex Real Filter
open ModularForm ModularGroup SlashAction EisensteinSeries
open scoped Manifold MatrixGroups ModularForm Real Topology

noncomputable section

local notation "D" => Derivative.normalizedDerivOfComplex
local notation "∂[" k "]" => Derivative.serreDerivative k

/-! ## Bundling the Serre derivative -/

/-- A level-one modular form is fixed by the integral slash action. -/
@[simp]
theorem levelOne_slash_eq_self
    {k : ℤ} (f : ModularForm 𝒮ℒ k) (γ : SL(2, ℤ)) :
    (f : ℍ → ℂ) ∣[k] γ = f := by
  change
    (f : ℍ → ℂ) ∣[k]
        (Matrix.SpecialLinearGroup.mapGL ℝ γ) = f
  exact f.slash_action_eq' _
    (MonoidHom.mem_range.mpr ⟨γ, rfl⟩)

/-- The Serre derivative of a bundled level-one modular form, bundled at
the new weight. -/
def serreDerivativeModularForm
    (k : ℤ) (f : ModularForm 𝒮ℒ k) :
    ModularForm 𝒮ℒ (k + 2) where
  toSlashInvariantForm :=
    { toFun := ∂[(k : ℂ)] (f : ℍ → ℂ)
      slash_action_eq' := fun A hA ↦ by
        obtain ⟨γ, rfl⟩ := MonoidHom.mem_range.mp hA
        change
          (∂[(k : ℂ)] (f : ℍ → ℂ) ∣[k + 2] γ) =
            ∂[(k : ℂ)] (f : ℍ → ℂ)
        exact serreDerivative_slash_invariant
          k (f : ℍ → ℂ) f.holo' γ
          (levelOne_slash_eq_self f γ) }
  holo' :=
    Derivative.serreDerivative_mdifferentiable
      (k : ℂ) f.holo'
  bdd_at_cusps' := fun {c} hc ↦ by
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [serreDerivative_slash_invariant
      k (f : ℍ → ℂ) f.holo' γ
      (levelOne_slash_eq_self f γ)]
    exact serreDerivative_isBoundedAtImInfty_of_bounded
      (k : ℂ) f.holo' (ModularFormClass.bdd_at_infty f)

@[simp]
theorem serreDerivativeModularForm_apply
    (k : ℤ) (f : ModularForm 𝒮ℒ k) (z : ℍ) :
    serreDerivativeModularForm k f z =
      ∂[(k : ℂ)] (f : ℍ → ℂ) z := rfl

/-! ## The exceptional quasimodular calculation for `E₂` -/

private lemma deriv_denom (γ : SL(2, ℤ)) (z : ℂ) :
    deriv (fun w ↦ denom γ w) z = ((γ 1 0 : ℤ) : ℂ) := by
  simp only [denom]
  rw [deriv_add_const, deriv_const_mul _ differentiableAt_id,
    deriv_id'', mul_one]
  simp

private lemma differentiableAt_denom
    (γ : SL(2, ℤ)) (z : ℂ) :
    DifferentiableAt ℂ (fun w ↦ denom γ w) z := by
  simp only [denom]
  fun_prop

/-- The quasimodular anomaly `D2 γ` is holomorphic on the upper
half-plane. -/
private theorem d2_mdifferentiable (γ : SL(2, ℤ)) :
    MDiff (EisensteinSeries.D2 γ) := fun z ↦ by
  have heq :
      EisensteinSeries.D2 γ =
        (fun w ↦
          (2 * π * I * (γ 1 0 : ℂ)) / denom γ w) ∘
            (fun u : ℍ ↦ (u : ℂ)) := by
    ext
    rfl
  rw [heq]
  exact HGAS.Analysis.mdifferentiableAt_restrict
    ((differentiableAt_const _).div
      (differentiableAt_denom γ z)
      (UpperHalfPlane.denom_ne_zero γ z))

/-- Derivative of the `E₂` anomaly
`D₂(γ,τ)=2πi c/(cτ+d)`. -/
theorem normalizedDeriv_D2
    (γ : SL(2, ℤ)) (z : ℍ) :
    D (EisensteinSeries.D2 γ) z =
      -((γ 1 0 : ℂ) ^ 2) / (denom γ z) ^ 2 := by
  have hden : denom γ z ≠ 0 :=
    UpperHalfPlane.denom_ne_zero γ z
  have hderiv :
      deriv ((EisensteinSeries.D2 γ) ∘ ofComplex) z =
        deriv
          (fun w ↦
            (2 * π * I * (γ 1 0 : ℂ)) / denom γ w) z := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards
      [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    simp only [Function.comp_apply,
      ofComplex_apply_of_im_pos hw, EisensteinSeries.D2]
  unfold Derivative.normalizedDerivOfComplex
  rw [hderiv]
  have hdiff : DifferentiableAt ℂ (fun w ↦ denom γ w) z :=
    differentiableAt_denom γ z
  rw [deriv_const_div _ hdiff hden, deriv_denom]
  field_simp [hden, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]

/-- The exceptional Serre combination
`D E₂ - E₂²/12` transforms as a genuine weight-four modular form. -/
theorem serreDerivative_e2_slash_invariant
    (γ : SL(2, ℤ)) :
    (∂[(1 : ℂ)] EisensteinSeries.E2 ∣[(4 : ℤ)] γ) =
      ∂[(1 : ℂ)] EisensteinSeries.E2 := by
  have hdecompose :
      ∂[(1 : ℂ)] EisensteinSeries.E2 =
        ∂[(2 : ℂ)] EisensteinSeries.E2 +
          (1 / 12 : ℂ) •
            (EisensteinSeries.E2 * EisensteinSeries.E2) := by
    ext z
    simp only [Derivative.serreDerivative_apply, Pi.add_apply,
      Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    ring
  have hequiv :=
    serreDerivative_slash_equivariant
      2 EisensteinSeries.E2 E2_mdifferentiable γ
  have hEslash := EisensteinSeries.E2_slash_action γ
  have hproduct :=
    ModularForm.mul_slash_SL2
      (2 : ℤ) (2 : ℤ) γ
      EisensteinSeries.E2 EisensteinSeries.E2
  ext z
  rw [hdecompose]
  simp only [SlashAction.add_slash, Pi.add_apply,
    ModularForm.SL_smul_slash, Pi.smul_apply, smul_eq_mul]
  rw [show
      (∂[(2 : ℂ)] EisensteinSeries.E2 ∣[(4 : ℤ)] γ) z =
        ∂[(2 : ℂ)]
          (EisensteinSeries.E2 ∣[(2 : ℤ)] γ) z by
      simpa using congrFun hequiv z,
    show
      ((EisensteinSeries.E2 * EisensteinSeries.E2)
          ∣[(4 : ℤ)] γ) z =
        (EisensteinSeries.E2 ∣[(2 : ℤ)] γ) z *
          (EisensteinSeries.E2 ∣[(2 : ℤ)] γ) z by
      simpa using congrFun hproduct z]
  let α : ℂ := 1 / (2 * riemannZeta 2)
  have hEfun :
      (EisensteinSeries.E2 ∣[(2 : ℤ)] γ) =
        EisensteinSeries.E2 - α • EisensteinSeries.D2 γ := by
    ext w
    simpa [α] using congrFun hEslash w
  rw [hEfun]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hDlinear :
      D (EisensteinSeries.E2 - α • EisensteinSeries.D2 γ) z =
        D EisensteinSeries.E2 z -
          α * D (EisensteinSeries.D2 γ) z := by
    rw [Derivative.normalizedDerivOfComplex_sub
      EisensteinSeries.E2 (α • EisensteinSeries.D2 γ)
      E2_mdifferentiable
      (d2_mdifferentiable γ |>.const_smul α),
      Derivative.normalizedDerivOfComplex_smul
        α (EisensteinSeries.D2 γ)
        (d2_mdifferentiable γ)]
    rfl
  simp only [Derivative.serreDerivative_apply, Pi.sub_apply,
    Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  rw [hDlinear, normalizedDeriv_D2 γ z]
  have hα : α = 3 / π ^ 2 := by
    simp only [α, riemannZeta_two]
    field_simp
    ring
  have hpi : (π : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show
      EisensteinSeries.D2 γ z =
        (2 * π * I * (γ 1 0 : ℂ)) / denom γ z by
      rfl,
    hα]
  field_simp [UpperHalfPlane.denom_ne_zero γ z, hpi]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- The exceptional weight-four modular form obtained from `E₂`. -/
def serreDerivativeE2ModularForm :
    ModularForm 𝒮ℒ 4 where
  toSlashInvariantForm :=
    { toFun := ∂[(1 : ℂ)] EisensteinSeries.E2
      slash_action_eq' := fun A hA ↦ by
        obtain ⟨γ, rfl⟩ := MonoidHom.mem_range.mp hA
        change
          (∂[(1 : ℂ)] EisensteinSeries.E2
              ∣[(4 : ℤ)] γ) =
            ∂[(1 : ℂ)] EisensteinSeries.E2
        exact serreDerivative_e2_slash_invariant γ }
  holo' :=
    Derivative.serreDerivative_mdifferentiable
      (1 : ℂ) E2_mdifferentiable
  bdd_at_cusps' := fun {c} hc ↦ by
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [serreDerivative_e2_slash_invariant γ]
    exact serreDerivative_isBoundedAtImInfty_of_bounded
      (1 : ℂ) E2_mdifferentiable e2_isBoundedAtImInfty

@[simp]
theorem serreDerivativeE2ModularForm_apply (z : ℍ) :
    serreDerivativeE2ModularForm z =
      ∂[(1 : ℂ)] EisensteinSeries.E2 z := rfl

/-! ## Limits which determine the scalar multiples -/

/-- A scalar is determined by comparing a multiple with a function
normalized to tend to one. -/
theorem scalar_eq_of_tendsto
    {f g : ℍ → ℂ} {c L : ℂ}
    (hfun : ∀ z, f z = c * g z)
    (hf : Tendsto f atImInfty (𝓝 L))
    (hg : Tendsto g atImInfty (𝓝 1)) :
    c = L := by
  refine (tendsto_nhds_unique hf ?_).symm
  simpa [mul_one] using
    (show Tendsto f atImInfty (𝓝 (c * 1)) by
      convert tendsto_const_nhds.mul hg using 1
      ext z
      exact hfun z)

/-- Limit of a Serre derivative when the original bounded holomorphic
function has a finite cusp limit. -/
theorem serreDerivative_tendsto_of_tendsto
    (k : ℂ) (f : ℍ → ℂ) (c : ℂ)
    (hfhol : MDiff f)
    (hfbdd : IsBoundedAtImInfty f)
    (hflim : Tendsto f atImInfty (𝓝 c)) :
    Tendsto (∂[k] f) atImInfty
      (𝓝 (-k * c / 12)) := by
  have hD :=
    normalizedDeriv_tendsto_zero_of_bounded hfhol hfbdd
  have hproduct :=
    e2_tendsto_one_atImInfty.mul hflim
  have hscaled :=
    (tendsto_const_nhds :
      Tendsto (fun _ : ℍ ↦ k * 12⁻¹)
        atImInfty (𝓝 (k * 12⁻¹))).mul hproduct
  convert hD.sub hscaled using 1
  · ext z
    simp only [Derivative.serreDerivative_apply]
    ring
  · ring_nf

/-! ## Ramanujan identities in Serre form -/

/-- Serre derivative of `E₂`. -/
theorem serreDerivative_E2 :
    ∂[(1 : ℂ)] EisensteinSeries.E2 =
      fun z ↦ -(12 : ℂ)⁻¹ * ModularForm.E₄ z := by
  obtain ⟨c, hc⟩ :
      ∃ c : ℂ, c • ModularForm.E₄ =
        serreDerivativeE2ModularForm :=
    (finrank_eq_one_iff_of_nonzero'
      ModularForm.E₄
      (EisensteinSeries.E_ne_zero
        (by norm_num) ⟨2, rfl⟩)).mp
      (Module.rank_eq_one_iff_finrank_eq_one.mp
        ModularForm.levelOne_weight_four_rank_one)
      serreDerivativeE2ModularForm
  have hfun :
      ∀ z,
        ∂[(1 : ℂ)] EisensteinSeries.E2 z =
          c * ModularForm.E₄ z := by
    intro z
    have h := congrArg (fun F : ModularForm 𝒮ℒ 4 ↦ F z) hc
    simpa using h.symm
  have hcusp :
      Tendsto (∂[(1 : ℂ)] EisensteinSeries.E2)
        atImInfty (𝓝 (-(1 / 12 : ℂ))) := by
    convert
      serreDerivative_tendsto_of_tendsto
        1 EisensteinSeries.E2 1
        E2_mdifferentiable e2_isBoundedAtImInfty
        e2_tendsto_one_atImInfty using 1
    all_goals norm_num
  have hE4 :
      Tendsto (ModularForm.E₄ : ℍ → ℂ)
        atImInfty (𝓝 1) :=
    eisensteinSeries_tendsto_one_atImInfty
      (by norm_num) ⟨2, rfl⟩
  have hcvalue : c = -(1 / 12 : ℂ) :=
    scalar_eq_of_tendsto hfun hcusp hE4
  ext z
  rw [hfun z, hcvalue]
  ring

/-- Serre derivative of `E₄`. -/
theorem serreDerivative_E4 :
    ∂[(4 : ℂ)] (ModularForm.E₄ : ℍ → ℂ) =
      fun z ↦ -(3 : ℂ)⁻¹ * ModularForm.E₆ z := by
  let S4 : ModularForm 𝒮ℒ 6 :=
    (by norm_num : (4 : ℤ) + 2 = 6) ▸
      serreDerivativeModularForm 4 ModularForm.E₄
  obtain ⟨c, hc⟩ :
      ∃ c : ℂ, c • ModularForm.E₆ = S4 :=
    (finrank_eq_one_iff_of_nonzero'
      ModularForm.E₆
      (EisensteinSeries.E_ne_zero
        (by norm_num) ⟨3, rfl⟩)).mp
      (Module.rank_eq_one_iff_finrank_eq_one.mp
        ModularForm.levelOne_weight_six_rank_one)
      S4
  have hfun :
      ∀ z,
        ∂[(4 : ℂ)] (ModularForm.E₄ : ℍ → ℂ) z =
          c * ModularForm.E₆ z := by
    intro z
    have h := congrArg (fun F : ModularForm 𝒮ℒ 6 ↦ F z) hc
    simpa [S4] using h.symm
  have hE4 :
      Tendsto (ModularForm.E₄ : ℍ → ℂ)
        atImInfty (𝓝 1) :=
    eisensteinSeries_tendsto_one_atImInfty
      (by norm_num) ⟨2, rfl⟩
  have hcusp :
      Tendsto (∂[(4 : ℂ)] (ModularForm.E₄ : ℍ → ℂ))
        atImInfty (𝓝 (-(1 / 3 : ℂ))) := by
    convert
      serreDerivative_tendsto_of_tendsto
        4 (ModularForm.E₄ : ℍ → ℂ) 1
        ModularForm.E₄.holo'
        (ModularFormClass.bdd_at_infty ModularForm.E₄)
        hE4 using 1
    all_goals norm_num
  have hE6 :
      Tendsto (ModularForm.E₆ : ℍ → ℂ)
        atImInfty (𝓝 1) :=
    eisensteinSeries_tendsto_one_atImInfty
      (by norm_num) ⟨3, rfl⟩
  have hcvalue : c = -(1 / 3 : ℂ) :=
    scalar_eq_of_tendsto hfun hcusp hE6
  ext z
  rw [hfun z, hcvalue]
  ring

/-- The space of level-one weight-eight modular forms has dimension one. -/
theorem levelOne_weight_eight_rank_one :
    Module.rank ℂ (ModularForm 𝒮ℒ 8) = 1 := by
  exact
    (ModularForm.rank_eq_one_add_rank_cuspForm
      (k := 8) (by norm_num) ⟨4, rfl⟩).trans
      ((congrArg (1 + ·)
        (CuspForm.rank_eq_zero_of_weight_lt_twelve
          (k := 8) (by norm_num))).trans (by norm_cast))

/-- Serre derivative of `E₆`. -/
theorem serreDerivative_E6 :
    ∂[(6 : ℂ)] (ModularForm.E₆ : ℍ → ℂ) =
      fun z ↦ -(2 : ℂ)⁻¹ * ModularForm.E₄ z ^ 2 := by
  let E4sq : ModularForm 𝒮ℒ 8 :=
    (by norm_num : (4 : ℤ) + 4 = 8) ▸
      ModularForm.E₄.mul ModularForm.E₄
  have hE4sq : E4sq ≠ 0 := by
    intro hz
    apply
      (EisensteinSeries.E_ne_zero
        (by norm_num) ⟨2, rfl⟩)
    ext z
    have h :=
      congrArg (fun F : ModularForm 𝒮ℒ 8 ↦ F z) hz
    simp only [E4sq, ModularForm.zero_apply] at h
    exact mul_self_eq_zero.mp h
  let S6 : ModularForm 𝒮ℒ 8 :=
    (by norm_num : (6 : ℤ) + 2 = 8) ▸
      serreDerivativeModularForm 6 ModularForm.E₆
  obtain ⟨c, hc⟩ :
      ∃ c : ℂ, c • E4sq = S6 :=
    (finrank_eq_one_iff_of_nonzero' E4sq hE4sq).mp
      (Module.rank_eq_one_iff_finrank_eq_one.mp
        levelOne_weight_eight_rank_one)
      S6
  have hfun :
      ∀ z,
        ∂[(6 : ℂ)] (ModularForm.E₆ : ℍ → ℂ) z =
          c * ModularForm.E₄ z ^ 2 := by
    intro z
    calc
      ∂[(6 : ℂ)] (ModularForm.E₆ : ℍ → ℂ) z =
          S6 z := by
            change
              ∂[(6 : ℂ)] (ModularForm.E₆ : ℍ → ℂ) z =
                serreDerivativeModularForm 6 ModularForm.E₆ z
            exact
              (serreDerivativeModularForm_apply
                6 ModularForm.E₆ z).symm
      _ = (c • E4sq) z := by
            rw [hc]
      _ = c * ModularForm.E₄ z ^ 2 := by
            rw [ModularForm.IsGLPos.smul_apply]
            simp only [smul_eq_mul]
            change
              c * (ModularForm.E₄ z * ModularForm.E₄ z) =
                c * ModularForm.E₄ z ^ 2
            rw [pow_two]
  have hE6 :
      Tendsto (ModularForm.E₆ : ℍ → ℂ)
        atImInfty (𝓝 1) :=
    eisensteinSeries_tendsto_one_atImInfty
      (by norm_num) ⟨3, rfl⟩
  have hcusp :
      Tendsto (∂[(6 : ℂ)] (ModularForm.E₆ : ℍ → ℂ))
        atImInfty (𝓝 (-(1 / 2 : ℂ))) := by
    convert
      serreDerivative_tendsto_of_tendsto
        6 (ModularForm.E₆ : ℍ → ℂ) 1
        ModularForm.E₆.holo'
        (ModularFormClass.bdd_at_infty ModularForm.E₆)
        hE6 using 1
    all_goals norm_num
  have hE4 :
      Tendsto (fun z ↦ ModularForm.E₄ z ^ 2)
        atImInfty (𝓝 1) := by
    simpa using
      (eisensteinSeries_tendsto_one_atImInfty
        (by norm_num) (⟨2, rfl⟩ : Even 4)).pow 2
  have hcvalue : c = -(1 / 2 : ℂ) :=
    scalar_eq_of_tendsto hfun hcusp hE4
  ext z
  rw [hfun z, hcvalue]
  ring

/-! ## Ordinary-derivative forms -/

/-- Ramanujan's differential identity for `E₂`. -/
theorem ramanujan_E2 :
    D EisensteinSeries.E2 =
      fun z ↦ (12 : ℂ)⁻¹ *
        (EisensteinSeries.E2 z ^ 2 - ModularForm.E₄ z) := by
  ext z
  have h := congrFun serreDerivative_E2 z
  simp only [Derivative.serreDerivative_apply] at h
  linear_combination h

/-- Ramanujan's differential identity for `E₄`. -/
theorem ramanujan_E4 :
    D (ModularForm.E₄ : ℍ → ℂ) =
      fun z ↦ (3 : ℂ)⁻¹ *
        (EisensteinSeries.E2 z * ModularForm.E₄ z -
          ModularForm.E₆ z) := by
  ext z
  have h := congrFun serreDerivative_E4 z
  simp only [Derivative.serreDerivative_apply] at h
  linear_combination h

/-- Ramanujan's differential identity for `E₆`. -/
theorem ramanujan_E6 :
    D (ModularForm.E₆ : ℍ → ℂ) =
      fun z ↦ (2 : ℂ)⁻¹ *
        (EisensteinSeries.E2 z * ModularForm.E₆ z -
          ModularForm.E₄ z ^ 2) := by
  ext z
  have h := congrFun serreDerivative_E6 z
  simp only [Derivative.serreDerivative_apply] at h
  linear_combination h

end

end HGAS.Modular
