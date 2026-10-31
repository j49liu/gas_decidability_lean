import HGAS.Modular.RecurrentUnarySelectorReduction
import HGAS.Modular.HorizontalThetaCesaro

/-!
# A nonzero harmonic mean excludes recurrent unary divisors

On each invariant degenerate divisor, recurrence forces the unary
coordinate `Y` to be constant. Its mean against a nonzero-frequency
character is therefore zero. This proves the genericity step using the
first harmonic itself, without an auxiliary root-coordinate moment.

See Proposition `prop:modselect`, Step 1, in Section 8.
-/

noncomputable section

namespace Stability.Selection

open HGAS HGAS.Modular Filter Topology

/-- On the recurrent `A = 0` branch, the zero Riccati coordinate persists,
so the unary root coordinate is constant for all real times. -/
theorem unaryY_constant_of_recurrent_A_zero
    {κ : ℂ} {z : ℝ → UnaryModularState ℂ}
    (hz : IsScaledUnaryModularTrajectory κ z) (hκ : κ ≠ 0)
    {t₀ : ℝ} (hrec : ForwardRecurrentUnaryModularAt z t₀) (hA : (z t₀).A = 0) :
    ∀ t, (z t).Y = (z t₀).Y := by
  let q : ℝ → ℂ := fun t ↦ (z t).E - (z t).C
  have hqcont : Continuous q := hz.continuous_E.sub hz.continuous_C
  have hAall := hz.A_eq_zero hA
  have hqderiv : ∀ t, HasDerivAt q ((κ / 6 * q t) * q t) t := by
    intro t
    convert (hz.E t).sub (hz.C t) using 1
    simp only [q, UnaryModularState.vectorField, hAall t]
    ring
  have hqzero := complex_eq_zero_of_hasDerivAt_eq_mul
    (fun t ↦ κ / 6 * q t) q (continuous_const.mul hqcont) hqderiv
    (hz.E_sub_C_eq_zero_of_A_eq_zero_of_recurrent hκ hrec hA)
  have hYderiv : ∀ t, HasDerivAt (fun u ↦ (z u).Y) 0 t := by
    intro t
    have hEC : (z t).E - (z t).C = 0 := congrFun hqzero t
    simpa only [UnaryModularState.vectorField, hAall t, add_zero, hEC, mul_zero,
      zero_mul] using hz.Y t
  exact fun t ↦ is_const_of_deriv_eq_zero
    (fun u ↦ (hYderiv u).differentiableAt) (fun u ↦ (hYderiv u).deriv) t t₀

/-- The recurrent `C = 0` branch also has constant unary root coordinate. -/
theorem unaryY_constant_of_recurrent_C_zero
    {κ : ℂ} {z : ℝ → UnaryModularState ℂ}
    (hz : IsScaledUnaryModularTrajectory κ z) (hκ : κ ≠ 0)
    {t₀ : ℝ} (hrec : ForwardRecurrentUnaryModularAt z t₀) (hC : (z t₀).C = 0) :
    ∀ t, (z t).Y = (z t₀).Y := by
  let q : ℝ → ℂ := fun t ↦ (z t).E + (z t).A
  have hqcont : Continuous q := hz.continuous_E.add hz.continuous_A
  have hCall := hz.C_eq_zero hC
  have hqderiv : ∀ t, HasDerivAt q ((κ / 6 * q t) * q t) t := by
    intro t
    convert (hz.E t).add (hz.A t) using 1
    simp only [q, UnaryModularState.vectorField, hCall t]
    ring
  have hqzero := complex_eq_zero_of_hasDerivAt_eq_mul
    (fun t ↦ κ / 6 * q t) q (continuous_const.mul hqcont) hqderiv
    (hz.E_add_A_eq_zero_of_C_eq_zero_of_recurrent hκ hrec hC)
  have hYderiv : ∀ t, HasDerivAt (fun u ↦ (z u).Y) 0 t := by
    intro t
    have hEA : (z t).E + (z t).A = 0 := congrFun hqzero t
    simpa only [UnaryModularState.vectorField, hCall t, sub_zero, hEA, mul_zero,
      zero_mul] using hz.Y t
  exact fun t ↦ is_const_of_deriv_eq_zero
    (fun u ↦ (hYderiv u).differentiableAt) (fun u ↦ (hYderiv u).deriv) t t₀

/-- A nonzero first-harmonic limit excludes all three recurrent unary
divisors. This statement needs only the unary ODE and its Jacobi residual;
the harmonic coefficient and frequency may be arbitrary. -/
theorem unary_generic_of_recurrent_nonzero_harmonic_mean
    {κ : ℂ} {z : ℝ → UnaryModularState ℂ}
    (hz : IsScaledUnaryModularTrajectory κ z) (hκ : κ ≠ 0)
    {t₀ : ℝ} (hrec : ForwardRecurrentUnaryModularAt z t₀)
    (hresidual : UnaryModularState.jacobiResidual (z t₀) = 0)
    (η : ℂ) {ω : ℝ} (hω : ω ≠ 0) {L : ℂ} (hL : L ≠ 0)
    (hmean : Tendsto (HGAS.Analysis.cesaroMeanAt
      (fun t ↦ (z t).Y * (η * HGAS.Analysis.realFrequencyExponential ω t)))
      atTop (𝓝 L)) :
    (z t₀).A ≠ 0 ∧ (z t₀).C ≠ 0 ∧ UnaryModularState.B (z t₀) ≠ 0 := by
  have hnotconst : ¬ ∀ t, (z t).Y = (z t₀).Y := by
    intro hconst
    have htimes : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have hkernel := HGAS.Analysis.cesaroKernelAt_tendsto_zero htimes hω
    have hzero : Tendsto (fun n : ℕ ↦ HGAS.Analysis.cesaroMeanAt
        (fun t ↦ (z t).Y * (η * HGAS.Analysis.realFrequencyExponential ω t))
        (n + 1 : ℝ)) atTop (𝓝 0) := by
      simpa only [hconst, ← mul_assoc, cesaroMeanAt_const_mul,
        HGAS.Analysis.cesaroKernelAt, mul_zero] using hkernel.const_mul ((z t₀).Y * η)
    exact hL (tendsto_nhds_unique (hmean.comp htimes) hzero)
  refine ⟨fun hA ↦ hnotconst (unaryY_constant_of_recurrent_A_zero hz hκ hrec hA),
    fun hC ↦ hnotconst (unaryY_constant_of_recurrent_C_zero hz hκ hrec hC), ?_⟩
  intro hB
  have hY : (z t₀).Y = 0 := by
    have hsum : (z t₀).A + (z t₀).C = 0 := hB
    have hfourth : (z t₀).Y ^ 4 = 0 := by
      unfold UnaryModularState.jacobiResidual at hresidual
      linear_combination hresidual + hsum
    exact (pow_eq_zero_iff (by norm_num : (4 : ℕ) ≠ 0)).mp hfourth
  exact hnotconst (fun t ↦ (hz.Y_eq_zero hY t).trans hY.symm)

end Stability.Selection
