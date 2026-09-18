import HGAS.Propagation.DegreePadding
import HGAS.Dynamics.ProductGAS
import HGAS.Dynamics.StateTimeChange
import Mathlib.Tactic

/-!
# Global asymptotic stability under dimension padding

This module proves the dynamical part of dimension padding that does not
involve a state-dependent change of time.

The auxiliary vector field on `Fin k → ℝ` is

```
z' i = -(z i)^3.
```

Each coordinate is the scalar cubic sink from
`HGAS.Dynamics.ProductGAS`.  We prove global asymptotic stability directly
for every finite `k`, including `k = 0`.  The proof is deliberately
coordinatewise:

* an explicit finite-vector trajectory is assembled from the scalar
  trajectories;
* every arbitrary finite-vector trajectory projects to an arbitrary scalar
  trajectory;
* scalar Lyapunov stability transfers using the sup metric on a finite
  product;
* scalar attraction times are combined by summing the finitely many
  nonnegative times.

This makes the construction reusable independently of degree padding.  The
general product theorem then gives the exact equivalence

```
GAS (x,z ↦ (H x, -(z i)^3)) (0,0) ↔ GAS H 0.
```

## State-dependent time change

The full degree-padded field is

```
p ↦ (splitNormSq p)^j • directProductCubic H p.
```

We prove below that its scalar factor is nonnegative everywhere and, for a
positive exponent, vanishes exactly at the origin.  The reusable theorem in
`HGAS.Dynamics.StateTimeChange` then supplies the required forward and
inverse clocks, proves that their positive-time ranges are unbounded, and
transfers completeness, stability, and attraction.  This yields the full
GAS equivalence for every exponent.
-/

namespace HGAS

open Set

noncomputable section

/-! ## A finite product of scalar cubic sinks -/

/-- Independent scalar cubic sinks on a finite real coordinate space. -/
def finiteCubicSink (z : FinVector k ℝ) : FinVector k ℝ :=
  fun i ↦ cubicSink (z i)

/-- The coordinatewise explicit trajectory of the finite cubic sink. -/
def finiteCubicSinkTrajectory
    (z₀ : FinVector k ℝ) (t : ℝ) : FinVector k ℝ :=
  fun i ↦ cubicSinkTrajectory (z₀ i) t

@[simp]
theorem finiteCubicSinkTrajectory_zero (z₀ : FinVector k ℝ) :
    finiteCubicSinkTrajectory z₀ 0 = z₀ := by
  funext i
  simp [finiteCubicSinkTrajectory]

/-- The coordinatewise explicit formula is a forward trajectory of the
finite sink. -/
theorem finiteCubicSinkTrajectory_isForwardTrajectory
    (z₀ : FinVector k ℝ) :
    IsForwardTrajectory (finiteCubicSink (k := k))
      (finiteCubicSinkTrajectory z₀) z₀ := by
  refine ⟨finiteCubicSinkTrajectory_zero z₀, ?_⟩
  intro t ht
  rw [hasDerivWithinAt_pi]
  intro i
  simpa [finiteCubicSink, finiteCubicSinkTrajectory] using
    (cubicSinkTrajectory_isForwardTrajectory (z₀ i)).2 t ht

/-- Every coordinate projection of an arbitrary finite-sink trajectory is
an arbitrary trajectory of the scalar cubic sink.  This is the key fact
that lets scalar estimates apply without assuming uniqueness. -/
theorem IsForwardTrajectory.coordinate_finiteCubicSink
    {z₀ : FinVector k ℝ} {γ : ℝ → FinVector k ℝ}
    (hγ : IsForwardTrajectory (finiteCubicSink (k := k)) γ z₀)
    (i : Fin k) :
    IsForwardTrajectory cubicSink (fun t ↦ γ t i) (z₀ i) := by
  refine ⟨congrFun hγ.1 i, ?_⟩
  intro t ht
  have hi := (hasDerivWithinAt_pi.mp (hγ.2 t ht)) i
  simpa [finiteCubicSink] using hi

/-- The finite cubic sink admits a forward trajectory from every point. -/
theorem finiteCubicSink_forwardComplete :
    ForwardComplete (finiteCubicSink (k := k)) :=
  fun z₀ ↦
    ⟨finiteCubicSinkTrajectory z₀,
      finiteCubicSinkTrajectory_isForwardTrajectory z₀⟩

/-- The origin is Lyapunov stable for every finite product of cubic sinks. -/
theorem finiteCubicSink_lyapunovStable :
    LyapunovStable (finiteCubicSink (k := k)) 0 := by
  intro ε hε
  obtain ⟨δ, hδ, hstable⟩ := cubicSink_gas.stable ε hε
  refine ⟨δ, hδ, ?_⟩
  intro z₀ hz₀ γ hγ t ht
  rw [dist_pi_lt_iff hε]
  intro i
  change dist (γ t i) 0 < ε
  have hi0 : dist (z₀ i) 0 < δ :=
    lt_of_le_of_lt
      (by
        simpa using
          dist_le_pi_dist z₀ (0 : FinVector k ℝ) i)
      hz₀
  exact hstable (z₀ i) hi0 (fun s ↦ γ s i)
    (hγ.coordinate_finiteCubicSink i) t ht

/-- Every trajectory of the finite cubic sink converges to the origin.

For each coordinate, scalar attraction supplies a nonnegative entry time.
The sum of those finitely many times is at least every individual time and
therefore works simultaneously for all coordinates.  This also avoids a
separate maximum construction for the empty coordinate type. -/
theorem finiteCubicSink_globallyAttractive :
    GloballyAttractive (finiteCubicSink (k := k)) 0 := by
  intro z₀ γ hγ ε hε
  have hentry : ∀ i : Fin k,
      ∃ T : ℝ, 0 ≤ T ∧
        ∀ t, T ≤ t → dist (γ t i) 0 < ε := by
    intro i
    exact cubicSink_gas.attractive (z₀ i) (fun t ↦ γ t i)
      (hγ.coordinate_finiteCubicSink i) ε hε
  let Tcoord : Fin k → ℝ :=
    fun i ↦ Classical.choose (hentry i)
  have hTcoord (i : Fin k) : 0 ≤ Tcoord i :=
    (Classical.choose_spec (hentry i)).1
  let T : ℝ := ∑ i, Tcoord i
  have hT : 0 ≤ T :=
    Finset.sum_nonneg fun i _ ↦ hTcoord i
  refine ⟨T, hT, ?_⟩
  intro t ht
  rw [dist_pi_lt_iff hε]
  intro i
  change dist (γ t i) 0 < ε
  have hiT : Tcoord i ≤ T := by
    apply Finset.single_le_sum
      (fun j _ ↦ hTcoord j) (Finset.mem_univ i)
  exact (Classical.choose_spec (hentry i)).2 t (hiT.trans ht)

/-- The coordinatewise cubic sink is globally asymptotically stable in
every finite dimension. -/
theorem finiteCubicSink_gas :
    GloballyAsymptoticallyStable
      (finiteCubicSink (k := k)) 0 where
  equilibrium := by
    funext i
    simp [finiteCubicSink, cubicSink]
  forwardComplete := finiteCubicSink_forwardComplete
  stable := finiteCubicSink_lyapunovStable
  attractive := finiteCubicSink_globallyAttractive

/-! ## GAS equivalence for dimension padding -/

/-- The dimension-padding field before degree raising is literally the
product of `H` and the finite cubic sink. -/
theorem directProductCubic_eq_productField
    (H : FinVector m ℝ → FinVector m ℝ) :
    directProductCubic (k := k) H =
      productField H (finiteCubicSink (k := k)) := by
  rfl

/-- Adding any finite number of independent cubic sink coordinates
preserves and reflects global asymptotic stability at the origin. -/
theorem directProductCubic_gas_iff
    (H : FinVector m ℝ → FinVector m ℝ) :
    GloballyAsymptoticallyStable
        (directProductCubic (k := k) H) (0, 0) ↔
      GloballyAsymptoticallyStable H 0 := by
  constructor
  · intro hp
    have hp' :
        GloballyAsymptoticallyStable
          (productField H (finiteCubicSink (k := k))) (0, 0) := by
      simpa [directProductCubic, productField,
        finiteCubicSink, cubicSink] using hp
    exact hp'.fst_of_product
      (by
        funext i
        simp [finiteCubicSink, cubicSink])
  · intro hH
    simpa [directProductCubic, productField,
      finiteCubicSink, cubicSink] using
      hH.prod (finiteCubicSink_gas (k := k))

/-- With exponent zero, degree padding has no dynamical effect. -/
@[simp]
theorem degreePaddedField_zero
    (H : FinVector m ℝ → FinVector m ℝ) :
    degreePaddedField (k := k) H 0 =
      directProductCubic H := by
  funext p
  simp [degreePaddedField, degreePaddingFactor]

/-- The full GAS equivalence is therefore already available for the
zero-exponent (no degree raising) case. -/
theorem degreePaddedField_zero_gas_iff
    (H : FinVector m ℝ → FinVector m ℝ) :
    GloballyAsymptoticallyStable
        (degreePaddedField (k := k) H 0) (0, 0) ↔
      GloballyAsymptoticallyStable H 0 := by
  rw [degreePaddedField_zero]
  exact directProductCubic_gas_iff H

/-! ## Positivity facts needed by the future time-change theorem -/

/-- Over the reals, the algebraic squared norm of a finite vector vanishes
exactly at the zero vector. -/
theorem finVector_normSq_eq_zero_iff (x : FinVector n ℝ) :
    normSq x = 0 ↔ x = 0 := by
  constructor
  · intro h
    change (∑ i, x i * x i) = 0 at h
    funext i
    change x i = 0
    have hterm : x i * x i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ ↦ mul_self_nonneg (x j))).mp
        h i (Finset.mem_univ i)
    exact mul_self_eq_zero.mp hterm
  · rintro rfl
    simp

/-- The total squared radius of a split point is nonnegative. -/
theorem splitNormSq_nonneg_real (p : SplitPoint m k ℝ) :
    0 ≤ splitNormSq p := by
  exact add_nonneg (normSq_nonneg p.1) (normSq_nonneg p.2)

/-- The total squared radius of a split point vanishes exactly at the
origin. -/
theorem splitNormSq_eq_zero_iff_real (p : SplitPoint m k ℝ) :
    splitNormSq p = 0 ↔ p = 0 := by
  constructor
  · intro h
    have hx : normSq p.1 = 0 := by
      have hxnonneg := normSq_nonneg p.1
      have hznonneg := normSq_nonneg p.2
      change normSq p.1 + normSq p.2 = 0 at h
      linarith
    have hz : normSq p.2 = 0 := by
      have hxnonneg := normSq_nonneg p.1
      have hznonneg := normSq_nonneg p.2
      change normSq p.1 + normSq p.2 = 0 at h
      linarith
    apply Prod.ext
    · exact (finVector_normSq_eq_zero_iff p.1).mp hx
    · exact (finVector_normSq_eq_zero_iff p.2).mp hz
  · rintro rfl
    simp [splitNormSq]

/-- The total squared radius is strictly positive at every nonzero split
point. -/
theorem splitNormSq_pos_iff_real (p : SplitPoint m k ℝ) :
    0 < splitNormSq p ↔ p ≠ 0 := by
  constructor
  · intro hpos hp
    subst p
    simp [splitNormSq] at hpos
  · intro hp
    have hne : splitNormSq p ≠ 0 :=
      (splitNormSq_eq_zero_iff_real p).not.mpr hp
    exact lt_of_le_of_ne (splitNormSq_nonneg_real p) hne.symm

/-- The degree-raising factor is strictly positive away from the origin. -/
theorem degreePaddingFactor_pos_of_ne_real
    (j : ℕ) {p : SplitPoint m k ℝ} (hp : p ≠ 0) :
    0 < degreePaddingFactor j p := by
  exact pow_pos ((splitNormSq_pos_iff_real p).2 hp) j

/-- The degree-raising factor is nonnegative everywhere. -/
theorem degreePaddingFactor_nonneg_real
    (j : ℕ) (p : SplitPoint m k ℝ) :
    0 ≤ degreePaddingFactor j p := by
  exact pow_nonneg (splitNormSq_nonneg_real p) j

/-! ## Smoothness and the full degree-padding equivalence -/

/-- Appending the coordinatewise cubic sink preserves `C¹` regularity. -/
theorem directProductCubic_contDiff
    {H : FinVector m ℝ → FinVector m ℝ}
    (hH : ContDiff ℝ 1 H) :
    ContDiff ℝ 1 (directProductCubic (k := k) H) := by
  unfold directProductCubic
  fun_prop

/-- The polynomial degree-padding factor is `C¹` (indeed smooth). -/
theorem degreePaddingFactor_contDiff
    (j : ℕ) :
    ContDiff ℝ 1
      (degreePaddingFactor (m := m) (k := k) (R := ℝ) j) := by
  unfold degreePaddingFactor splitNormSq normSq dot
  fun_prop

/-- For a positive exponent, the degree-padding factor vanishes exactly at
the origin. -/
theorem degreePaddingFactor_eq_zero_iff_real
    {j : ℕ} (hj : 0 < j) (p : SplitPoint m k ℝ) :
    degreePaddingFactor j p = 0 ↔ p = 0 := by
  rw [degreePaddingFactor, pow_eq_zero_iff
    (Nat.ne_of_gt hj)]
  exact splitNormSq_eq_zero_iff_real p

/-- The direct-product field has the origin as an equilibrium whenever the
base field does. -/
theorem directProductCubic_zero
    {H : FinVector m ℝ → FinVector m ℝ}
    (hH0 : H 0 = 0) :
    directProductCubic (k := k) H (0, 0) = 0 := by
  apply Prod.ext
  · exact hH0
  · funext i
    simp [directProductCubic]

/-- Degree and dimension padding preserve and reflect GAS for every
exponent.  The `C¹` and equilibrium hypotheses are exactly those needed by
the reusable state-dependent time-change theorem; polynomial homogeneous
fields satisfy them automatically. -/
theorem degreePaddedField_gas_iff
    (H : FinVector m ℝ → FinVector m ℝ)
    (hH : ContDiff ℝ 1 H) (hH0 : H 0 = 0)
    (j : ℕ) :
    GloballyAsymptoticallyStable
        (degreePaddedField (k := k) H j) (0, 0) ↔
      GloballyAsymptoticallyStable H 0 := by
  by_cases hj : j = 0
  · subst j
    exact degreePaddedField_zero_gas_iff H
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj
    have htime :
        GloballyAsymptoticallyStable
            (degreePaddedField (k := k) H j) (0, 0) ↔
          GloballyAsymptoticallyStable
            (directProductCubic (k := k) H) (0, 0) := by
      simpa only [degreePaddedField, timeScaledField] using
        (globallyAsymptoticallyStable_timeScaledField_iff
          (a := degreePaddingFactor
            (m := m) (k := k) (R := ℝ) j)
          (F := directProductCubic (k := k) H)
          (degreePaddingFactor_contDiff (m := m) (k := k) j)
          (degreePaddingFactor_nonneg_real (m := m) (k := k) j)
          (degreePaddingFactor_eq_zero_iff_real
            (m := m) (k := k) hjpos)
          (directProductCubic_contDiff (k := k) hH)
          (directProductCubic_zero (k := k) hH0))
    exact htime.trans (directProductCubic_gas_iff H)

end

end HGAS
