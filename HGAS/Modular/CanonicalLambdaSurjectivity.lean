import HGAS.Modular.CanonicalLambdaAbsoluteInvariant
import HGAS.Modular.CanonicalLambdaTargetTopology
import Mathlib.NumberTheory.Modular
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Global surjectivity of canonical lambda

This module proves that canonical lambda maps the upper half-plane onto the
twice-punctured complex plane.  The argument is deliberately independent of
the construction of the level-two modular quotient.

The local inverse theorem makes the image open.  To prove that it is also
closed, take a convergent sequence of lambda values and choose arbitrary
preimages.  Move every preimage into the standard `SL(2, ℤ)` fundamental
domain.  The absolute invariant

```
                  (1 - λ + λ²)³
             J₀ = ----------------
                       λ²(1-λ)²
```

is unchanged by this move.  Since the target sequence converges away from
`0` and `1`, these invariant values stay bounded.  On the other hand `J₀`
tends to infinity at the cusp.  Thus the moved preimages have uniformly
bounded height and lie in a compact truncated fundamental domain.  A
convergent subsequence supplies a limiting preimage up to one of the six
cross-ratio transformations.  The elementary `S` and `T` transformation
laws for lambda realize all six alternatives.

This is also a reusable compactness pattern: a finite-fiber invariant that
is proper at the cusp converts local uniformization into global
surjectivity.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open Complex Real ModularGroup Filter Topology
open scoped MatrixGroups Topology

noncomputable section

/-- The absolute invariant, regarded as a function on the punctured target.
The subtype hypotheses make its denominator nonzero. -/
def lambdaAbsoluteInvariantPunctured
    (x : LambdaPuncturedPlane) : ℂ :=
  lambdaAbsoluteInvariant x

/-- The absolute invariant is continuous on the twice-punctured plane. -/
theorem lambdaAbsoluteInvariantPunctured_continuous :
    Continuous lambdaAbsoluteInvariantPunctured := by
  unfold lambdaAbsoluteInvariantPunctured lambdaAbsoluteInvariant
  apply
    ((continuous_const.sub continuous_subtype_val).add
      (continuous_subtype_val.pow 2)).pow 3 |>.div
  · exact
      (continuous_subtype_val.pow 2).mul
        ((continuous_const.sub continuous_subtype_val).pow 2)
  · intro x
    exact
      mul_ne_zero
        (pow_ne_zero 2 x.property.1)
        (pow_ne_zero 2
          (sub_ne_zero.mpr x.property.2.symm))

/-- The absolute invariant of canonical lambda is continuous on the upper
half-plane. -/
theorem canonicalLambdaAbsoluteInvariant_continuous :
    Continuous canonicalLambdaAbsoluteInvariant := by
  have hcomp :=
    lambdaAbsoluteInvariantPunctured_continuous.comp
      canonicalLambdaPunctured_continuous
  simpa only [Function.comp_apply,
    lambdaAbsoluteInvariantPunctured,
    canonicalLambdaAbsoluteInvariant,
    canonicalLambdaPunctured_coe] using hcomp

/-- The transformation `T S` realizes `x ↦ (x-1)/x`. -/
theorem canonicalLambda_vadd_one_modularSPoint
    (z : ℍ) :
    canonicalLambda
        ((1 : ℝ) +ᵥ modularSPoint z) =
      (canonicalLambda z - 1) / canonicalLambda z := by
  rw [canonicalLambda_vadd_one,
    canonicalLambda_modularSPoint]
  field_simp [canonicalLambda_ne_zero z]
  ring

/-- The transformation `S T` realizes `x ↦ 1/(1-x)`. -/
theorem canonicalLambda_modularSPoint_vadd_one
    (z : ℍ) :
    canonicalLambda
        (modularSPoint ((1 : ℝ) +ᵥ z)) =
      1 / (1 - canonicalLambda z) := by
  rw [canonicalLambda_modularSPoint,
    canonicalLambda_vadd_one]
  field_simp [
    sub_ne_zero.mpr (canonicalLambda_ne_one z),
    sub_ne_zero.mpr (canonicalLambda_ne_one z).symm]
  ring

/-- The transformation `S T S` realizes `x ↦ 1/x`. -/
theorem canonicalLambda_modularSPoint_vadd_one_modularSPoint
    (z : ℍ) :
    canonicalLambda
        (modularSPoint
          ((1 : ℝ) +ᵥ modularSPoint z)) =
      1 / canonicalLambda z := by
  rw [canonicalLambda_modularSPoint,
    canonicalLambda_vadd_one_modularSPoint]
  field_simp [canonicalLambda_ne_zero z]
  ring

/-- Every one of the six cross-ratio transforms of a canonical-lambda
value is again a canonical-lambda value. -/
theorem mem_range_canonicalLambdaPunctured_of_crossRatio
    (z : ℍ) (y : LambdaPuncturedPlane)
    (h :
      (y : ℂ) = canonicalLambda z ∨
      (y : ℂ) = 1 - canonicalLambda z ∨
      (y : ℂ) = 1 / canonicalLambda z ∨
      (y : ℂ) =
        (canonicalLambda z - 1) /
          canonicalLambda z ∨
      (y : ℂ) = 1 / (1 - canonicalLambda z) ∨
      (y : ℂ) =
        canonicalLambda z /
          (canonicalLambda z - 1)) :
    y ∈ Set.range canonicalLambdaPunctured := by
  rcases h with h | h | h | h | h | h
  · exact ⟨z, Subtype.ext h.symm⟩
  · exact
      ⟨modularSPoint z,
        Subtype.ext
          ((canonicalLambda_modularSPoint z).trans
            h.symm)⟩
  · exact
      ⟨modularSPoint
          ((1 : ℝ) +ᵥ modularSPoint z),
        Subtype.ext
          ((canonicalLambda_modularSPoint_vadd_one_modularSPoint
            z).trans h.symm)⟩
  · exact
      ⟨(1 : ℝ) +ᵥ modularSPoint z,
        Subtype.ext
          ((canonicalLambda_vadd_one_modularSPoint z).trans
            h.symm)⟩
  · exact
      ⟨modularSPoint ((1 : ℝ) +ᵥ z),
        Subtype.ext
          ((canonicalLambda_modularSPoint_vadd_one z).trans
            h.symm)⟩
  · exact
      ⟨(1 : ℝ) +ᵥ z,
        Subtype.ext
          ((canonicalLambda_vadd_one z).trans h.symm)⟩

/-- The image of canonical lambda in the punctured plane is closed.

The proof is the compactness-at-the-cusp argument described in the module
docstring.  Notice that no quotient-space uniformization theorem is used:
only the standard `SL(2,ℤ)` fundamental domain, the two elementary
transformation laws, and the explicitly factorized six-fold invariant enter
the proof. -/
theorem isClosed_range_canonicalLambdaPunctured :
    IsClosed (Set.range canonicalLambdaPunctured) := by
  apply IsSeqClosed.isClosed
  intro u a hu hua
  choose z hz using hu
  choose g hg using
    fun n ↦ ModularGroup.exists_smul_mem_fd (z n)
  let w : ℕ → ℍ := fun n ↦ g n • z n
  have hw_fd (n : ℕ) :
      w n ∈ ModularGroup.fd := by
    exact hg n
  have hinvariant (n : ℕ) :
      canonicalLambdaAbsoluteInvariant (w n) =
        lambdaAbsoluteInvariantPunctured (u n) := by
    calc
      canonicalLambdaAbsoluteInvariant (w n) =
          canonicalLambdaAbsoluteInvariant (z n) := by
        exact canonicalLambdaAbsoluteInvariant_smul
          (g n) (z n)
      _ = lambdaAbsoluteInvariantPunctured (u n) := by
        unfold canonicalLambdaAbsoluteInvariant
          lambdaAbsoluteInvariantPunctured
        congr 1
        exact congrArg Subtype.val (hz n)
  have hnorm_tendsto :
      Tendsto
        (fun n ↦
          ‖lambdaAbsoluteInvariantPunctured (u n)‖)
        atTop
        (𝓝 ‖lambdaAbsoluteInvariantPunctured a‖) := by
    have hbase :
        Tendsto
          (fun n ↦
            lambdaAbsoluteInvariantPunctured (u n))
          atTop
          (𝓝 (lambdaAbsoluteInvariantPunctured a)) := by
      have hcont :
          Tendsto lambdaAbsoluteInvariantPunctured
            (𝓝 a)
            (𝓝 (lambdaAbsoluteInvariantPunctured a)) :=
        lambdaAbsoluteInvariantPunctured_continuous.continuousAt
      exact hcont.comp hua
    exact hbase.norm
  obtain ⟨M, hM⟩ := hnorm_tendsto.bddAbove_range
  have hnorm_le (n : ℕ) :
      ‖lambdaAbsoluteInvariantPunctured (u n)‖ ≤ M :=
    hM ⟨n, rfl⟩
  have hcusp :
      ∀ᶠ q in atImInfty,
        M <
          ‖lambdaAbsoluteInvariant
            (canonicalLambda q)‖ :=
    norm_lambdaAbsoluteInvariant_canonicalLambda_tendsto_atTop.eventually
      (eventually_gt_atTop M)
  rw [HGAS.Analysis.eventually_atImInfty] at hcusp
  obtain ⟨A, hA⟩ := hcusp
  have hw_height (n : ℕ) :
      (w n).im ≤ A := by
    by_contra hnot
    have hlarge :
        M <
          ‖lambdaAbsoluteInvariant
            (canonicalLambda (w n))‖ :=
      hA (w n) (le_of_not_ge hnot)
    have heq :
        ‖lambdaAbsoluteInvariant
            (canonicalLambda (w n))‖ =
          ‖lambdaAbsoluteInvariantPunctured (u n)‖ := by
      exact congrArg norm (hinvariant n)
    rw [heq] at hlarge
    exact (not_lt_of_ge (hnorm_le n)) hlarge
  have hw_truncated (n : ℕ) :
      w n ∈
        ModularGroup.truncatedFundamentalDomain A :=
    ⟨hw_fd n, hw_height n⟩
  obtain ⟨zlim, hzlim, φ, hφ, hφlim⟩ :=
    (ModularGroup.isCompact_truncatedFundamentalDomain A).tendsto_subseq
      hw_truncated
  have huφ :
      Tendsto (u ∘ φ) atTop (𝓝 a) :=
    hua.comp hφ.tendsto_atTop
  have hright :
      Tendsto
        (fun n ↦
          lambdaAbsoluteInvariantPunctured (u (φ n)))
        atTop
        (𝓝 (lambdaAbsoluteInvariantPunctured a)) := by
    have hcont :
        Tendsto lambdaAbsoluteInvariantPunctured
          (𝓝 a)
          (𝓝 (lambdaAbsoluteInvariantPunctured a)) :=
      lambdaAbsoluteInvariantPunctured_continuous.continuousAt
    simpa only [Function.comp_apply] using hcont.comp huφ
  have hleft :
      Tendsto
        (fun n ↦
          canonicalLambdaAbsoluteInvariant (w (φ n)))
        atTop
        (𝓝 (canonicalLambdaAbsoluteInvariant zlim)) := by
    have hcont :
        Tendsto canonicalLambdaAbsoluteInvariant
          (𝓝 zlim)
          (𝓝 (canonicalLambdaAbsoluteInvariant zlim)) :=
      canonicalLambdaAbsoluteInvariant_continuous.continuousAt
    simpa only [Function.comp_apply] using hcont.comp hφlim
  have hinvariant_limit :
      canonicalLambdaAbsoluteInvariant zlim =
        lambdaAbsoluteInvariantPunctured a := by
    apply tendsto_nhds_unique hleft
    convert hright using 1
    ext n
    exact hinvariant (φ n)
  have hsix :
      (a : ℂ) = canonicalLambda zlim ∨
      (a : ℂ) = 1 - canonicalLambda zlim ∨
      (a : ℂ) = 1 / canonicalLambda zlim ∨
      (a : ℂ) =
        (canonicalLambda zlim - 1) /
          canonicalLambda zlim ∨
      (a : ℂ) =
        1 / (1 - canonicalLambda zlim) ∨
      (a : ℂ) =
        canonicalLambda zlim /
          (canonicalLambda zlim - 1) := by
    apply eq_crossRatio_of_lambdaAbsoluteInvariant_eq
      (canonicalLambda_ne_zero zlim)
      (canonicalLambda_ne_one zlim)
      a.property.1 a.property.2
    exact hinvariant_limit
  exact
    mem_range_canonicalLambdaPunctured_of_crossRatio
      zlim a hsix

/-- Canonical lambda maps the upper half-plane onto the twice-punctured
plane. -/
theorem canonicalLambdaPunctured_surjective :
    Function.Surjective canonicalLambdaPunctured :=
  canonicalLambdaPunctured_surjective_of_isClosed_range
    isClosed_range_canonicalLambdaPunctured

end

end HGAS.Modular
