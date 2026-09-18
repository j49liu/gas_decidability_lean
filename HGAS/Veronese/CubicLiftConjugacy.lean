import HGAS.Analysis.MvPolynomialCalculus
import HGAS.Dynamics.Angular
import HGAS.Veronese.RealCone
import HGAS.Veronese.TransverseStabilization
import Mathlib.Tactic

/-!
# Angular conjugacy of the cubic Veronese lift

This file proves equation (16.5) of the paper.  Its basic metric identity is

```
⟪νₖ(x), Dνₖ(x)h⟫_Q
  = k (∑ i, x i ^ 2)^(k-1) (∑ i, x i * h i).
```

On the Euclidean unit sphere the middle factor is one.  Consequently the
canonical cubic lift multiplies radial reward by `k`, while its weighted
angular field is the differential of the source angular field.  Cubic
oddness gives the corresponding identities on the negative Veronese sheet.

The metric identity is proved by differentiating the already established
normalization

```
Q (νₖ(x)) = (∑ i, x i ^ 2)^k
```

along an affine line.  This keeps the proof close to the human argument and
avoids reopening multinomial-coefficient combinatorics.
-/

namespace HGAS.Veronese

open scoped BigOperators

noncomputable section

variable {n k : ℕ}

/-! ## Differential of the Veronese normalization -/

/-- The coordinate differential `dVeronese` is the actual derivative of
the Veronese map along a differentiable curve. -/
theorem HasDerivAt.veroneseMap
    {γ : ℝ → (Fin n → ℝ)} {h : Fin n → ℝ} {t : ℝ}
    (hγ : HasDerivAt γ h t) :
    HasDerivAt (fun s ↦ veroneseMap (k := k) (γ s))
      (dVeronese (k := k) (γ t) h) t := by
  rw [hasDerivAt_pi]
  intro a
  have hp :=
    HGAS.HasDerivAt.ratMvPolynomialEval hγ
      (sourceVeronesePolynomial a)
  simp only [HGAS.ratMvPolynomialEval,
    MvPolynomial.eval_map] at hp
  convert hp using 1
  · funext s
    exact (eval₂Hom_sourceVeronesePolynomial a (γ s)).symm
  · exact
      (sourcePolynomialDirectional_sourceVeronesePolynomial
        a (γ t) h).symm

/-- The quadratic form has derivative twice its weighted inner product
along any differentiable curve. -/
theorem HasDerivAt.Q_veroneseSpace
    {γ : ℝ → RealVeroneseSpace n k}
    {h : RealVeroneseSpace n k} {t : ℝ}
    (hγ : HasDerivAt γ h t) :
    HasDerivAt (fun s ↦ Q (γ s))
      (2 * weightedInner (γ t) h) t := by
  simp only [Q]
  have ha (a : MultiIndex n k) :
      HasDerivAt
        (fun s ↦ (multinomialWeight a : ℝ) * γ s a ^ 2)
        (2 * (multinomialWeight a : ℝ) * γ t a * h a) t := by
    have hcoord : HasDerivAt (fun s ↦ γ s a) (h a) t :=
      hasDerivAt_pi.mp hγ a
    convert (hcoord.pow 2).const_mul (multinomialWeight a : ℝ) using 1
    ring
  convert
    HasDerivAt.fun_sum
      (u := (Finset.univ : Finset (MultiIndex n k)))
      (fun a _ ↦ ha a) using 1
  unfold weightedInner
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The source squared radius has derivative twice the Euclidean coordinate
dot product. -/
theorem HasDerivAt.sourceRadiusSq
    {γ : ℝ → (Fin n → ℝ)} {h : Fin n → ℝ} {t : ℝ}
    (hγ : HasDerivAt γ h t) :
    HasDerivAt (fun s ↦ sourceRadiusSq (γ s))
      (2 * HGAS.dot (γ t) h) t := by
  simp only [HGAS.dot]
  have hi (i : Fin n) :
      HasDerivAt (fun s ↦ γ s i ^ 2)
        (2 * γ t i * h i) t := by
    have hcoord : HasDerivAt (fun s ↦ γ s i) (h i) t :=
      hasDerivAt_pi.mp hγ i
    convert hcoord.pow 2 using 1
    ring
  convert
    HasDerivAt.fun_sum
      (u := (Finset.univ : Finset (Fin n)))
      (fun i _ ↦ hi i) using 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Polarization of the Veronese normalization.  This is the weighted
metric identity underlying the radial and angular conjugacy. -/
theorem weightedInner_veroneseMap_dVeronese
    (x h : Fin n → ℝ) :
    weightedInner (veroneseMap (k := k) x)
        (dVeronese x h) =
      (k : ℝ) * sourceRadiusSq x ^ (k - 1) *
        HGAS.dot x h := by
  let γ : ℝ → (Fin n → ℝ) :=
    fun s ↦ x + s • h
  have hγ : HasDerivAt γ h 0 := by
    convert
      (hasDerivAt_const (x := (0 : ℝ)) x).add
        ((hasDerivAt_id (𝕜 := ℝ) 0).smul_const h) using 1
    simp
  have hleft :
      HasDerivAt
        (fun s ↦ Q (veroneseMap (k := k) (γ s)))
        (2 * weightedInner (veroneseMap (k := k) x)
          (dVeronese x h)) 0 := by
    have hv :=
      HGAS.Veronese.HasDerivAt.veroneseMap (k := k) hγ
    have hQ :=
      HGAS.Veronese.HasDerivAt.Q_veroneseSpace hv
    simpa only [γ, zero_smul, add_zero] using hQ
  have hradius :=
    HGAS.Veronese.HasDerivAt.sourceRadiusSq hγ
  have hright :
      HasDerivAt (fun s ↦ sourceRadiusSq (γ s) ^ k)
        ((k : ℝ) * sourceRadiusSq x ^ (k - 1) *
          (2 * HGAS.dot x h)) 0 := by
    convert hradius.pow k using 1
    simp only [γ, zero_smul, add_zero]
  have heq :
      (fun s ↦ Q (veroneseMap (k := k) (γ s))) =
        fun s ↦ sourceRadiusSq (γ s) ^ k := by
    funext s
    rw [Q_veroneseMap]
    simp only [sourceRadiusSq]
  rw [heq] at hleft
  have hderiv := hleft.unique hright
  linarith

/-! ## Positive-sheet conjugacy -/

/-- Real linearity of `Dνₖ(x)` in subtraction form. -/
theorem dVeronese_sub_real
    (x h₁ h₂ : Fin n → ℝ) :
    dVeronese (k := k) x (h₁ - h₂) =
      dVeronese x h₁ - dVeronese x h₂ := by
  rw [sub_eq_add_neg, dVeronese_add]
  have hneg :
      dVeronese (k := k) x (-h₂) =
        -dVeronese (k := k) x h₂ := by
    simpa only [neg_one_smul] using
      dVeronese_smul (k := k) (-1 : ℝ) x h₂
  rw [hneg]
  rw [sub_eq_add_neg]

/-- On a unit source vector, the weighted radial reward of the cubic lift
is `k` times the source radial reward. -/
theorem weightedRadialReward_cubicLiftField_veronese
    (F : HGAS.PolynomialField n)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F)
    (hk : 1 ≤ k)
    (u : Fin n → ℝ) (hu : sourceRadiusSq u = 1) :
    weightedRadialReward
        (fun y ↦ evalCoordinateField
          (cubicLiftField (k := k) F) y)
        (veroneseMap (k := k) u) =
      (k : ℝ) *
        HGAS.radialReward (fun x ↦ evalSourceField F x) u := by
  rw [weightedRadialReward,
    eval_cubicLiftField_veronese F hF hk u,
    weightedInner_veroneseMap_dVeronese]
  simp [hu, HGAS.radialReward]

/-- Equation (16.5), positive sheet: the lifted angular field is exactly
the Veronese differential of the source angular field. -/
theorem weightedAngularField_cubicLiftField_veronese
    (F : HGAS.PolynomialField n)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F)
    (hk : 1 ≤ k)
    (u : Fin n → ℝ) (hu : sourceRadiusSq u = 1) :
    weightedAngularField
        (fun y ↦ evalCoordinateField
          (cubicLiftField (k := k) F) y)
        (veroneseMap (k := k) u) =
      dVeronese u
        (HGAS.angularField
          (fun x ↦ evalSourceField F x) u) := by
  rw [weightedAngularField,
    weightedRadialReward_cubicLiftField_veronese
      F hF hk u hu,
    eval_cubicLiftField_veronese F hF hk u]
  rw [show
      ((k : ℝ) *
          HGAS.radialReward
            (fun x ↦ evalSourceField F x) u) •
          veroneseMap (k := k) u =
        dVeronese u
          (HGAS.radialReward
            (fun x ↦ evalSourceField F x) u • u) by
      rw [dVeronese_smul, dVeronese_self]
      funext a
      simp only [Pi.smul_apply, smul_eq_mul]
      ring]
  rw [← dVeronese_sub_real]
  congr 1

/-! ## Negative-sheet conjugacy -/

/-- The radial reward on the negative signed sheet is the same as on the
positive sheet. -/
theorem weightedRadialReward_cubicLiftField_neg_veronese
    (F : HGAS.PolynomialField n)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F)
    (hk : 1 ≤ k)
    (u : Fin n → ℝ) (hu : sourceRadiusSq u = 1) :
    weightedRadialReward
        (fun y ↦ evalCoordinateField
          (cubicLiftField (k := k) F) y)
        (-veroneseMap (k := k) u) =
      (k : ℝ) *
        HGAS.radialReward (fun x ↦ evalSourceField F x) u := by
  rw [weightedRadialReward,
    eval_cubicLiftField_neg_veronese F hF hk u]
  simp only [weightedInner, Pi.neg_apply]
  rw [show
      (∑ a : MultiIndex n k,
          (multinomialWeight a : ℝ) *
              -veroneseMap (k := k) u a *
            -dVeronese u (evalSourceField F u) a) =
        weightedInner (veroneseMap (k := k) u)
          (dVeronese u (evalSourceField F u)) by
      unfold weightedInner
      apply Finset.sum_congr rfl
      intro a _
      ring]
  rw [weightedInner_veroneseMap_dVeronese]
  simp [hu, HGAS.radialReward]

/-- Equation (16.5), negative sheet.  The signed parametrization
`u ↦ -νₖ(u)` intertwines the source angular field with the negative of its
Veronese differential. -/
theorem weightedAngularField_cubicLiftField_neg_veronese
    (F : HGAS.PolynomialField n)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F)
    (hk : 1 ≤ k)
    (u : Fin n → ℝ) (hu : sourceRadiusSq u = 1) :
    weightedAngularField
        (fun y ↦ evalCoordinateField
          (cubicLiftField (k := k) F) y)
        (-veroneseMap (k := k) u) =
      -dVeronese u
        (HGAS.angularField
          (fun x ↦ evalSourceField F x) u) := by
  rw [weightedAngularField,
    weightedRadialReward_cubicLiftField_neg_veronese
      F hF hk u hu,
    eval_cubicLiftField_neg_veronese F hF hk u]
  have hpositive :=
    weightedAngularField_cubicLiftField_veronese
      F hF hk u hu
  rw [weightedAngularField,
    weightedRadialReward_cubicLiftField_veronese
      F hF hk u hu,
    eval_cubicLiftField_veronese F hF hk u] at hpositive
  rw [← hpositive]
  funext a
  simp only [Pi.sub_apply, Pi.neg_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

end

end HGAS.Veronese
