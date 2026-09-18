import HGAS.Modular.JacobiThetaReciprocalLocalRank
import Mathlib.Analysis.Complex.CoveringMap

/-!
# Fiber rigidity in the reciprocal Jacobi residual family

Fix the modulus and one of the three reciprocal affine coordinates.
The two residual equations then determine the *squares* of the other two
coordinates.  Hence each remaining ambiguity is only a sign.  Near a
point where those two coordinates are nonzero, the square map is locally
injective and the signs cannot change.

This file formalizes both statements.  The final theorem says that the
projection

```
             (τ,a,b,c) ↦ (τ, selected coordinate)
```

is locally injective whenever the two complementary coordinates are
nonzero.  Combined with the nonzero derivative theorem in
`JacobiThetaReciprocalLocalRank`, this is the algebraic half of the
local-homeomorphism argument for the reciprocal theta map.
-/

namespace HGAS.Modular

open Complex Real Topology
open UpperHalfPlane hiding I

noncomputable section

/-- Projection to the modulus and one selected reciprocal coordinate. -/
def jacobiThetaReciprocalProjection
    (k : Fin 3) (p : JacobiThetaReciprocalTotal) :
    ℍ × ℂ :=
  (p.modulus, p.coordinates k)

theorem continuous_jacobiThetaReciprocalCoordinate_fromTotal
    (k : Fin 3) :
    Continuous
      (fun p : JacobiThetaReciprocalTotal ↦
        p.coordinates k) := by
  exact
    (continuous_apply k).comp
      (continuous_snd.comp
        continuous_jacobiThetaReciprocalTotal_toBase)

theorem continuous_jacobiThetaReciprocalProjection
    (k : Fin 3) :
    Continuous (jacobiThetaReciprocalProjection k) := by
  exact
    (continuous_fst.comp
        continuous_jacobiThetaReciprocalTotal_toBase).prodMk
      (continuous_jacobiThetaReciprocalCoordinate_fromTotal k)

/-- If two reciprocal residual points have the same modulus and the
same selected coordinate, then all three coordinate squares agree. -/
theorem jacobiThetaReciprocal_coordinates_sq_eq_of_projection_eq
    (P Q : JacobiThetaReciprocalTotal)
    (k : Fin 3)
    (hmodulus : P.modulus = Q.modulus)
    (hselected : P.coordinates k = Q.coordinates k) :
    ∀ j : Fin 3,
      P.coordinates j ^ 2 = Q.coordinates j ^ 2 := by
  have hp :=
    canonicalUnaryRoots_p_product_ne_zero P.modulus
  have hp23 :
      (canonicalUnaryRoots P.modulus).p2 *
          (canonicalUnaryRoots P.modulus).p3 ≠ 0 :=
    (mul_ne_zero_iff.mp hp).1
  have hp2 :
      (canonicalUnaryRoots P.modulus).p2 ≠ 0 :=
    (mul_ne_zero_iff.mp hp23).1
  have hp3 :
      (canonicalUnaryRoots P.modulus).p3 ≠ 0 :=
    (mul_ne_zero_iff.mp hp23).2
  have hp4 :
      (canonicalUnaryRoots P.modulus).p4 ≠ 0 :=
    (mul_ne_zero_iff.mp hp).2
  have hP1 := P.q1
  have hQ1 := Q.q1
  have hP2 := P.q2
  have hQ2 := Q.q2
  rw [← hmodulus] at hQ1 hQ2
  change
    (canonicalUnaryRoots P.modulus).p2 *
          P.coordinates 2 ^ 2 -
        (canonicalUnaryRoots P.modulus).p4 *
          P.coordinates 0 ^ 2 -
      (canonicalUnaryRoots P.modulus).p3 = 0 at hP1
  change
    (canonicalUnaryRoots P.modulus).p2 *
          Q.coordinates 2 ^ 2 -
        (canonicalUnaryRoots P.modulus).p4 *
          Q.coordinates 0 ^ 2 -
      (canonicalUnaryRoots P.modulus).p3 = 0 at hQ1
  change
    (canonicalUnaryRoots P.modulus).p2 *
          P.coordinates 1 ^ 2 -
        (canonicalUnaryRoots P.modulus).p3 *
          P.coordinates 0 ^ 2 -
      (canonicalUnaryRoots P.modulus).p4 = 0 at hP2
  change
    (canonicalUnaryRoots P.modulus).p2 *
          Q.coordinates 1 ^ 2 -
        (canonicalUnaryRoots P.modulus).p3 *
          Q.coordinates 0 ^ 2 -
      (canonicalUnaryRoots P.modulus).p4 = 0 at hQ2
  fin_cases k
  · have h0 :
        P.coordinates 0 = Q.coordinates 0 := by
      exact hselected
    have h1 :
        P.coordinates 1 ^ 2 =
          Q.coordinates 1 ^ 2 := by
      have hP2' := hP2
      rw [h0] at hP2'
      apply mul_left_cancel₀ hp2
      linear_combination hP2' - hQ2
    have h2 :
        P.coordinates 2 ^ 2 =
          Q.coordinates 2 ^ 2 := by
      have hP1' := hP1
      rw [h0] at hP1'
      apply mul_left_cancel₀ hp2
      linear_combination hP1' - hQ1
    intro j
    fin_cases j
    · exact congrArg (· ^ 2) h0
    · exact h1
    · exact h2
  · have h1 :
        P.coordinates 1 = Q.coordinates 1 := by
      exact hselected
    have h0 :
        P.coordinates 0 ^ 2 =
          Q.coordinates 0 ^ 2 := by
      have hP2' := hP2
      rw [h1] at hP2'
      apply mul_left_cancel₀ hp3
      linear_combination -(hP2' - hQ2)
    have h2 :
        P.coordinates 2 ^ 2 =
          Q.coordinates 2 ^ 2 := by
      have hP1' := hP1
      rw [h0] at hP1'
      apply mul_left_cancel₀ hp2
      linear_combination hP1' - hQ1
    intro j
    fin_cases j
    · exact h0
    · exact congrArg (· ^ 2) h1
    · exact h2
  · have h2 :
        P.coordinates 2 = Q.coordinates 2 := by
      exact hselected
    have h0 :
        P.coordinates 0 ^ 2 =
          Q.coordinates 0 ^ 2 := by
      have hP1' := hP1
      rw [h2] at hP1'
      apply mul_left_cancel₀ hp4
      linear_combination -(hP1' - hQ1)
    have h1 :
        P.coordinates 1 ^ 2 =
          Q.coordinates 1 ^ 2 := by
      have hP2' := hP2
      rw [h0] at hP2'
      apply mul_left_cancel₀ hp2
      linear_combination hP2' - hQ2
    intro j
    fin_cases j
    · exact h0
    · exact h1
    · exact congrArg (· ^ 2) h2

/-- Equivalent sign form of fiber rigidity. -/
theorem jacobiThetaReciprocal_coordinate_eq_or_eq_neg_of_projection_eq
    (P Q : JacobiThetaReciprocalTotal)
    (k : Fin 3)
    (hmodulus : P.modulus = Q.modulus)
    (hselected : P.coordinates k = Q.coordinates k)
    (j : Fin 3) :
    P.coordinates j = Q.coordinates j ∨
      P.coordinates j = -Q.coordinates j :=
  sq_eq_sq_iff_eq_or_eq_neg.mp
    (jacobiThetaReciprocal_coordinates_sq_eq_of_projection_eq
      P Q k hmodulus hselected j)

/-- The condition that the two coordinates complementary to `k` are
nonzero. -/
def JacobiThetaReciprocalComplementNonzero
    (k : Fin 3) (p : JacobiThetaReciprocalTotal) : Prop :=
  match k with
  | 0 => p.coordinates 1 ≠ 0 ∧ p.coordinates 2 ≠ 0
  | 1 => p.coordinates 0 ≠ 0 ∧ p.coordinates 2 ≠ 0
  | 2 => p.coordinates 0 ≠ 0 ∧ p.coordinates 1 ≠ 0

/-- The complex square map is injective on some open neighborhood of
every nonzero point. -/
theorem exists_open_square_injOn
    {x : ℂ} (hx : x ≠ 0) :
    ∃ U : Set ℂ,
      IsOpen U ∧ x ∈ U ∧
        Set.InjOn (fun w : ℂ ↦ w ^ 2) U := by
  have hcover :
      IsCoveringMapOn
        (fun w : ℂ ↦ w ^ 2) ({0}ᶜ : Set ℂ) :=
    isCoveringMapOn_npow 2 (by norm_num)
  have hxsource :
      x ∈ (fun w : ℂ ↦ w ^ 2) ⁻¹' ({0}ᶜ : Set ℂ) := by
    exact pow_ne_zero 2 hx
  obtain ⟨e, hxe, he⟩ :=
    hcover.isLocalHomeomorphOn x hxsource
  refine ⟨e.source, e.open_source, hxe, ?_⟩
  rw [he]
  exact e.injOn

/-- Near a reciprocal residual point with nonzero complementary
coordinates, projection to the modulus and selected coordinate is
injective. -/
theorem exists_open_jacobiThetaReciprocalProjection_injOn
    (P : JacobiThetaReciprocalTotal)
    (k : Fin 3)
    (hcomplement :
      JacobiThetaReciprocalComplementNonzero k P) :
    ∃ U : Set JacobiThetaReciprocalTotal,
      IsOpen U ∧ P ∈ U ∧
        Set.InjOn (jacobiThetaReciprocalProjection k) U := by
  fin_cases k
  · obtain ⟨U1, hU1open, hP1, hU1inj⟩ :=
      exists_open_square_injOn hcomplement.1
    obtain ⟨U2, hU2open, hP2, hU2inj⟩ :=
      exists_open_square_injOn hcomplement.2
    let U : Set JacobiThetaReciprocalTotal :=
      (fun Q ↦ Q.coordinates 1) ⁻¹' U1 ∩
        (fun Q ↦ Q.coordinates 2) ⁻¹' U2
    refine ⟨U, ?_, ⟨hP1, hP2⟩, ?_⟩
    · exact
        hU1open.preimage
            (continuous_jacobiThetaReciprocalCoordinate_fromTotal 1)
          |>.inter
            (hU2open.preimage
              (continuous_jacobiThetaReciprocalCoordinate_fromTotal 2))
    · intro Q hQ R hR heq
      have hmodulus : Q.modulus = R.modulus :=
        congrArg Prod.fst heq
      have hselected :
          Q.coordinates 0 = R.coordinates 0 :=
        congrArg Prod.snd heq
      have hsquares :=
        jacobiThetaReciprocal_coordinates_sq_eq_of_projection_eq
          Q R 0 hmodulus hselected
      have h1 :
          Q.coordinates 1 = R.coordinates 1 :=
        hU1inj hQ.1 hR.1 (hsquares 1)
      have h2 :
          Q.coordinates 2 = R.coordinates 2 :=
        hU2inj hQ.2 hR.2 (hsquares 2)
      apply JacobiThetaReciprocalTotal.ext hmodulus
      funext j
      fin_cases j
      · exact hselected
      · exact h1
      · exact h2
  · obtain ⟨U0, hU0open, hP0, hU0inj⟩ :=
      exists_open_square_injOn hcomplement.1
    obtain ⟨U2, hU2open, hP2, hU2inj⟩ :=
      exists_open_square_injOn hcomplement.2
    let U : Set JacobiThetaReciprocalTotal :=
      (fun Q ↦ Q.coordinates 0) ⁻¹' U0 ∩
        (fun Q ↦ Q.coordinates 2) ⁻¹' U2
    refine ⟨U, ?_, ⟨hP0, hP2⟩, ?_⟩
    · exact
        hU0open.preimage
            (continuous_jacobiThetaReciprocalCoordinate_fromTotal 0)
          |>.inter
            (hU2open.preimage
              (continuous_jacobiThetaReciprocalCoordinate_fromTotal 2))
    · intro Q hQ R hR heq
      have hmodulus : Q.modulus = R.modulus :=
        congrArg Prod.fst heq
      have hselected :
          Q.coordinates 1 = R.coordinates 1 :=
        congrArg Prod.snd heq
      have hsquares :=
        jacobiThetaReciprocal_coordinates_sq_eq_of_projection_eq
          Q R 1 hmodulus hselected
      have h0 :
          Q.coordinates 0 = R.coordinates 0 :=
        hU0inj hQ.1 hR.1 (hsquares 0)
      have h2 :
          Q.coordinates 2 = R.coordinates 2 :=
        hU2inj hQ.2 hR.2 (hsquares 2)
      apply JacobiThetaReciprocalTotal.ext hmodulus
      funext j
      fin_cases j
      · exact h0
      · exact hselected
      · exact h2
  · obtain ⟨U0, hU0open, hP0, hU0inj⟩ :=
      exists_open_square_injOn hcomplement.1
    obtain ⟨U1, hU1open, hP1, hU1inj⟩ :=
      exists_open_square_injOn hcomplement.2
    let U : Set JacobiThetaReciprocalTotal :=
      (fun Q ↦ Q.coordinates 0) ⁻¹' U0 ∩
        (fun Q ↦ Q.coordinates 1) ⁻¹' U1
    refine ⟨U, ?_, ⟨hP0, hP1⟩, ?_⟩
    · exact
        hU0open.preimage
            (continuous_jacobiThetaReciprocalCoordinate_fromTotal 0)
          |>.inter
            (hU1open.preimage
              (continuous_jacobiThetaReciprocalCoordinate_fromTotal 1))
    · intro Q hQ R hR heq
      have hmodulus : Q.modulus = R.modulus :=
        congrArg Prod.fst heq
      have hselected :
          Q.coordinates 2 = R.coordinates 2 :=
        congrArg Prod.snd heq
      have hsquares :=
        jacobiThetaReciprocal_coordinates_sq_eq_of_projection_eq
          Q R 2 hmodulus hselected
      have h0 :
          Q.coordinates 0 = R.coordinates 0 :=
        hU0inj hQ.1 hR.1 (hsquares 0)
      have h1 :
          Q.coordinates 1 = R.coordinates 1 :=
        hU1inj hQ.2 hR.2 (hsquares 1)
      apply JacobiThetaReciprocalTotal.ext hmodulus
      funext j
      fin_cases j
      · exact h0
      · exact h1
      · exact hselected

end

end HGAS.Modular
