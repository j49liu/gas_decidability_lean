import HGAS.Modular.JacobiThetaProjectiveSurjectivity
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Tactic

/-!
# The varying-modulus reciprocal theta map

The algebraic `Projectivization` currently used for the set-theoretic
theta-saturation theorem has no topology in Mathlib.  Consequently the
moving-parameter selection problem should not be phrased as a covering
map into that type.

This file gives the topologically honest replacement.  On the chart
`θ₁ ≠ 0`, divide all theta coordinates by `θ₁` and write

```
  a = θ₂ / θ₁,   b = θ₃ / θ₁,   c = θ₄ / θ₁.
```

The two homogeneous Jacobi quadrics become

```
  p₂ c² - p₄ a² - p₃ = 0,
  p₂ b² - p₃ a² - p₄ = 0.
```

Their varying-modulus zero set is an ordinary subtype of
`ℍ × (Fin 3 → ℂ)`, hence carries the correct induced topology.  We prove
that the normalized total theta map into this subtype is continuous and
surjective.  The last section isolates the one genuinely global input
still needed for coherent parameter selection: that this total map is a
covering map.  Once that proposition is supplied, Mathlib's covering
homotopy theorem gives the desired unique lift of every continuous real
trajectory immediately.

No global covering claim is made here.  Its proof requires a
varying-lattice continuation argument (equivalently, a construction of
the universal level-two elliptic quotient) which is not contained in the
current theta library.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open Complex Real Topology

noncomputable section

/-- The three affine coordinates after normalizing by the first theta
coordinate.  Index `0` is `θ₂/θ₁`, index `1` is `θ₃/θ₁`, and index `2`
is `θ₄/θ₁`. -/
abbrev JacobiThetaReciprocalCoordinates := Fin 3 → ℂ

/-- The first normalized residual quadric. -/
def jacobiThetaReciprocalQ1
    (τ : ℍ) (x : JacobiThetaReciprocalCoordinates) : ℂ :=
  (canonicalUnaryRoots τ).p2 * x 2 ^ 2 -
      (canonicalUnaryRoots τ).p4 * x 0 ^ 2 -
    (canonicalUnaryRoots τ).p3

/-- The second normalized residual quadric. -/
def jacobiThetaReciprocalQ2
    (τ : ℍ) (x : JacobiThetaReciprocalCoordinates) : ℂ :=
  (canonicalUnaryRoots τ).p2 * x 1 ^ 2 -
      (canonicalUnaryRoots τ).p3 * x 0 ^ 2 -
    (canonicalUnaryRoots τ).p4

/-- The varying-modulus affine residual curve in the reciprocal chart. -/
@[ext]
structure JacobiThetaReciprocalTotal where
  modulus : ℍ
  coordinates : JacobiThetaReciprocalCoordinates
  q1 : jacobiThetaReciprocalQ1 modulus coordinates = 0
  q2 : jacobiThetaReciprocalQ2 modulus coordinates = 0

/-- Forget the residual equations and retain the ordinary ambient
coordinates. -/
abbrev JacobiThetaReciprocalTotal.toBase
    (p : JacobiThetaReciprocalTotal) :
    ℍ × JacobiThetaReciprocalCoordinates :=
  (p.modulus, p.coordinates)

instance jacobiThetaReciprocalTotalTopologicalSpace :
    TopologicalSpace JacobiThetaReciprocalTotal :=
  TopologicalSpace.induced
    JacobiThetaReciprocalTotal.toBase inferInstance

theorem continuous_jacobiThetaReciprocalTotal_toBase :
    Continuous JacobiThetaReciprocalTotal.toBase :=
  continuous_induced_dom

/-- The natural domain of the reciprocal theta parametrization. -/
@[ext]
structure JacobiThetaReciprocalDomain where
  modulus : ℍ
  parameter : ℂ
  thetaOne_ne_zero :
    jacobiTheta1 parameter (modulus : ℂ) ≠ 0

/-- Forget the divisor-complement proof and retain the ordinary
coordinates. -/
abbrev JacobiThetaReciprocalDomain.toBase
    (p : JacobiThetaReciprocalDomain) : ℍ × ℂ :=
  (p.modulus, p.parameter)

instance jacobiThetaReciprocalDomainTopologicalSpace :
    TopologicalSpace JacobiThetaReciprocalDomain :=
  TopologicalSpace.induced
    JacobiThetaReciprocalDomain.toBase inferInstance

theorem continuous_jacobiThetaReciprocalDomain_toBase :
    Continuous JacobiThetaReciprocalDomain.toBase :=
  continuous_induced_dom

/-- Joint continuity of one theta-vector component before restricting
to the reciprocal divisor complement. -/
theorem continuous_jacobiThetaVectorComponent_upperHalfPlane
    (j : Fin 4) :
    Continuous
      (fun p : ℂ × ℍ =>
        jacobiThetaVector p.1 (p.2 : ℂ) j) :=
  (continuous_apply j).comp
    continuous_jacobiThetaVector_upperHalfPlane

/-- The normalized theta coordinates on the reciprocal chart. -/
def jacobiThetaReciprocalCoordinates
    (τ : ℍ) (z : ℂ) : JacobiThetaReciprocalCoordinates :=
  fun k =>
    jacobiThetaVector z (τ : ℂ) k.succ /
      jacobiThetaVector z (τ : ℂ) 0

@[simp]
theorem jacobiThetaReciprocalCoordinates_zero
    (τ : ℍ) (z : ℂ) :
    jacobiThetaReciprocalCoordinates τ z 0 =
      jacobiTheta2 z (τ : ℂ) /
        jacobiTheta1 z (τ : ℂ) := by
  rfl

@[simp]
theorem jacobiThetaReciprocalCoordinates_one
    (τ : ℍ) (z : ℂ) :
    jacobiThetaReciprocalCoordinates τ z 1 =
      jacobiTheta3 z (τ : ℂ) /
        jacobiTheta1 z (τ : ℂ) := by
  rfl

@[simp]
theorem jacobiThetaReciprocalCoordinates_two
    (τ : ℍ) (z : ℂ) :
    jacobiThetaReciprocalCoordinates τ z 2 =
      jacobiTheta4 z (τ : ℂ) /
        jacobiTheta1 z (τ : ℂ) := by
  rfl

/-- Normalizing a theta vector in the reciprocal chart preserves the
first residual equation. -/
theorem jacobiThetaReciprocalQ1_coordinates_eq_zero
    (τ : ℍ) (z : ℂ)
    (h1 : jacobiTheta1 z (τ : ℂ) ≠ 0) :
    jacobiThetaReciprocalQ1 τ
        (jacobiThetaReciprocalCoordinates τ z) = 0 := by
  have hQ :=
    canonical_jacobiResidualQ1_jacobiThetaVector z τ
  change
    (canonicalUnaryRoots τ).p2 *
          jacobiTheta4 z (τ : ℂ) ^ 2 -
        (canonicalUnaryRoots τ).p4 *
          jacobiTheta2 z (τ : ℂ) ^ 2 -
      (canonicalUnaryRoots τ).p3 *
          jacobiTheta1 z (τ : ℂ) ^ 2 = 0 at hQ
  unfold jacobiThetaReciprocalQ1
  simp only [jacobiThetaReciprocalCoordinates_two,
    jacobiThetaReciprocalCoordinates_zero]
  field_simp [h1]
  simpa only [mul_assoc, mul_comm, zero_mul] using hQ

/-- Normalizing a theta vector in the reciprocal chart preserves the
second residual equation. -/
theorem jacobiThetaReciprocalQ2_coordinates_eq_zero
    (τ : ℍ) (z : ℂ)
    (h1 : jacobiTheta1 z (τ : ℂ) ≠ 0) :
    jacobiThetaReciprocalQ2 τ
        (jacobiThetaReciprocalCoordinates τ z) = 0 := by
  have hQ :=
    canonical_jacobiResidualQ2_jacobiThetaVector z τ
  change
    (canonicalUnaryRoots τ).p2 *
          jacobiTheta3 z (τ : ℂ) ^ 2 -
        (canonicalUnaryRoots τ).p3 *
          jacobiTheta2 z (τ : ℂ) ^ 2 -
      (canonicalUnaryRoots τ).p4 *
          jacobiTheta1 z (τ : ℂ) ^ 2 = 0 at hQ
  unfold jacobiThetaReciprocalQ2
  simp only [jacobiThetaReciprocalCoordinates_one,
    jacobiThetaReciprocalCoordinates_zero]
  field_simp [h1]
  simpa only [mul_assoc, mul_comm, zero_mul] using hQ

/-- The varying-modulus reciprocal theta parametrization. -/
def jacobiThetaReciprocalTotalMap
    (p : JacobiThetaReciprocalDomain) :
    JacobiThetaReciprocalTotal :=
  ⟨p.modulus,
    jacobiThetaReciprocalCoordinates p.modulus p.parameter,
    jacobiThetaReciprocalQ1_coordinates_eq_zero
      p.modulus p.parameter p.thetaOne_ne_zero,
    jacobiThetaReciprocalQ2_coordinates_eq_zero
      p.modulus p.parameter p.thetaOne_ne_zero⟩

@[simp]
theorem jacobiThetaReciprocalTotalMap_modulus
    (p : JacobiThetaReciprocalDomain) :
    (jacobiThetaReciprocalTotalMap p).modulus = p.modulus :=
  rfl

@[simp]
theorem jacobiThetaReciprocalTotalMap_coordinates
    (p : JacobiThetaReciprocalDomain) :
    (jacobiThetaReciprocalTotalMap p).coordinates =
      jacobiThetaReciprocalCoordinates p.modulus p.parameter :=
  rfl

/-- Joint continuity of each normalized theta coordinate on the
reciprocal domain. -/
theorem continuous_jacobiThetaReciprocalCoordinate
    (k : Fin 3) :
    Continuous
      (fun p : JacobiThetaReciprocalDomain =>
        jacobiThetaVector
              p.parameter (p.modulus : ℂ) k.succ /
          jacobiThetaVector
              p.parameter (p.modulus : ℂ) 0) := by
  have hbase :
      Continuous
        (fun p : JacobiThetaReciprocalDomain =>
          (p.modulus, p.parameter)) :=
    continuous_jacobiThetaReciprocalDomain_toBase
  have hpair :
      Continuous
        (fun p : JacobiThetaReciprocalDomain =>
          (p.parameter, p.modulus)) :=
    (continuous_snd.comp hbase).prodMk
      (continuous_fst.comp hbase)
  have h1 :
      Continuous
        (fun p : JacobiThetaReciprocalDomain =>
          jacobiTheta1 p.parameter (p.modulus : ℂ)) :=
    by
      simpa only [Function.comp_apply] using
        continuous_jacobiTheta1_upperHalfPlane.comp hpair
  have h2 :
      Continuous
        (fun p : JacobiThetaReciprocalDomain =>
          jacobiTheta2 p.parameter (p.modulus : ℂ)) :=
    by
      simpa only [Function.comp_apply] using
        continuous_jacobiTheta2_upperHalfPlane.comp hpair
  have h3 :
      Continuous
        (fun p : JacobiThetaReciprocalDomain =>
          jacobiTheta3 p.parameter (p.modulus : ℂ)) :=
    by
      simpa only [Function.comp_apply] using
        continuous_jacobiTheta3_upperHalfPlane.comp hpair
  have h4 :
      Continuous
        (fun p : JacobiThetaReciprocalDomain =>
          jacobiTheta4 p.parameter (p.modulus : ℂ)) :=
    by
      simpa only [Function.comp_apply] using
        continuous_jacobiTheta4_upperHalfPlane.comp hpair
  fin_cases k
  · simpa [jacobiThetaVector] using
      h2.div h1 (fun p => p.thetaOne_ne_zero)
  · simpa [jacobiThetaVector] using
      h3.div h1 (fun p => p.thetaOne_ne_zero)
  · simpa [jacobiThetaVector] using
      h4.div h1 (fun p => p.thetaOne_ne_zero)

/-- The normalized total theta map is continuous. -/
theorem continuous_jacobiThetaReciprocalTotalMap :
    Continuous jacobiThetaReciprocalTotalMap := by
  rw [continuous_induced_rng]
  change
    Continuous
      (fun p : JacobiThetaReciprocalDomain =>
        (p.modulus,
          fun k : Fin 3 =>
            jacobiThetaVector
                  p.parameter (p.modulus : ℂ) k.succ /
              jacobiThetaVector
                  p.parameter (p.modulus : ℂ) 0))
  exact
    (continuous_fst.comp
        continuous_jacobiThetaReciprocalDomain_toBase).prodMk
      (continuous_pi
        continuous_jacobiThetaReciprocalCoordinate)

/-! ## Exact global coverage of the affine residual family -/

/-- Insert the affine reciprocal coordinates into a four-vector whose
first coordinate is one. -/
def jacobiThetaReciprocalRepresentative
    (x : JacobiThetaReciprocalCoordinates) : Fin 4 → ℂ :=
  ![1, x 0, x 1, x 2]

theorem jacobiThetaReciprocalRepresentative_ne_zero
    (x : JacobiThetaReciprocalCoordinates) :
    jacobiThetaReciprocalRepresentative x ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  norm_num [jacobiThetaReciprocalRepresentative] at h0

@[simp]
theorem jacobiThetaReciprocalRepresentative_succ
    (x : JacobiThetaReciprocalCoordinates) (k : Fin 3) :
    jacobiThetaReciprocalRepresentative x k.succ = x k := by
  fin_cases k <;> rfl

theorem jacobiResidualQ1_reciprocalRepresentative
    (τ : ℍ) (x : JacobiThetaReciprocalCoordinates) :
    jacobiResidualQ1
        (canonicalUnaryRoots τ).p2
        (canonicalUnaryRoots τ).p3
        (canonicalUnaryRoots τ).p4
        (jacobiThetaReciprocalRepresentative x) =
      jacobiThetaReciprocalQ1 τ x := by
  simp [jacobiResidualQ1,
    jacobiThetaReciprocalRepresentative,
    jacobiThetaReciprocalQ1]

theorem jacobiResidualQ2_reciprocalRepresentative
    (τ : ℍ) (x : JacobiThetaReciprocalCoordinates) :
    jacobiResidualQ2
        (canonicalUnaryRoots τ).p2
        (canonicalUnaryRoots τ).p3
        (canonicalUnaryRoots τ).p4
        (jacobiThetaReciprocalRepresentative x) =
      jacobiThetaReciprocalQ2 τ x := by
  simp [jacobiResidualQ2,
    jacobiThetaReciprocalRepresentative,
    jacobiThetaReciprocalQ2]

/-- Every point of the varying-modulus reciprocal residual family is a
normalized theta value.  This is the affine-chart form of global
projective saturation. -/
theorem jacobiThetaReciprocalTotalMap_surjective :
    Function.Surjective jacobiThetaReciprocalTotalMap := by
  rintro ⟨τ, x, hQ1, hQ2⟩
  let X := jacobiThetaReciprocalRepresentative x
  have hX : X ≠ 0 :=
    jacobiThetaReciprocalRepresentative_ne_zero x
  have hXQ1 :
      jacobiResidualQ1
          (canonicalUnaryRoots τ).p2
          (canonicalUnaryRoots τ).p3
          (canonicalUnaryRoots τ).p4 X = 0 := by
    rw [jacobiResidualQ1_reciprocalRepresentative]
    exact hQ1
  have hXQ2 :
      jacobiResidualQ2
          (canonicalUnaryRoots τ).p2
          (canonicalUnaryRoots τ).p3
          (canonicalUnaryRoots τ).p4 X = 0 := by
    rw [jacobiResidualQ2_reciprocalRepresentative]
    exact hQ2
  obtain ⟨z, c, hc, hcz⟩ :=
    exists_smul_jacobiThetaVector_eq_of_residual
      τ X hX hXQ1 hXQ2
  have hfirst :
      c * jacobiTheta1 z (τ : ℂ) = 1 := by
    have h := congrFun hcz 0
    simpa [X, jacobiThetaReciprocalRepresentative,
      jacobiThetaVector] using h
  have htheta1 :
      jacobiTheta1 z (τ : ℂ) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hfirst
    norm_num at hfirst
  let p : JacobiThetaReciprocalDomain :=
    ⟨τ, z, htheta1⟩
  refine ⟨p, JacobiThetaReciprocalTotal.ext rfl ?_⟩
  funext k
  have hk := congrFun hcz k.succ
  have hc_inv :
      jacobiTheta1 z (τ : ℂ) = c⁻¹ := by
    exact eq_inv_of_mul_eq_one_right hfirst
  change
    jacobiThetaVector z (τ : ℂ) k.succ /
        jacobiThetaVector z (τ : ℂ) 0 =
      x k
  have hsucc :
      c * jacobiThetaVector z (τ : ℂ) k.succ =
        x k := by
    simpa [X] using hk
  rw [show jacobiThetaVector z (τ : ℂ) 0 =
    jacobiTheta1 z (τ : ℂ) by rfl, hc_inv]
  field_simp [hc]
  simpa [mul_comm] using hsucc

/-! ## The exact remaining global topological input -/

/-- The global varying-modulus covering statement.

Mathematically, this is the covering by the level-two lattice
`z ↦ z + 2m + 2nτ`, restricted to the divisor complement `θ₁ ≠ 0`.
Its proof requires constructing that varying lattice quotient or an
equivalent proper-continuation argument. -/
def JacobiThetaReciprocalTotalIsCovering : Prop :=
  IsCoveringMap jacobiThetaReciprocalTotalMap

/-- Once the global covering statement is available, every continuous
real trajectory in the affine residual family has a unique coherent
reciprocal theta parameter after fixing one initial preimage. -/
theorem jacobiThetaReciprocalTotal_existsUnique_continuous_lift
    (hcover : JacobiThetaReciprocalTotalIsCovering)
    (y : C(ℝ, JacobiThetaReciprocalTotal))
    (t₀ : ℝ) (p₀ : JacobiThetaReciprocalDomain)
    (hinitial :
      jacobiThetaReciprocalTotalMap p₀ = y t₀) :
    ∃! p : C(ℝ, JacobiThetaReciprocalDomain),
      p t₀ = p₀ ∧
        jacobiThetaReciprocalTotalMap ∘ p = y :=
  hcover.existsUnique_continuousMap_lifts
    y t₀ p₀ hinitial

/-- Pointwise coverage supplies an initial preimage at every chosen
base time, so a covering proof would make every continuous real
trajectory lift without any additional existence assumption. -/
theorem jacobiThetaReciprocalTotal_exists_continuous_lift
    (hcover : JacobiThetaReciprocalTotalIsCovering)
    (y : C(ℝ, JacobiThetaReciprocalTotal))
    (t₀ : ℝ) :
    ∃ p : C(ℝ, JacobiThetaReciprocalDomain),
      jacobiThetaReciprocalTotalMap ∘ p = y := by
  obtain ⟨p₀, hp₀⟩ :=
    jacobiThetaReciprocalTotalMap_surjective (y t₀)
  obtain ⟨p, hp, -⟩ :=
    jacobiThetaReciprocalTotal_existsUnique_continuous_lift
      hcover y t₀ p₀ hp₀
  exact ⟨p, hp.2⟩

end

end HGAS.Modular
