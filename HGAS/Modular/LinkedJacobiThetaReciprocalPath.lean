import HGAS.Modular.JacobiThetaReciprocalCovering
import HGAS.Modular.LinkedJacobiCoherentBlochParameters

/-!
# The linked Jacobi trajectory as a reciprocal theta path

The global coefficient twists constructed in
`LinkedJacobiCoherentCoefficientTwist` put every point of a linked
Jacobi trajectory on the *canonical* pair of theta quadrics.  Since the
reciprocal residual keeps the first coordinate nonzero, these twisted
projective coordinates can be divided by their first entry.  This file
does that division coherently and proves that the result is a continuous
path in `JacobiThetaReciprocalTotal`.

This is the exact bridge between the algebraic trajectory and the
topological lifting problem in `JacobiThetaReciprocalCovering`.  In
particular, if the varying-modulus reciprocal theta map is a covering,
the lifted domain path supplies a continuous elliptic parameter `ξ(t)`.
The final theorem checks, by clearing the two nonzero denominators, that
this parameter satisfies the cross-multiplied projective identity used
by `IsCoherentJacobiThetaProjectiveLift`.

No covering assertion is made in this file.  All results before the last
section are unconditional.
-/

namespace HGAS.Modular

open HGAS
open Complex Real Topology
open UpperHalfPlane hiding I

noncomputable section

/-- The four twisted homogeneous coordinates attached to a coherent
coefficient branch. -/
def coherentTwistedJacobiProjectiveCoordinates
    {T : ℝ → ℍ} {z : ℝ → LinkedJacobiState ℂ}
    (d : CoherentJacobiCoefficientTwist T z)
    (t : ℝ) : Fin 4 → ℂ :=
  jacobiCoefficientTwist d.d₁ d.d₂
    (jacobiResidualProjectiveCoordinates (z t).jacobi)

/-- Divide a nonzero first homogeneous coordinate out of a four-vector.
The resulting three coordinates are indexed by `Fin 3`. -/
def jacobiReciprocalNormalize
    (X : Fin 4 → ℂ) : JacobiThetaReciprocalCoordinates :=
  fun k ↦ X k.succ / X 0

/-- The first normalized quadric is obtained from its homogeneous
counterpart by dividing by the square of the first coordinate. -/
theorem jacobiThetaReciprocalQ1_normalize_eq_zero
    (τ : ℍ) (X : Fin 4 → ℂ)
    (hX0 : X 0 ≠ 0)
    (hQ1 :
      jacobiResidualQ1
          (canonicalUnaryRoots τ).p2
          (canonicalUnaryRoots τ).p3
          (canonicalUnaryRoots τ).p4 X = 0) :
    jacobiThetaReciprocalQ1 τ
        (jacobiReciprocalNormalize X) = 0 := by
  change
    (canonicalUnaryRoots τ).p2 * X 3 ^ 2 -
        (canonicalUnaryRoots τ).p4 * X 1 ^ 2 -
      (canonicalUnaryRoots τ).p3 * X 0 ^ 2 = 0 at hQ1
  unfold jacobiThetaReciprocalQ1
    jacobiReciprocalNormalize
  field_simp [hX0]
  simpa only [mul_assoc, mul_comm, zero_mul] using hQ1

/-- The second normalized quadric is obtained in the same way. -/
theorem jacobiThetaReciprocalQ2_normalize_eq_zero
    (τ : ℍ) (X : Fin 4 → ℂ)
    (hX0 : X 0 ≠ 0)
    (hQ2 :
      jacobiResidualQ2
          (canonicalUnaryRoots τ).p2
          (canonicalUnaryRoots τ).p3
          (canonicalUnaryRoots τ).p4 X = 0) :
    jacobiThetaReciprocalQ2 τ
        (jacobiReciprocalNormalize X) = 0 := by
  change
    (canonicalUnaryRoots τ).p2 * X 2 ^ 2 -
        (canonicalUnaryRoots τ).p3 * X 1 ^ 2 -
      (canonicalUnaryRoots τ).p4 * X 0 ^ 2 = 0 at hQ2
  unfold jacobiThetaReciprocalQ2
    jacobiReciprocalNormalize
  field_simp [hX0]
  simpa only [mul_assoc, mul_comm, zero_mul] using hQ2

/-- A coherent coefficient twist forces the linked coefficient `p₂` to
be nonzero at every generic residual point.

Indeed, the first branch equation has right-hand side `P₂ p₃`.
The canonical coefficient `P₂` never vanishes, and `p₃` is nonzero
because the signed link says `p₃=Y²` while `Y⁴=B`. -/
theorem linkedJacobi_p2_ne_zero_of_coherentTwist
    {T : ℝ → ℍ} {z : ℝ → LinkedJacobiState ℂ}
    (d : CoherentJacobiCoefficientTwist T z)
    (t : ℝ)
    (hB : UnaryModularState.B (z t).unary ≠ 0)
    (hresidual :
      ∀ i : LinkedJacobiResidualIndex,
        linkedJacobiResidual i (z t) = 0) :
    (z t).jacobi.p2 ≠ 0 := by
  have hcanonical :=
    canonicalUnaryRoots_p_product_ne_zero (T t)
  have hP2 :
      (canonicalUnaryRoots (T t)).p2 ≠ 0 := by
    intro hzero
    apply hcanonical
    rw [hzero, zero_mul]
    exact zero_mul _
  have hp3 :
      (z t).jacobi.p3 ≠ 0 :=
    linkedJacobi_p3_ne_zero_of_B_ne_zero
      (z t) hB hresidual
  intro hp2
  have hzero :
      (canonicalUnaryRoots (T t)).p2 *
          (z t).jacobi.p3 = 0 := by
    simpa only [hp2, zero_mul] using
      (d.coefficientThree t).symm
  exact (mul_ne_zero hP2 hp3) hzero

/-- The twisted linked coordinates satisfy both canonical homogeneous
theta quadrics at every point of the generic residual trajectory. -/
theorem coherentTwistedJacobiProjectiveCoordinates_residuals
    {κZ κPhi : ℂ}
    {T : ℝ → ℍ} {z : ℝ → LinkedJacobiState ℂ}
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z)
    {t₀ : ℝ}
    (hB : UnaryModularState.B (z t₀).unary ≠ 0)
    (hresidual :
      ∀ i : LinkedJacobiResidualIndex,
        linkedJacobiResidual i (z t₀) = 0)
    (d : CoherentJacobiCoefficientTwist T z)
    (t : ℝ) :
    jacobiResidualQ1
        (canonicalUnaryRoots (T t)).p2
        (canonicalUnaryRoots (T t)).p3
        (canonicalUnaryRoots (T t)).p4
        (coherentTwistedJacobiProjectiveCoordinates d t) = 0 ∧
      jacobiResidualQ2
        (canonicalUnaryRoots (T t)).p2
        (canonicalUnaryRoots (T t)).p3
        (canonicalUnaryRoots (T t)).p4
        (coherentTwistedJacobiProjectiveCoordinates d t) = 0 := by
  have hB_all := hz.unary.B_ne_zero hB
  have hresidual_all :=
    linkedJacobiResiduals_eq_zero_along_trajectory
      hz hresidual
  let X : Fin 4 → ℂ :=
    jacobiResidualProjectiveCoordinates (z t).jacobi
  have hQ1 :
      jacobiResidualQ1
          (z t).jacobi.p2
          (z t).jacobi.p3
          (z t).jacobi.p4 X = 0 := by
    simpa only [X,
      jacobiResidualQ1_projectiveCoordinates] using
      hresidual_all t .thetaQuadricOne
  have hQ2 :
      jacobiResidualQ2
          (z t).jacobi.p2
          (z t).jacobi.p3
          (z t).jacobi.p4 X = 0 := by
    simpa only [X,
      jacobiResidualQ2_projectiveCoordinates] using
      hresidual_all t .thetaQuadricTwo
  have hp2 :
      (z t).jacobi.p2 ≠ 0 :=
    linkedJacobi_p2_ne_zero_of_coherentTwist
      d t (hB_all t) (hresidual_all t)
  simpa only [coherentTwistedJacobiProjectiveCoordinates,
    X] using
    jacobiResiduals_coefficientTwist
      (canonicalUnaryRoots (T t)).p2
      (canonicalUnaryRoots (T t)).p3
      (canonicalUnaryRoots (T t)).p4
      (z t).jacobi.p2
      (z t).jacobi.p3
      (z t).jacobi.p4
      d.d₁ d.d₂ X hp2 d.d₁_fourth d.d₂_fourth
      (d.coefficientThree t) (d.coefficientFour t)
      hQ1 hQ2

/-- The first twisted homogeneous coordinate never vanishes along a
trajectory on the reciprocal residual chart. -/
theorem coherentTwistedJacobiProjectiveCoordinates_zero_ne_zero
    {κZ κPhi : ℂ}
    {T : ℝ → ℍ} {z : ℝ → LinkedJacobiState ℂ}
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z)
    {t₀ : ℝ}
    (hresidual :
      ∀ i : LinkedJacobiResidualIndex,
        linkedJacobiResidual i (z t₀) = 0)
    (d : CoherentJacobiCoefficientTwist T z)
    (t : ℝ) :
    coherentTwistedJacobiProjectiveCoordinates d t 0 ≠ 0 := by
  have hresidual_all :=
    linkedJacobiResiduals_eq_zero_along_trajectory
      hz hresidual
  simpa only [coherentTwistedJacobiProjectiveCoordinates,
    jacobiCoefficientTwist_zero,
    jacobiResidualProjectiveCoordinates,
    Matrix.cons_val_zero] using
    mul_ne_zero d.d₁_ne_zero
      (linkedJacobi_T1_ne_zero_of_residual
        (z t) (hresidual_all t))

/-- The twisted homogeneous coordinate vector varies continuously. -/
theorem continuous_coherentTwistedJacobiProjectiveCoordinates
    {κZ κPhi : ℂ}
    {T : ℝ → ℍ} {z : ℝ → LinkedJacobiState ℂ}
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z)
    (d : CoherentJacobiCoefficientTwist T z) :
    Continuous
      (coherentTwistedJacobiProjectiveCoordinates d) := by
  apply continuous_pi
  intro k
  fin_cases k
  · simpa only [coherentTwistedJacobiProjectiveCoordinates,
      jacobiCoefficientTwist_zero,
      jacobiResidualProjectiveCoordinates,
      Matrix.cons_val_zero] using
      continuous_const.mul hz.jacobi.continuous_T1
  · simpa only [coherentTwistedJacobiProjectiveCoordinates,
      jacobiCoefficientTwist_one,
      jacobiResidualProjectiveCoordinates,
      Matrix.cons_val_one, Matrix.cons_val_zero] using
      continuous_const.mul hz.jacobi.continuous_T2
  · simpa only [coherentTwistedJacobiProjectiveCoordinates,
      jacobiCoefficientTwist_two,
      jacobiResidualProjectiveCoordinates,
      Matrix.cons_val_one, Matrix.cons_val_zero] using
      continuous_const.mul hz.jacobi.continuous_T3
  · simpa only [coherentTwistedJacobiProjectiveCoordinates,
      jacobiCoefficientTwist_three,
      jacobiResidualProjectiveCoordinates,
      Matrix.cons_val_one, Matrix.cons_val_zero] using
      hz.jacobi.continuous_T4

/-- Normalized twisted coordinates form a continuous three-vector. -/
theorem continuous_coherentTwistedJacobiReciprocalCoordinates
    {κZ κPhi : ℂ}
    {T : ℝ → ℍ} {z : ℝ → LinkedJacobiState ℂ}
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z)
    {t₀ : ℝ}
    (hresidual :
      ∀ i : LinkedJacobiResidualIndex,
        linkedJacobiResidual i (z t₀) = 0)
    (d : CoherentJacobiCoefficientTwist T z) :
    Continuous
      (fun t ↦
        jacobiReciprocalNormalize
          (coherentTwistedJacobiProjectiveCoordinates d t)) := by
  have hX :=
    continuous_coherentTwistedJacobiProjectiveCoordinates
      hz d
  apply continuous_pi
  intro k
  exact
    ((continuous_apply k.succ).comp hX).div
      ((continuous_apply 0).comp hX)
      (coherentTwistedJacobiProjectiveCoordinates_zero_ne_zero
        hz hresidual d)

/-- The normalized twisted linked trajectory, regarded as a point of
the varying-modulus reciprocal residual family. -/
def coherentLinkedJacobiReciprocalPoint
    {κZ κPhi : ℂ}
    {T : ℝ → ℍ} {z : ℝ → LinkedJacobiState ℂ}
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z)
    {t₀ : ℝ}
    (hB : UnaryModularState.B (z t₀).unary ≠ 0)
    (hresidual :
      ∀ i : LinkedJacobiResidualIndex,
        linkedJacobiResidual i (z t₀) = 0)
    (d : CoherentJacobiCoefficientTwist T z)
    (t : ℝ) : JacobiThetaReciprocalTotal :=
  ⟨T t,
    jacobiReciprocalNormalize
      (coherentTwistedJacobiProjectiveCoordinates d t),
    jacobiThetaReciprocalQ1_normalize_eq_zero
      (T t) _
      (coherentTwistedJacobiProjectiveCoordinates_zero_ne_zero
        hz hresidual d t)
      (coherentTwistedJacobiProjectiveCoordinates_residuals
        hz hB hresidual d t).1,
    jacobiThetaReciprocalQ2_normalize_eq_zero
      (T t) _
      (coherentTwistedJacobiProjectiveCoordinates_zero_ne_zero
        hz hresidual d t)
      (coherentTwistedJacobiProjectiveCoordinates_residuals
        hz hB hresidual d t).2⟩

/-- The preceding point construction is continuous whenever the modulus
lift is continuous. -/
theorem continuous_coherentLinkedJacobiReciprocalPoint
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
    Continuous
      (coherentLinkedJacobiReciprocalPoint
        hz hB hresidual d) := by
  rw [continuous_induced_rng]
  exact hT.prodMk
    (continuous_coherentTwistedJacobiReciprocalCoordinates
      hz hresidual d)

/-- Bundled continuous-map form of the reciprocal linked trajectory. -/
def coherentLinkedJacobiReciprocalPath
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
    C(ℝ, JacobiThetaReciprocalTotal) :=
  ⟨coherentLinkedJacobiReciprocalPoint
      hz hB hresidual d,
    continuous_coherentLinkedJacobiReciprocalPoint
      hz hB hresidual hT d⟩

/-! ## Extraction of a coherent projective lift from a covering -/

/-- If the varying-modulus reciprocal theta map is a covering, the
continuous linked residual path has a coherent projective theta lift.

This theorem contains no further selection input.  Surjectivity chooses
one initial preimage; the covering theorem lifts the whole real line;
and equality of normalized coordinates is converted back to the
cross-multiplied projective identity. -/
theorem exists_coherentJacobiThetaProjectiveLift_of_reciprocalCovering
    (hcover : JacobiThetaReciprocalTotalIsCovering)
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
    jacobiThetaReciprocalTotal_exists_continuous_lift
      hcover y t₀
  let ξ : ℝ → ℂ := fun t ↦ (p t).parameter
  have hvalue (t : ℝ) :
      jacobiThetaReciprocalTotalMap (p t) = y t :=
    congrFun hp t
  have hmodulus (t : ℝ) :
      (p t).modulus = T t := by
    exact congrArg JacobiThetaReciprocalTotal.modulus
      (hvalue t)
  have hcoordinates (t : ℝ) :
      jacobiThetaReciprocalCoordinates
          (p t).modulus (p t).parameter =
        jacobiReciprocalNormalize
          (coherentTwistedJacobiProjectiveCoordinates d t) := by
    exact congrArg JacobiThetaReciprocalTotal.coordinates
      (hvalue t)
  refine ⟨ξ, ?_⟩
  constructor
  · exact
      (continuous_snd.comp
        (continuous_jacobiThetaReciprocalDomain_toBase.comp
          p.continuous))
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
        (div_eq_div_iff
          htheta0 hX0).mp (hratio 0)
      calc
        jacobiThetaVector (ξ t) (T t : ℂ) 0 * X 1 =
            X 1 * jacobiThetaVector (ξ t) (T t : ℂ) 0 := by
              ring
        _ =
            jacobiThetaVector (ξ t) (T t : ℂ) 1 * X 0 :=
          hcross.symm
        _ =
            X 0 * jacobiThetaVector (ξ t) (T t : ℂ) 1 := by
              ring
    · have hcross :=
        (div_eq_div_iff
          htheta0 hX0).mp (hratio 1)
      calc
        jacobiThetaVector (ξ t) (T t : ℂ) 0 * X 2 =
            X 2 * jacobiThetaVector (ξ t) (T t : ℂ) 0 := by
              ring
        _ =
            jacobiThetaVector (ξ t) (T t : ℂ) 2 * X 0 :=
          hcross.symm
        _ =
            X 0 * jacobiThetaVector (ξ t) (T t : ℂ) 2 := by
              ring
    · have hcross :=
        (div_eq_div_iff
          htheta0 hX0).mp (hratio 2)
      calc
        jacobiThetaVector (ξ t) (T t : ℂ) 0 * X 3 =
            X 3 * jacobiThetaVector (ξ t) (T t : ℂ) 0 := by
              ring
        _ =
            jacobiThetaVector (ξ t) (T t : ℂ) 3 * X 0 :=
          hcross.symm
        _ =
            X 0 * jacobiThetaVector (ξ t) (T t : ℂ) 3 := by
              ring

/-- Conditional end-to-end completion of the continuous Bloch parameter
selection step from the single reciprocal covering proposition. -/
theorem exists_continuous_twistedBlochSeed_parameters_of_reciprocalCovering
    (hcover : JacobiThetaReciprocalTotalIsCovering)
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
    exists_coherentJacobiThetaProjectiveLift_of_reciprocalCovering
      hcover hz hB hresidual hT d
  obtain ⟨S, L, hS, hξcontinuous, hL, hseed⟩ :=
    exists_continuous_twistedBlochSeed_parameters_of_projectiveLift
      hz hresidual hT d hξ w
  exact
    ⟨S, ξ, L, hS, hξcontinuous, hL, hseed⟩

end

end HGAS.Modular
