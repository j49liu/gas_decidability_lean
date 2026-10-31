import Stability.Selection.UnaryClockConjugation
import HGAS.Modular.LinkedConstantTimeRescaling
import HGAS.Modular.LinkedJacobiPolynomialCode

/-!
# Conjugation of the linked unary--Jacobi trajectory

The two Jacobi derivations have rational coefficients, including the
reciprocal-chart equation. Coordinatewise complex conjugation therefore
conjugates both clocks and all ten validity residuals. It preserves
forward recurrence in the literal fourteen-coordinate state.

For physical clocks `κZ = (Ω + N) / 2` and `κPhi = i * Ω`, conjugation
leaves the real elliptic clock `κZ` unchanged and negates the imaginary
modular clock. This is not the physical parameter change `(Ω,N) ↦ (-Ω,-N)`.
The arbitrary-clock linked trajectory is sufficient for the modular
coefficient/root selector; the original Jacobi trajectory must be retained
for subsequent physical-time selection.
-/

namespace Stability.Selection

open HGAS HGAS.Modular Filter Topology

noncomputable section

/-- Complex conjugation of all ten reciprocal Jacobi-chart coordinates. -/
def conjugateJacobi (z : JacobiState ℂ) : JacobiState ℂ where
  p2 := star z.p2
  p3 := star z.p3
  p4 := star z.p4
  H := star z.H
  T1 := star z.T1
  T2 := star z.T2
  T3 := star z.T3
  T4 := star z.T4
  Delta := star z.Delta
  U := star z.U

/-- Conjugation of both linked coefficient blocks. -/
def conjugateLinked (z : LinkedJacobiState ℂ) : LinkedJacobiState ℂ where
  unary := conjugateUnary z.unary
  jacobi := conjugateJacobi z.jacobi

@[simp]
theorem conjugateJacobi_involutive (z : JacobiState ℂ) :
    conjugateJacobi (conjugateJacobi z) = z := by
  ext <;> simp [conjugateJacobi]

@[simp]
theorem conjugateLinked_involutive (z : LinkedJacobiState ℂ) :
    conjugateLinked (conjugateLinked z) = z := by
  cases z
  simp [conjugateLinked]

/-- The elliptic derivation commutes with conjugation. -/
theorem conjugateJacobi_ellipticVectorField (z : JacobiState ℂ) :
    conjugateJacobi (JacobiState.ellipticVectorField z) =
      JacobiState.ellipticVectorField (conjugateJacobi z) := by
  ext <;> simp [conjugateJacobi, JacobiState.ellipticVectorField, JacobiState.K]

/-- The modular derivation commutes with conjugation. -/
theorem conjugateJacobi_modularVectorField (z : JacobiState ℂ) :
    conjugateJacobi (JacobiState.modularVectorField z) =
      JacobiState.modularVectorField (conjugateJacobi z) := by
  ext <;> simp [conjugateJacobi, JacobiState.modularVectorField, JacobiState.K]

/-- The combined vector field conjugates both clock coefficients. -/
theorem conjugateJacobi_combinedVectorField (κZ κPhi : ℂ) (z : JacobiState ℂ) :
    conjugateJacobi (JacobiState.combinedVectorField κZ κPhi z) =
      JacobiState.combinedVectorField (star κZ) (star κPhi) (conjugateJacobi z) := by
  have hZ := conjugateJacobi_ellipticVectorField z
  have hPhi := conjugateJacobi_modularVectorField z
  rw [JacobiState.combinedVectorField, JacobiState.combinedVectorField,
    ← hZ, ← hPhi]
  ext <;> simp [conjugateJacobi]

/-- Conjugating a Jacobi trajectory does not reverse time. -/
theorem conjugateJacobi_isScaledTrajectory
    {κZ κPhi : ℂ} {z : ℝ → JacobiState ℂ}
    (hz : IsScaledJacobiTrajectory κZ κPhi z) :
    IsScaledJacobiTrajectory (star κZ) (star κPhi)
      (fun t ↦ conjugateJacobi (z t)) := by
  constructor
  · intro t
    rw [← conjugateJacobi_combinedVectorField]
    exact (hz.p2 t).star
  · intro t
    rw [← conjugateJacobi_combinedVectorField]
    exact (hz.p3 t).star
  · intro t
    rw [← conjugateJacobi_combinedVectorField]
    exact (hz.p4 t).star
  · intro t
    rw [← conjugateJacobi_combinedVectorField]
    exact (hz.H t).star
  · intro t
    rw [← conjugateJacobi_combinedVectorField]
    exact (hz.T1 t).star
  · intro t
    rw [← conjugateJacobi_combinedVectorField]
    exact (hz.T2 t).star
  · intro t
    rw [← conjugateJacobi_combinedVectorField]
    exact (hz.T3 t).star
  · intro t
    rw [← conjugateJacobi_combinedVectorField]
    exact (hz.T4 t).star
  · intro t
    rw [← conjugateJacobi_combinedVectorField]
    exact (hz.Delta t).star
  · intro t
    rw [← conjugateJacobi_combinedVectorField]
    exact (hz.U t).star

/-- The full linked trajectory transforms with the conjugate clocks. -/
theorem conjugateLinked_isScaledTrajectory
    {κZ κPhi : ℂ} {z : ℝ → LinkedJacobiState ℂ}
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z) :
    IsScaledLinkedJacobiTrajectory (star κZ) (star κPhi)
      (fun t ↦ conjugateLinked (z t)) where
  unary := conjugateUnary_isScaledTrajectory hz.unary
  jacobi := conjugateJacobi_isScaledTrajectory hz.jacobi

/-- All coefficient links, root signs, theta quadrics, and the reciprocal
constraint are transported by one exact residual identity. -/
theorem linkedJacobiResidual_conjugateLinked
    (r : LinkedJacobiResidualIndex) (z : LinkedJacobiState ℂ) :
    linkedJacobiResidual r (conjugateLinked z) = star (linkedJacobiResidual r z) := by
  cases r <;> simp [linkedJacobiResidual, conjugateLinked, conjugateUnary,
    conjugateJacobi, JacobiState.residualR0, JacobiState.residualR1,
    JacobiState.residualR2, JacobiState.residualRU,
    LinkedJacobiState.jacobiResidual, LinkedJacobiState.link2,
    LinkedJacobiState.link3, LinkedJacobiState.link4,
    LinkedJacobiState.linkH, LinkedJacobiState.signedLink3]

/-- Validity is equivalent before and after conjugation. -/
theorem linkedJacobiResidual_conjugateLinked_eq_zero_iff
    (r : LinkedJacobiResidualIndex) (z : LinkedJacobiState ℂ) :
    linkedJacobiResidual r (conjugateLinked z) = 0 ↔ linkedJacobiResidual r z = 0 := by
  rw [linkedJacobiResidual_conjugateLinked]
  exact star_eq_zero

/-- Conjugation agrees with coordinatewise conjugation of the finite state. -/
theorem linkedPoint_conjugateLinked (z : LinkedJacobiState ℂ) :
    LinkedJacobiPolynomialCode.point (conjugateLinked z) =
      fun i ↦ star (LinkedJacobiPolynomialCode.point z i) := by
  funext i
  fin_cases i <;> rfl

/-- The finite-state norm is unchanged, so forward norm-power growth
conditions remain unchanged before positive rescaling. -/
theorem norm_linkedPoint_conjugateLinked (z : LinkedJacobiState ℂ) :
    ‖LinkedJacobiPolynomialCode.point (conjugateLinked z)‖ =
      ‖LinkedJacobiPolynomialCode.point z‖ := by
  rw [linkedPoint_conjugateLinked]
  exact norm_star _

/-- Forward recurrence of the full polynomial state is preserved by the
same time sequence; no backward recurrence is required. -/
theorem conjugateLinked_forwardRecurrentAt
    {z : ℝ → LinkedJacobiState ℂ} {t₀ : ℝ}
    (hrec : ForwardRecurrentAt (fun t ↦ LinkedJacobiPolynomialCode.point (z t)) t₀) :
    ForwardRecurrentAt
      (fun t ↦ LinkedJacobiPolynomialCode.point (conjugateLinked (z t))) t₀ := by
  obtain ⟨τ, hτ, hreturn⟩ := hrec
  refine ⟨τ, hτ, ?_⟩
  simp only [linkedPoint_conjugateLinked]
  exact hreturn.star

end

end Stability.Selection
