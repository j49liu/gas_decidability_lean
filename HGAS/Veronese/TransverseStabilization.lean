import HGAS.Veronese.CubicLiftAlgebra
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic

/-!
# Transverse stabilization near the real Veronese cone

This module formalizes the dynamical algebra behind equations
(16.11)--(16.13).  The earlier Veronese modules construct the cubic lift
and its cubic constraint-gradient penalty.  Here we show why that penalty
has the required dynamical effect.

For a field `G` on Veronese coordinate space, we use the weighted radial
reward

```
a_G(y) = ⟪y, G(y)⟫_Q
```

and the corresponding angular field on `Q(y)=1`,

```
Y_G(y) = G(y) - a_G(y) y.
```

The stabilized field is

```
H = G - K grad_Q W.
```

We prove:

* `a_H = a_G - 4 K W`;
* `Y_H = Y_G - K grad_{S_Q} W`;
* `Y_H W = Y_G W - K ‖grad_{S_Q} W‖_Q²`;
* a Morse--Bott lower bound and first-order tangency bound imply strict
  exponential-type decay throughout the tube;
* on the complement of the tube, the radial reward is at most `-1`.

The existence and effective computation of the Morse--Bott and tangency
constants remain separate geometric obligations.  Once supplied, the
conclusions below are proved, rather than included as fields of an
interface.
-/

namespace HGAS.Veronese

open scoped BigOperators

noncomputable section

variable {n k : ℕ}

/-- Real Veronese coordinate space. -/
abbrev RealVeroneseSpace (n k : ℕ) :=
  MultiIndex n k → ℝ

/-! ## Weighted angular geometry -/

/-- Radial reward for the diagonal metric encoded by `Q`. -/
def weightedRadialReward
    (G : RealVeroneseSpace n k → RealVeroneseSpace n k)
    (y : RealVeroneseSpace n k) : ℝ :=
  weightedInner y (G y)

/-- Angular part of an ambient field on the unit `Q`-sphere. -/
def weightedAngularField
    (G : RealVeroneseSpace n k → RealVeroneseSpace n k)
    (y : RealVeroneseSpace n k) : RealVeroneseSpace n k :=
  G y - weightedRadialReward G y • y

/-- The weighted angular field is tangent to `Q=1`. -/
theorem weightedAngularField_isQTangent
    (G : RealVeroneseSpace n k → RealVeroneseSpace n k)
    (y : RealVeroneseSpace n k) (hQ : Q y = 1) :
    IsQTangent y (weightedAngularField G y) := by
  rw [isQTangent_iff_weightedOrthogonal_real]
  rw [weightedAngularField, weightedInner_sub_right,
    weightedInner_smul_right, weightedInner_self, weightedRadialReward,
    hQ]
  ring

/-! ## The penalty gradient and its exact differential -/

/-- The evaluated ambient `Q`-gradient of the toric penalty. -/
def penaltyAmbientGradient
    (y : RealVeroneseSpace n k) : RealVeroneseSpace n k :=
  ambientQGradient (ordinaryPenaltyGradientReal y)

/-- The tangential penalty gradient on the unit `Q`-sphere. -/
def penaltySphereGradient
    (y : RealVeroneseSpace n k) : RealVeroneseSpace n k :=
  quarticSphereGradient y (toricPenalty y)
    (ordinaryPenaltyGradientReal y)

/-- Squared weighted norm of the tangential penalty gradient. -/
def penaltyDissipation (y : RealVeroneseSpace n k) : ℝ :=
  weightedNormSq (penaltySphereGradient y)

/-- Directional derivative of one toric relation. -/
theorem HasDerivAt.toricRelation_comp
    {γ : ℝ → RealVeroneseSpace n k}
    {v : RealVeroneseSpace n k} {t : ℝ}
    (hγ : HasDerivAt γ v t) (r : ToricRelationIndex n k) :
    HasDerivAt (fun s ↦ toricRelation r (γ s))
      (toricRelationDifferential r (γ t) v) t := by
  have hc (a : MultiIndex n k) :
      HasDerivAt (fun s ↦ γ s a) (v a) t :=
    hasDerivAt_pi.mp hγ a
  simpa only [toricRelation, toricRelationDifferential] using
    ((hc r.alpha).mul (hc r.beta)).sub
      ((hc r.gamma).mul (hc r.delta))

/-- Explicit directional derivative of the sum-of-squares penalty. -/
def toricPenaltyDirectional
    (y h : RealVeroneseSpace n k) : ℝ :=
  ∑ r : ToricRelationIndex n k,
    2 * toricRelation r y *
      toricRelationDifferential r y h

/-- Chain rule for the toric penalty along an arbitrary differentiable
curve. -/
theorem HasDerivAt.toricPenalty_comp
    {γ : ℝ → RealVeroneseSpace n k}
    {v : RealVeroneseSpace n k} {t : ℝ}
    (hγ : HasDerivAt γ v t) :
    HasDerivAt (fun s ↦ toricPenalty (γ s))
      (toricPenaltyDirectional (γ t) v) t := by
  have hr (r : ToricRelationIndex n k) :
      HasDerivAt (fun s ↦ toricRelation r (γ s) ^ 2)
        (2 * toricRelation r (γ t) *
          toricRelationDifferential r (γ t) v) t := by
    convert
      (HGAS.Veronese.HasDerivAt.toricRelation_comp hγ r).pow 2
        using 1
    all_goals ring
  simpa only [toricPenalty, toricPenaltyDirectional] using
    (HasDerivAt.fun_sum
      (u := (Finset.univ : Finset (ToricRelationIndex n k)))
      (fun r _ ↦ hr r))

/-- Evaluated formal directional derivative of one quadratic binomial. -/
private theorem sum_eval₂Hom_pderiv_X_mul
    (b : MultiIndex n k) (y h : RealVeroneseSpace n k) :
    (∑ a : MultiIndex n k,
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) y
          (MvPolynomial.pderiv a (MvPolynomial.X b)) * h a) =
      h b := by
  classical
  simp [MvPolynomial.pderiv_X, Pi.single_apply]

/-- Evaluated formal directional derivative of one quadratic binomial. -/
theorem eval₂Hom_pderiv_toricBinomial_directional
    (r : ToricRelationIndex n k)
    (y h : RealVeroneseSpace n k) :
    (∑ a : MultiIndex n k,
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) y
          (MvPolynomial.pderiv a (toricBinomial r)) * h a) =
      toricRelationDifferential r y h := by
  classical
  simp only [toricBinomial, map_sub,
    MvPolynomial.pderiv_mul, map_sub, map_add, map_mul,
    MvPolynomial.eval₂Hom_X', sub_mul,
    Finset.sum_sub_distrib]
  rw [show
      (∑ a : MultiIndex n k,
          ((MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) y)
                ((MvPolynomial.pderiv a) (MvPolynomial.X r.alpha)) *
              y r.beta +
            y r.alpha *
              (MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) y)
                ((MvPolynomial.pderiv a) (MvPolynomial.X r.beta))) *
            h a) =
        (∑ a : MultiIndex n k,
            (MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) y)
                ((MvPolynomial.pderiv a) (MvPolynomial.X r.alpha)) *
              h a) * y r.beta +
          y r.alpha *
            (∑ a : MultiIndex n k,
              (MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) y)
                  ((MvPolynomial.pderiv a) (MvPolynomial.X r.beta)) *
                h a) by
      simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum,
        Finset.sum_mul]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro a _ <;> ring]
  rw [show
      (∑ a : MultiIndex n k,
          ((MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) y)
                ((MvPolynomial.pderiv a) (MvPolynomial.X r.gamma)) *
              y r.delta +
            y r.gamma *
              (MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) y)
                ((MvPolynomial.pderiv a) (MvPolynomial.X r.delta))) *
            h a) =
        (∑ a : MultiIndex n k,
            (MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) y)
                ((MvPolynomial.pderiv a) (MvPolynomial.X r.gamma)) *
              h a) * y r.delta +
          y r.gamma *
            (∑ a : MultiIndex n k,
              (MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) y)
                  ((MvPolynomial.pderiv a) (MvPolynomial.X r.delta)) *
                h a) by
      simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum,
        Finset.sum_mul]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro a _ <;> ring]
  rw [sum_eval₂Hom_pderiv_X_mul, sum_eval₂Hom_pderiv_X_mul,
    sum_eval₂Hom_pderiv_X_mul, sum_eval₂Hom_pderiv_X_mul]
  rfl

/-- The explicit sum-of-squares differential agrees with pairing against
the evaluated ambient `Q`-gradient. -/
theorem toricPenaltyDirectional_eq_weightedInner
    (y h : RealVeroneseSpace n k) :
    toricPenaltyDirectional y h =
      weightedInner (penaltyAmbientGradient y) h := by
  rw [penaltyAmbientGradient, weightedInner_ambientQGradient]
  simp only [coordinateDot, ordinaryPenaltyGradientReal,
    ordinaryPenaltyGradientPolynomial,
    eval₂Hom_pderiv_toricPenaltyPolynomial,
    toricPenaltyDirectional]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [eval₂Hom_toricBinomial]
  rw [← eval₂Hom_pderiv_toricBinomial_directional r y h]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Analytic chain rule written directly with the ambient weighted
gradient. -/
theorem HasDerivAt.toricPenalty_comp_eq_weightedInner
    {γ : ℝ → RealVeroneseSpace n k}
    {v : RealVeroneseSpace n k} {t : ℝ}
    (hγ : HasDerivAt γ v t) :
    HasDerivAt (fun s ↦ toricPenalty (γ s))
      (weightedInner (penaltyAmbientGradient (γ t)) v) t := by
  simpa only [toricPenaltyDirectional_eq_weightedInner] using
    HGAS.Veronese.HasDerivAt.toricPenalty_comp hγ

/-! ## Euler and spherical-gradient identities -/

/-- Generic-algebra evaluation of the rational penalty polynomial. -/
theorem eval₂Hom_toricPenaltyPolynomial
    {S : Type*} [CommRing S] [Algebra ℚ S]
    (y : MultiIndex n k → S) :
    MvPolynomial.eval₂Hom (algebraMap ℚ S) y
        (toricPenaltyPolynomial n k) =
      toricPenalty y := by
  simp only [toricPenaltyPolynomial, toricPenalty, map_sum, map_pow]
  apply Finset.sum_congr rfl
  intro r _
  rw [eval₂Hom_toricBinomial]

/-- Euler's identity for the quartic toric penalty. -/
theorem coordinateDot_ordinaryPenaltyGradientReal
    (y : RealVeroneseSpace n k) :
    coordinateDot y (ordinaryPenaltyGradientReal y) =
      4 * toricPenalty y := by
  have hEuler :=
    (toricPenaltyPolynomial_isHomogeneous n k).sum_X_mul_pderiv
  have heval :=
    congrArg
      (MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) y)
      hEuler
  simp only [map_sum, map_mul, MvPolynomial.eval₂Hom_X',
    eval₂Hom_toricPenaltyPolynomial, nsmul_eq_mul] at heval
  norm_num at heval ⊢
  exact heval

/-- The spherical penalty gradient is tangent to `Q=1`. -/
theorem penaltySphereGradient_isQTangent
    (y : RealVeroneseSpace n k) (hQ : Q y = 1) :
    IsQTangent y (penaltySphereGradient y) := by
  exact quarticSphereGradient_isQTangent y (toricPenalty y)
    (ordinaryPenaltyGradientReal y) hQ
      (coordinateDot_ordinaryPenaltyGradientReal y)

/-- Equation (15.10) for the concrete toric penalty. -/
theorem penaltyDissipation_eq
    (y : RealVeroneseSpace n k) (hQ : Q y = 1) :
    penaltyDissipation y =
      weightedNormSq (penaltyAmbientGradient y) -
        16 * toricPenalty y ^ 2 := by
  exact weightedNormSq_quarticSphereGradient y (toricPenalty y)
    (ordinaryPenaltyGradientReal y) hQ
      (coordinateDot_ordinaryPenaltyGradientReal y)

/-- Pairing the ambient gradient with its tangential projection gives the
squared tangential norm. -/
theorem weightedInner_penaltyAmbientGradient_penaltySphereGradient
    (y : RealVeroneseSpace n k) (hQ : Q y = 1) :
    weightedInner (penaltyAmbientGradient y)
        (penaltySphereGradient y) =
      penaltyDissipation y := by
  have hdecomp :
      penaltyAmbientGradient y =
        penaltySphereGradient y +
          (4 * toricPenalty y) • y := by
    exact ambientQGradient_decomposition y (toricPenalty y)
      (ordinaryPenaltyGradientReal y)
  have htangent :
      weightedInner y (penaltySphereGradient y) = 0 := by
    rw [← isQTangent_iff_weightedOrthogonal_real]
    exact penaltySphereGradient_isQTangent y hQ
  rw [weightedInner_comm, hdecomp, weightedInner_add_right,
    weightedInner_smul_right,
    weightedInner_comm (penaltySphereGradient y) y,
    htangent, mul_zero, add_zero]
  rfl

/-! ## Exact effect of transverse stabilization -/

/-- Subtract the ambient weighted penalty gradient with gain `K`.

This is the semantic (evaluated) counterpart of
`stabilizedCubicField`.  It is deliberately defined for an arbitrary
ambient field `G`, so the dynamical lemmas below can be reused
independently of the polynomial lift. -/
def transverseStabilizedField
    (G : RealVeroneseSpace n k → RealVeroneseSpace n k)
    (K : ℝ) (y : RealVeroneseSpace n k) :
    RealVeroneseSpace n k :=
  G y - K • penaltyAmbientGradient y

/-- Directional derivative of the toric penalty along a vector field,
written as its weighted-gradient pairing. -/
def penaltyLieDerivative
    (V : RealVeroneseSpace n k → RealVeroneseSpace n k)
    (y : RealVeroneseSpace n k) : ℝ :=
  weightedInner (penaltyAmbientGradient y) (V y)

/-- Euler's identity in weighted-gradient form. -/
theorem weightedInner_y_penaltyAmbientGradient
    (y : RealVeroneseSpace n k) :
    weightedInner y (penaltyAmbientGradient y) =
      4 * toricPenalty y := by
  rw [penaltyAmbientGradient, weightedInner_left_ambientQGradient,
    coordinateDot_ordinaryPenaltyGradientReal]

/-- Equation (16.11): stabilization subtracts exactly `4 K W` from
the radial reward. -/
theorem weightedRadialReward_transverseStabilizedField
    (G : RealVeroneseSpace n k → RealVeroneseSpace n k)
    (K : ℝ) (y : RealVeroneseSpace n k) :
    weightedRadialReward (transverseStabilizedField G K) y =
      weightedRadialReward G y - 4 * K * toricPenalty y := by
  rw [weightedRadialReward, transverseStabilizedField,
    weightedInner_sub_right, weightedInner_smul_right,
    weightedRadialReward, weightedInner_y_penaltyAmbientGradient]
  ring

/-- Equation (16.12): on the unit `Q`-sphere, stabilization subtracts
the spherical penalty gradient from the angular field.

The equality itself is algebraic and does not need `Q(y)=1`; the unit
sphere hypothesis enters when interpreting both sides as tangent
vectors. -/
theorem weightedAngularField_transverseStabilizedField
    (G : RealVeroneseSpace n k → RealVeroneseSpace n k)
    (K : ℝ) (y : RealVeroneseSpace n k) :
    weightedAngularField (transverseStabilizedField G K) y =
      weightedAngularField G y - K • penaltySphereGradient y := by
  funext a
  simp only [weightedAngularField, transverseStabilizedField,
    weightedRadialReward_transverseStabilizedField,
    penaltySphereGradient, quarticSphereGradient,
    penaltyAmbientGradient, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

/-- Equation (16.13): the penalty derivative along the stabilized
angular field is the original angular derivative minus `K` times the
squared tangential gradient. -/
theorem penaltyLieDerivative_stabilizedAngular
    (G : RealVeroneseSpace n k → RealVeroneseSpace n k)
    (K : ℝ) (y : RealVeroneseSpace n k)
    (hQ : Q y = 1) :
    penaltyLieDerivative
        (weightedAngularField (transverseStabilizedField G K)) y =
      penaltyLieDerivative (weightedAngularField G) y -
        K * penaltyDissipation y := by
  rw [penaltyLieDerivative, weightedAngularField_transverseStabilizedField,
    weightedInner_sub_right, weightedInner_smul_right,
    weightedInner_penaltyAmbientGradient_penaltySphereGradient y hQ]
  rfl

/-- Along a differentiable trajectory of the stabilized angular field,
the derivative of `W` is exactly the right-hand side of (16.13). -/
theorem HasDerivAt.toricPenalty_along_stabilizedAngular
    {G : RealVeroneseSpace n k → RealVeroneseSpace n k}
    {K t : ℝ} {γ : ℝ → RealVeroneseSpace n k}
    (hγ : HasDerivAt γ
      (weightedAngularField (transverseStabilizedField G K) (γ t)) t)
    (hQ : Q (γ t) = 1) :
    HasDerivAt (fun s ↦ toricPenalty (γ s))
      (penaltyLieDerivative (weightedAngularField G) (γ t) -
        K * penaltyDissipation (γ t)) t := by
  have hchain :=
    HGAS.Veronese.HasDerivAt.toricPenalty_comp_eq_weightedInner hγ
  change HasDerivAt (fun s ↦ toricPenalty (γ s))
    (penaltyLieDerivative
      (weightedAngularField (transverseStabilizedField G K)) (γ t)) t
    at hchain
  rw [penaltyLieDerivative_stabilizedAngular G K (γ t) hQ] at hchain
  exact hchain

/-- Evaluation commutes with stabilization: the rational polynomial
construction in `CubicLiftAlgebra` is exactly the semantic field above. -/
theorem eval_stabilizedCubicField_real_eq_transverse
    (F : HGAS.PolynomialField n) (K : ℚ)
    (y : RealVeroneseSpace n k) :
    evalCoordinateField (stabilizedCubicField (k := k) F K) y =
      transverseStabilizedField
        (fun z ↦ evalCoordinateField (cubicLiftField (k := k) F) z)
        (K : ℝ) y := by
  rw [transverseStabilizedField]
  unfold penaltyAmbientGradient
  rw [← eval_penaltyQGradientField_real y]
  funext a
  simp only [evalCoordinateField_apply, stabilizedCubicField,
    map_sub, map_mul, MvPolynomial.eval₂Hom_C, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  norm_num

/-! ## Quantitative tube mechanism

The next statements are the rigorous pointwise heart of the
Morse--Bott stabilization argument.  The two geometric estimates are
ordinary hypotheses:

* `c W(y) ≤ D(y)` is the transverse Morse--Bott inequality;
* `|Y_G W(y)| ≤ C W(y)` is first-order tangency of the lifted field.

No existence claim for `c`, `C`, or the tube radius is made here. -/

/-- A Morse--Bott lower bound and a tangency upper bound give the
claimed quantitative decay for the stabilized angular field. -/
theorem penaltyLieDerivative_stabilizedAngular_le
    (G : RealVeroneseSpace n k → RealVeroneseSpace n k)
    (K c C : ℝ) (y : RealVeroneseSpace n k)
    (hQ : Q y = 1) (hK : 0 ≤ K)
    (hMorseBott :
      c * toricPenalty y ≤ penaltyDissipation y)
    (hTangency :
      |penaltyLieDerivative (weightedAngularField G) y| ≤
        C * toricPenalty y) :
    penaltyLieDerivative
        (weightedAngularField (transverseStabilizedField G K)) y ≤
      -(K * c - C) * toricPenalty y := by
  rw [penaltyLieDerivative_stabilizedAngular G K y hQ]
  have hupper :
      penaltyLieDerivative (weightedAngularField G) y ≤
        C * toricPenalty y :=
    (le_abs_self _).trans hTangency
  have hscaled :
      K * (c * toricPenalty y) ≤
        K * penaltyDissipation y :=
    mul_le_mul_of_nonneg_left hMorseBott hK
  calc
    penaltyLieDerivative (weightedAngularField G) y -
          K * penaltyDissipation y ≤
        C * toricPenalty y -
          K * (c * toricPenalty y) :=
      sub_le_sub hupper hscaled
    _ = -(K * c - C) * toricPenalty y := by ring

/-- If the gain strictly dominates the tangency constant, the penalty
strictly decreases at every nonzero-penalty point in the tube. -/
theorem penaltyLieDerivative_stabilizedAngular_lt_zero
    (G : RealVeroneseSpace n k → RealVeroneseSpace n k)
    (K c C : ℝ) (y : RealVeroneseSpace n k)
    (hQ : Q y = 1) (hK : 0 ≤ K)
    (hGain : C < K * c)
    (hW : 0 < toricPenalty y)
    (hMorseBott :
      c * toricPenalty y ≤ penaltyDissipation y)
    (hTangency :
      |penaltyLieDerivative (weightedAngularField G) y| ≤
        C * toricPenalty y) :
    penaltyLieDerivative
        (weightedAngularField (transverseStabilizedField G K)) y < 0 := by
  refine lt_of_le_of_lt
    (penaltyLieDerivative_stabilizedAngular_le
      G K c C y hQ hK hMorseBott hTangency) ?_
  have hgap : 0 < K * c - C := sub_pos.mpr hGain
  have hproduct : 0 < (K * c - C) * toricPenalty y :=
    mul_pos hgap hW
  linarith

/-- Uniform tube estimates imply pointwise decay everywhere in that
tube.  The estimates remain visible as explicit quantified hypotheses. -/
theorem penaltyLieDerivative_stabilizedAngular_le_in_tube
    (G : RealVeroneseSpace n k → RealVeroneseSpace n k)
    (K c C η : ℝ) (y : RealVeroneseSpace n k)
    (hK : 0 ≤ K)
    (hMorseBott :
      ∀ z : RealVeroneseSpace n k,
        Q z = 1 → toricPenalty z ≤ η →
          c * toricPenalty z ≤ penaltyDissipation z)
    (hTangency :
      ∀ z : RealVeroneseSpace n k,
        Q z = 1 → toricPenalty z ≤ η →
          |penaltyLieDerivative (weightedAngularField G) z| ≤
            C * toricPenalty z)
    (hQ : Q y = 1) (hTube : toricPenalty y ≤ η) :
    penaltyLieDerivative
        (weightedAngularField (transverseStabilizedField G K)) y ≤
      -(K * c - C) * toricPenalty y :=
  penaltyLieDerivative_stabilizedAngular_le
    G K c C y hQ hK
      (hMorseBott y hQ hTube) (hTangency y hQ hTube)

/-- At a positive-radius tube boundary the stabilized angular field
points strictly inward.  This is the local barrier statement used in
the forward-invariance argument. -/
theorem penaltyLieDerivative_stabilizedAngular_boundary_lt_zero
    (G : RealVeroneseSpace n k → RealVeroneseSpace n k)
    (K c C η : ℝ) (y : RealVeroneseSpace n k)
    (hK : 0 ≤ K) (hGain : C < K * c) (hη : 0 < η)
    (hQ : Q y = 1) (hBoundary : toricPenalty y = η)
    (hMorseBott :
      c * toricPenalty y ≤ penaltyDissipation y)
    (hTangency :
      |penaltyLieDerivative (weightedAngularField G) y| ≤
        C * toricPenalty y) :
    penaltyLieDerivative
        (weightedAngularField (transverseStabilizedField G K)) y < 0 := by
  apply penaltyLieDerivative_stabilizedAngular_lt_zero
    G K c C y hQ hK hGain
  · rwa [hBoundary]
  · exact hMorseBott
  · exact hTangency

/-- Outside the tube, the exact radial identity makes the stabilized
reward uniformly negative once `4 K η ≥ A + 1`. -/
theorem weightedRadialReward_transverse_le_neg_one
    (G : RealVeroneseSpace n k → RealVeroneseSpace n k)
    (K A η : ℝ) (y : RealVeroneseSpace n k)
    (hK : 0 ≤ K) (hOutside : η ≤ toricPenalty y)
    (hReward : |weightedRadialReward G y| ≤ A)
    (hGain : A + 1 ≤ 4 * K * η) :
    weightedRadialReward (transverseStabilizedField G K) y ≤ -1 := by
  rw [weightedRadialReward_transverseStabilizedField]
  have hrewardUpper :
      weightedRadialReward G y ≤ A :=
    (le_abs_self _).trans hReward
  have hfourK : 0 ≤ 4 * K := mul_nonneg (by norm_num) hK
  have hpenalty :
      4 * K * η ≤ 4 * K * toricPenalty y := by
    exact mul_le_mul_of_nonneg_left hOutside hfourK
  linarith

end

end HGAS.Veronese
