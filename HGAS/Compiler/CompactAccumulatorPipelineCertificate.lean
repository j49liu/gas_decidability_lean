import HGAS.Compiler.CompactAccumulatorPipelineDegrees
import HGAS.Compiler.CompactAccumulatorPipelineReward
import HGAS.Compiler.CompactSignSourceWrapper
import Mathlib.Tactic

/-!
# Turning the concrete pipeline into a compact-sign source certificate

The compact-sign wrapper expects a polynomial source field of one fixed odd
degree, a reward of one lower degree, product-sphere tangency, and a source
flow solving the polynomial ODE.  All of those items are now generated from
the concrete mixed-central/accumulator compiler.

Only the genuinely dynamical statement remains an input:

```
 maximalInvariantAverage sourceFlow sourceReward < 0
      ↔ I.Solvable.
```

Thus this module is an effectivity firewall.  Degree padding, tangency on
all boundary strata, and construction of the compact source flow cannot be
hidden inside the modular/Jacobi classification theorem.
-/

namespace HGAS

noncomputable section

namespace CompactAccumulatorPipelineCode

variable {n k l m eqs vars : ℕ}

/-- A uniform odd wrapper degree large enough for both the complete source
field and its reward. -/
def wrapperDegree (E k M : ℕ) : ℕ :=
  2 * max (E + k * M + 3) (max 1 (2 * k) + 1) + 1

theorem wrapperDegree_ge_three (E k M : ℕ) :
    3 ≤ wrapperDegree E k M := by
  unfold wrapperDegree
  omega

theorem wrapperDegree_odd (E k M : ℕ) :
    wrapperDegree E k M % 2 = 1 := by
  unfold wrapperDegree
  omega

theorem fieldCode_termsDegreeLE_wrapperDegree
    (layout : Fin n → Fin k ⊕ Fin l)
    (E M : ℕ) (κ : RationalCode)
    (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE E (P j))
    (h : Fin m → PolynomialCode n)
    (hh : ∀ i, PolynomialCode.TermsDegreeLE E (h i)) :
    ∀ q,
      PolynomialCode.TermsDegreeLE
        (wrapperDegree E k M)
        (fieldCode layout M κ P h q) := by
  intro q
  exact
    (fieldCode_termsDegreeLE layout M κ P hP h hh q).promote
      (by
        unfold wrapperDegree
        omega)

theorem rewardCode_termsDegreeLE_wrapperDegree_sub_one
    (E M : ℕ) (ε : RationalCode) :
    PolynomialCode.TermsDegreeLE
        (wrapperDegree E k M - 1)
        (rewardCode (n := n) (k := k) (m := m) ε) := by
  exact
    (rewardCode_termsDegreeLE
      (n := n) (k := k) (m := m) ε).promote
      (by
        unfold wrapperDegree
        omega)

/-- The canonical compact source flow obtained from the positive sheet of
the exact homogeneous wrapper. -/
def sourceFlow
    (layout : Fin n → Fin k ⊕ Fin l)
    (E M : ℕ) (κ : RationalCode)
    (P : PolynomialFieldCode n)
    (h : Fin m → PolynomialCode n)
    (ε : RationalCode) :
    Flow ℝ
      (UnitSpherePolynomialWrapper.SourceProductSphere
        (sourceBlock (m := m) layout)) :=
  UnitSpherePolynomialWrapper.positiveSourceFlow
    (sourceBlock (m := m) layout)
    (wrapperDegree E k M)
    (fieldCode layout M κ P h)
    (rewardCode (n := n) (k := k) (m := m) ε)

/-- Every trajectory of the canonical compact source flow solves the
literal pipeline polynomial ODE. -/
theorem sourceFlow_integralCurve
    (layout : Fin n → Fin k ⊕ Fin l)
    (E M : ℕ) (κ : RationalCode)
    (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE E (P j))
    (h : Fin m → PolynomialCode n)
    (hh : ∀ i, PolynomialCode.TermsDegreeLE E (h i))
    (ε : RationalCode)
    (hcompact :
      ∀ v :
          UnitSpherePolynomialWrapper.SourceProductSphere
            (sourceBlock (m := m) layout),
        let y : Fin (n + k) → ℝ :=
          fun q ↦
            v.1 (AccumulatorPolynomialCode.baseIndex
              (m := m) q)
        let x : Fin n → ℝ :=
          fun j ↦ y (MixedCentralPolynomialCode.xIndex
            (k := k) j)
        ∀ c, MixedCentralPolynomialCode.compactBlockDot layout x
          (MixedCentralPolynomialCode.clearedSourceVelocity
            layout M P y) c = 0)
    (v :
      UnitSpherePolynomialWrapper.SourceProductSphere
        (sourceBlock (m := m) layout)) :
    IsIntegralCurve
      (fun t ↦
        (sourceFlow layout E M κ P h ε t v).1)
      (fun _ x ↦
        PolynomialFieldCode.realize
          (fieldCode layout M κ P h) x) := by
  apply
    UnitSpherePolynomialWrapper.positiveSourceFlow_isIntegralCurve_sourceField
        (sourceBlock (m := m) layout)
        (wrapperDegree E k M)
        (wrapperDegree_odd E k M)
        (fieldCode layout M κ P h)
        (fieldCode_termsDegreeLE_wrapperDegree
          layout E M κ P hP h hh)
        (rewardCode (n := n) (k := k) (m := m) ε)
  intro y
  exact
    fieldCode_sourceTangentAt
      layout M κ P h y.1 y.2 (hcompact y)

/-- Construct the exact source certificate from concrete finite pipeline
data and the one remaining compact-sign classification theorem. -/
def compactSignSourceCertificate
    (I : DQLSystem eqs vars)
    (layout : Fin n → Fin k ⊕ Fin l)
    (E M : ℕ) (κ : RationalCode)
    (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE E (P j))
    (h : Fin m → PolynomialCode n)
    (hh : ∀ i, PolynomialCode.TermsDegreeLE E (h i))
    (ε : RationalCode)
    [Nonempty
      (UnitSpherePolynomialWrapper.SourceProductSphere
        (sourceBlock (m := m) layout))]
    (hcompact :
      ∀ v :
          UnitSpherePolynomialWrapper.SourceProductSphere
            (sourceBlock (m := m) layout),
        let y : Fin (n + k) → ℝ :=
          fun q ↦
            v.1 (AccumulatorPolynomialCode.baseIndex
              (m := m) q)
        let x : Fin n → ℝ :=
          fun j ↦ y (MixedCentralPolynomialCode.xIndex
            (k := k) j)
        ∀ c, MixedCentralPolynomialCode.compactBlockDot layout x
          (MixedCentralPolynomialCode.clearedSourceVelocity
            layout M P y) c = 0)
    (hsign :
      Dynamics.maximalInvariantAverage
          (sourceFlow layout E M κ P h ε)
          (UnitSpherePolynomialWrapper.sourceRewardBCF
            (sourceBlock (m := m) layout)
            (rewardCode (n := n) (k := k) (m := m) ε)) < 0 ↔
        I.Solvable) :
    Compiler.CompactSignSourceCertificate
      (sourceBlock (m := m) layout) I where
  degree := wrapperDegree E k M
  degree_ge_three := wrapperDegree_ge_three E k M
  degree_odd := wrapperDegree_odd E k M
  fieldCode := fieldCode layout M κ P h
  field_degree :=
    fieldCode_termsDegreeLE_wrapperDegree
      layout E M κ P hP h hh
  rewardCode := rewardCode ε
  reward_degree :=
    rewardCode_termsDegreeLE_wrapperDegree_sub_one
      (n := n) (m := m) E M ε
  properFaceBlock :=
    AccumulatorPolynomialCode.accumulatorSphereIndex (k + l)
  tangent := by
    intro v
    exact
      fieldCode_sourceTangentAt
        layout M κ P h v.1 v.2 (hcompact v)
  sourceFlow := sourceFlow layout E M κ P h ε
  sourceFlow_integralCurve :=
    sourceFlow_integralCurve
      layout E M κ P hP h hh ε hcompact
  sourceMaximum_neg_iff_solvable := hsign

/-- The final homogeneous field emitted from the pipeline is GAS exactly
for solvable DQL instances, once the compact-sign theorem is supplied. -/
theorem finalField_gas_iff_solvable
    (I : DQLSystem eqs vars)
    (layout : Fin n → Fin k ⊕ Fin l)
    (E M : ℕ) (κ : RationalCode)
    (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE E (P j))
    (h : Fin m → PolynomialCode n)
    (hh : ∀ i, PolynomialCode.TermsDegreeLE E (h i))
    (ε : RationalCode)
    [Nonempty
      (UnitSpherePolynomialWrapper.SourceProductSphere
        (sourceBlock (m := m) layout))]
    (hcompact :
      ∀ v :
          UnitSpherePolynomialWrapper.SourceProductSphere
            (sourceBlock (m := m) layout),
        let y : Fin (n + k) → ℝ :=
          fun q ↦
            v.1 (AccumulatorPolynomialCode.baseIndex
              (m := m) q)
        let x : Fin n → ℝ :=
          fun j ↦ y (MixedCentralPolynomialCode.xIndex
            (k := k) j)
        ∀ c, MixedCentralPolynomialCode.compactBlockDot layout x
          (MixedCentralPolynomialCode.clearedSourceVelocity
            layout M P y) c = 0)
    (hsign :
      Dynamics.maximalInvariantAverage
          (sourceFlow layout E M κ P h ε)
          (UnitSpherePolynomialWrapper.sourceRewardBCF
            (sourceBlock (m := m) layout)
            (rewardCode (n := n) (k := k) (m := m) ε)) < 0 ↔
        I.Solvable) :
    GloballyAsymptoticallyStable
        (PolynomialFieldCode.realize
          (Compiler.CompactSignSourceCertificate.finalFieldCode
            (compactSignSourceCertificate
              I layout E M κ P hP h hh ε hcompact hsign))) 0 ↔
      I.Solvable :=
  Compiler.CompactSignSourceCertificate.finalField_gas_iff_solvable
    (compactSignSourceCertificate
      I layout E M κ P hP h hh ε hcompact hsign)

end CompactAccumulatorPipelineCode

end

end HGAS
