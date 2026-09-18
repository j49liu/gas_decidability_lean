import HGAS.Algebra.ComplexPolynomialFamilyCode
import HGAS.Algebra.PolynomialVariableEmbedding
import HGAS.Modular.JacobiPolynomialCode
import HGAS.Modular.JacobiResidualEnergy
import HGAS.Modular.UnaryPolynomialCode
import Mathlib.Tactic

/-!
# Finite polynomial compiler for the linked unary--Jacobi source

The analytic source uses two copies of its modular coefficients:

* the unary block `(A,C,E,Y)`, on which the modular flow is easiest to
  classify; and
* the Jacobi block
  `(p₂,p₃,p₄,H,T₁,T₂,T₃,T₄,Δ,U)`, on which the theta selector is
  polynomial.

They are kept as independent coordinates and tied together by polynomial
residuals.  `JacobiCoefficientLinks` proves that these relations form an
invariant ideal.  This file supplies the missing finite syntax: a
fourteen-complex-coordinate polynomial field and finite codes for all ten
validity residuals named by `LinkedJacobiResidualIndex`.

The field compiler is assembled from the already checked unary and Jacobi
compilers through the generic block operation in
`PolynomialVariableEmbedding`.  Thus no coordinate formula is copied.  The
semantic theorem states exact equality with
`LinkedJacobiState.combinedVectorField`, both on structured states and on
arbitrary points of the real ambient space.
-/

namespace HGAS.Modular

open HGAS

namespace LinkedJacobiPolynomialCode

open ComplexPolynomialCode

abbrev unaryDimension : ℕ :=
  UnaryPolynomialCode.modularDimension

abbrev jacobiDimension : ℕ :=
  JacobiPolynomialCode.dimension

/-- Four unary coordinates followed by ten Jacobi coordinates. -/
abbrev dimension : ℕ := unaryDimension + jacobiDimension

def unaryEmbedding :
    Fin unaryDimension ↪ Fin dimension :=
  ComplexPolynomialBlockCode.leftEmbedding

def jacobiEmbedding :
    Fin jacobiDimension ↪ Fin dimension :=
  ComplexPolynomialBlockCode.rightEmbedding

/-- Flatten a linked structured state into its fourteen complex
coordinates. -/
def point
    (z : LinkedJacobiState ℂ) : Fin dimension → ℂ :=
  ComplexPolynomialBlockCode.point
    (UnaryPolynomialCode.modularPoint z.unary)
    (JacobiPolynomialCode.point z.jacobi)

/-- Reassemble a linked structured state from fourteen coordinates. -/
def state
    (z : Fin dimension → ℂ) : LinkedJacobiState ℂ where
  unary :=
    UnaryPolynomialCode.modularState (z ∘ unaryEmbedding)
  jacobi :=
    JacobiPolynomialCode.state (z ∘ jacobiEmbedding)

@[simp]
theorem state_point (z : LinkedJacobiState ℂ) :
    state (point z) = z := by
  ext <;>
    simp [state, point, unaryEmbedding, jacobiEmbedding]

@[simp]
theorem point_state (z : Fin dimension → ℂ) :
    point (state z) = z := by
  unfold point state
  funext q
  obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective q
  · rw [show finSumFinEquiv (Sum.inl i) =
      ComplexPolynomialBlockCode.leftEmbedding
        (p := jacobiDimension) i by rfl]
    simp [unaryEmbedding]
  · rw [show finSumFinEquiv (Sum.inr j) =
      ComplexPolynomialBlockCode.rightEmbedding
        (m := unaryDimension) j by rfl]
    simp [jacobiEmbedding]

/-! ## The linked two-clock field -/

/-- Complex finite field code for the linked state.  The elliptic clock
acts only on the Jacobi block; the modular clock acts on both blocks. -/
def complexFieldCode
    (κZ κPhi : GaussianRationalCode) :
    ComplexPolynomialFieldCode dimension :=
  ComplexPolynomialBlockCode.field
    (UnaryPolynomialCode.scaledModularFieldCode κPhi)
    (JacobiPolynomialCode.combinedFieldCode κZ κPhi)

/-- Ordinary rational real polynomial code on twenty-eight real
coordinates. -/
def compileFieldCode
    (κZ κPhi : GaussianRationalCode) :
    PolynomialFieldCode (dimension + dimension) :=
  ComplexPolynomialFieldCode.realify
    (complexFieldCode κZ κPhi)

/-- Exact semantics of every complex component of the linked finite
compiler. -/
@[simp]
theorem eval_complexFieldCode
    (κZ κPhi : GaussianRationalCode)
    (z : LinkedJacobiState ℂ) :
    (fun i ↦ eval (complexFieldCode κZ κPhi i) (point z)) =
      point
        (LinkedJacobiState.combinedVectorField
          (GaussianRationalCode.decode κZ)
          (GaussianRationalCode.decode κPhi) z) := by
  unfold point
  rw [complexFieldCode,
    ComplexPolynomialBlockCode.eval_field]
  funext q
  obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective q
  · rw [show finSumFinEquiv (Sum.inl i) =
      ComplexPolynomialBlockCode.leftEmbedding
        (p := jacobiDimension) i by rfl]
    simp only [ComplexPolynomialBlockCode.point_leftEmbedding]
    rw [UnaryPolynomialCode.eval_scaledModularFieldCode
      κPhi z.unary i]
    fin_cases i <;>
      simp [LinkedJacobiState.combinedVectorField,
        UnaryPolynomialCode.modularPoint]
  · rw [show finSumFinEquiv (Sum.inr j) =
      ComplexPolynomialBlockCode.rightEmbedding
        (m := unaryDimension) j by rfl]
    simp only [ComplexPolynomialBlockCode.point_rightEmbedding]
    simp [LinkedJacobiState.combinedVectorField]

/-- Realification and reassembly recover the linked complex vector field
exactly. -/
@[simp]
theorem complexify_realize_compileFieldCode
    (κZ κPhi : GaussianRationalCode)
    (z : LinkedJacobiState ℂ) :
    ComplexCoordinates.complexifyPoint
        (PolynomialFieldCode.realize
          (compileFieldCode κZ κPhi)
          (ComplexCoordinates.realifyPoint (point z))) =
      point
        (LinkedJacobiState.combinedVectorField
          (GaussianRationalCode.decode κZ)
          (GaussianRationalCode.decode κPhi) z) := by
  unfold compileFieldCode
  rw [ComplexPolynomialFieldCode.complexifyPoint_realize_realify]
  exact eval_complexFieldCode κZ κPhi z

/-- Ambient form of the compiler theorem: it applies to every real point,
without assuming any residual equation. -/
@[simp]
theorem complexify_realize_compileFieldCode_arbitrary
    (κZ κPhi : GaussianRationalCode)
    (x : Fin (dimension + dimension) → ℝ) :
    ComplexCoordinates.complexifyPoint
        (PolynomialFieldCode.realize
          (compileFieldCode κZ κPhi) x) =
      point
        (LinkedJacobiState.combinedVectorField
          (GaussianRationalCode.decode κZ)
          (GaussianRationalCode.decode κPhi)
          (state (ComplexCoordinates.complexifyPoint x))) := by
  have h :=
    complexify_realize_compileFieldCode κZ κPhi
      (state (ComplexCoordinates.complexifyPoint x))
  simpa using h

/-! ## Coordinate syntax for the ten validity residuals -/

def ACode : ComplexPolynomialCode dimension :=
  var (unaryEmbedding UnaryPolynomialCode.AIndex)

def CCode : ComplexPolynomialCode dimension :=
  var (unaryEmbedding UnaryPolynomialCode.CIndex)

def ECode : ComplexPolynomialCode dimension :=
  var (unaryEmbedding UnaryPolynomialCode.EIndex)

def YCode : ComplexPolynomialCode dimension :=
  var (unaryEmbedding UnaryPolynomialCode.YIndex)

def p2Code : ComplexPolynomialCode dimension :=
  var (jacobiEmbedding JacobiPolynomialCode.p2Index)

def p3Code : ComplexPolynomialCode dimension :=
  var (jacobiEmbedding JacobiPolynomialCode.p3Index)

def p4Code : ComplexPolynomialCode dimension :=
  var (jacobiEmbedding JacobiPolynomialCode.p4Index)

def HCode : ComplexPolynomialCode dimension :=
  var (jacobiEmbedding JacobiPolynomialCode.HIndex)

/-- `Y⁴-A-C`. -/
def unaryJacobiCode : ComplexPolynomialCode dimension :=
  sub (sub (pow YCode 4) ACode) CCode

/-- `p₂²-A`. -/
def link2Code : ComplexPolynomialCode dimension :=
  sub (pow p2Code 2) ACode

/-- `p₃²-Y⁴`. -/
def link3Code : ComplexPolynomialCode dimension :=
  sub (pow p3Code 2) (pow YCode 4)

/-- `p₄²-C`. -/
def link4Code : ComplexPolynomialCode dimension :=
  sub (pow p4Code 2) CCode

/-- `12H-E`. -/
def linkHCode : ComplexPolynomialCode dimension :=
  sub
    (mul (UnaryPolynomialCode.rational 12) HCode)
    ECode

/-- Signed branch selector `p₃-Y²`. -/
def signedLink3Code : ComplexPolynomialCode dimension :=
  sub p3Code (pow YCode 2)

/-- The first four codes are the intrinsic Jacobi residuals, embedded in the
right block.  The last six are the coefficient and signed-link residuals.
The order agrees with `LinkedJacobiResidualIndex`. -/
def residualCode (i : Fin 10) :
    ComplexPolynomialCode dimension :=
  ![
    ComplexPolynomialBlockCode.right
      (m := unaryDimension) JacobiPolynomialCode.residualR0Code,
    ComplexPolynomialBlockCode.right
      (m := unaryDimension) JacobiPolynomialCode.residualR1Code,
    ComplexPolynomialBlockCode.right
      (m := unaryDimension) JacobiPolynomialCode.residualR2Code,
    ComplexPolynomialBlockCode.right
      (m := unaryDimension) JacobiPolynomialCode.residualRUCode,
    unaryJacobiCode,
    link2Code,
    link3Code,
    link4Code,
    linkHCode,
    signedLink3Code
  ] i

/-- Convert the executable `Fin 10` ordering to the semantic index type used
by `JacobiResidualEnergy`. -/
def residualIndex (i : Fin 10) :
    LinkedJacobiResidualIndex :=
  ![
    .coefficientCurve,
    .thetaQuadricOne,
    .thetaQuadricTwo,
    .reciprocalChart,
    .unaryJacobi,
    .coefficientLinkTwo,
    .coefficientLinkThree,
    .coefficientLinkFour,
    .eisensteinLink,
    .signedRootLinkThree
  ] i

@[simp]
theorem eval_rightCode
    (q : ComplexPolynomialCode jacobiDimension)
    (z : LinkedJacobiState ℂ) :
    eval
        (ComplexPolynomialBlockCode.right
          (m := unaryDimension) q)
        (point z) =
      eval q (JacobiPolynomialCode.point z.jacobi) := by
  unfold point
  exact
    ComplexPolynomialBlockCode.eval_right q
      (UnaryPolynomialCode.modularPoint z.unary)
      (JacobiPolynomialCode.point z.jacobi)

@[simp]
theorem eval_unaryJacobiCode (z : LinkedJacobiState ℂ) :
    eval unaryJacobiCode (point z) =
      LinkedJacobiState.jacobiResidual z := by
  simp [unaryJacobiCode, ACode, CCode, YCode,
    point, unaryEmbedding, LinkedJacobiState.jacobiResidual,
    UnaryPolynomialCode.modularPoint,
    UnaryPolynomialCode.AIndex, UnaryPolynomialCode.CIndex,
    UnaryPolynomialCode.YIndex]

@[simp]
theorem eval_link2Code (z : LinkedJacobiState ℂ) :
    eval link2Code (point z) =
      LinkedJacobiState.link2 z := by
  simp [link2Code, ACode, p2Code, point, unaryEmbedding,
    jacobiEmbedding, LinkedJacobiState.link2,
    UnaryPolynomialCode.modularPoint,
    JacobiPolynomialCode.point,
    UnaryPolynomialCode.AIndex,
    JacobiPolynomialCode.p2Index]

@[simp]
theorem eval_link3Code (z : LinkedJacobiState ℂ) :
    eval link3Code (point z) =
      LinkedJacobiState.link3 z := by
  simp [link3Code, YCode, p3Code, point, unaryEmbedding,
    jacobiEmbedding, LinkedJacobiState.link3,
    UnaryPolynomialCode.modularPoint,
    JacobiPolynomialCode.point,
    UnaryPolynomialCode.YIndex,
    JacobiPolynomialCode.p3Index]

@[simp]
theorem eval_link4Code (z : LinkedJacobiState ℂ) :
    eval link4Code (point z) =
      LinkedJacobiState.link4 z := by
  simp [link4Code, CCode, p4Code, point, unaryEmbedding,
    jacobiEmbedding, LinkedJacobiState.link4,
    UnaryPolynomialCode.modularPoint,
    JacobiPolynomialCode.point,
    UnaryPolynomialCode.CIndex,
    JacobiPolynomialCode.p4Index]

@[simp]
theorem eval_linkHCode (z : LinkedJacobiState ℂ) :
    eval linkHCode (point z) =
      LinkedJacobiState.linkH z := by
  simp [linkHCode, ECode, HCode, point, unaryEmbedding,
    jacobiEmbedding, LinkedJacobiState.linkH,
    UnaryPolynomialCode.modularPoint,
    JacobiPolynomialCode.point,
    UnaryPolynomialCode.rational,
    UnaryPolynomialCode.EIndex,
    JacobiPolynomialCode.HIndex]

@[simp]
theorem eval_signedLink3Code (z : LinkedJacobiState ℂ) :
    eval signedLink3Code (point z) =
      LinkedJacobiState.signedLink3 z := by
  simp [signedLink3Code, YCode, p3Code, point, unaryEmbedding,
    jacobiEmbedding, LinkedJacobiState.signedLink3,
    UnaryPolynomialCode.modularPoint,
    JacobiPolynomialCode.point,
    UnaryPolynomialCode.YIndex,
    JacobiPolynomialCode.p3Index]

/-- Every executable residual code evaluates to the correspondingly named
semantic linked residual. -/
@[simp]
theorem eval_residualCode
    (z : LinkedJacobiState ℂ) (i : Fin 10) :
    eval (residualCode i) (point z) =
      linkedJacobiResidual (residualIndex i) z := by
  fin_cases i <;>
    simp [residualCode, residualIndex, linkedJacobiResidual]

/-- `residualIndex` is a bijective enumeration of the ten semantic
residual names. -/
theorem residualIndex_bijective :
    Function.Bijective residualIndex := by
  decide

/-! ## Scalar real residual family for the accumulator compiler -/

/-- Twenty scalar residuals: the real parts of all ten complex residuals,
followed by their imaginary parts. -/
def realResidualCode :
    Fin (10 + 10) → PolynomialCode (dimension + dimension) :=
  ComplexPolynomialFamilyCode.realify residualCode

/-- Evaluating and reassembling the twenty scalar codes gives precisely the
ten semantic linked residuals. -/
@[simp]
theorem complexifyPoint_eval_realResidualCode
    (z : LinkedJacobiState ℂ) :
    ComplexCoordinates.complexifyPoint
        (fun q ↦
          MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
            (ComplexCoordinates.realifyPoint (point z))
            (PolynomialCode.decode (realResidualCode q))) =
      fun i ↦ linkedJacobiResidual (residualIndex i) z := by
  rw [realResidualCode,
    ComplexPolynomialFamilyCode.complexifyPoint_eval_realify]
  funext i
  exact eval_residualCode z i

/-- Simultaneous vanishing of the twenty scalar codes is equivalent to
vanishing of every named linked Jacobi residual. -/
theorem forall_eval_realResidualCode_eq_zero_iff
    (z : LinkedJacobiState ℂ) :
    (∀ q,
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (ComplexCoordinates.realifyPoint (point z))
        (PolynomialCode.decode (realResidualCode q)) = 0) ↔
      ∀ r : LinkedJacobiResidualIndex,
        linkedJacobiResidual r z = 0 := by
  rw [realResidualCode,
    ComplexPolynomialFamilyCode.forall_eval_realify_eq_zero_iff]
  constructor
  · intro h r
    obtain ⟨i, rfl⟩ := residualIndex_bijective.2 r
    simpa using h i
  · intro h i
    simpa using h (residualIndex i)

end LinkedJacobiPolynomialCode

end HGAS.Modular
