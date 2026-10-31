import Stability

/-! Semantic regressions for the stability decision languages. These are
kernel-checked examples, including normalization and malformed inputs. -/

open HGAS Stability

-- Normalizing a sparse code leaves both decoded-degree languages unchanged.
example (n d : ℕ) (F : PolynomialFieldCode n) :
    PGASQ n d (fun i ↦ PolynomialCode.normalize (F i)) ↔ PGASQ n d F := by
  exact pgasQ_iff_of_decode_eq (fun i ↦ PolynomialCode.decode_normalize (F i))

example (n d : ℕ) (F : PolynomialFieldCode n) :
    PLASQ n d (fun i ↦ PolynomialCode.normalize (F i)) ↔ PLASQ n d F := by
  exact plasQ_iff_of_decode_eq (fun i ↦ PolynomialCode.decode_normalize (F i))

-- Arbitrarily high-degree terms are harmless when they cancel.
example (n d : ℕ) (F G : PolynomialFieldCode n) :
    PGASQ n d
        (fun i ↦ PolynomialCode.add (F i)
          (PolynomialCode.add (G i) (PolynomialCode.neg (G i)))) ↔
      PGASQ n d F := by
  apply pgasQ_iff_of_decode_eq
  intro i
  simp only [PolynomialCode.decode_add_code, PolynomialCode.decode_neg_code,
    add_neg_cancel, add_zero]

example (n d : ℕ) (F G : PolynomialFieldCode n) :
    PLASQ n d
        (fun i ↦ PolynomialCode.add (F i)
          (PolynomialCode.add (G i) (PolynomialCode.neg (G i)))) ↔
      PLASQ n d F := by
  apply plasQ_iff_of_decode_eq
  intro i
  simp only [PolynomialCode.decode_add_code, PolynomialCode.decode_neg_code,
    add_neg_cancel, add_zero]

-- A nonzero constant is malformed as a homogeneous cubic source.
example :
    ¬ PGASQ 1 3 (cubicToPolynomialCode 1 (fun _ ↦ PolynomialCode.one)) := by
  rw [cubicToPolynomialCode_of_not_homogeneous (by decide)]
  exact zeroPolynomialFieldCode_not_pgasQ (by decide) 3

example :
    ¬ PLASQ 1 3 (cubicToPolynomialCode 1 (fun _ ↦ PolynomialCode.one)) := by
  rw [cubicToPolynomialCode_of_not_homogeneous (by decide)]
  exact zeroPolynomialFieldCode_not_plasQ (by decide) 3

example : cubicToPolynomialCode 1 (fun _ ↦ PolynomialCode.zero) =
    (fun _ ↦ PolynomialCode.zero) := by
  apply cubicToPolynomialCode_of_homogeneous
  decide

example : ¬ PLASQ 1 0 (Veronese.zeroPolynomialFieldCode 1) :=
  zeroPolynomialFieldCode_not_plasQ (by decide) 0

-- An even upper degree bound still contains all homogeneous cubics.
example (n : ℕ)
    (hn : NormalizedCorrectedAugmentedEffectiveFamily.cofinalDimensionThreshold ≤ n) :
    ManyOneHard (PLASQ n 4) :=
  plasQ_manyOneHard n 4 hn (by decide)

-- The degree-input language explicitly rejects even degree tags.
example (n : ℕ) (F : PolynomialFieldCode n) :
    ¬ VariableOddHGASQ n (2, F) := by
  simp [VariableOddHGASQ]

-- The shifted quadratic really has a negative term; the bound includes it.
example : (((-1 : ℤ) : ℝ) + 1) ^ 2 - 1 / 4 < 0 := by norm_num

-- Constants at different occurrences may change independently.
open Stability.Simulation in
example :
    AbsFormula.eraseConstants
        (.add (.constant 1) (.constant 1) : AbsFormula (Fin 1)) =
      AbsFormula.eraseConstants (.add (.constant 2) (.constant 3)) := rfl

-- A genuine absolute-value coordinate gets a global vector error bound,
-- including the nondifferentiable point of the original formula.
open Stability.Simulation in
example (x : Fin 1 → ℝ) :
    ‖AbsFormula.smoothingError
      (fun _ : Fin 1 ↦ .abs (.coordinate 0)) 0 (1 / 4) x‖ ≤
        (1 / 4 : ℝ) / (1 + (x 0) ^ 2) := by
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
    AbsFormula.norm_smoothingError_le_clockTail
    (fun _ : Fin 1 ↦ .abs (.coordinate 0)) 0 (ε := 1 / 4)
    (by norm_num) (by norm_num) x

-- The degree bound concerns polynomial syntax and does not require a
-- positive precision; positivity is needed for analytic error bounds.
open Stability.Simulation in
example (ε : ℚ) :
    (AbsFormula.precisionPolynomial
      (fun _ : Fin 1 ↦ .abs (.coordinate (0 : Fin 1))) 0 ε).totalDegree ≤ 4 := by
  simpa [AbsFormula.familyDegreeBound, AbsFormula.majorantDegreeBound] using
    AbsFormula.precisionPolynomial_totalDegree_le
      (fun _ : Fin 1 ↦ .abs (.coordinate (0 : Fin 1))) 0 ε

-- The fixed stack-machine interpreter follows the same universal source.
example (p : Nat.Partrec.Code × ℕ) :
    Stability.UniversalMachineSource.Halts (Stability.UniversalMachineSource.inputCode p) ↔
      HGAS.UniversalHalts p := Stability.UniversalMachineSource.halts_inputCode_iff p

-- Concrete runs check the final zero test, other registers, and halt.
open Stability.RegisterMachine in
example : run (clearProgram (0 : Fin 3)) 5
    ⟨some 0, ![4, 7, 9]⟩ = ⟨none, ![0, 7, 9]⟩ := by
  apply Configuration.ext
  · decide
  · funext j; fin_cases j <;> decide

open Stability.RegisterMachine in
example : run (clearProgram (0 : Fin 3)) 1
    ⟨some 0, ![0, 7, 9]⟩ = ⟨none, ![0, 7, 9]⟩ := by decide

open Stability.RegisterMachine in
example : run (transferProgram (0 : Fin 3) 1) 9
    ⟨some 0, ![4, 7, 9]⟩ = ⟨none, ![0, 11, 9]⟩ := by
  apply Configuration.ext
  · decide
  · funext j; fin_cases j <;> decide

open Stability.RegisterMachine in
example : run (transferProgram (0 : Fin 3) 1) 1
    ⟨some 0, ![0, 7, 9]⟩ = ⟨none, ![0, 7, 9]⟩ := by decide

open Stability.RegisterMachine in
example : (run (transferProgram (0 : Fin 3) 1) 8
    ⟨some 0, ![4, 7, 9]⟩).label = some 0 := by decide

open Stability.RegisterMachine in
example : run (transferProgram (0 : Fin 3) 1) 19
    ⟨some 0, ![4, 7, 9]⟩ = ⟨none, ![0, 11, 9]⟩ := by
  apply Configuration.ext
  · decide
  · funext j; fin_cases j <;> decide

example : Stability.UniversalMachineSource.Halts
    (Stability.UniversalMachineSource.inputCode (Nat.Partrec.Code.zero, 17)) := by
  rw [Stability.UniversalMachineSource.halts_inputCode_iff]
  trivial

section RegisterArithmeticExamples

open Stability.RegisterMachine

private def binaryPush : Program 3 6 := ![
  .dec 0 (some 3) (some 1), .inc 1 (some 2), .inc 1 (some 0),
  .dec 1 (some 5) (some 4), .inc 0 (some 3), .inc 0 none]

example : run binaryPush 24 ⟨some 0, ![3, 0, 9]⟩ = ⟨none, ![7, 0, 9]⟩ := by
  apply Configuration.ext
  · decide
  · funext j; fin_cases j <;> decide

example (r : Fin 3 → ℕ) (hr : r 1 = 0) :
    run binaryPush ((3 * r 0 + 1) + (2 * (2 * r 0) + 1) + 1) ⟨some 0, r⟩ =
      ⟨none, Function.update (Function.update r 1 0) 0 (2 * r 0 + 1)⟩ := by
  simpa using run_stackPush (P := binaryPush) (multiply := 0) (copy := 3) (add := 4)
    (value := 0) (scratch := 1) (base := [1, 2]) (digit := [5]) (exit := none)
    (by decide) rfl (by simp [IncrementChain, blockEntry, binaryPush])
    rfl rfl (by simp [IncrementChain, blockEntry, binaryPush]) r hr

private def binaryPop : Program 3 8 := ![
  .dec 0 (some 3) (some 1), .dec 0 (some 5) (some 2), .inc 1 (some 0),
  .dec 1 none (some 4), .inc 0 (some 3),
  .dec 1 (some 7) (some 6), .inc 0 (some 5), .inc 2 none]

-- The odd remainder branches to label 7, before its instruction executes.
example : run binaryPop 18 ⟨some 0, ![7, 0, 9]⟩ = ⟨some 7, ![3, 0, 9]⟩ := by
  apply Configuration.ext
  · decide
  · funext j; fin_cases j <;> decide

example : run binaryPop 17 ⟨some 0, ![6, 0, 9]⟩ = ⟨none, ![3, 0, 9]⟩ := by
  apply Configuration.ext
  · decide
  · funext j; fin_cases j <;> decide

example : run binaryPop 2 ⟨some 0, ![0, 0, 9]⟩ = ⟨none, ![0, 0, 9]⟩ := by decide

end RegisterArithmeticExamples

section RadicalCompilerExamples

open Stability.Simulation
open Stability.Simulation.AbsFormula

-- Equal or zero constants do not remove syntactic roots, and a prefix
-- offset does not change the number of allocated roots.
example : (extractRadicalFamily (1 : MvPolynomial (Fin 1) ℚ)
    [.abs (.constant 0), .add (.abs (.constant 7)) (.abs (.constant 7))] 11).program.length =
      3 := by
  rw [(extractRadicalFamily_lengths _ _ _).1]
  rfl

-- All outputs use the final shared root assignment, even if every root
-- initially contains an arbitrary value unrelated to its equation.
example (x : Fin 1 → ℝ) (initialRoots : ℕ → ℝ) :
    let es : List (AbsFormula (Fin 1)) :=
      [.abs (.coordinate 0), .abs (.abs (.coordinate 0))]
    let E := extractRadicalFamily 1 es 5
    E.results.map (PowerFraction.value 1
      (RadicalProgram.point x (RadicalProgram.run E.program 5 x initialRoots))) =
        [Real.sqrt ((x 0) ^ 2 + 1), Real.sqrt ((Real.sqrt ((x 0) ^ 2 + 1)) ^ 2 + 1)] := by
  dsimp only
  have h := extractRadicalFamily_run_values (1 : MvPolynomial (Fin 1) ℚ)
    [.abs (.coordinate 0), .abs (.abs (.coordinate 0))] 5 x initialRoots
    (by simp [polynomialValue])
  simpa [polynomialValue, smoothEval] using h

-- Finite restriction needs no default root when there are zero radicals.
example (x : Fin 1 → ℝ) (roots : Fin 0 → ℝ) :
    polynomialValue (Sum.elim x roots)
      (RadicalProgram.finitePolynomial 0
        (RadicalProgram.basePolynomial (MvPolynomial.X (0 : Fin 1)))) = x 0 := by
  rw [RadicalProgram.finitePolynomial_value
    (RadicalProgram.dependsBelow_basePolynomial _ 0), RadicalProgram.basePolynomial_value]
  simp [polynomialValue]

-- A vanishing coefficient does not invalidate the global radicand bound.
example (x : Fin 1 → ℝ) (roots : ℕ → ℝ)
    (D : RadicalProgram.Polynomial (Fin 1))
    (hD : D ∈ (extractRadicals 1 (.abs (.constant 0)) 0).program) :
    1 ≤ RadicalProgram.polynomialValue x roots D :=
  extractRadicals_radicands_one_le 1 (.abs (.constant 0)) 0 x roots
    (by simp [polynomialValue]) D hD

end RadicalCompilerExamples

section CyclicMachineExamples

open Stability.RegisterMachine Stability.RegisterMachine.TM2Encoding
open Turing.PartrecToTM2

private def cyclicPush : Program 2 12 := fun q ↦
  (pushBlockCode 0 1 0 (some (0 : Fin 12)) q).reindex (blockEmbedding id)

-- Both pushes use the same twelve instructions and jump backward.
set_option maxRecDepth 4096 in
example : run cyclicPush 214 ⟨some 0, ![2, 0]⟩ = ⟨some 0, ![56, 0]⟩ := by
  apply Configuration.ext
  · decide
  · funext j; fin_cases j <;> decide

private def cyclicPop : Program 2 16 := fun q ↦
  (popBlockCode 0 1 (fun _ ↦ some (0 : Fin 16)) q).reindex (blockEmbedding id)

example : run cyclicPop 26 ⟨some 0, ![14, 0]⟩ = ⟨some 0, ![0, 0]⟩ := by
  apply Configuration.ext
  · decide
  · funext j; fin_cases j <;> decide

private def storeContinuation : Program 5 5 := fun _ ↦ .inc 4 none
private def storeExit (store : Option Γ') : Option (Fin 5) := some (storeCode store)

-- Peek keeps the OLD store when requested, restores the popped symbol,
-- and reaches (but does not execute) the scratch-changing continuation.
example : run (peekDispatchProgram .main (fun old _ ↦ old) storeExit storeContinuation) 60
    ⟨some 48, ![14, 3, 0, 1, 0]⟩ = ⟨some 383, ![14, 3, 0, 1, 0]⟩ := by
  apply Configuration.ext
  · decide
  · funext j; fin_cases j <;> decide

example : run (peekDispatchProgram .main (fun _ head ↦ head) storeExit storeContinuation) 3
    ⟨some 48, ![0, 3, 0, 1, 0]⟩ = ⟨some 380, ![0, 3, 0, 1, 0]⟩ := by
  apply Configuration.ext
  · decide
  · funext j; fin_cases j <;> decide

end CyclicMachineExamples

section StatementCompilerExamples

open Stability.RegisterMachine Stability.RegisterMachine.TM2Encoding
open Turing.PartrecToTM2

private def skippedPush : StackStatement (Fin 1) :=
  .branch (fun _ ↦ false) (.push .main (fun _ ↦ .bit0) .halt) (.goto (fun _ ↦ 0))

-- The false arm skips the entire allocated left subtree, not just its
-- first instruction. The destination instruction has not executed.
example : run (compileStatement skippedPush (fun _ store ↦ some (storeCode store))
      (fun _ : Fin 5 ↦ .inc 4 none)) 2
    ⟨some 3, ![2, 3, 0, 1, 0]⟩ = ⟨some 78, ![2, 3, 0, 1, 0]⟩ := by
  apply Configuration.ext
  · decide
  · funext j; fin_cases j <;> decide

end StatementCompilerExamples

section UniversalMachineExamples

open Stability.RegisterMachine.TM2Encoding Stability.UniversalRegisterMachine

-- Literal binary-stack encodings, including the empty binary numeral.
example : inputNumeral 0 = 2 := by decide
example : inputNumeral 1 = 14 := by decide
example : inputNumeral 2 = 73 := by decide
example : inputNumeral 6 = 373 := by decide

-- The reduction handles every argument of the constant-zero program.
example (n : ℕ) : Halts (inputCode (Nat.Partrec.Code.zero, n)) := by
  rw [halts_inputCode_iff]
  trivial

-- Divergence is preserved, not merely halting in one direction.
example (input : Nat.Partrec.Code × ℕ) :
    ¬ Halts (inputCode input) ↔ ¬ HGAS.UniversalHalts input :=
  not_congr (halts_inputCode_iff input)

end UniversalMachineExamples

section LiftedTrajectoryExamples

open Stability.Simulation Stability.Simulation.AbsFormula

-- The zero argument of an absolute value causes no singularity in the
-- smoothed graph. Its base velocity is one and its radical is constant.
example (t : ℝ) :
    let es : List (AbsFormula (Fin 1)) := [.abs (.constant 0)]
    let component : Fin 1 → Fin es.length := fun _ ↦ 0
    HasDerivAt (fun u : ℝ ↦ CompiledFormulaLift.graph 1 es (fun _ ↦ u))
      (CompiledFormulaLift.realize 1 es component
        (CompiledFormulaLift.graph 1 es (fun _ ↦ t))) t := by
  dsimp only
  apply CompiledFormulaLift.hasDerivAt_graph 1 _ _ (fun _ ↦ by simp [polynomialValue])
  apply hasDerivAt_pi.mpr
  intro i
  simpa [polynomialValue, smoothEval] using hasDerivAt_id t

end LiftedTrajectoryExamples

section RawDimensionExamples

-- Dimension zero is a genuine input, with the expected vacuous sphere test.
example : RawHGASChecker.checkCandidate (0, 1, []) ((0, []), (1, 1)) = true := by decide
example : RawHGASChecker.checkCandidate (0, 2, []) ((0, []), (1, 1)) = false := by decide

-- Malformed field dimensions and exponent lengths cannot be accepted.
example : RawHGASChecker.checkCandidate (2, 3, [[]]) ((0, []), (1, 1)) = false := by decide
example : RawPolynomialFieldCode.wellFormed 1 [[([], RationalCode.one)]] = false := by decide
example : RawHGASChecker.checkCandidate (1, 3, [[]])
    ((0, [([], RationalCode.one)]), (1, 1)) = false := by decide

private def cancelledScalarField : RawPolynomialFieldCode :=
  [[([2], RationalCode.one), ([2], RationalCode.neg RationalCode.one),
    ([3], RationalCode.neg RationalCode.one)]]

private def scalarCertificate : RawGridCandidate :=
  ((0, [([2], RationalCode.one)]), (3, 7))

-- Displayed quadratic terms cancel, leaving the certified field -x³.
example : RawHGASChecker.fieldHomogeneous 3 cancelledScalarField = true := by decide
example : RawHGASChecker.checkCandidate (1, 3, cancelledScalarField) scalarCertificate = true :=
  by decide
example : RawHGASChecker.check (1, 3, cancelledScalarField)
    (Encodable.encode scalarCertificate) = true := by
  rw [RawHGASChecker.check, RawHGASChecker.decodeCandidate_encode]
  decide

-- Zero-resolution fallback witnesses are rejected even in dimension zero.
example : RawHGASChecker.check (0, 1, [])
    (Encodable.encode (((0, []), (0, 0)) : RawGridCandidate)) = false := by
  rw [RawHGASChecker.check, RawHGASChecker.decodeCandidate_encode]
  decide

end RawDimensionExamples

section GlobalDefectExamples

open Stability.Simulation Stability.Simulation.AbsFormula

-- The scalar bound permits negative auxiliaries arbitrarily far from the graph.
example (w : ℝ) : |w ^ 2 - 1| ≤ |w ^ 4 - 1| := by
  simpa using abs_sq_sub_sqrt_le_quarticDefect (w := w) (D := 1) le_rfl

-- No roots means zero defect energy, without choosing an element of Fin 0.
example (D : Fin 0 → MvPolynomial (Fin 1 ⊕ Fin 0) ℚ)
    (y : Fin 1 ⊕ Fin 0 → ℝ) : RadicalDefectBounds.defectNorm D y = 0 := by
  simp [RadicalDefectBounds.defectNorm, RadicalDefectBounds.defectEnergy, polynomialValue]

-- Constant radicands keep the recursive majorant degree bound at zero.
example (J : ℕ) : RadicalMajorant.degreeBound 0 J = 0 :=
  RadicalMajorant.degreeBound_zero_degree J

-- The current root is absent from its own triangular comparison polynomial.
example {σ : Type*} [Fintype σ] {J : ℕ}
    (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (htri : ∀ j, RadicalProgram.FiniteDependsBelow (D j) j.val) (j : Fin J) :
    RadicalComparison.weight D (D j) j = 0 :=
  RadicalComparison.weight_eq_zero_of_dependsBelow D (htri j) j le_rfl

end GlobalDefectExamples

section FiniteTrajectoryExamples

open Set Stability.ProjectivePolynomialCode

-- A zero output is uniformly bounded even if the field is incomplete.
example : HasBoundedFiniteOutput (fun x : ℝ ↦ x ^ 2) (fun _ ↦ 0) := by
  refine ⟨0, fun T _ y _ _ ↦ ?_⟩
  simp

-- A constant positive output is not bounded, even for a stationary field.
example : ¬ HasBoundedFiniteOutput (fun _ : ℝ ↦ 0) (fun _ ↦ 1) := by
  rintro ⟨M, hM⟩
  have h := hM (max M 0 + 1) (by positivity) (fun _ ↦ 0)
    continuousOn_const (fun t _ ↦ hasDerivAt_const t 0)
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] at h
  linarith [le_max_left M 0]

-- A collapsed interval needs no differential equation outside its interior.
example (γ η : ℝ → ℝ) (a : ℝ) (heq : γ a = η a) : EqOn γ η (Icc a a) := by
  intro t ht
  have htEq : t = a := le_antisymm ht.2 ht.1
  simpa only [htEq] using heq

-- The central chart includes the zero-dimensional affine space.
example (x : Fin 0 → ℝ) : centralLift x (Fin.last 0) = 1 := by
  rw [centralLift_last]
  simp [centralScale, HGAS.positiveCentralScale, HGAS.normSq, HGAS.dot]

-- Chart normalization uses the Euclidean sum of squares, not the sup norm.
example (x : Fin 3 → ℝ) : HGAS.Veronese.sourceRadiusSq (centralLift x) = 1 :=
  sourceRadiusSq_centralLift x

end FiniteTrajectoryExamples

section FourierAlgebraExamples

open Stability.Selection

-- The zero-dimensional torus has exactly its constant Fourier mode.
example (c : ℂ) (ρ : ℝ) :
    (∑' a : Fin 0 → ℤ, ‖UnitAddTorus.mFourierCoeff
      (fun _ : UnitAddTorus (Fin 0) ↦ c) a‖ * ρ ^ (∑ j, |(a j : ℝ)|)) = ‖c‖ :=
  (exponential_fourierCoeff_const c ρ).2

-- Opposite frequencies cancel before the coefficient norm is taken.
example {d : Type*} [Fintype d] (a : d → ℤ) :
    UnitAddTorus.mFourierCoeff
      (fun x ↦ UnitAddTorus.mFourier a x * UnitAddTorus.mFourier (-a) x) 0 = 1 := by
  have he : (fun x ↦ UnitAddTorus.mFourier a x * UnitAddTorus.mFourier (-a) x) =
      fun _ ↦ (1 : ℂ) := by
    funext x
    rw [← UnitAddTorus.mFourier_add, add_neg_cancel, UnitAddTorus.mFourier_zero]
    rfl
  rw [he, fourierCoeff_const]
  simp

-- Realification splits a nonzero character evenly between two frequencies.
example : UnitAddTorus.mFourierCoeff
    (fun x : UnitAddTorus Unit ↦ ((UnitAddTorus.mFourier (fun _ ↦ 1) x).re : ℂ))
      (fun _ ↦ 1) = 1 / 2 := by
  rw [fourierCoeff_re _ (UnitAddTorus.mFourier _).continuous]
  simp [fourierCoeff_character, funext_iff]

-- The imaginary coordinate has the required negative-frequency sign.
example : UnitAddTorus.mFourierCoeff
    (fun x : UnitAddTorus Unit ↦ ((UnitAddTorus.mFourier (fun _ ↦ 1) x).im : ℂ))
      (fun _ ↦ -1) = -1 / (2 * Complex.I) := by
  rw [fourierCoeff_im _ (UnitAddTorus.mFourier _).continuous]
  simp [fourierCoeff_character, funext_iff]

end FourierAlgebraExamples

section SparseDegreeExamples

open Stability.PolynomialCodeOperations

-- An arbitrarily displayed high-degree group disappears after cancellation.
example : trim (PolynomialCode.add
      (PolynomialCode.pow (PolynomialCode.varCode (0 : Fin 1)) 7)
      (PolynomialCode.neg (PolynomialCode.pow (PolynomialCode.varCode (0 : Fin 1)) 7))) =
    PolynomialCode.zero := by decide

-- Trimming does not silently normalize a nonzero duplicate group away.
example : trim (PolynomialCode.add (PolynomialCode.one : PolynomialCode 0)
      PolynomialCode.one) = PolynomialCode.add PolynomialCode.one PolynomialCode.one := by decide

-- Semantic degree zero suffices for the raw constant-term bound after trimming.
example (p : PolynomialCode 2) (hp : PolynomialCode.decode p = MvPolynomial.C 3) :
    PolynomialCode.TermsDegreeLE 0 (trim p) := by
  apply termsDegreeLE_trim_of_totalDegree_le
  simp [hp]

end SparseDegreeExamples

section FourierResourceExamples

open Stability.Selection

-- The primitive budget also covers the zero-dimensional clock family.
example (p : Fin 0 → ℕ) (m : ℕ) : radicalFourierBudget p m = 1 := by
  simp [radicalFourierBudget]

-- With zero exponents, the first positive radius index is already admissible.
example : radiusIndex 0 0 = 1 := by
  have hlo := radiusIndex_pos 0 0
  have hhi := radiusIndex_min 0 0 1 (by decide)
  omega

-- A zero primitive needs no small gain; the least positive denominator is one.
example (M : ℕ) : gainDenominator M RationalCode.zero = 1 := by
  have hlo := gainDenominator_pos M RationalCode.zero
  have hhi := gainDenominator_min M RationalCode.zero 1 (by
    simp [gainAdmissible, RationalCode.zero])
  omega

-- The integer gain test handles negative numerators exactly, not by rejecting them.
example : gainAdmissible 0 (RationalCode.neg RationalCode.one) 2 := by decide

end FourierResourceExamples

namespace RegisterMonitorExamples

def haltProgram : RegisterMachine.Program 1 1 := fun _ ↦ .inc 0 none

def loopProgram : RegisterMachine.Program 1 1 := fun _ ↦ .inc 0 (some 0)

theorem haltProgram_halts (r : Fin 1 → ℕ) :
    RegisterMachine.Halts haltProgram ⟨some 0, r⟩ := ⟨1, rfl⟩

theorem loopProgram_label (m : ℕ) (r : Fin 1 → ℕ) :
    (RegisterMachine.run loopProgram m ⟨some 0, r⟩).label = some 0 := by
  induction m generalizing r with
  | zero => rfl
  | succ m ih => exact ih _

theorem loopProgram_not_halts (r : Fin 1 → ℕ) :
    ¬ RegisterMachine.Halts loopProgram ⟨some 0, r⟩ := by
  rintro ⟨m, hm⟩
  rw [loopProgram_label] at hm
  contradiction

-- A literal one-step halt produces a stable homogeneous field for every loaded input.
example (r : Fin 1 → ℕ) :
    HLSQ (ClockedMonitorCode.dimension haltProgram 0 + 1)
      (2 * HomogeneousStabilityReduction.degreeIndex haltProgram 0 + 1)
      (HomogeneousStabilityReduction.fieldCode haltProgram 0 r) :=
  (HomogeneousStabilityReduction.hlsQ_fieldCode_iff haltProgram 0 r).mpr
    (haltProgram_halts r)

-- An infinite increment loop produces an unstable field for every loaded input.
example (r : Fin 1 → ℕ) :
    ¬ HLSQ (ClockedMonitorCode.dimension loopProgram 0 + 1)
      (2 * HomogeneousStabilityReduction.degreeIndex loopProgram 0 + 1)
      (HomogeneousStabilityReduction.fieldCode loopProgram 0 r) := by
  rw [HomogeneousStabilityReduction.hlsQ_fieldCode_iff]
  exact loopProgram_not_halts r

end RegisterMonitorExamples

section CompactGraphExamples

open HGAS.CompactAccumulatorPipelineCode Stability.Selection

-- Both compactification charts retain their reward formula in dimension zero.
example (ε : RationalCode) :
    UnitSpherePolynomialWrapper.sourceRewardBCF
      (sourceBlock (m := 0) (AllAffineCompactSourceChart.layout 0))
      (rewardCode (n := 0) (k := 1) (m := 0) ε)
      (positiveCompactGraphPoint (0 : Fin 0 → ℝ) (0 : Fin 0 → ℝ)) =
        2 - (ε.decode : ℝ) := by
  rw [positiveCompactGraphPoint_reward]
  simp [normSq, dot]

-- A noninjective parametrization needs only a compact invariant image.
example : ∃ μ : HGAS.Dynamics.InvariantProbabilityMeasure (Flow.id ℝ ℝ),
    (μ.measure : MeasureTheory.Measure ℝ) (Set.range (fun _ : Bool ↦ (0 : ℝ))) = 1 ∧
      0 ≤ HGAS.Dynamics.observableAverage
        (BoundedContinuousFunction.const ℝ (0 : ℝ)) μ.measure := by
  apply Stability.Dynamics.exists_invariantProbability_on_compact_range
    (Flow.id ℝ ℝ) (fun _ : Bool ↦ (0 : ℝ)) continuous_const
  · intro t a
    exact Set.mem_range_self a
  · intro a
    exact le_rfl

end CompactGraphExamples

section DetectorCompilerExamples

open Stability.Selection

-- The raw code map is defined even for empty source and equation families.
example (I : DQLSystem 0 0) :
    Computable (fun rhs : Fin 0 → ℤ ↦
      detectorWrappedFieldCode { I with rhs := rhs } Fin.elim0) :=
  detectorWrappedFieldCode_rhs_computable I Fin.elim0

example (I : DQLSystem 2 0) (p : Fin 2 → ℕ) :
    Computable (fun rhs : Fin 2 → ℤ ↦
      HGAS.NormalizedCorrectedFixedDetectorCompactSourceCode.compile
        (detectorCompilerInput { I with rhs := rhs } p)) :=
  detectorCompiledSourceCode_rhs_computable I p

example (I : DQLSystem 0 2) (p : Fin 2 → ℕ) :
    Computable (fun rhs : Fin 0 → ℤ ↦
      detectorWrappedFieldCode { I with rhs := rhs } p) :=
  detectorWrappedFieldCode_rhs_computable I p

end DetectorCompilerExamples
