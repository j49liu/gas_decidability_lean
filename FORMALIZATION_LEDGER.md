# Formalization ledger

Last updated: 2026-10-31

Current status: **the unconditional augmented fixed-pair GAS theorem, its
cofinal cubic consequence, and the fixed-parameter GAS/HLS cubicization
theorems are complete and kernel checked**. The new `Stability` library
also proves unconditional fixed-source, cubic, and cofinal HLS hardness
from Mathlib's halting problem. It discharges the external source hypothesis
of the preserved conditional transfer theorems without changing them.

This ledger records the public theorem chain in the current worktree.  It
supersedes the early-development checklist that described the
modular/Jacobi-to-compiler integration as open.

This ledger uses five status labels:

- **Exact**: the Lean declaration has the intended coded input language,
  hypotheses, and conclusion.
- **Equivalent or alternative**: Lean proves a result sufficient for the
  dependency chain through a norm-equivalent, representation-equivalent, or
  different fixed-resource formulation.
- **Conditional**: the declaration exposes an unformalized literature input
  as a hypothesis.
- **Not formalized**: the repository makes no claim that Lean verifies the
  stated result.
- **Partial**: named supporting results are proved, but the broader paper
  statement still has explicitly listed obligations.

The preserved GAS companion is
`docs/hgas_sigma1_complete_formalization_companion.tex`. It records the
preceding 824-module formalization. The additive HLS and shadowing extension
is documented in `docs/cubicization_hls_formalization_companion.tex`. This
ledger, rather than either companion alone, is the authoritative coverage
record for the published 837-module library and the additions below.

## Further stability results

Baseline: Lean release `81276ab`; target manuscript: Overleaf `6f5bced`,
`new Main Document/main.tex`. The 837 published `HGAS/` modules, public
root, theorem statements, and pinned Lean/Mathlib environment are preserved.
Additions use the separate `Stability/` library and import root. The two
existing companion documents remain historical artifacts of their releases.

The agreed work has the following scope:

- **Exact, compiled**: general polynomial GAS with decoded total degree at
  most `d`. `Stability/Computability/PolynomialGAS.lean` defines `PGASQ`,
  a total primitive-recursive reduction from homogeneous cubic GAS (including
  malformed source codes), and cofinal fixed-dimension many-one hardness,
  undecidability, and non-r.e.-complement results for every `d >= 3`.
  This is not a recursive-enumerability or completeness claim for `PGASQ`.
- **Exact, compiled**: local asymptotic stability with explicit local
  forward existence, its equivalence to GAS for homogeneous fields, and
  the bounded-degree general polynomial LAS hardness corollary. See
  `Stability/Dynamics/LocalAsymptoticStability.lean` and
  `Stability/Computability/PolynomialLAS.lean`. The theorem is for the
  stated trajectory predicates; the usual maximal-solution interpretation
  uses polynomial local uniqueness.
- **Exact, compiled supporting estimate**: the shifted-theta weighted
  summability in `Stability/Analysis/ShiftedThetaBounds.lean` permits
  negative quadratic exponents and matches the revised coefficient and
  frequency majorants. The modules listed below identify and explicitly
  bound all actual canonical-graph coordinate Fourier norms. This is an added correspondence
  result, not a correction to the published Gaussian proofs.
- **Exact source-level equivalence and compact graph bounds**: the
  broader ordinary-time source-trajectory/test equivalence is compiled in
  `Selection/OrdinaryTimeSourceEquivalence.lean`. The existing selected-orbit result
  has stronger hypotheses and is not relabeled as the broader theorem.
  `Stability/Dynamics/CompactTranslationRecurrence.lean` proves the
  reusable compact-translation recurrence step for intended trajectories.
  `Selection/UnaryClockConjugation.lean` and
  `Selection/LinkedClockConjugation.lean` under `Stability/` provide
  forward-only clock normalization and conjugation of linked residuals.
  They do not import reverse recurrence or a selected invariant measure.
  `Selection/CanonicalThetaReflection.lean` proves the theta/Eisenstein
  reflection identities from their series. `Selection/LinearCuspDivergence.lean`
  and `Selection/LinearThetaCuspExclusion.lean` handle the critical first
  moment and exclude nonperiodic reconstructed frames under real-order
  `μ >= 1` forward growth bounds. `Selection/OrdinaryTimeGenericity.lean`,
  `OrdinaryTimeClosedFrame.lean`, and `OrdinaryTimeUnarySelection.lean`
  now derive the canonical unary trajectory, its gauge height, its literal
  phase relation, and the `p4` formula from the linked ODE at modular clock
  `πi`, forward recurrence, all residuals, full forward `Y`, `p4`, and
  first-harmonic means, and eventual full-state real-order growth bounds.
  No `p2` mean, supplied frame, or selected measure is assumed in the
  strongest endpoint. `OrdinaryTimePhysicalClock.lean` transports this
  result to either sign of a nonzero physical modular clock, preserving
  forward time and giving signed speed `Ω/π`. It assumes recurrence at
  time zero. `OrdinaryTimeBlochClassification.lean` derives the global
  regular affine Bloch path and reality of its parameter from the same
  data with a real elliptic clock. `OrdinaryTimeJacobiMoments.lean`
  derives the actual gauge branch from its ODE and identifies the gauged
  Jacobi output with a normalized quadratic-geometric target from three
  further full forward means, at irrational physical clock ratio `N/Ω`.
  `OrdinaryTimeDetectorProjection.lean` through
  `OrdinaryTimeDetectorAverage.lean` now instantiate the literal source
  field and scalar polynomial tests. They derive its signed prime clocks,
  rational independence, actual phase, theta target, reciprocal factors,
  and unit RHS phase factor. The actual scalar detector means vanish
  exactly when the integer system is unsolvable, on every trajectory
  satisfying the stated selector hypotheses. These hypotheses include an
  all-real complete trajectory, pointwise validity, forward recurrence,
  the scalar moment means, and an eventual Euclidean `μ >= 1` growth bound.
  Pointwise validity is not inferred from zero residual averages. The
  converse is now proved in `OrdinaryTimeIntendedOrbit.lean` through
  `OrdinaryTimePrimeExistence.lean`: a canonical orbit-closure construction
  supplies a uniformly bounded complete valid recurrent trajectory, and
  actual bounded primitives give all full ordinary-time scalar drift means.
  No selected measure or test means are supplied as hypotheses of this
  converse. `exists_prime_source_trajectory_iff_not_solvable` combines the
  directions for every fixed real `μ >= 1`, with the exact normalized
  scalar drift codes. This is not a direct construction of the manuscript's
  literal torus graph. `OrdinaryTimeAverageHorizon.lean` through
  `OrdinaryTimeDetectorExtraction.lean` now construct an actual complete
  source trajectory from an ergodic invariant probability for the literal
  compact base flow, full finite-chart mass, and zero compact drift means.
  Recurrence, pointwise validity, all full-horizon means, and a Euclidean
  growth bound at the actual clearing exponent are conclusions. No selected
  orbit or backward recurrence is assumed. `OrdinaryTimeConditionalBase.lean`
  derives that ergodic full-chart factor from an actual positive-interior
  accumulator measure and cancels any nonzero gain from its zero drift means.
  `OrdinaryTimeAccumulatorGap.lean` combines the resulting obstruction with
  the published no-instance finite graph and proves GAS iff solvability for
  the literal effective compiler. `OrdinaryTimeUniversalFamily.lean` supplies
  nonzero columns by the existing computable augmentation and proves fixed-
  pair/cofinal SigmaOneComplete endpoints on this new proof route. Emitted
  code is definitionally the existing compiler, independent of semantic
  selections. This is an **alternative** effective gain/reward-margin
  result, not an identification with the printed least-integer gain or full
  Γ Fourier package.
  `OrdinaryTimeWeightedFourier.lean` identifies genuine Haar coefficients
  by collecting expansion frequencies, including collisions.
  `OrdinaryTimeThetaGraph.lean` identifies the literal half-period `T₁`
  coordinate at every real phase lift and proves its actual weighted
  coefficient summability, retaining the shifted frequency `4n²-1`.
  It also computes the exact RHS-character weighted norm.
  `OrdinaryTimeFourierInverse.lean` constructs the Neumann expansion and
  proves bounds on the actual weighted Haar coefficients of reciprocals.
  `OrdinaryTimePoissonGraph.lean` applies this to both Poisson reciprocal
  coordinates, with norm bound 4 under the stated frequency condition.
  `OrdinaryTimeThetaReciprocal.lean` proves global nonvanishing and the
  literal identity `T₁ U = 1`, and bounds the actual weighted norm of `U`
  by `(7/20) ρ^(1+2 Σ|B_j|)` under its explicit ratio condition.
  `OrdinaryTimeJacobiGraph.lean` identifies all four literal Jacobi
  coordinates at every real phase and proves their weighted summability.
  `OrdinaryTimeJacobiDerivativeGraph.lean`, `OrdinaryTimeUnaryThetaGraph.lean`,
  and `OrdinaryTimeEisensteinGraph.lean` do the same for the normalized
  derivative, unary theta constants, and `E₂` coordinate, respectively.
  `OrdinaryTimeSourceGraph.lean` now assembles the literal full Γ in the
  actual flattened source coordinates, and `OrdinaryTimeSourceFourier.lean`
  proves weighted Haar-coefficient summability for every coordinate under
  the two matrix-norm inequalities. The reusable Fourier algebra supports
  products, powers, linear combinations, conjugation, and realification.
  `OrdinaryTimeSourceSize.lean` proves exact RHS-independence of the squared
  norm and a common natural size bound by compactness; the latter is
  explicitly non-effective. `OrdinaryTimePolynomialFourier.lean` proves
  the coefficient-mass/degree bound for actual polynomial substitution.
  `OrdinaryTimeSourceFourierBound.lean` isolates the exact RHS dependence
  `ρ^(4 * totalDegree * Σ |rhs|)` with a common natural constant, again
  explicitly non-effective. `OrdinaryTimeThetaBudget.lean`,
  `OrdinaryTimeSourceBudget.lean`, and `OrdinaryTimeSourcePolynomialBudget.lean`
  now replace that existence bound by the explicit natural coordinate
  budget `C = 262144^4 + 1048576 + 385 + 32 + 1`. They prove the actual
  polynomial Fourier bound `mass(P) * C^degree(P) * ρ^(4 degree(P) Σ|rhs|)`
  and the RHS-independent squared-norm bound `dimension * C^2`.
  `OrdinaryTimeRadicalFourierBudget.lean` and
  `OrdinaryTimeRadicalPrimitive.lean` prove an explicit natural
  small-divisor multiplier, continuity and reality of the literal Haar
  primitive, and its physical-time derivative with the actual zero mode
  subtracted. `OrdinaryTimeSourcePrimitive.lean` gives a positive rational
  common primitive budget. `OrdinaryTimeDetectorResources.lean` instantiates
  this for the actual normalized detector drift and proves RHS-independence
  of that drift, its semantic degree, and its base primitive budget.
  `OrdinaryTimeRadiusChoice.lean` and `OrdinaryTimeGainChoice.lean` implement
  the printed least positive integer choices by total computable searches
  with primitive-recursive integer tests. `OrdinaryTimeDetectorGain.lean`
  proves the actual scaled-primitive bound and the literal pointwise
  stereographic reward lower bound `5*w*/4`.
  `OrdinaryTimeDetectorGainCode.lean` computes the actual budget code
  primitive-recursively and the actual gain code computably as the RHS varies.
  `OrdinaryTimeSourceFlow.lean` and `OrdinaryTimeDetectorGraphFlow.lean`
  prove that the whole literal Γ solves the actual polynomial source ODE
  at every initial phase with the printed physical clock.
  `OrdinaryTimeDetectorZeroMode.lean` derives the actual Haar zero-mode
  vanishing from arithmetic unsolvability, and proves the uncentered
  primitive equation everywhere. `OrdinaryTimeDetectorBounds.lean` packages
  the fixed-matrix graph, Euclidean primitive bound, and actual skew ODE.
  `OrdinaryTimeCompactGraphTrajectory.lean` and `OrdinaryTimePositiveGraph.lean`
  prove graph-image invariance for the actual compact flow, using the same
  reciprocal central clock for the base and primitive. They require neither
  injectivity of Γ nor same-time equivariance. `CompactInvariantGraph.lean`
  constructs an invariant probability on a compact invariant image.
  `OrdinaryTimeDetectorInvariantGraph.lean` applies it to the actual detector,
  with the printed raw gain code and margin: an unsolvable instance has a
  probability giving the graph full mass and reward average at least
  `5*w*/4 > 0`. `OrdinaryTimeDetectorGap.lean` proves the matching
  `β <= -ε` bound for a solvable instance with nonzero linear columns.
  Its general negative bound works for every nonzero gain and any margin.
  `OrdinaryTimeDetectorSign.lean` assembles both branches for the same raw
  compiler input and proves exact maximal-average negativity iff arithmetic
  solvability. Its sign certificate has the literal compiled source codes;
  the faithful homogeneous wrapper is GAS iff that instance is solvable.
  `OrdinaryTimeDetectorCompiler.lean` proves computability of the literal
  compact source and proof-independent wrapped field as the RHS varies.
  `OrdinaryTimeUniversalDetector.lean` composes the fixed augmented DQL
  template with this compiler, giving exact code-level halting/GAS
  correspondence and fixed-pair/cofinal SigmaOneComplete endpoints with
  the printed gain. The preserved alternative-gain family is unchanged.
  This is not the standalone unary two-mean proposition:
  the linked `p4` mean and linked residuals remain explicit hypotheses.
- **Exact, scoped result compiled**: `VariableOddHGASQ n`, on raw
  `(d,F)` inputs, has one primitive-recursive witness checker uniform in
  degree and is SigmaOneComplete above the cubic dimension threshold. See
  `Stability/Computability/VariableHGASDegree.lean`. The odd-degree
  condition is explicit; dimension is fixed in that module.
  `VariableDimensionHGAS.lean` now defines `DimensionDegreeHGASQ` on a single
  raw list-code type with both dimension and odd degree as input. The
  `RawPolynomialCode`, `RawPolynomialArithmetic`, `RawPolynomialComputability`,
  `RawGridCertificate`, and `RawGridComputability` modules prove shape-valid
  decoding/encoding round trips, cancellation-aware exact arithmetic, and
  joint primitive recursiveness of the actual dimension-dependent grid loops.
  `RawHGASChecker.check_primrec` is one checker on `(n,d,F,c)`, not a family
  of per-dimension assertions. Exact correspondence with the published
  checker yields uniform RE; a fixed cubic slice supplies SigmaOneComplete,
  undecidability, and non-RE complement. Dimension zero is included.
  Malformed field/exponent shapes and even-degree tags are negative inputs;
  failed witness decodes have zero resolutions and cannot be accepted.
  These statements provide partial coverage of Corollary `cor:variable`.
  Separate dimension-input theorems for fixed degree three or fixed odd
  degree are not formalized. Nor is a literal identification with the
  paper's all-degree `HGAS` language: the joint Lean language admits
  dimension zero and explicitly rejects even-degree tags.
- **Exact, unconditional result compiled**: the fixed-resource halting-to-HLS
  reduction and its cubic/cofinal consequences.
  `HomogeneousStabilityReduction.lean` constructs a primitive-recursive
  homogeneous code from the loaded input of any fixed register program,
  with exact `HLSQ` iff halting. `UniversalStabilityReduction.lean` applies
  it to the checked fixed universal INC/DEC machine and composes the
  preserved cubicization and padding reductions. It proves `ManyOneHard`,
  undecidability, and non-RE complement in a fixed cubic dimension and
  every larger dimension and odd degree at least three. There is no
  source-hardness, simulation, or effectivity assumption. These theorems
  do not claim RE membership for HLS. The dimensions are closed symbolic
  terms, not evaluated numerical bounds. The implementation follows the
  written proof without copying or porting the earlier Lean code.
  Positive finite-curve time change is proved in `FiniteTimeChange.lean`
  and `FiniteOutputTimeChange.lean`, without global completeness assumptions.
  `PolynomialMonitorCriterion.lean` now proves that halting is equivalent
  to bounded finite output integrals for the actual cleared polynomial
  field and penalized output. Its degree bounds are input-independent.
  `ProjectivePolynomialCode.lean` and `ProjectivePolynomialComputability.lean`
  implement the literal projective field, prove its homogeneity and equator
  identities, and prove primitive recursiveness of its raw-code operations.
  `ProjectiveStabilityCriterion.lean` now proves the full geometric
  equivalence between bounded finite source output and existence-aware
  Lyapunov stability of the literal homogeneous field. Equator stationarity,
  noncrossing by uniqueness, positive rates in both hemispheres, and central
  lifting of every finite source curve are proved, not assumed.
  `ClockedMonitorPolynomialCode.lean` supplies the exact primitive-recursive
  field/output pair with input-independent decoded degree bounds;
  `PolynomialCodeConjugacy.lean` and `PolynomialOutputReduction.lean`
  complete its fixed-coordinate and homogeneous-code bridges.
  `SourceAngularStability.lean` transports
  the preserved angular stability criterion to polynomial code coordinates;
  `FiniteSolutionUniqueness.lean` supplies uniqueness for closed finite
  curves whose ODE is stated only in the open interval.
  Completed supporting modules under `Stability/Simulation/` are:
  `RestartBudget.lean` (Proposition 4.5's finite counting invariant),
  `CubicRelaxation.lean`, `ConstantTargetCubicRelaxation.lean`,
  `MovingTargetCubicRelaxation.lean`, and `ForcedCubicRelaxation.lean`
  (the finite-solution-segment estimates of Lemma 4.1, including moving
  targets, additive forcing with coefficient one, and magnitude bounds).
  These do not prove solution existence or continuation.
  `ClockGain.lean` proves the unit-speed and oscillator identities on
  supplied solution segments and the central-arc integrated gain bound.
  `ClockErrorSummability.lean` proves a uniform integer-lattice error sum
  at most `29/10`, hence the strict forward sum bound `3/sqrt(gain)`.
  `AlternatingClock.lean` connects the actual oscillator and clock ODEs
  to centered arcs under an explicit aligned initial phase.
  `HalfTurnForcingMass.lean` partitions actual absolute forcing integrals;
  `HalfTurnErrorBudget.lean` bounds the resulting explicitly defined
  allowances, including the constant `11/1024`. `DoubleBufferUpdate.lean`,
  `HalfTurnGain.lean`, and `ClockedDoubleBufferUpdate.lean` derive the
  actual compute/copy update estimate from component ODEs and clock
  dynamics, with no bound on the temporary buffer's initial value. The
  hypothesis that the real transition map agrees with a nonexpansive map
  along the compute segment is explicit. `DoubleBufferBudget.lean` and
  `ClockedBudget.lean` derive the ordinary and productive one-sided budget
  inequalities from actual component ODEs. `HeldBufferMotion.lean` and
  `DoubleBufferReset.lean` derive a clean reset from a held-label event.
  `TransitionGates.lean`, `RegisterTransition.lean`,
  `RegisterLocalBranches.lean`, and `RegisterTransitionExactness.lean`
  construct the real transition map, prove its local nonexpansive
  branches on the stated regular neighborhoods, and prove exact
  agreement with literal register instructions, exhausted countdown,
  reset, and halt. `RegisterTransitionFormula.lean` gives explicit
  absolute-value formulas for every coordinate of this map, proves their
  evaluations, and proves input-independent erased shape and resources.
  `RegisterRestart.lean`, `RegisterRestartNonhalting.lean`, and
  `RegisterRestartEmbedding.lean` define actual restart steps and runs,
  prove a uniform reset-count bound from halting, and prove unbounded
  reset counts along the designated nonhalting orbit. The real map
  agrees with every embedded discrete step and iterate. The resulting
  equivalence is for natural budgets and integer countdowns, not for
  arbitrary real states or the continuous monitor.
  `FundedRealRun.lean` tracks genuinely funded real countdowns and proves
  that a sufficiently funded clean reset reaches a fixed halted state.
  It does not assert honest tracking after fractional countdown exhaustion.
  `ClockedMonitor.lean` and `ClockedMonitorFormula.lean` construct the actual
  gated two-buffer field/output and its exact formula family, with
  input-independent erased syntax. `ClockedMonitorDynamics.lean` derives
  update/reset bounds from this actual vector ODE. Positive actual output
  yields the amplitude and label restrictions used in its reset theorem.
  `FormulaLocalExistence.lean` proves local Lipschitz regularity and genuine
  local solutions, without treating absolute-value formulas as C¹.
  `OscillatorPhase.lean` supplies phase alignment on a full supplied period;
  `MonitorPhaseBounds.lean` bounds arbitrary partial compute/copy segments
  using the constructed transition map. Its uniform bound is chosen before
  the solution segment. `OscillatorPartition.lean` constructs a clipped
  half-turn partition from arbitrary initial oscillator data, without
  assuming future existence. `MonitorFiniteBounds.lean` uses a finite
  recurrence to give a uniform full-state bound chosen from time-horizon,
  initial-norm, and forcing-mass caps before the trajectory.
  `BoundedContinuation.lean` constructs finite-horizon solutions by a
  compact Lipschitz cutoff and first-exit contradiction, then patches them
  by uniqueness. `MonitorCompleteness.lean` applies it to prove actual
  forward completeness of the unsmoothed monitor from every real state.
  `SmoothedMonitorCompleteness.lean` proves the same for its actual shared-
  precision smoothing: clock and oscillator equations remain exact, and
  the actual buffer residual has total mass less than `ε*pi` on every
  finite segment. `LiftedMonitorExistence.lean` constructs global rational
  trajectories from every canonical graph point, including the one-sided
  derivative at time zero. No off-graph or time-accelerated completeness
  is claimed.
  `FundedMonitorTracking.lean` now derives finite robust tracking for clean
  funded real attempts, discharging the actual local nonexpansive branches.
  `HaltingMonitorTracking.lean` extends tracking arbitrarily far after a
  funded source halt and proves zero actual output throughout every complete
  post-halt turn. Initial error at most `1/16`, forcing mass at most `1/256`,
  aligned phase, and squared amplitude above `1/2` are explicit hypotheses.
  `MonitorEvents.lean` and `MonitorEventBound.lean` instantiate the restart
  count argument with actual positive-output events. If the source halts
  after `T` instructions and whole-segment forcing mass is at most `1/256`,
  at most `T+1` complete aligned turns have positive output, uniformly over
  arbitrary initial buffers. An event itself supplies the needed amplitude
  condition. `MonitorOutputIntegral.lean` handles arbitrary phase and
  truncated endpoint turns. `MonitorForcingIntegral.lean` uses IVT cuts
  of the actual cumulative forcing integral to prove the uniform bound
  `∫o ≤ 4*pi*(T+3)*(256*forcingMass+2)` for arbitrary continuous forcing.
  `IntegerMonitorTracking.lean` proves actual local branches and continuous
  tracking of the embedded integer restart orbit.
  `ResetTurnOutput.lean` proves output integral 2 on each reference reset
  compute half-turn. `NonhaltingMonitorOutput.lean` combines unbounded
  reset counts with actual smoothed completeness to obtain a global
  nonhalting witness. `NonhaltingLiftedOutput.lean` lifts it to a genuine
  rational trajectory with unbounded finite penalized-output integrals,
  for `0 < ε ≤ 1/1024`.
  `FormulaSmoothing.lean` proves Lemma 5.1's explicit polynomial majorant
  construction and semantic bounds; `FormulaResources.lean` bounds the
  majorant degrees and radical counts independently of the values of the
  constants. `FormulaPrecision.lean` constructs one rational polynomial
  precision for a finite family, proves its shape-dependent degree bound,
  and derives each error bound `ε/(1+clock²)`. `FormulaSmoothness.lean`
  proves that the resulting family is globally smooth.
  `SmoothingPerturbation.lean` bounds the actual vector error in the finite
  sup norm, proves its finite-forward-interval norm integral is less than
  `ε*pi` along a unit-speed clock curve, and proves integrability and the
  nonstrict total bound on the full forward ray. `FormulaTemplate.lean`
  and `FormulaPrecisionCode.lean` supply raw-code primitive recursiveness.
  These reusable smoothing modules feed the monitor-correctness proof;
  they do not by themselves assert the full halting reduction.
  `PowerFraction.lean` constructs common-power-denominator arithmetic and
  the exact polynomial radicand for one smoothing node, proving the
  radicand is at least one. `RadicalProgram.lean`, `FormulaRadicals.lean`,
  and `FormulaRadicalFamily.lean` now construct the shared triangular
  program and prove correctness of its actual sequential evaluator for
  every output. Its length is exactly the sum of absolute-value counts;
  every radicand is at least one at every extended real state.
  `FormulaRadicalResources.lean` bounds all numerator and radicand degrees
  independently of coefficient values. `RadicalFiniteCoordinates.lean`
  explicitly restricts bounded natural root indices to finite coordinates,
  preserving evaluation and degree, including an empty root range.
  `FiniteRadicalFamily.lean` assembles the actual finite polynomial tuple
  and its computed root graph. `RadicalSmoothness.lean` proves global
  smoothness of the canonical root and fourth-root graphs, using the
  constructed radicands' strict positivity.
  `RadicalLiftPolynomials.lean` performs the literal root-square
  polynomial substitution and proves the canonical quartic equations
  and globally positive radicands. `PolynomialCurveDerivative.lean`
  supplies the formal-partial-derivative chain rule on arbitrary finite
  coordinate types. `PolynomialFraction.lean` and
  `RationalDirectionalDerivative.lean` construct uncancelled rational
  arithmetic and directional derivatives. `RadicalDependencies.lean`
  derives the actual compiler's finite triangularity and zero later partials.
  `TriangularLift.lean` recursively constructs every auxiliary velocity and
  proves its full directional-derivative equation and denominator bound.
  `TriangularLiftInvariant.lean` proves smoothness and preservation of
  quartic constraints along actual vector-field solution segments.
  `CompiledFormulaLift.lean` instantiates these properties with the actual
  compiled family, proving base-value agreement on the canonical graph.
  `TriangularLiftTangent.lean` proves tangent uniqueness from differentiated
  quartics; `CompiledGraphTrajectory.lean` uses it to lift an actual smoothed
  base trajectory to the actual rational field. It constructs the positive
  graph through the evaluator and does not assume a lifted solution.
  `FormulaFamilyList.lean` preserves original positions under a fixed finite
  ordering. `ClockedMonitorLift.lean` applies the compiler to the actual
  shared monitor field/output family and precision, proving denominator
  bounds, smoothness, and exact graph trajectory transfer.
  `ClockedMonitorResources.lean` proves input-independent precision and
  finite-radicand degree bounds and the exact auxiliary count.
  `PositiveDenominatorClearing.lean` constructs a common positive product
  denominator, literal cleared polynomials, and degree bounds. Its algebraic
  value identity feeds the finite-curve time-change and penalized-output
  theorems in `PolynomialMonitorCriterion.lean`.
  `PolynomialFractionResources.lean`, `TriangularLiftResources.lean`,
  `CompiledLiftResources.lean`, and `ClockedMonitorClearing.lean` bound the
  actual stored numerator/denominator degrees and the joint field/output
  clearing degrees independently of input and precision coefficient.
  `RadicalInvariant.lean` proves conservation of `w^4/D` from the scalar
  lift equation, preservation of exact constraints, selection of the
  nonnegative square-root branch, and the elementary defect estimates.
  `PolynomialEnvelope.lean` and `PolynomialDifferenceBounds.lean` give
  coefficient-mass cube bounds and coordinatewise polynomial difference
  bounds. `RadicalMajorant.lean` constructs global polynomial bounds on
  the actual canonical roots, using only earlier roots at each step.
  `RadicalComparison.lean`, `TriangularErrorWeights.lean`, and
  `RadicalDefectBounds.lean` construct nonnegative polynomial weights and
  prove global root/output errors bounded by those weights times the
  Euclidean quartic-defect norm. No small-error or graph-neighborhood
  hypothesis is present. Their resource modules give coefficient-independent
  degree bounds, including empty root systems and degree zero.
  `CompiledFormulaError.lean` instantiates one common error weight with the
  actual compiler. `CompiledPolynomialFormula.lean` proves that abs-free
  formulas remain exact under arbitrary root assignments.
  `ClockedMonitorLiftError.lean` obtains actual monitor error bounds and exact
  clock/oscillator equations off graph. `ClockedMonitorPenalty.lean` constructs
  the actual polynomial penalty `(1+clock²) W² Σ R_j²`, proves its
  nonnegativity, and proves that the penalized rational output agrees with
  the smoothed output on the constructed canonical graph. The output
  denominator is unchanged. `ClockedMonitorPenaltyResources.lean` bounds
  the actual error weight, defect energy, penalty, and stored penalized
  fraction degrees independently of input and precision coefficient.
  The reusable raw-code weight layer is now checked:
  `PolynomialWeightCode.lean`, `TriangularWeightCode.lean`,
  `RadicalMajorantCode.lean`, `RadicalComparisonCode.lean`,
  `PolynomialDefectCode.lean`, and `PolynomialErrorWeightCode.lean`
  compile the literal majorants, triangular comparison weights, quartic
  defects, and penalty. Their primitive-recursive operations decode to
  the stated polynomials, including empty root families. The exact degree
  and coefficient-mass computations account for canceled terms. The
  specialization to the actual monitor is checked in
  `ClockedMonitorPenaltyCode.lean` and `ClockedMonitorRationalCode.lean`.
  `ClockedMonitorPolynomialCode.lean` clears the original field/output
  family once and subtracts the common multiplier times the penalty.
  `QuadraticPenalty.lean` proves the finite-segment uniform
  upper integral bound for a linear error cost minus its clock-weighted
  quadratic penalty. `ClockedMonitorLiftForcing.lean` identifies the actual
  off-graph projection as a forced monitor, with forcing and output errors
  bounded by the smoothing tail plus weighted defect.
  `ClockedMonitorLiftIntegral.lean` bounds the resulting actual forcing
  mass and projected output. `PenalizedMonitorIntegral.lean` absorbs the
  linear defect cost by the actual quadratic penalty and obtains one bound
  for every finite rational solution segment, with no state or time cap.
  Finally, `RationalMonitorCriterion.halts_iff_bounded_penalizedOutput`
  proves halting iff `HasBoundedFiniteOutput` for the actual rational field
  and output, for `0 < ε ≤ 1/1024`. The predicate quantifies over every
  finite continuous solution segment and does not require off-graph
  completeness. This exact rational-monitor criterion feeds the polynomial
  and homogeneous stability reductions described above.
- **Exact supporting computation, compiled**:
  `Stability/Computability/RegisterMachine.lean` defines actual finite
  increment/decrement programs and proves absorbing halt, compatibility
  with Mathlib's partial evaluator, and clear/transfer macros with exact
  step counts and preservation of other registers.
  `RegisterMachineArithmetic.lean` adds base-numeral stack encodings,
  literal-instruction push/pop and division macros, exact step counts,
  and scratch-register cleanup. `RegisterMachineStackBlocks.lean` and
  `RegisterMachineDispatch.lean` allocate actual finite blocks and store
  dispatch tables. They simulate literal Mathlib push/pop instructions
  on its four stacks, using five natural registers; runtime store is
  encoded in the control label, not in a runtime-dependent program.
  `RegisterMachinePeek.lean` adds literal peek semantics while restoring
  all stacks and preserving the old store for the requested update.
  `RegisterMachineEmbedding.lean` proves arbitrary cyclic wiring from
  local instruction equations, with no supplied simulation relation.
  `RegisterMachineStatement.lean` compiles all seven constructors of
  Mathlib's actual stack-statement syntax, allocates both branch arms,
  and proves positive finite execution to the exact `TM2.stepAux`
  result while leaving the external destination instruction unexecuted.
  `RegisterMachineFinite.lean` assembles the complete finite cyclic program,
  computing its block width internally and proving actual halting equivalence.
  `UniversalMachineSource.lean` derives one fixed finite-control-support
  stack-machine interpreter from Mathlib's universal evaluator and proves
  a primitive-recursive input reduction preserving `HGAS.UniversalHalts`.
  Its halting language is SigmaOneComplete. `RegisterMachineSupport.lean`
  restricts the reachable control labels to that finite support, and
  `RegisterMachineInput.lean` primitive-recursively encodes the actual binary
  input stack. `RegisterMachineUniversal.lean` composes the literal compiler
  to obtain one fixed finite five-register INC/DEC program and a primitive-
  recursive reduction from `HGAS.UniversalHalts` to its ordinary input-register
  halting language. `RegisterMachineComputability.lean` proves primitive-
  recursive steps/runs and RE membership for every raw input. Consequently
  this fixed register program's halting language is SigmaOneComplete. No
  universality or semantic-simulation hypothesis is supplied.

The source paper and earlier implementation are linked in the README.
The companion records the provenance of the proof-based implementation. New source files retain
the same no-project-axiom/no-placeholder trust policy. The completed source
reduction discharges the original HLS source-hardness assumption without
changing the preserved conditional transfer theorems.
The new explanations are in `docs/stability_formalization_companion.tex` and
its rendered PDF. `scripts/StabilityAxiomAudit.lean` audits the completed
stability endpoints separately from the preserved release audit.

Final validation (2026-10-31): `lake build Stability` passes
(4,913 jobs), as does `StabilityRegression.lean`. All 454 declarations
reported by the stability axiom audit and all 29 preserved release-audit
declarations depend only on subsets of `propext`, `Classical.choice`, and
`Quot.sound`. The new audit also rejects axiom declarations under `Stability`
or `HGAS` in the loaded public-root environment; none are present.
All 251 new modules belong to the transitive `Stability.lean` import closure,
with no orphan modules or missing project imports. The preserved source
and pinned-environment diff against `81276ab` is empty;
`lake build HGAS` passes (4,713 jobs), and the 837-module import-closure/catalog
check passes. The companion PDF has 33 pages and compiles without missing
references or overfull boxes. These checks certify the scoped results above.
Publication history is recorded by the repository's commits and release tags.

The independent semantic checks include the all-state halting estimate,
the rational and polynomial monitor criteria, and the full nonhalting
output chain. The latter constructs a designated global smoothed trajectory,
gets two units of actual output per tracked reset turn, and lifts it to the
zero-penalty rational graph. It uses unbounded finite integrals, not a
default-valued improper integral. Finite time changes, endpoint uniqueness,
central-chart identities, and the actual-coefficient Fourier algebra have
also been read against their stated hypotheses. These checks are in addition
to kernel compilation. The completed raw-code compiler and final HLS
composition have also received independent statement and semantic audits.

The mathematical language is

```lean
HGASQ n d : PolynomialFieldCode n → Prop
```

from `HGAS/Computability/HGASLanguage.lean`.  Its inputs are finite rational
codes for polynomial vector fields on `ℝⁿ`, and syntactic homogeneity of
the requested degree is part of the language definition.

The corresponding homogeneous Lyapunov-stability language is

```lean
HLSQ n d : PolynomialFieldCode n → Prop
```

from `HGAS/Stability/KordaLyapunov.lean`. Invalid homogeneity codes are
negative instances for both languages.

## Headline theorems

The final endpoint is
`HGAS/Arithmetic/NormalizedCorrectedAugmentedEffectiveFamily.lean`, which is
imported by the public root `HGAS.lean`.

It defines three fixed natural-number expressions:

```lean
HGAS.NormalizedCorrectedAugmentedEffectiveFamily.fixedDimension
HGAS.NormalizedCorrectedAugmentedEffectiveFamily.fixedDegree
HGAS.NormalizedCorrectedAugmentedEffectiveFamily.cofinalDimensionThreshold
```

and proves:

```lean
fixedPair_sigmaOneComplete :
  SigmaOneComplete (HGASQ fixedDimension fixedDegree)

fixedPair_not_computable :
  ¬ ComputablePred (HGASQ fixedDimension fixedDegree)

fixedPair_complement_not_re :
  ¬ REPred (fun code ↦ ¬ HGASQ fixedDimension fixedDegree code)

fixedDimension_pos :
  0 < fixedDimension

fixedDegree_odd :
  Odd fixedDegree

fixedDegree_ge_three :
  3 ≤ fixedDegree

cofinal_sigmaOneComplete
    (N d : ℕ)
    (hN : cofinalDimensionThreshold ≤ N)
    (hd : Odd d)
    (hthree : 3 ≤ d) :
  SigmaOneComplete (HGASQ N d)

cubic_sigmaOneComplete
    (N : ℕ)
    (hN : cofinalDimensionThreshold ≤ N) :
  SigmaOneComplete (HGASQ N 3)

cubic_not_computable
    (N : ℕ)
    (hN : cofinalDimensionThreshold ≤ N) :
  ¬ ComputablePred (HGASQ N 3)

cubic_complement_not_re
    (N : ℕ)
    (hN : cofinalDimensionThreshold ≤ N) :
  ¬ REPred (fun code ↦ ¬ HGASQ N 3 code)
```

Thus the formalization proves:

1. `Σ⁰₁`-completeness, and hence undecidability, for one fixed dimension
   and one fixed odd degree;
2. `Σ⁰₁`-completeness for every fixed odd degree at least three in every
   dimension beyond one fixed threshold; and
3. in particular, `Σ⁰₁`-completeness of cubic homogeneous GAS in every
   sufficiently large fixed dimension.

These are unconditional Lean theorems: the endpoint takes no unproved
classification proposition, compiler certificate, or semantic gap as a
hypothesis.

## HLS and common cubicization theorems

The additive endpoint is
`HGAS/Propagation/CofinalLyapunovReduction.lean`, supported by the new
stability, Veronese, and computability modules listed below. For fixed
`n >= 2` and `k >= 1`, it proves:

```lean
hlsQ_manyOneReducible_cubic :
  HLSQ n (2 * k + 1) ≤₀
    HLSQ (cubicLiftCodeDimension n k) 3

exists_computable_cubicization :
  ∃ f, Computable f ∧
    ∀ F,
      (HGASQ n (2 * k + 1) F ↔
        HGASQ (cubicLiftCodeDimension n k) 3 (f F)) ∧
      (HLSQ n (2 * k + 1) F ↔
        HLSQ (cubicLiftCodeDimension n k) 3 (f F))
```

Thus one fixed-parameter code map preserves both properties. The theorem
`hlsQ_manyOneReducible_cofinalFixedPair` composes this map with dimension
and odd-degree padding to obtain

```lean
HLSQ n (2 * k + 1) ≤₀ HLSQ N d
```

whenever `cubicLiftCodeDimension n k <= N`, `Odd d`, and `3 <= d`.

The semantic core is unconditional. In particular, the extension proves

```lean
sourceLS_iff_stabilizedCubicLS
```

for every homogeneous source field of degree `2*k+1` with `k >= 1`. The
raw-code compiler's additional `n >= 2` hypothesis is needed only for its
explicit malformed-code fallback.

The exported cofinal HLS consequences have two deliberately separate
forms:

- `hlsQ_manyOneHard_cofinal_of_source` transfers `ManyOneHard` from a fixed
  source language and derives target hardness, undecidability, and a
  non-c.e. complement; and
- `hlsQ_not_computable_cofinal_of_source` transfers noncomputability alone.

Both preserved transfer theorems are **conditional**: source hardness is
represented by the explicit hypothesis `hsource`. The new
`Stability.Computability.UniversalStabilityReduction` proves the source
result by a checked register-machine reduction and applies these transfer
theorems. Its fixed cubic and cofinal HLS hardness endpoints are therefore
unconditional.

## What is not claimed

The present result does **not** settle `HGASQ 3 3`.

In particular:

- `fixedDimension` is not proved equal to `3`;
- `fixedDegree` is proved odd and at least three, but is not proved equal
  to `3`;
- `cubic_sigmaOneComplete` requires
  `cofinalDimensionThreshold ≤ N`; and
- there is no theorem establishing
  `cofinalDimensionThreshold ≤ 3`.

Consequently, this development proves neither decidability nor
`Σ⁰₁`-hardness for the specific three-dimensional cubic language
`HGASQ 3 3`.  That low-dimensional problem remains separate from the
completed cofinal theorem.

The word “cofinal” is important: the cubic result applies to every
*sufficiently large* fixed dimension, not to every positive dimension.

The repository also does not claim:

- a common raw-code GAS/HLS compiler in source dimension `n = 1`;
- one cubic compiler computable uniformly while `(n,k)` varies;
- an evaluable numerical value for the chosen shadow gain or cofinal
  threshold;
- a maximal-solution API theorem equating the paper's wording with Lean's
  global-forward-trajectory representation;
- a verbatim `Q`-norm version of the printed finite-horizon shadowing
  proposition;
- formalizations of normal forms (iii) and (iv), the even-degree and
  linear-field lemmas, or the separate literature corollary concerning GAS
  and forward completeness.

The degree-input and joint dimension-and-odd-degree-input results, together
with the unconditional HLS source reduction, are now formalized in
`Stability`. Coverage of the full variable-resource corollary remains partial.

The GAS-only cubic compiler covers every positive source dimension. The
semantic HLS preservation theorem also has no `n >= 2` restriction; only
the bundled raw-code theorem has that restriction.

## Trust and build status

The project is pinned to Lean/Mathlib 4.30.0 and uses:

```toml
warningAsError = true
```

The authoritative full build is:

```bash
lake build HGAS Stability
```

It succeeds for both public roots. The preserved `HGAS` tree has 837 modules:
796 in the `HGAS.lean` closure and 41 independently elaborated modules
outside that root. All 251 `Stability` modules belong to its public closure,
which also uses items 33 and 35 of the HGAS legacy catalog.

The source audit

```bash
rg -n '(^|[^A-Za-z])(sorry|admit)\b|^\s*axiom\b|^\s*unsafe\b' \
  HGAS HGAS.lean Stability Stability.lean --glob '*.lean'
```

finds no proof placeholder, project axiom declaration, or unsafe
declaration.  Incidental English words such as “admit” or “axiom-free” in
module comments are not declarations.

Direct `#print axioms` checks on

```text
NormalizedCorrectedAugmentedEffectiveFamily.gap
NormalizedCorrectedAugmentedEffectiveFamily.family
NormalizedCorrectedAugmentedEffectiveFamily.fixedPair_sigmaOneComplete
NormalizedCorrectedAugmentedEffectiveFamily.fixedPair_not_computable
NormalizedCorrectedAugmentedEffectiveFamily.fixedPair_complement_not_re
NormalizedCorrectedAugmentedEffectiveFamily.cofinal_sigmaOneComplete
NormalizedCorrectedAugmentedEffectiveFamily.cubic_sigmaOneComplete
NormalizedCorrectedAugmentedEffectiveFamily.cubic_not_computable
NormalizedCorrectedAugmentedEffectiveFamily.cubic_complement_not_re
HGAS.lyapunovStableWithExistence_iff_uniformLinearTrajectoryBound
HGAS.lyapunovStableWithExistence_iff_boundedEuclideanAngularCocycle
HGAS.Veronese.exists_finiteHorizonOrbitShadowing
HGAS.Veronese.exists_finiteHorizonShadowing
HGAS.Veronese.sourceLS_iff_stabilizedCubicLS
HGAS.Veronese.effectiveCubicLSReductionCode_hgasQ_iff
HGAS.Propagation.effectiveCubicLSReductionCode_hlsQ_iff
HGAS.Propagation.exists_computable_cubicization
HGAS.Propagation.hlsQ_manyOneHard_cofinal_of_source
HGAS.Propagation.hlsQ_not_computable_cofinal_of_source
```

report only:

```text
propext
Classical.choice
Quot.sound
```

These are the ordinary Lean/Mathlib logical foundations used by the
development. No project-defined axiom appears in the dependency closure of
the headline GAS or HLS results. The occurrence of `Classical.choice`
records nonconstructive existence choices; it is not a project axiom.

## Fixed constants and the meaning of computability

The fixed universal Diophantine representation is selected from a proved
MRDP existence theorem.  In particular,
`UniversalHalting.unconditionalUniversalHaltingRepresentation` is a
`noncomputable def`: classical choice selects one finite representative
once and for all.

As a consequence, the following are fixed closed natural-number
expressions in Lean but are not currently reducible numerical literals:

- the universal DQL equation and variable counts;
- the augmented source dimension;
- the fixed wrapper and output degrees; and
- the cofinal cubic dimension threshold.

The formalization proves `Computable` for the specialization and source-code
maps in Mathlib's recursion-theoretic sense.  This is exactly the
effectivity required for a many-one reduction: there exists a Turing
computation of the finite output code, uniformly in the input, after the
once-and-for-all fixed representation has been selected.

It does **not** follow that Lean can presently evaluate

```lean
#eval HGAS.NormalizedCorrectedAugmentedUniversalResources.sourceCode 0
```

to a concrete printed list.  The current definitions retain the classical
choice of the universal polynomial and its dimensions, so that expression
depends on noncomputable constants.  No numerical value for
`fixedDimension`, `fixedDegree`, or `cofinalDimensionThreshold` is claimed.
This extraction caveat does not weaken the proved `Computable` maps or the
many-one reductions.

The shadow-gain compiler has a parallel fixed-parameter qualification. For
each fixed `(n,k)`, `fixedCubicShadowGainParameters` selects a natural gain
by classical choice, and `effectiveCubicLSReductionCode_primrec` proves that
the resulting map is primitive recursive in the input field code. Lean
therefore proves existence of a computable reduction for each fixed pair.
It does not provide one algorithm uniform in varying `(n,k)`, and the
selected gain need not reduce to a printed numeral.

## End-to-end theorem/module crosswalk

Every row in the first table is complete (`[x]`) on the dependency path of
the headline GAS theorem.

| Stage | Principal declaration | Module | Status |
|---|---|---|---|
| Rational fixed-pair GAS language | `HGASQ` | `HGAS/Computability/HGASLanguage.lean` | `[x]` |
| Homogeneous angular characterization | `globallyAsymptoticallyStable_iff_maximalAngularAverage_neg` | `HGAS/Wrapper/AngularAverageGAS.lean` | `[x]` |
| Odd-degree c.e. upper bound | `hgasQ_re_of_oddDegree` | `HGAS/Lyapunov/RationalHomogeneousConverse.lean` | `[x]` |
| Primitive-recursive MRDP closure | `UniversalHalting.binaryPrimitiveRecursiveRelationsAreDiophantine` | `HGAS/Arithmetic/UnconditionalMRDP.lean` | `[x]` |
| Fixed-arity DQL source | `UniversalHalting.unconditionalUniversalHaltingFixedDQL_solvable_iff` | `HGAS/Arithmetic/UnconditionalFixedDQL.lean` | `[x]` |
| Fixed-DQL `Σ⁰₁`-completeness | `UniversalHalting.unconditionalFixedDQLSolvability_sigmaOneComplete` | `HGAS/Arithmetic/UnconditionalFixedDQL.lean` | `[x]` |
| Solvability-preserving linear-column repair | `DQLNonzeroLinearAugmentation.augment_solvable_iff` | `HGAS/Arithmetic/DQLNonzeroLinearAugmentation.lean` | `[x]` |
| Nonzero linear column in every augmented variable | `DQLNonzeroLinearAugmentation.augment_hasNonzeroLinearColumn` | `HGAS/Arithmetic/DQLNonzeroLinearAugmentation.lean` | `[x]` |
| Effective augmentation | `DQLNonzeroLinearAugmentation.augment_computable` | `HGAS/Arithmetic/DQLNonzeroLinearAugmentation.lean` | `[x]` |
| Augmented universal semantics | `UniversalHalting.augmentedUniversalHaltingFixedDQL_solvable_iff` | `HGAS/Arithmetic/NormalizedCorrectedAugmentedUniversalResources.lean` | `[x]` |
| Fixed augmented dimensions and degrees | `NormalizedCorrectedAugmentedUniversalResources.instance_wrapperDegree_eq` | `HGAS/Arithmetic/NormalizedCorrectedAugmentedUniversalResources.lean` | `[x]` |
| Computable normalized source syntax | `NormalizedCorrectedAugmentedUniversalResources.sourceCode_computable` | `HGAS/Arithmetic/NormalizedCorrectedAugmentedUniversalResources.lean` | `[x]` |
| Canonical theta output on every selected orbit | `NormalizedCorrectedEffectiveCanonicalThetaOutputs.hasCanonicalThetaOutputs` | `HGAS/Arithmetic/NormalizedCorrectedEffectiveCanonicalThetaOutputs.lean` | `[x]` |
| No-instance positive finite graph | `NormalizedCorrectedEffectiveNoInstanceFiniteGraph.finite_graph` | `HGAS/Arithmetic/NormalizedCorrectedEffectiveNoInstanceFiniteGraph.lean` | `[x]` |
| Solvable-instance nonzero drift mean | `NormalizedCorrectedEffectiveNonzeroMeanFromTheta.not_conditionalBaseDriftZero_of_solvable` | `HGAS/Arithmetic/NormalizedCorrectedEffectiveNonzeroMeanFromTheta.lean` | `[x]` |
| Two-sided semantic gap | `NormalizedCorrectedEffectiveGapFromCanonicalTheta.gapOfCanonicalThetaOutputs` | `HGAS/Arithmetic/NormalizedCorrectedEffectiveGapFromCanonicalTheta.lean` | `[x]` |
| Literal source-code/certificate equality | `NormalizedCorrectedAugmentedFamilyFromGap.sourceCode_eq_certificateOfGap` | `HGAS/Arithmetic/NormalizedCorrectedAugmentedFamilyFromGap.lean` | `[x]` |
| Fixed-resource family from gaps | `NormalizedCorrectedAugmentedFamilyFromGap.familyOfGaps` | `HGAS/Arithmetic/NormalizedCorrectedAugmentedFamilyFromGap.lean` | `[x]` |
| Exact compiled correctness | `Compiler.FixedUniversalDQLCompactSignSourceFamily.hgasQ_output_iff_predicate` | `HGAS/Compiler/FixedUniversalDQLCompactSignSourceFamily.lean` | `[x]` |
| Generic fixed-pair completeness | `Compiler.FixedUniversalDQLCompactSignSourceFamily.fixedPair_sigmaOneComplete` | `HGAS/Compiler/FixedUniversalDQLCompactSignSourceFamily.lean` | `[x]` |
| Generic cofinal propagation | `Compiler.FixedUniversalDQLCompactSignSourceFamily.cofinal_sigmaOneComplete` | `HGAS/Compiler/FixedUniversalDQLCompactSignSourceFamily.lean` | `[x]` |
| Unconditional semantic gap | `NormalizedCorrectedAugmentedEffectiveFamily.gap` | `HGAS/Arithmetic/NormalizedCorrectedAugmentedEffectiveFamily.lean` | `[x]` |
| Unconditional computable family | `NormalizedCorrectedAugmentedEffectiveFamily.family` | `HGAS/Arithmetic/NormalizedCorrectedAugmentedEffectiveFamily.lean` | `[x]` |
| Final fixed-pair theorem | `NormalizedCorrectedAugmentedEffectiveFamily.fixedPair_sigmaOneComplete` | `HGAS/Arithmetic/NormalizedCorrectedAugmentedEffectiveFamily.lean` | `[x]` |
| Fixed-pair complement is not c.e. | `NormalizedCorrectedAugmentedEffectiveFamily.fixedPair_complement_not_re` | `HGAS/Arithmetic/NormalizedCorrectedAugmentedEffectiveFamily.lean` | `[x]` |
| Final cofinal odd-degree theorem | `NormalizedCorrectedAugmentedEffectiveFamily.cofinal_sigmaOneComplete` | `HGAS/Arithmetic/NormalizedCorrectedAugmentedEffectiveFamily.lean` | `[x]` |
| Final sufficiently-large-dimension cubic theorem | `NormalizedCorrectedAugmentedEffectiveFamily.cubic_sigmaOneComplete` | `HGAS/Arithmetic/NormalizedCorrectedAugmentedEffectiveFamily.lean` | `[x]` |
| Cofinal cubic complement is not c.e. | `NormalizedCorrectedAugmentedEffectiveFamily.cubic_complement_not_re` | `HGAS/Arithmetic/NormalizedCorrectedAugmentedEffectiveFamily.lean` | `[x]` |

The HLS extension is a strict additive layer. All 13 modules in the next
table lie in the public import closure; every preceding `HGAS/` module is
unchanged.

| Stage | Principal declaration or role | Module | Status |
|---|---|---|---|
| Nonvacuous HLS predicate and code language | `LyapunovStableWithExistence`, `HLSQ` | `HGAS/Stability/KordaLyapunov.lean` | `[x]` |
| Uniform linear bound | `lyapunovStableWithExistence_iff_uniformLinearTrajectoryBound` | `HGAS/Stability/KordaLyapunov.lean` | `[x]` |
| Euclidean angular criterion | `lyapunovStableWithExistence_iff_boundedEuclideanAngularCocycle` | `HGAS/Stability/AngularLyapunov.lean` | `[x]` |
| Angular-field congruence | `lyapunovStableWithExistence_iff_of_eqOn_sphere` | `HGAS/Stability/AngularCongruence.lean` | `[x]` |
| Linear conjugacy | `lyapunovStableWithExistence_conjugateField_iff` | `HGAS/Stability/LinearConjugacyLyapunov.lean` | `[x]` |
| HLS product, dimension, and degree padding | `degreeDimensionPadCode_hlsQ_iff_of_homogeneous` | `HGAS/Stability/PaddingLyapunov.lean` | `[x]` |
| Source and weighted angular criteria | `lyapunovStableWithExistence_iff_boundedWeightedAngularCocycle` | `HGAS/Veronese/LyapunovAngularCriteria.lean` | `[x]` |
| Distance to the Veronese cone | `exists_coneDistanceSq_le_energy` | `HGAS/Veronese/ConeDistance.lean` | `[x]` |
| Decay and Lipschitz preliminaries | shadowing estimates and cone invariance | `HGAS/Veronese/ShadowingPrelims.lean` | `[x]` |
| Shadowing parameter package | `CubicLiftShadowingBounds` | `HGAS/Veronese/CubicLiftShadowingBounds.lean` | `[x]` |
| Finite-horizon shadowing and semantic HLS preservation | `exists_finiteHorizonOrbitShadowing`, `exists_finiteHorizonShadowing`, `sourceLS_iff_stabilizedCubicLS` | `HGAS/Veronese/CubicLiftLyapunovConjugacy.lean` | `[x]` |
| Generic hardness transfers | `ManyOneHard` and its consequences | `HGAS/Computability/ManyOneHard.lean` | `[x]` |
| Fixed-parameter effective gain and common compiler | `effectiveCubicLSReductionCode_primrec`, code-level GAS/HLS correctness | `HGAS/Computability/CubicLiftEffectiveShadowGain.lean` | `[x]` |
| Cubic/cofinal HLS reductions | `exists_computable_cubicization`, `hlsQ_manyOneReducible_cofinalFixedPair` | `HGAS/Propagation/CofinalLyapunovReduction.lean` | `[x]` |

## Paper-to-Lean scope matrix

This table records what the repository verifies literally. It avoids the
stronger and inaccurate claim that every printed intermediate lemma is
formalized verbatim.

| Manuscript result or ingredient | Status | Qualification |
|---|---|---|
| Main cofinal and fixed-pair GAS theorems | **Exact** | Unconditional statements about raw rational field codes |
| Cubic GAS consequence | **Exact** | Every dimension beyond the symbolic fixed threshold |
| GAS angular criterion | **Exact for the Euclidean form** | Negativity of the maximal invariant angular average on the Euclidean unit sphere |
| Odd-degree c.e. upper bound | **Exact statement; alternative proof** | The printed endpoint is proved through finite-grid certificates rather than Tarski elimination |
| Required MRDP input | **Equivalent or alternative** | The universal-halting case needed by the reduction, not the printed arbitrary-r.e.-set theorem verbatim |
| Fixed-resource DQL construction | **Equivalent or alternative** | Exact fixed arities and semantics, but not the paper's affine-right-hand-side form verbatim |
| Homogeneous scaling lemma for HLS | **Equivalent or alternative** | Uses the repository's global-forward-trajectory representation |
| Angular HLS criterion | **Equivalent or alternative** | Uses a bounded-cocycle witness rather than the paper's named optimum |
| GAS cubicization | **Exact** | Code reduction for positive source dimension; fixed-parameter computability |
| Common GAS/HLS cubicization | **Exact** | One raw-code compiler for `n >= 2`, `k >= 1`; fixed-parameter computability |
| Finite-horizon shadowing | **Equivalent or alternative** | Split orbit/cocycle statements in a norm equivalent to the paper's `Q`-norm formulation |
| GAS and HLS degree/dimension padding | **Exact** | Exact code-level equivalences under their stated homogeneity hypotheses |
| HLS cofinal fixed-pair transfer | **Exact** | Source dimension at least two for the raw-code compiler |
| HLS source, cubic, and cofinal hardness | **Exact** | `Stability` proves the halting reduction and discharges `hsource`; hardness, not RE membership |
| Broader ordinary-time trajectory/test equivalence | **Exact** | Stated distinct-prime and nonzero-column hypotheses; arbitrary real growth order at least one |
| Literal graph Fourier/primitive bounds and printed reward gap | **Exact** | Actual Haar coefficients, computable least-denominator gain, and constructed compact graph measure |
| Theta, drift, compactification, and wrapper chain | **Equivalent or alternative** | Distributed formal analogues; exact code-level GAS endpoints |
| Bounded-degree polynomial GAS and LAS hardness | **Exact** | At least cubic degree and sufficiently large fixed dimension; no RE membership claim |
| Compiler uniformity in varying `(n,k)` | **Not formalized** | The proved code maps are computable separately for fixed `(n,k)` |
| Maximal-solution/global-trajectory bridge | **Not formalized** | Polynomial regularity and uniqueness support the representation, but no standalone API theorem is exported |
| Raw degree-input and joint dimension-and-odd-degree-input languages | **Exact, scoped** | Explicit oddness and raw-shape conventions; the joint language admits dimension zero |
| Corollary `cor:variable` | **Partial** | Fixed-degree dimension-input languages are not separately formalized; no literal identification with the full all-degree language |
| Normal forms (iii),(iv) | **Not formalized** | No Lean coverage claimed |
| Even-degree, linear-field, and separate GAS/forward-completeness results | **Not formalized** | No Lean coverage claimed |

## Mathematical dependency chain

### 1. The c.e. upper bound

`HGASQ n d` checks syntactic homogeneity and asks whether the realized
rational polynomial field is globally asymptotically stable at the origin.
For odd `d`,
`HGAS/Lyapunov/RationalHomogeneousConverse.lean` proves
`hgasQ_re_of_oddDegree`: the language is recursively enumerable.  This is
the upper half of every `SigmaOneComplete` endpoint.

The reusable dynamics behind this layer include homogeneous scaling,
forward completeness, invariant measures, uniform negative orbit blocks,
and the maximal invariant angular average.  Their public synthesis is
`globallyAsymptoticallyStable_iff_maximalAngularAverage_neg`.

### 2. Universal halting to one fixed DQL type

`HGAS/Arithmetic/UnconditionalMRDP.lean` closes the formerly parameterized
MRDP interface with
`binaryPrimitiveRecursiveRelationsAreDiophantine`.  The resulting fixed
universal polynomial is compiled to a fixed-row, fixed-variable
quadratic-linear Diophantine system in
`HGAS/Arithmetic/UnconditionalFixedDQL.lean`.

The detector requires every variable to occur in a nonzero linear column.
`DQLNonzeroLinearAugmentation.augment` duplicates every variable and adds
the equations

```text
x_j - y_j = 0.
```

The transformation preserves and reflects integer solvability, makes both
the old and duplicate columns visibly nonzero, and is primitive recursive.
The augmented universal family therefore still represents the same unary
universal-halting predicate with fixed arities.

### 3. Canonical normalized detector

The normalized-corrected compiler combines:

- prime-radical controller clocks;
- physical detector phases;
- canonical theta coefficients;
- a three-moment rigidity argument;
- the DQL detector Fourier series;
- compact source charts; and
- an accumulator drift and reward.

The all-orbit endpoint
`NormalizedCorrectedEffectiveCanonicalThetaOutputs.hasCanonicalThetaOutputs`
uses the nonzero-linear-column property delivered by the augmentation.  It
identifies the selected drift outputs with the required canonical theta
series on every selected bidirectional validity orbit.

The main reusable modules immediately upstream include:

- `HGAS/Arithmetic/NormalizedCorrectedEffectiveColumnFrequencyIrrational.lean`;
- `HGAS/Arithmetic/CanonicalDetectorThetaQuadraticGeometric.lean`;
- `HGAS/Arithmetic/NormalizedCorrectedFixedDetectorThreeMomentTargetOutput.lean`;
- `HGAS/Modular/JacobiThreeMomentTargetRigidity.lean`; and
- `HGAS/Modular/QuadraticGeometricSequence.lean`.

### 4. The two semantic sides of the gap

For a nonsolvable DQL instance,
`NormalizedCorrectedEffectiveNoInstanceFiniteGraph.finite_graph` constructs
an invariant finite graph with a uniform positive reward gap.  Its proof
uses the explicit prime-controller orbit-closure model, the full normalized
drift Fourier expansion, radical small-divisor bounds, the effective
primitive gain, and a positive lower bound for the canonical central chart.

For a solvable instance,
`NormalizedCorrectedEffectiveNonzeroMeanFromTheta.not_conditionalBaseDriftZero_of_solvable`
shows that an ergodic invariant measure with positive finite-interior mass
cannot have every conditional base-drift mean equal to zero.  Otherwise
recurrence supplies a selected bidirectional validity orbit, and its
canonical theta output contradicts the solvable detector mean theorem.

`NormalizedCorrectedEffectiveGapFromCanonicalTheta.gapOfCanonicalThetaOutputs`
joins these branches into the exact
`CanonicalCompactAccumulatorGap` required by the compact accumulator
wrapper.

### 5. The effectivity firewall and homogeneous wrapper

The semantic certificate may contain classically selected invariant
measures and orbit data.  The emitted program must not compute from those
objects.

`NormalizedCorrectedAugmentedFamilyFromGap.familyOfGaps` enforces that
separation:

- semantic certificates prove the GAS equivalence;
- `NormalizedCorrectedAugmentedUniversalResources.sourceCode` supplies the
  finite field and reward syntax;
- `sourceCode_computable` proves the syntax map computable; and
- `sourceCode_eq_certificateOfGap` proves, definitionally, that the emitted
  syntax is exactly the syntax stored in the certificate.

The reusable structure
`Compiler.FixedUniversalDQLCompactSignSourceFamily` then applies the
product-of-spheres homogeneous wrapper and proves
`hgasQ_output_iff_predicate`.  The output is homogeneous at one fixed odd
degree, its code map is computable, and its GAS semantics are exactly the
universal-halting predicate.

### 6. Fixed-pair completeness and cubic propagation

`NormalizedCorrectedAugmentedEffectiveFamily.gap` instantiates the gap for
every augmented universal input.  `family` packages these instances into
the completed fixed-resource family.  The fixed-pair lower bound is
combined with `hgasQ_re_of_oddDegree`, yielding
`fixedPair_sigmaOneComplete`.

The effective Veronese cubic lift and odd-degree/dimension padding are
implemented principally in:

- `HGAS/Computability/CubicLiftEffectiveGain.lean`;
- `HGAS/Computability/CubicLiftCodeCompiler.lean`;
- `HGAS/Propagation/DegreePaddingGAS.lean`;
- `HGAS/Propagation/DegreePaddingCode.lean`;
- `HGAS/Propagation/CofinalFixedPairReduction.lean`; and
- `HGAS/Propagation/CofinalSigmaOne.lean`.

They preserve GAS exactly, preserve finite-code computability, and turn the
one fixed-pair reduction into `cofinal_sigmaOneComplete`.  Specializing the
target degree to `3` gives `cubic_sigmaOneComplete`.

### 7. Homogeneous Lyapunov stability and shadowing

`HGAS/Stability/KordaLyapunov.lean` prevents the trajectory-only stability
predicate from becoming vacuous when solutions blow up. Its
`LyapunovStableWithExistence` predicate requires existence of a global
forward trajectory from every sufficiently small initial state and bounds
every global forward trajectory from that state. Homogeneous scaling gives
`lyapunovStableWithExistence_iff_uniformLinearTrajectoryBound`.

`HGAS/Stability/AngularLyapunov.lean` converts this linear trajectory bound
to boundedness of the Euclidean angular radial cocycle. The Veronese layer
transfers that criterion to the source and weighted target geometries.

The stabilized cubic field contracts the toric penalty away from the
Veronese cone. `exists_finiteHorizonOrbitShadowing` compares each finite
target orbit segment with an orbit on the invariant cone, and
`exists_finiteHorizonShadowing` derives the corresponding radial-cocycle
bound. Together with exact conjugacy on the cone, these estimates prove
`sourceLS_iff_stabilizedCubicLS`.

The exported finite-horizon results are a split, norm-equivalent formal
analogue of the manuscript's one displayed `Q`-norm proposition. They are
the actual results used by the Lean proof; this ledger does not claim that
the printed proposition is exported verbatim.

### 8. Effective common compiler and conditional HLS transfer

`HGAS/Computability/CubicLiftEffectiveShadowGain.lean` selects a sufficient
shadow gain for each fixed `(n,k)` and proves the resulting field-code map
primitive recursive in the input code. Valid codes use the stabilized
cubic lift. Invalid codes map to an explicit unstable homogeneous cubic
field, making the compiler total and preserving negative instances.

`HGAS/Propagation/CofinalLyapunovReduction.lean` instantiates the semantic
theorem rather than assuming it. The resulting
`exists_computable_cubicization` declaration uses the same map for GAS and
HLS. HLS padding then yields the exact cofinal fixed-pair reduction.

In the preserved release, the generic `ManyOneHard` lemmas take source
hardness as the explicit hypothesis `hsource`. They remain unchanged.
The new `Stability` library supplies the checked source reduction and
composes it with these lemmas, so its final HLS hardness endpoints have
no such hypothesis. This does not establish RE membership for HLS.

## Historical interfaces retained in the tree

The development deliberately retains several structures and conditional
theorems that were useful while the proof was assembled.  Examples include
the generic `CanonicalCompactAccumulatorGap`, the older
`FixedUniversalCompactSignSourceFamily`, and named classification
propositions in the modular dynamics directories.

Historically, the first ledger treated inhabitants of these interfaces as
future obligations.  That status is now obsolete for the headline theorem:

- `NormalizedCorrectedAugmentedEffectiveFamily.gap` supplies the required
  semantic gaps unconditionally;
- `NormalizedCorrectedAugmentedEffectiveFamily.family` supplies the actual
  fixed-resource family; and
- the final endpoint's `#print axioms` closure contains no such proposition
  as an assumption.

The old interfaces remain useful abstractions and alternate proof routes;
their continued presence must not be read as an open hypothesis of the
completed augmented endpoint.

The source history is similarly explicit. The HLS release retains all 824
preceding `HGAS/` modules byte for byte and adds 13 public-closure modules.
The original GAS companion is preserved rather than silently rewritten; the
new companion documents the additive layer.

## Reproducibility checklist

From the `lean/` directory:

```bash
# Full warning-as-error project build
lake build HGAS Stability

# Narrow endpoint build
lake build HGAS.Arithmetic.NormalizedCorrectedAugmentedEffectiveFamily
lake build HGAS.Propagation.CofinalLyapunovReduction

# Import-closure and legacy-catalog check
python3 scripts/check_import_closure.py

# Placeholder/project-axiom scan
rg -n '(^|[^A-Za-z])(sorry|admit)\b|^\s*axiom\b|^\s*unsafe\b' \
  HGAS HGAS.lean Stability Stability.lean --glob '*.lean'
```

For trust auditing, run

```bash
lake env lean -DwarningAsError=true scripts/ReleaseAxiomAudit.lean
lake env lean -DwarningAsError=true scripts/StabilityAxiomAudit.lean
lake env lean -DwarningAsError=true scripts/StabilityRegression.lean
```

and inspect every `#print axioms` result. Each audited endpoint must use only
a subset of `[propext, Classical.choice, Quot.sound]`. The printouts require
allowlist inspection; the Stability audit additionally rejects axiom
declarations under the `Stability` or `HGAS` namespaces. The regression
script checks the examples and coding boundary cases.

A release check should also elaborate each of the 41 paths in
`LEGACY_MODULES.md` directly with `-DwarningAsError=true`. The closure script
checks their exact catalog membership; direct elaboration checks that the
files remain valid even though `HGAS.lean` does not import them.
