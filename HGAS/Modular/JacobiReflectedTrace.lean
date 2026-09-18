import HGAS.Modular.JacobiMomentResonance
import Mathlib.Tactic

/-!
# The reflected Bloch branch has the canonical Jacobi trace

The three-moment calculation leaves two possible Bloch classes.  In the
reflected class, the moment equations normalize the complete coefficient
of the `k`-th term to

```
                         g(k) exp(-i k χ),
```

while its remaining temporal phase is

```
                    exp(i (k²-ρk) α).
```

The canonical phase, with `β = ρ α + χ`, is

```
                       exp(i (k² α + k β)).
```

Because the Gaussian coefficient `g` is even, replacing `k` by `-k`
identifies the two terms exactly.  This file records that coefficientwise
identity and reindexes the full infinite sum by the negation equivalence
of `ℤ`.

No convergence hypothesis is required for the reindexing theorem:
topological sums are invariant under equivalence of the index type.  A
separate norm-summability theorem is included for downstream analytic use.
-/

noncomputable section

namespace HGAS.Modular

/-- A unit complex phase written in the same convention as the Cesàro
extraction module. -/
def jacobiUnitPhase (θ : ℝ) : ℂ :=
  HGAS.Analysis.realFrequencyExponential θ 1

@[simp]
theorem norm_jacobiUnitPhase (θ : ℝ) :
    ‖jacobiUnitPhase θ‖ = 1 := by
  exact HGAS.Analysis.norm_realFrequencyExponential θ 1

/-- One term of the canonical two-clock theta trace after substituting
`β = ρ α + χ`. -/
def canonicalJacobiTraceTerm
    (g : ℤ → ℂ) (ρ χ α : ℝ) (k : ℤ) : ℂ :=
  g k * jacobiUnitPhase
    (((k : ℝ) ^ 2) * α +
      (k : ℝ) * (ρ * α + χ))

/-- One term of the normalized reflected branch. -/
def reflectedJacobiTraceTerm
    (g : ℤ → ℂ) (ρ χ α : ℝ) (k : ℤ) : ℂ :=
  g k * jacobiUnitPhase
    (-(k : ℝ) * χ +
      (((k : ℝ) ^ 2) - ρ * (k : ℝ)) * α)

/-- Coefficientwise reflected-branch identity: the reflected `k`-term is
the canonical `-k`-term. -/
theorem reflectedJacobiTraceTerm_eq_canonical_neg
    (g : ℤ → ℂ)
    (hg : ∀ k : ℤ, g (-k) = g k)
    (ρ χ α : ℝ) (k : ℤ) :
    reflectedJacobiTraceTerm g ρ χ α k =
      canonicalJacobiTraceTerm g ρ χ α (-k) := by
  rw [reflectedJacobiTraceTerm, canonicalJacobiTraceTerm,
    hg]
  congr 1
  simp only [jacobiUnitPhase,
    HGAS.Analysis.realFrequencyExponential,
    Int.cast_neg, neg_sq]
  congr 2
  push_cast
  ring

/-- The canonical trace as a topological sum over its integer modes. -/
def canonicalJacobiTrace
    (g : ℤ → ℂ) (ρ χ α : ℝ) : ℂ :=
  ∑' k : ℤ, canonicalJacobiTraceTerm g ρ χ α k

/-- The normalized reflected trace. -/
def reflectedJacobiTrace
    (g : ℤ → ℂ) (ρ χ α : ℝ) : ℂ :=
  ∑' k : ℤ, reflectedJacobiTraceTerm g ρ χ α k

/-- **Reflected-branch elimination.**  For every even coefficient family,
the entire reflected trace equals the canonical trace pointwise. -/
theorem reflectedJacobiTrace_eq_canonical
    (g : ℤ → ℂ)
    (hg : ∀ k : ℤ, g (-k) = g k)
    (ρ χ α : ℝ) :
    reflectedJacobiTrace g ρ χ α =
      canonicalJacobiTrace g ρ χ α := by
  rw [reflectedJacobiTrace, canonicalJacobiTrace,
    ← (Equiv.neg ℤ).tsum_eq]
  apply tsum_congr
  intro k
  simpa only [Equiv.neg_apply, neg_neg] using
    reflectedJacobiTraceTerm_eq_canonical_neg
      g hg ρ χ α (-k)

/-- The norm of either trace term is just the norm of its coefficient. -/
theorem norm_canonicalJacobiTraceTerm
    (g : ℤ → ℂ) (ρ χ α : ℝ) (k : ℤ) :
    ‖canonicalJacobiTraceTerm g ρ χ α k‖ = ‖g k‖ := by
  simp [canonicalJacobiTraceTerm]

theorem norm_reflectedJacobiTraceTerm
    (g : ℤ → ℂ) (ρ χ α : ℝ) (k : ℤ) :
    ‖reflectedJacobiTraceTerm g ρ χ α k‖ = ‖g k‖ := by
  simp [reflectedJacobiTraceTerm]

/-- Absolute summability of the base coefficients gives absolute
summability of both the canonical and reflected traces, uniformly in all
phases. -/
theorem summable_norm_canonicalJacobiTraceTerm
    (g : ℤ → ℂ)
    (hg : Summable fun k ↦ ‖g k‖)
    (ρ χ α : ℝ) :
    Summable fun k ↦
      ‖canonicalJacobiTraceTerm g ρ χ α k‖ := by
  simpa only [norm_canonicalJacobiTraceTerm] using hg

theorem summable_norm_reflectedJacobiTraceTerm
    (g : ℤ → ℂ)
    (hg : Summable fun k ↦ ‖g k‖)
    (ρ χ α : ℝ) :
    Summable fun k ↦
      ‖reflectedJacobiTraceTerm g ρ χ α k‖ := by
  simpa only [norm_reflectedJacobiTraceTerm] using hg

end HGAS.Modular
