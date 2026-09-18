import HGAS.Compiler.CompactAccumulatorPipelineTangency
import HGAS.Compactification.AllAffinePolynomialCode
import HGAS.Wrapper.UnitSphereWrapperSourceCompact
import Mathlib.Tactic

/-!
# Inhabited product-sphere sources for the compact accumulator

The final compact-sign certificate requires the compiled source product of
spheres to be nonempty.  This is purely finite index bookkeeping:

* surjectivity of the old base-block assignment supplies every old sphere;
* the accumulator `W` coordinate supplies the newly adjoined sphere.

For the detector compiler all affine coordinates belong to one block, and
the newly introduced central coordinate supplies that block even when the
original affine dimension is zero.  The lemmas are stated separately so
the first can be reused by other compact-accumulator sources.
-/

namespace HGAS

open Function

namespace AccumulatorPolynomialCode

variable {N m k : ℕ}

/-- Adjoining a compact accumulator preserves surjectivity of the sphere
block assignment. -/
theorem productSphereBlock_surjective
    {baseBlock : Fin N → Fin k}
    (hbase : Surjective baseBlock) :
    Surjective (productSphereBlock (m := m) baseBlock) := by
  intro block
  obtain ⟨oldBlock | newBlock, rfl⟩ :=
    finSumFinEquiv.surjective block
  · obtain ⟨j, rfl⟩ := hbase oldBlock
    refine ⟨baseIndex (m := m) j, ?_⟩
    rw [productSphereBlock_baseIndex]
    rfl
  · fin_cases newBlock
    refine ⟨wIndex N m, ?_⟩
    rw [productSphereBlock_wIndex]
    rfl

end AccumulatorPolynomialCode

namespace CompactAccumulatorPipelineCode

/-- The complete block assignment of a one-block all-affine compact
accumulator is surjective. -/
theorem sourceBlock_oneBlockAllAffine_surjective
    (n m : ℕ) :
    Surjective
      (sourceBlock
        (m := m)
        (MixedCentralPolynomialCode.oneBlockAllAffineLayout n)) := by
  apply AccumulatorPolynomialCode.productSphereBlock_surjective
  intro block
  fin_cases block
  refine
    ⟨MixedCentralPolynomialCode.wIndex (n := n) (0 : Fin 1), ?_⟩
  rw [MixedCentralPolynomialCode.targetBlock_wIndex]
  apply Fin.ext
  rfl

/-- The exact source product of spheres used by every one-block
all-affine detector compiler is inhabited. -/
theorem nonempty_sourceProductSphere_oneBlockAllAffine
    (n m : ℕ) :
    Nonempty
      (UnitSpherePolynomialWrapper.SourceProductSphere
        (sourceBlock
          (m := m)
          (MixedCentralPolynomialCode.oneBlockAllAffineLayout n))) := by
  rw [
    UnitSpherePolynomialWrapper.nonempty_sourceProductSphere_iff_surjective]
  exact sourceBlock_oneBlockAllAffine_surjective n m

end CompactAccumulatorPipelineCode

end HGAS
