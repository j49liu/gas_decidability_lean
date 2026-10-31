import Stability.Computability.RegisterMachinePeek

/-!
# Embedding verified blocks in cyclic programs

A block's external labels may refer to any label of the ambient program,
including earlier blocks. To reuse the allocated-block execution proofs,
take the ambient program itself as the continuation and fold its copied
labels back by the identity. Only the internal instruction equations need
to be checked. No condition is imposed on instructions at the exits.
-/

namespace Stability.RegisterMachine

variable {k m n : ℕ}

/-- Internal labels use the supplied allocation; external labels already
name instructions of the ambient program. -/
def blockEmbedding (allocate : Fin m → Fin n) : Fin (m + n) → Fin n :=
  Fin.addCases allocate id

@[simp]
theorem blockEmbedding_internal (allocate : Fin m → Fin n) (q : Fin m) :
    blockEmbedding allocate (q.castAdd n) = allocate q := by
  simp [blockEmbedding]

@[simp]
theorem blockEmbedding_external (allocate : Fin m → Fin n) (q : Fin n) :
    blockEmbedding allocate (q.natAdd m) = q := by
  simp [blockEmbedding]

/-- Literal internal code equations suffice to fold the entire allocated
program into its ambient program, even when exits jump backward. -/
theorem assembleBlock_embedding_code (P : Program k n)
    (body : Fin m → Instruction k (m + n)) (allocate : Fin m → Fin n)
    (hcode : ∀ q, P (allocate q) = (body q).reindex (blockEmbedding allocate))
    (q : Fin (m + n)) :
    P (blockEmbedding allocate q) =
      (assembleBlock body P q).reindex (blockEmbedding allocate) := by
  induction q using Fin.addCases with
  | left q => simpa using hcode q
  | right q =>
      cases h : P q with
      | inc r next =>
          simp [h, Instruction.reindex, Option.map_map, Function.comp_def]
      | dec r zero positive =>
          simp [h, Instruction.reindex, Option.map_map, Function.comp_def]

/-- Run a verified block in an arbitrary ambient program. The hypothesis
is an instruction-by-instruction code check, not a simulation assumption. -/
theorem run_assembleBlock_embedding (P : Program k n)
    (body : Fin m → Instruction k (m + n)) (allocate : Fin m → Fin n)
    (hcode : ∀ q, P (allocate q) = (body q).reindex (blockEmbedding allocate))
    (steps : ℕ) (c : Configuration k (m + n)) :
    run P steps (c.reindex (blockEmbedding allocate)) =
      (run (assembleBlock body P) steps c).reindex (blockEmbedding allocate) :=
  run_reindex (blockEmbedding allocate)
    (assembleBlock_embedding_code P body allocate hcode) steps c

/-- The explicit twelve-label push block can be placed anywhere, with an
arbitrary active or halted exit. Its exit instruction has not yet run. -/
theorem run_embedded_stackPush (P : Program k n) (allocate : Fin 12 → Fin n)
    (value scratch : Fin k) (hne : value ≠ scratch) (d : Fin 4)
    (exit : Option (Fin n))
    (hcode : ∀ q, P (allocate q) =
      (pushBlockCode value scratch d exit q).reindex (blockEmbedding allocate))
    (r : Fin k → ℕ) (hscratch : r scratch = 0) :
    run P ((6 * r value + 1) + (2 * (5 * r value) + 1) + (d.val + 1))
      ⟨some (allocate 0), r⟩ =
      ⟨exit, Function.update (Function.update r scratch 0) value
        (5 * r value + (d.val + 1))⟩ := by
  have h := run_assembleBlock_embedding P (pushBlockCode value scratch d exit)
    allocate hcode ((6 * r value + 1) + (2 * (5 * r value) + 1) + (d.val + 1))
    ⟨some ((0 : Fin 12).castAdd n), r⟩
  change run P _ _ =
    (run (stackPushProgram value scratch d exit P) _ _).reindex _ at h
  rw [run_stackPushProgram value scratch hne d exit P r hscratch] at h
  simpa [Configuration.reindex, Option.map_map, Function.comp_def] using h

/-- The explicit sixteen-label pop block can dispatch to arbitrary labels
of a cyclic ambient program, according to the actual remainder. -/
theorem run_embedded_stackPop (P : Program k n) (allocate : Fin 16 → Fin n)
    (value scratch : Fin k) (hne : value ≠ scratch)
    (exit : Fin 5 → Option (Fin n))
    (hcode : ∀ q, P (allocate q) =
      (popBlockCode value scratch exit q).reindex (blockEmbedding allocate))
    (r : Fin k → ℕ) (hscratch : r scratch = 0) :
    run P ((6 * (r value / 5) + r value % 5 + 1) + (2 * (r value / 5) + 1))
      ⟨some (allocate 0), r⟩ =
      ⟨exit ⟨r value % 5, Nat.mod_lt _ (by decide)⟩,
        Function.update (Function.update r scratch 0) value (r value / 5)⟩ := by
  have h := run_assembleBlock_embedding P (popBlockCode value scratch exit)
    allocate hcode ((6 * (r value / 5) + r value % 5 + 1) + (2 * (r value / 5) + 1))
    ⟨some ((0 : Fin 16).castAdd n), r⟩
  change run P _ _ = (run (stackPopProgram value scratch exit P) _ _).reindex _ at h
  rw [run_stackPopProgram value scratch hne exit P r hscratch] at h
  simpa [Configuration.reindex, Option.map_map, Function.comp_def] using h

end Stability.RegisterMachine
