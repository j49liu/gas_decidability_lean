import Stability.Computability.RegisterMachineFinite

/-!
# Restricting a supported stack machine to finite control

Every goto in a supported statement stays in the finite control support.
Renaming that support by `Fin` therefore gives an actual finite-control
TM2 machine, with the same halting behavior on supported configurations.
The total label map uses a fixed supported fallback outside the support;
the refinement proof shows that this fallback is never used by such runs.
-/

noncomputable section

namespace Stability.RegisterMachine.TM2Encoding

open Turing.PartrecToTM2

variable {Λ Λ₂ : Type*}

/-- Rename only the external labels in the actual TM2 statement syntax. -/
def mapStatementLabels (f : Λ → Λ₂) : StackStatement Λ → StackStatement Λ₂
  | .push j a q => .push j a (mapStatementLabels f q)
  | .pop j a q => .pop j a (mapStatementLabels f q)
  | .peek j a q => .peek j a (mapStatementLabels f q)
  | .load a q => .load a (mapStatementLabels f q)
  | .branch a q₁ q₂ => .branch a (mapStatementLabels f q₁) (mapStatementLabels f q₂)
  | .goto a => .goto (f ∘ a)
  | .halt => .halt

/-- Renaming control labels does not change the local store or stacks. -/
def mapConfigurationLabels (f : Λ → Λ₂)
    (c : Turing.TM2.Cfg (fun _ : K' ↦ Γ') Λ (Option Γ')) :
    Turing.TM2.Cfg (fun _ : K' ↦ Γ') Λ₂ (Option Γ') :=
  ⟨c.l.map f, c.var, c.stk⟩

theorem stepAux_mapStatementLabels (f : Λ → Λ₂) (q : StackStatement Λ)
    (store : Option Γ') (S : K' → List Γ') :
    Turing.TM2.stepAux (mapStatementLabels f q) store S =
      mapConfigurationLabels f (Turing.TM2.stepAux q store S) := by
  induction q generalizing store S with
  | push j a q ih => exact ih store (Function.update S j (a store :: S j))
  | pop j a q ih => exact ih (a store (S j).head?) (Function.update S j (S j).tail)
  | peek j a q ih => exact ih (a store (S j).head?) S
  | load a q ih => exact ih (a store) S
  | branch a q₁ q₂ ih₁ ih₂ => cases ha : a store <;> simp [mapStatementLabels, ha, ih₁, ih₂]
  | goto a => rfl
  | halt => rfl

variable [DecidableEq Λ] [Inhabited Λ]

/-- A fixed finite enumeration of the supported control labels. -/
def supportEquiv (S : Finset Λ) : {l // l ∈ S} ≃ Fin S.card :=
  Fintype.equivFinOfCardEq (Fintype.card_coe S)

/-- Totalize the finite label encoder with the fixed supported default.
The fallback is irrelevant on every source-supported execution. -/
def supportLabelCode (S : Finset Λ) (hdefault : default ∈ S) (l : Λ) : Fin S.card :=
  if h : l ∈ S then supportEquiv S ⟨l, h⟩ else supportEquiv S ⟨default, hdefault⟩

theorem supportLabelCode_decode (S : Finset Λ) (hdefault : default ∈ S)
    (l : Λ) (hl : l ∈ S) :
    ((supportEquiv S).symm (supportLabelCode S hdefault l)).val = l := by
  simp [supportLabelCode, hl]

/-- The actual finite-control machine obtained by renaming supported roots. -/
def supportedMachine (M : Λ → StackStatement Λ) (S : Finset Λ)
    (hM : Turing.TM2.Supports M S) : Fin S.card → StackStatement (Fin S.card) :=
  fun i ↦ mapStatementLabels (supportLabelCode S hM.1) (M ((supportEquiv S).symm i).val)

/-- Restriction to finite support is a one-step refinement on supported
configurations. Both source and restricted machines use actual TM2 steps. -/
theorem supportedMachine_respects (M : Λ → StackStatement Λ) (S : Finset Λ)
    (hM : Turing.TM2.Supports M S) :
    StateTransition.Respects (Turing.TM2.step M) (Turing.TM2.step (supportedMachine M S hM))
      (fun c d ↦ c.l ∈ Finset.insertNone S ∧
        mapConfigurationLabels (supportLabelCode S hM.1) c = d) := by
  intro c d h
  obtain ⟨hsupport, rfl⟩ := h
  cases c with
  | mk label store stk =>
      cases label with
      | none => rfl
      | some l =>
          have hl : l ∈ S := Finset.some_mem_insertNone.mp hsupport
          let out := Turing.TM2.stepAux (M l) store stk
          refine ⟨mapConfigurationLabels (supportLabelCode S hM.1) out, ⟨?_, rfl⟩, ?_⟩
          · exact Turing.TM2.step_supports M hM (c := ⟨some l, store, stk⟩) rfl hsupport
          · apply Relation.TransGen.single
            simp only [mapConfigurationLabels, Option.map_some, Turing.TM2.step]
            rw [supportedMachine, supportLabelCode_decode S hM.1 l hl,
              stepAux_mapStatementLabels]
            rfl

/-- Exact halting equivalence after reducing the original label support
to a finite type. -/
theorem supportedMachine_eval_dom_iff (M : Λ → StackStatement Λ) (S : Finset Λ)
    (hM : Turing.TM2.Supports M S)
    (c : Turing.TM2.Cfg (fun _ : K' ↦ Γ') Λ (Option Γ'))
    (hc : c.l ∈ Finset.insertNone S) :
    (StateTransition.eval (Turing.TM2.step (supportedMachine M S hM))
      (mapConfigurationLabels (supportLabelCode S hM.1) c)).Dom ↔
      (StateTransition.eval (Turing.TM2.step M) c).Dom :=
  StateTransition.tr_eval_dom (supportedMachine_respects M S hM) ⟨hc, rfl⟩

end Stability.RegisterMachine.TM2Encoding
