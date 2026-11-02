import EthInapproximability.CurrentPaper.SourceOriginalListPacketizerCleanup
import EthInapproximability.CurrentPaper.SourceOriginalListPacketizerField

/-! The exact physical loop that clears every reusable framing bank except unary `n`. -/

namespace EthInapproximability.CurrentPaper.SourceOriginalListPacketizerCleanupRun

open Turing BitMachineEncoding
open EthInapproximability.CurrentPaper.SourceOriginalListPacketizer
open scoped BigOperators

private theorem clear_skip_run {K L V : Type*} [DecidableEq K]
    (P : L → TM2.Stmt (fun _ : K => Bool) L (V × Option Bool))
    (reset : V → V) (next : L) (n : ℕ) (bank : Fin n → K)
    (hbank : Function.Injective bank) (skip : K) (label : Fin (n+1) → L)
    (hsteps : ∀ i : Fin n, P (label i.castSucc) =
      if bank i = skip then .goto (fun _ => label i.succ)
      else BitMachineClearBank.clearStep (bank i) (label i.castSucc) (label i.succ))
    (hfinish : P (label (Fin.last n)) = BitMachineClearBank.finishStep reset next)
    (v : V) (S : K → List Bool) :
    ((advance P)^[(∑ i : Fin n,
        if bank i = skip then 0 else (S (bank i)).length) + n + 1])
      ⟨some (label 0), (v,none), S⟩ =
      ⟨some next, (reset v,none),
        SourceOriginalListPacketizerCleanup.clearedExcept bank skip S⟩ := by
  induction n generalizing S with
  | zero =>
      have hf : P (label 0) = BitMachineClearBank.finishStep reset next := hfinish
      simp [advance, TM2.step, hf, BitMachineClearBank.finishStep,
        TM2.stepAux, SourceOriginalListPacketizerCleanup.clearedExcept_zero]
  | succ n ih =>
      let tailBank : Fin n → K := fun i => bank i.succ
      let tailLabel : Fin (n+1) → L := fun i => label i.succ
      let S' : K → List Bool :=
        if bank 0 = skip then S else Function.update S (bank 0) []
      have htailInj : Function.Injective tailBank :=
        hbank.comp (Fin.succ_injective n)
      have htailSteps : ∀ i : Fin n, P (tailLabel i.castSucc) =
          if tailBank i = skip then .goto (fun _ => tailLabel i.succ)
          else BitMachineClearBank.clearStep (tailBank i)
            (tailLabel i.castSucc) (tailLabel i.succ) := by
        intro i
        exact hsteps i.succ
      have htailFinish : P (tailLabel (Fin.last n)) =
          BitMachineClearBank.finishStep reset next := hfinish
      have htail := ih tailBank htailInj tailLabel htailSteps htailFinish S'
      have hsums : (∑ i : Fin n,
          if tailBank i = skip then 0 else (S' (tailBank i)).length) =
          ∑ i : Fin n,
            if bank i.succ = skip then 0 else (S (bank i.succ)).length := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hskip : bank 0 = skip
        · simp [S', hskip, tailBank]
        · have hne : bank i.succ ≠ bank 0 := by
            intro h
            have he := hbank h
            have hv := congrArg Fin.val he
            simp at hv
          simp [S', hskip, tailBank, hne]
      rw [hsums] at htail
      have htime :
          (∑ i : Fin (n+1),
            if bank i = skip then 0 else (S (bank i)).length) + (n+1) + 1 =
          ((∑ i : Fin n,
            if bank i.succ = skip then 0 else (S (bank i.succ)).length) + n + 1) +
            (if bank 0 = skip then 1 else (S (bank 0)).length + 1) := by
        rw [Fin.sum_univ_succ]
        split <;> omega
      by_cases hskip : bank 0 = skip
      · have hp : P (label 0) = .goto (fun _ => label (Fin.succ 0)) := by
          simpa only [hskip, ↓reduceIte] using hsteps 0
        have hstep : advance P ⟨some (label 0), (v,none), S⟩ =
            ⟨some (label (Fin.succ 0)), (v,none), S⟩ := by
          simp [advance, TM2.step, hp, TM2.stepAux]
        rw [htime]
        simp only [if_pos hskip]
        rw [Function.iterate_add_apply, Function.iterate_one, hstep]
        have htail' : ((advance P)^[(∑ i : Fin n,
              if bank i.succ = skip then 0 else (S (bank i.succ)).length) + n + 1])
            ⟨some (label (Fin.succ 0)), (v,none), S⟩ =
            ⟨some next, (reset v,none),
              SourceOriginalListPacketizerCleanup.clearedExcept tailBank skip S'⟩ := by
          simpa only [tailLabel, S', hskip, ↓reduceIte] using htail
        rw [htail']
        congr 1
        exact SourceOriginalListPacketizerCleanup.clearedExcept_succ bank skip S

      · have hp : P (label 0) = BitMachineClearBank.clearStep (bank 0)
            (label 0) (label (Fin.succ 0)) := by
          simpa only [hskip, ↓reduceIte] using hsteps 0
        rw [htime]
        simp only [if_neg hskip]
        rw [Function.iterate_add_apply,
          BitMachineClearBank.clear_one_run P (bank 0) (label 0)
            (label (Fin.succ 0)) hp v S]
        have htail' : ((advance P)^[(∑ i : Fin n,
              if bank i.succ = skip then 0 else (S (bank i.succ)).length) + n + 1])
            ⟨some (label (Fin.succ 0)), (v,none), Function.update S (bank 0) []⟩ =
            ⟨some next, (reset v,none),
              SourceOriginalListPacketizerCleanup.clearedExcept tailBank skip S'⟩ := by
          simpa only [tailLabel, S', hskip, ↓reduceIte] using htail
        rw [htail']
        congr 1
        exact SourceOriginalListPacketizerCleanup.clearedExcept_succ bank skip S

abbrev PreControl :=
  (((SourceListMachineInitialize.Control × SourceListMachineCounter.Control) ×
    SourceListMachineFields.Control) × SourceOriginalPacketFraming.Control)

noncomputable def frameBank (i : Fin (Fintype.card FrameStack)) : Stack :=
  .inl ((Fintype.equivFin FrameStack).symm i)

def clearLabel (i : Fin (Fintype.card FrameStack+1)) : Label :=
  adminLabel (.clearFrame i)

theorem frameBank_injective : Function.Injective frameBank := by
  intro a b h
  exact (Fintype.equivFin FrameStack).symm.injective (Sum.inl.inj h)

theorem clearFrame_steps (i : Fin (Fintype.card FrameStack)) :
    program (clearLabel i.castSucc) =
      if frameBank i = .inl SourceOriginalPacketFraming.nStack then
        .goto (fun _ => clearLabel i.succ)
      else BitMachineClearBank.clearStep (frameBank i)
        (clearLabel i.castSucc) (clearLabel i.succ) := by
  have hi : i.val < Fintype.card FrameStack := i.isLt
  simp only [clearLabel, adminLabel, program, Fin.val_castSucc]
  simp only [hi, ↓reduceDIte, frameBank]
  split_ifs <;> simp_all [BitMachineClearBank.clearStep] <;>
    (funext x; congr 5)

theorem clearFrame_finish :
    program (clearLabel (Fin.last (Fintype.card FrameStack))) =
      BitMachineClearBank.finishStep
        (fun _ : PreControl => (counterControl SourceListMachineCounter.initialControl).1)
        (counterLabel (.inr .scan)) := by
  simp [clearLabel, adminLabel, program, BitMachineClearBank.finishStep,
    counterControl]

theorem clearFrame_run (v : PreControl) (S : Stack → List Bool) :
    ((advance program)^[(∑ i : Fin (Fintype.card FrameStack),
        if frameBank i = .inl SourceOriginalPacketFraming.nStack then 0
        else (S (frameBank i)).length) + Fintype.card FrameStack + 1])
      ⟨some (adminLabel (.clearFrame 0)), (v,none),S⟩ =
      ⟨some (counterLabel (.inr .scan)),
        counterControl SourceListMachineCounter.initialControl,
        SourceOriginalListPacketizerCleanup.clearedExcept frameBank
          (.inl SourceOriginalPacketFraming.nStack) S⟩ := by
  exact clear_skip_run program
    (fun _ : PreControl => (counterControl SourceListMachineCounter.initialControl).1)
    (counterLabel (.inr .scan)) (Fintype.card FrameStack) frameBank
    frameBank_injective (.inl SourceOriginalPacketFraming.nStack) clearLabel
    clearFrame_steps clearFrame_finish v S

theorem cleared_n (S : Stack → List Bool) :
    SourceOriginalListPacketizerCleanup.clearedExcept frameBank
      (.inl SourceOriginalPacketFraming.nStack) S
      (.inl SourceOriginalPacketFraming.nStack) =
      S (.inl SourceOriginalPacketFraming.nStack) := by
  simp [SourceOriginalListPacketizerCleanup.clearedExcept]

theorem cleared_aux (S : Stack → List Bool) (k : Fin 10) :
    SourceOriginalListPacketizerCleanup.clearedExcept frameBank
      (.inl SourceOriginalPacketFraming.nStack) S (.inr k) = S (.inr k) := by
  simp [SourceOriginalListPacketizerCleanup.clearedExcept, frameBank]

theorem cleared_other_frame (S : Stack → List Bool) (k : FrameStack)
    (hk : k ≠ SourceOriginalPacketFraming.nStack) :
    SourceOriginalListPacketizerCleanup.clearedExcept frameBank
      (.inl SourceOriginalPacketFraming.nStack) S (.inl k) = [] := by
  unfold SourceOriginalListPacketizerCleanup.clearedExcept
  have hi : frameBank ((Fintype.equivFin FrameStack) k) = (.inl k : Stack) := by
    simp [frameBank]
  have hex : ∃ i : Fin (Fintype.card FrameStack),
      frameBank i = (.inl k : Stack) ∧
      frameBank i ≠ (.inl SourceOriginalPacketFraming.nStack : Stack) := by
    exact ⟨(Fintype.equivFin FrameStack) k, hi, by simpa [hi] using hk⟩
  simp [hex]

end EthInapproximability.CurrentPaper.SourceOriginalListPacketizerCleanupRun
