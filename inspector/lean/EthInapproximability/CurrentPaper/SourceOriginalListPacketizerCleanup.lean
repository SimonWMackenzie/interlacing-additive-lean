import EthInapproximability.CurrentPaper.SourceOriginalListPacketizerProgram

/-!
# Charged cleanup of the source packetizer's reusable framing banks

This owner proves the literal `clearFrame` transitions of the fixed outer
program. They visit every framing bank exactly once, skip the persistent
unary original size, and pop all other framing cells. The ten outer banks
(including source, count, and accumulated output) are never touched.
-/

namespace EthInapproximability.CurrentPaper.SourceOriginalListPacketizerCleanup

open Turing BitMachineEncoding
open EthInapproximability.CurrentPaper.SourceOriginalListPacketizer

def clearedExcept {K : Type*} [DecidableEq K] {n : ℕ}
    (bank : Fin n → K) (skip : K) (S : K → List Bool) : K → List Bool :=
  fun k => if ∃ i, bank i = k ∧ bank i ≠ skip then [] else S k

theorem clearedExcept_zero {K : Type*} [DecidableEq K]
    (bank : Fin 0 → K) (skip : K) (S : K → List Bool) :
    clearedExcept bank skip S = S := by
  funext k
  simp [clearedExcept]

theorem clearedExcept_succ {K : Type*} [DecidableEq K] {n : ℕ}
    (bank : Fin (n+1) → K) (skip : K) (S : K → List Bool) :
    clearedExcept (fun i : Fin n => bank i.succ) skip
      (if bank 0 = skip then S else Function.update S (bank 0) []) =
    clearedExcept bank skip S := by
  funext k
  by_cases hs : bank 0 = skip
  · simp only [hs, ↓reduceIte]
    simp [clearedExcept, Fin.exists_fin_succ, hs]
  · simp only [hs, ↓reduceIte]
    by_cases hk : bank 0 = k
    · subst k
      simp [clearedExcept, Fin.exists_fin_succ, hs]
    · have hne : k ≠ bank 0 := Ne.symm hk
      simp [clearedExcept, Fin.exists_fin_succ, hs, hk, hne]

private theorem clear_skip_run {K L V : Type*} [DecidableEq K]
    (P : L → TM2.Stmt (fun _ : K => Bool) L (V × Option Bool))
    (reset : V → V) (next : L) (n : ℕ) (bank : Fin n → K)
    (hbank : Function.Injective bank) (skip : K) (label : Fin (n+1) → L)
    (hsteps : ∀ i : Fin n, P (label i.castSucc) =
      if bank i = skip then .goto (fun _ => label i.succ)
      else BitMachineClearBank.clearStep (bank i) (label i.castSucc) (label i.succ))
    (hfinish : P (label (Fin.last n)) =
      BitMachineClearBank.finishStep reset next)
    (v : V) (S : K → List Bool) :
    ((advance P)^[(∑ i : Fin n,
        if bank i = skip then 0 else (S (bank i)).length) + n + 1])
      ⟨some (label 0), (v,none), S⟩ =
      ⟨some next, (reset v,none), clearedExcept bank skip S⟩ := by
  induction n generalizing S with
  | zero =>
      have hf : P (label 0) = BitMachineClearBank.finishStep reset next := hfinish
      simp [advance, TM2.step, hf, BitMachineClearBank.finishStep,
        TM2.stepAux, clearedExcept_zero]
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
        rw [Function.iterate_add_apply,
          Function.iterate_one, hstep]
        have htail' : ((advance P)^[(∑ i : Fin n,
              if bank i.succ = skip then 0 else (S (bank i.succ)).length) + n + 1])
            ⟨some (label (Fin.succ 0)), (v,none), S⟩ =
            ⟨some next, (reset v,none), clearedExcept tailBank skip S'⟩ := by
          simpa only [tailLabel, S', hskip, ↓reduceIte] using htail
        rw [htail']
        congr 1
        exact clearedExcept_succ bank skip S
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
            ⟨some next, (reset v,none), clearedExcept tailBank skip S'⟩ := by
          simpa only [tailLabel, S', hskip, ↓reduceIte] using htail
        rw [htail']
        congr 1
        exact clearedExcept_succ bank skip S

end EthInapproximability.CurrentPaper.SourceOriginalListPacketizerCleanup
