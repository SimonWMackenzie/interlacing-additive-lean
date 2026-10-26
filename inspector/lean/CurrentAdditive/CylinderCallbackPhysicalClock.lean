import CurrentAdditive.CylinderCallbackCleanupClock
import EthInapproximability.CurrentPaper.BitMachineStackGrowth

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 65536

namespace CurrentAdditive.CylinderCoordinateEqualityCallback

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackGrowth
open CurrentAdditive.GaussListContext

theorem physical_coordinate_pair_bounded (pre : List (List Bool))
    (word : List Bool) (suffix : List (List Bool))
    (right out : List Bool) (foreign : Stack → List Bool)
    (h16 : foreign 16 = right) (h9 : foreign 9 = out)
    (h27 : foreign 27 = []) (h28 : foreign 28 = [])
    (h29 : foreign 29 = []) :
    let tuple := SourceListEncoding.encode (pre ++ word :: suffix)
    let start := getterFrame foreign
      (CylinderContextScanStep.initial tuple pre.length)
    ∃ (t : Nat) (vFinal : Control) (SFinal SBefore : Stack → List Bool),
      t ≤ getterBound pre word suffix + 1 +
        CylinderEqualityAppendCallback.callbackBound word right out +
        15 * ((BitMachineBankCodec.encode start.stk).length +
          BitMachineStackGrowth.perStep program *
            (getterBound pre word suffix + 1 +
              CylinderEqualityAppendCallback.callbackBound word right out)) + 17 ∧
      run t start = ⟨none, vFinal, SFinal⟩ ∧
      SFinal 9 = out ++ [decide (word = right)] ∧
      SFinal = BitMachineClearBank.cleared cleanBank SBefore ∧
      (∀ i : Fin 15, SFinal (cleanBank i) = []) ∧
      (∀ k : Stack,
        k = 8 ∨ k = 10 ∨ k = 12 ∨ k = 13 ∨ k = 15 ∨ k = 16 →
          SFinal k = start.stk k) ∧
      t ≤ getterBound pre word suffix + 1 +
        CylinderEqualityAppendCallback.callbackBound word right out +
        (∑ i : Fin 15, (SBefore (cleanBank i)).length) + 17 ∧
      (∀ i : Fin 15,
        (SBefore (cleanBank i)).length ≤
          (start.stk (cleanBank i)).length +
            BitMachineStackGrowth.perStep program *
              (getterBound pre word suffix + 1 +
                CylinderEqualityAppendCallback.callbackBound word right out)) := by
  dsimp only
  let tuple := SourceListEncoding.encode (pre ++ word :: suffix)
  let start := getterFrame foreign
    (CylinderContextScanStep.initial tuple pre.length)
  obtain ⟨a, ha, hget⟩ := getter_run pre word suffix foreign
  let selected := selectedFrame foreign tuple
    (SourceListEncoding.fields suffix) word pre.length
  change run a start = selected at hget
  have hleft : selected.stk 17 = word :=
    selectedFrame_word foreign tuple
      (SourceListEncoding.fields suffix) word pre.length
  have hright : selected.stk 16 = right := by
    rw [selectedFrame_foreign foreign tuple
      (SourceListEncoding.fields suffix) word pre.length 16
      (by decide)]
    exact h16
  have hout : selected.stk 9 = out := by
    rw [selectedFrame_foreign foreign tuple
      (SourceListEncoding.fields suffix) word pre.length 9
      (by decide)]
    exact h9
  have hs27 : selected.stk 27 = [] := by
    rw [selectedFrame_foreign foreign tuple
      (SourceListEncoding.fields suffix) word pre.length 27
      (by decide)]
    exact h27
  have hs28 : selected.stk 28 = [] := by
    rw [selectedFrame_foreign foreign tuple
      (SourceListEncoding.fields suffix) word pre.length 28
      (by decide)]
    exact h28
  have hs29 : selected.stk 29 = [] := by
    rw [selectedFrame_foreign foreign tuple
      (SourceListEncoding.fields suffix) word pre.length 29
      (by decide)]
    exact h29
  have hhandoff := handoff_step selected.stk selected.var
  change run 1 selected = equalityFrame selected.stk
    ⟨some (.copyContext .scan),
     CylinderEqualityAppendCallback.bcontrol ((), none),
     fun k => selected.stk (equalityStack k)⟩ at hhandoff
  obtain ⟨b, hb, vEq, SEq, heq, hoEq, hpEq⟩ :=
    equality_run_frame selected.stk word right out
      hleft hright hout hs28 hs27 hs29
  let before := equalityFrame selected.stk ⟨none, vEq, SEq⟩
  have hbefore : before.stk 9 = out ++ [decide (word = right)] := by
    have hb9 := BitMachineStackEmbedding.bank_at equalityStack
      selected.stk SEq (9 : Fin 15)
    simpa [before, equalityFrame, BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, equalityStack, hoEq]
      using hb9
  have hclean := cleanup_run (equalityControl vEq).1 before.stk
  have hclean' : run ((∑ i : Fin 15,
      (before.stk (cleanBank i)).length) + 16) before =
      ⟨some (.inr (.inr .done)), equalityControl vEq,
       BitMachineClearBank.cleared cleanBank before.stk⟩ := by
    simpa [before, equalityFrame, BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
      equalityControl] using hclean
  have hdone (S : Stack → List Bool) (v : Control) :
      run 1 ⟨some (.inr (.inr .done)), v, S⟩ =
        ⟨none, v, S⟩ := by rfl
  have hfirst : run (a + 1) start =
      equalityFrame selected.stk
        ⟨some (.copyContext .scan),
         CylinderEqualityAppendCallback.bcontrol ((), none),
         fun k => selected.stk (equalityStack k)⟩ :=
    (run_add hget 1).trans hhandoff
  have hsecond : run (a + 1 + b) start = before :=
    (run_add hfirst b).trans heq
  have hprefix : a + 1 + b ≤
      getterBound pre word suffix + 1 +
        CylinderEqualityAppendCallback.callbackBound word right out := by
    change a ≤ getterBound pre word suffix at ha
    omega
  have hpoint (i : Fin 15) :
      (before.stk (cleanBank i)).length ≤
        (start.stk (cleanBank i)).length +
          BitMachineStackGrowth.perStep program *
            (getterBound pre word suffix + 1 +
              CylinderEqualityAppendCallback.callbackBound word right out) := by
    have hg := BitMachineStackGrowth.run_growth program start
      (a + 1 + b) (cleanBank i)
    change ((run (a + 1 + b) start).stk (cleanBank i)).length ≤
      (start.stk (cleanBank i)).length +
        BitMachineStackGrowth.perStep program * (a + 1 + b) at hg
    rw [hsecond] at hg
    exact hg.trans (Nat.add_le_add_left
      (Nat.mul_le_mul_left (BitMachineStackGrowth.perStep program) hprefix) _)
  have hsum : (∑ i : Fin 15, (before.stk (cleanBank i)).length) ≤
      15 * ((BitMachineBankCodec.encode start.stk).length +
        BitMachineStackGrowth.perStep program *
          (getterBound pre word suffix + 1 +
            CylinderEqualityAppendCallback.callbackBound word right out)) := by
    exact CylinderCallbackCleanupClock.callback_cleanup_sum_le_input
      pre word suffix right out start.stk before.stk hpoint
  dsimp only [start, tuple] at hsum
  have hthird : run (a + 1 + b +
      ((∑ i : Fin 15, (before.stk (cleanBank i)).length) + 16))
      start =
      ⟨some (.inr (.inr .done)), equalityControl vEq,
       BitMachineClearBank.cleared cleanBank before.stk⟩ :=
    (run_add hsecond _).trans hclean'
  have htotal := (run_add hthird 1).trans
    (hdone (BitMachineClearBank.cleared cleanBank before.stk)
      (equalityControl vEq))
  have hnot9 : ∀ i : Fin 15, cleanBank i ≠ (9 : Stack) := by
    decide
  have h9final : (BitMachineClearBank.cleared cleanBank
      before.stk) 9 = out ++ [decide (word = right)] :=
    (BitMachineClearBank.cleared_foreign cleanBank before.stk 9
      hnot9).trans hbefore
  refine ⟨a + 1 + b +
      ((∑ i : Fin 15, (before.stk (cleanBank i)).length) + 16) + 1,
      equalityControl vEq,
      BitMachineClearBank.cleared cleanBank before.stk,
      before.stk, ?_, htotal, h9final, rfl, ?_, ?_, ?_, ?_⟩
  · omega
  · intro i
    exact BitMachineClearBank.cleared_bank cleanBank before.stk i
  · intro k hk
    have hnotclean : ∀ i : Fin 15, cleanBank i ≠ k := by
      rcases hk with h | h | h | h | h | h <;> subst k <;> decide
    rw [BitMachineClearBank.cleared_foreign cleanBank before.stk k
      hnotclean]
    have hstart : start.stk k = selected.stk k := by
      rcases hk with h | h | h | h | h | h
      · subst k
        simpa [start, selected, getterFrame,
          BitMachineStackEmbedding.cfg,
          BitMachineStackEmbedding.stackCfg] using
          (BitMachineStackEmbedding.bank_outside getterStack foreign
            (CylinderContextScanStep.initial tuple pre.length).stk
            (8 : Stack) (by decide)).trans
          (selectedFrame_foreign foreign tuple
            (SourceListEncoding.fields suffix) word pre.length 8
            (by decide)).symm
      · subst k
        simpa [start, selected, getterFrame,
          BitMachineStackEmbedding.cfg,
          BitMachineStackEmbedding.stackCfg] using
          (BitMachineStackEmbedding.bank_outside getterStack foreign
            (CylinderContextScanStep.initial tuple pre.length).stk
            (10 : Stack) (by decide)).trans
          (selectedFrame_foreign foreign tuple
            (SourceListEncoding.fields suffix) word pre.length 10
            (by decide)).symm
      · subst k
        simpa [start, selected, getterFrame,
          BitMachineStackEmbedding.cfg,
          BitMachineStackEmbedding.stackCfg] using
          (BitMachineStackEmbedding.bank_outside getterStack foreign
            (CylinderContextScanStep.initial tuple pre.length).stk
            (12 : Stack) (by decide)).trans
          (selectedFrame_foreign foreign tuple
            (SourceListEncoding.fields suffix) word pre.length 12
            (by decide)).symm
      · subst k
        simpa [start, selected, getterFrame,
          BitMachineStackEmbedding.cfg,
          BitMachineStackEmbedding.stackCfg] using
          (BitMachineStackEmbedding.bank_outside getterStack foreign
            (CylinderContextScanStep.initial tuple pre.length).stk
            (13 : Stack) (by decide)).trans
          (selectedFrame_foreign foreign tuple
            (SourceListEncoding.fields suffix) word pre.length 13
            (by decide)).symm
      · subst k
        have hs := BitMachineStackEmbedding.bank_at getterStack foreign
          (CylinderContextScanStep.initial tuple pre.length).stk
          (10 : Fin 12)
        have ht := BitMachineStackEmbedding.bank_at getterStack foreign
          (CylinderContextScanStep.selectedBank tuple
            (SourceListEncoding.fields suffix) word pre.length)
          (10 : Fin 12)
        simpa [start, selected, getterFrame,
          BitMachineStackEmbedding.cfg,
          BitMachineStackEmbedding.stackCfg, getterStack,
          CylinderContextScanStep.initialBank,
          CylinderContextScanStep.selectedBank] using hs.trans ht.symm
      · subst k
        simpa [start, selected, getterFrame,
          BitMachineStackEmbedding.cfg,
          BitMachineStackEmbedding.stackCfg] using
          (BitMachineStackEmbedding.bank_outside getterStack foreign
            (CylinderContextScanStep.initial tuple pre.length).stk
            (16 : Stack) (by decide)).trans
          (selectedFrame_foreign foreign tuple
            (SourceListEncoding.fields suffix) word pre.length 16
            (by decide)).symm
    have hbefore : before.stk k = selected.stk k := by
      rcases hk with h | h | h | h | h | h
      · subst k
        have hb := BitMachineStackEmbedding.bank_at equalityStack
          selected.stk SEq (8 : Fin 15)
        simpa [before, equalityFrame,
          BitMachineStackEmbedding.cfg,
          BitMachineStackEmbedding.stackCfg, equalityStack]
          using hb.trans (hpEq 8 (by simp))
      · subst k
        have hb := BitMachineStackEmbedding.bank_at equalityStack
          selected.stk SEq (10 : Fin 15)
        simpa [before, equalityFrame,
          BitMachineStackEmbedding.cfg,
          BitMachineStackEmbedding.stackCfg, equalityStack]
          using hb.trans (hpEq 10 (by simp))
      · subst k
        exact BitMachineStackEmbedding.bank_outside equalityStack
          selected.stk SEq 12 (by decide)
      · subst k
        have hb := BitMachineStackEmbedding.bank_at equalityStack
          selected.stk SEq (13 : Fin 15)
        simpa [before, equalityFrame,
          BitMachineStackEmbedding.cfg,
          BitMachineStackEmbedding.stackCfg, equalityStack]
          using hb.trans (hpEq 13 (by simp))
      · subst k
        exact BitMachineStackEmbedding.bank_outside equalityStack
          selected.stk SEq 15 (by decide)
      · subst k
        have hb := BitMachineStackEmbedding.bank_at equalityStack
          selected.stk SEq (12 : Fin 15)
        simpa [before, equalityFrame,
          BitMachineStackEmbedding.cfg,
          BitMachineStackEmbedding.stackCfg, equalityStack]
          using hb.trans (hpEq 12 (by simp))
    exact hbefore.trans hstart.symm
  · omega
  · exact hpoint


#print axioms physical_coordinate_pair_bounded

end CurrentAdditive.CylinderCoordinateEqualityCallback
