import CurrentAdditive.MinimumRatioCallbackLayout
import CurrentAdditive.CylinderContextScanRun
import EthInapproximability.CurrentPaper.BitMachineClearBank

set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 100
set_option maxRecDepth 4096

/-! Physical coefficient lookup at the source-position cursor. The source
entry on bank 6 and accumulated output on bank 9 are preserved. The encoded
coefficient vector is read on bank 12; the unary index is read on bank 10.
The chosen coefficient is installed on bank 21 and all lookup scratch is
physically cleared. This is one producer component, not a whole list join. -/

namespace CurrentAdditive.RatioCoefficientLookup

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open MinimumRatioCallbackLayout CurrentAdditive.GaussListContext

def localSlot : CylinderContextScanStep.Stack → Fin 32 :=
  ![15,16,17,18,19,20,21,22,12,23,10,24]

noncomputable def locate : CylinderContextScanStep.Stack ↪ Stack where
  toFun j := low (localSlot j)
  inj' := by
    intro a b h
    have hh := congrArg Fin.val h
    fin_cases a <;> fin_cases b <;>
      simp_all [localSlot, low]

abbrev Label := CylinderContextScanStep.Label ⊕ Unit
abbrev Control := CylinderContextScanStep.Control

noncomputable def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineStackEmbedding.stmt locate Sum.inl id id
      (some (.inr ())) (CylinderContextScanStep.program l)
  | .inr () => .halt

noncomputable def initialControl := CylinderContextScanStep.copyControl ((),none)

def start : Label := .inl (.inl .scan)

noncomputable def finalControl :=
  CylinderContextScanStep.getterControl
    (PreservingV2Program.v2Control
      (IndexedV2Program.indexControl
        (SourceListMachineFields.coreControl (some true,false),none)))

def localScratch : Fin 9 → CylinderContextScanStep.Stack := ![0,1,2,3,4,5,7,9,11]

noncomputable def scratch : Fin 9 ↪ Stack where
  toFun i := locate (localScratch i)
  inj' := by
    intro a b h
    have hh := locate.injective h
    fin_cases a <;> fin_cases b <;> simp_all [localScratch]

abbrev ClearLabel := Fin 10 ⊕ Unit
abbrev ClearControl := Unit × Option Bool

def clearNext (j : Fin 10) : ClearLabel :=
  if h : j.val+1 < 10 then .inl ⟨j.val+1,h⟩ else .inr ()

noncomputable def clearProgram : ClearLabel →
    TM2.Stmt (fun _ : Stack => Bool) ClearLabel ClearControl
  | .inl j => if h : j.val < 9 then
      BitMachineClearBank.clearStep (scratch ⟨j.val,h⟩) (.inl j)
        (clearNext j)
    else BitMachineClearBank.finishStep id (.inr ())
  | .inr () => .halt

theorem clear_run (S : Bank) :
    ((advance clearProgram)^[(∑ i : Fin 9, (S (scratch i)).length)+11])
      (⟨some (.inl 0), ((),none), S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, ((),none), BitMachineClearBank.cleared scratch S⟩ := by
  have h := BitMachineClearBank.clear_bank_run clearProgram id (.inr ())
    9 scratch scratch.injective (fun j => .inl j) (by
      intro i
      have hn : clearNext i.castSucc = .inl i.succ := by
        unfold clearNext
        rw [dif_pos (by change i.val + 1 < 10; have := i.isLt; omega)]
        rfl
      simp [clearProgram, i.isLt, hn]) (by simp [clearProgram]) () S
  have hhalt : advance clearProgram
      (⟨some (.inr ()), ((),none), BitMachineClearBank.cleared scratch S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none,((),none),BitMachineClearBank.cleared scratch S⟩ := rfl
  rw [show (∑ i : Fin 9, (S (scratch i)).length)+11 =
      ((∑ i : Fin 9, (S (scratch i)).length)+9+1)+1 by omega,
    Function.iterate_succ_apply', h]
  exact hhalt

noncomputable def fullProgram := BitMachineRawSequence.program program clearProgram
  (.inl 0) initialControl ((),none)

noncomputable def fullControl : Control × ClearControl := (initialControl, ((),none))
noncomputable def fullStart : BitMachineRawSequence.Label Label ClearLabel :=
  BitMachineRawSequence.leftLabel start

private theorem bank_initial (S : Bank) (source : List Bool) (index : Nat)
    (hsource : S (locate 8) = source)
    (hindex : S (locate 10) = List.replicate index true)
    (hblank : ∀ j : CylinderContextScanStep.Stack, j ≠ 8 → j ≠ 10 →
      S (locate j) = []) :
    BitMachineStackEmbedding.bank locate S
      (CylinderContextScanStep.initialBank source index) = S := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro j
  fin_cases j
  · simpa [CylinderContextScanStep.initialBank] using (hblank 0 (by decide) (by decide)).symm
  · simpa [CylinderContextScanStep.initialBank] using (hblank 1 (by decide) (by decide)).symm
  · simpa [CylinderContextScanStep.initialBank] using (hblank 2 (by decide) (by decide)).symm
  · simpa [CylinderContextScanStep.initialBank] using (hblank 3 (by decide) (by decide)).symm
  · simpa [CylinderContextScanStep.initialBank] using (hblank 4 (by decide) (by decide)).symm
  · simpa [CylinderContextScanStep.initialBank] using (hblank 5 (by decide) (by decide)).symm
  · simpa [CylinderContextScanStep.initialBank] using (hblank 6 (by decide) (by decide)).symm
  · simpa [CylinderContextScanStep.initialBank] using (hblank 7 (by decide) (by decide)).symm
  · simpa [CylinderContextScanStep.initialBank] using hsource.symm
  · simpa [CylinderContextScanStep.initialBank] using (hblank 9 (by decide) (by decide)).symm
  · simpa [CylinderContextScanStep.initialBank] using hindex.symm
  · simpa [CylinderContextScanStep.initialBank] using (hblank 11 (by decide) (by decide)).symm

private theorem selected_as_updates (source suffix word : List Bool) (index : Nat) :
    CylinderContextScanStep.selectedBank source suffix word index =
      Function.update
        (Function.update
          (Function.update (CylinderContextScanStep.initialBank source index)
            0 suffix) 5 (List.replicate word.length true)) 6 word := by
  funext j
  fin_cases j <;>
    simp [CylinderContextScanStep.selectedBank, CylinderContextScanStep.initialBank]

theorem lookup_run (S : Bank) (pre : List (List Bool)) (word : List Bool)
    (tail : List (List Bool))
    (hsource : S (locate 8) = SourceListEncoding.encode (pre ++ word :: tail))
    (hindex : S (locate 10) = List.replicate pre.length true)
    (hblank : ∀ j : CylinderContextScanStep.Stack, j ≠ 8 → j ≠ 10 →
      S (locate j) = []) :
    let U := Function.update
      (Function.update
        (Function.update S (locate 0) (SourceListEncoding.fields tail))
        (locate 5) (List.replicate word.length true)) (locate 6) word
    ∃ t ≤ StatefulListScheduler.getterBudget pre word tail,
      ((advance program)^[t])
        (⟨some start, initialControl, S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, finalControl, U⟩ := by
  dsimp only
  let source := SourceListEncoding.encode (pre ++ word :: tail)
  have hinit := bank_initial S
    (SourceListEncoding.encode (pre ++ word :: tail)) pre.length hsource hindex hblank
  obtain ⟨t, ht, hr⟩ := CylinderContextScanStep.scan_step pre word tail
  obtain ⟨u, hu, he⟩ := BitMachineStackEmbedding.outputs locate S Sum.inl id id
    (by intro v; rfl) (some (.inr ())) CylinderContextScanStep.program program
    (by intro l; rfl) (CylinderContextScanStep.initial source pre.length) t
    (by change (CylinderContextScanStep.run t _).l = none; rw [hr])
  have hstep := he
  change ((advance program)^[u])
    (BitMachineStackEmbedding.cfg locate S Sum.inl id (some (.inr ())) _) = _ at hstep
  change ((advance CylinderContextScanStep.program)^[t]) _ = _ at hr
  rw [hr] at hstep
  simp only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg, CylinderContextScanStep.initial, hinit,
    selected_as_updates, BitMachineStackEmbedding.bank_update] at hstep
  simp only [source] at hstep
  rw [hinit] at hstep
  have hfinish : advance program
      (⟨some (.inr ()), finalControl,
        Function.update (Function.update
          (Function.update S (locate 0) (SourceListEncoding.fields tail))
          (locate 5) (List.replicate word.length true)) (locate 6) word⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, finalControl,
        Function.update (Function.update
          (Function.update S (locate 0) (SourceListEncoding.fields tail))
          (locate 5) (List.replicate word.length true)) (locate 6) word⟩ := rfl
  refine ⟨u+1, ?_, ?_⟩
  · have hb : t+1 ≤ StatefulListScheduler.getterBudget pre word tail := by
      simpa only [StatefulListScheduler.getterBudget] using Nat.add_le_add_right ht 1
    omega
  · have hstep' : ((advance program)^[u])
        (⟨some start, initialControl, S⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨some (.inr ()), finalControl,
          Function.update (Function.update
            (Function.update S (locate 0) (SourceListEncoding.fields tail))
            (locate 5) (List.replicate word.length true)) (locate 6) word⟩ := by
      simpa only [start,initialControl,finalControl,id_eq,hinit] using hstep
    rw [Function.iterate_succ_apply', hstep']
    exact hfinish

theorem cleanup_after_lookup (S : Bank) (suffix word : List Bool)
    (hblank : ∀ j : CylinderContextScanStep.Stack, j ≠ 8 → j ≠ 10 →
      S (locate j) = []) :
    BitMachineClearBank.cleared scratch
      (Function.update (Function.update (Function.update S (locate 0) suffix)
        (locate 5) (List.replicate word.length true)) (locate 6) word) =
      Function.update S (locate 6) word := by
  funext j
  by_cases hj : ∃ i, scratch i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [BitMachineClearBank.cleared_bank]
    have h6 : scratch i ≠ locate 6 := by
      intro he
      have hh := locate.injective he
      fin_cases i <;> simp [scratch, localScratch] at hh
    rw [Function.update_of_ne h6]
    have hs : S (scratch i) = [] := by
      apply hblank
      · fin_cases i <;> simp [localScratch]
      · fin_cases i <;> simp [localScratch]
    exact hs.symm
  · rw [BitMachineClearBank.cleared_foreign scratch _ j
      (by intro i; exact fun h => hj ⟨i,h⟩)]
    have h0 : j ≠ locate 0 := by
      intro he
      apply hj
      exact ⟨0, by simpa [scratch,localScratch] using he.symm⟩
    have h5 : j ≠ locate 5 := by
      intro he
      apply hj
      exact ⟨5, by simpa [scratch,localScratch] using he.symm⟩
    by_cases h6 : j = locate 6
    · subst j; simp
    · simp [Function.update_of_ne, h0,h5,h6]

def clock (pre : List (List Bool)) (word : List Bool)
    (tail : List (List Bool)) : Nat :=
  StatefulListScheduler.getterBudget pre word tail +
    (SourceListEncoding.fields tail).length + word.length + 12

theorem full_run (S : Bank) (pre : List (List Bool)) (word : List Bool)
    (tail : List (List Bool))
    (hsource : S (locate 8) = SourceListEncoding.encode (pre ++ word :: tail))
    (hindex : S (locate 10) = List.replicate pre.length true)
    (hblank : ∀ j : CylinderContextScanStep.Stack, j ≠ 8 → j ≠ 10 →
      S (locate j) = []) :
    ∃ t ≤ clock pre word tail,
      ((advance fullProgram)^[t])
        (⟨some fullStart, fullControl, S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, fullControl, Function.update S (locate 6) word⟩ := by
  let source := SourceListEncoding.encode (pre ++ word :: tail)
  let U := Function.update (Function.update
    (Function.update S (locate 0) (SourceListEncoding.fields tail))
    (locate 5) (List.replicate word.length true)) (locate 6) word
  obtain ⟨a,ha,hr⟩ := lookup_run S pre word tail hsource hindex hblank
  have hinit := bank_initial S
    (SourceListEncoding.encode (pre ++ word :: tail)) pre.length hsource hindex hblank
  have hu : U = BitMachineStackEmbedding.bank locate S
      (CylinderContextScanStep.selectedBank source
        (SourceListEncoding.fields tail) word pre.length) := by
    rw [selected_as_updates, BitMachineStackEmbedding.bank_update,
      BitMachineStackEmbedding.bank_update, BitMachineStackEmbedding.bank_update,
      hinit]
  have hsum : (∑ i : Fin 9, (U (scratch i)).length) =
      (SourceListEncoding.fields tail).length + word.length := by
    have hh (i : Fin 9) : U (scratch i) =
        CylinderContextScanStep.selectedBank source
          (SourceListEncoding.fields tail) word pre.length (localScratch i) := by
      rw [hu]
      exact BitMachineStackEmbedding.bank_at locate S _ _
    simp only [hh]
    simp [Fin.sum_univ_succ, localScratch, CylinderContextScanStep.selectedBank]
  have hb := clear_run U
  rw [hsum, cleanup_after_lookup S _ _ hblank] at hb
  obtain ⟨t,ht,he⟩ := BitMachineRawSequence.runs program clearProgram
    start (.inl 0) initialControl finalControl ((),none) ((),none)
    S U (Function.update S (locate 6) word) a
    ((SourceListEncoding.fields tail).length+word.length+11) hr hb
  refine ⟨t, ?_, ?_⟩
  · unfold clock
    omega
  · simpa only [fullProgram,fullStart,fullControl] using he

#print axioms full_run

end CurrentAdditive.RatioCoefficientLookup
