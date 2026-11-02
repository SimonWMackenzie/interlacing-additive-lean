import CurrentAdditive.GaussRowZeroCallback

set_option maxHeartbeats 1000000

namespace CurrentAdditive.GaussRowZeroCallback

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding

noncomputable def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c c' : Config} {n : Nat} (h : run n c = c') (m : Nat) :
    run (n + m) c = run m c' := by
  rw [Nat.add_comm, run, Function.iterate_add_apply]
  exact congrArg (run m) h

theorem bank_id (F T : Stack → List Bool) :
    BitMachineStackEmbedding.bank (Function.Embedding.refl Stack) F T = T := by
  funext j
  exact BitMachineStackEmbedding.bank_at _ _ _ _

theorem broadcast_phase (context : List Bool) (S : Stack → List Bool)
    (hcontext : S 12 = context) (htemp : S 24 = []) :
    ∃ t ≤ 2 * context.length + 3,
      run t ⟨some (bLabel .scan), bControl ((), none), S⟩ =
        ⟨some (aLabel .afterCopy), bControl ((), none),
          SourceClausePreservingBroadcast.result 12 24 [23] context S⟩ := by
  let P := SourceClausePreservingBroadcast.program (12 : Stack) 24 [23]
  let c : TM2.Cfg (fun _ : Stack => Bool)
      SourceClausePreservingBroadcast.Label (Unit × Option Bool) :=
    ⟨some .scan, ((), none), S⟩
  have hlocal := SourceClausePreservingBroadcast.run_halt
    (12 : Stack) 24 [23] (by decide) (by decide) (by decide)
      (by decide) context S hcontext htemp
  have hh : (((advance P)^[2 * context.length + 3]) c).l = none := by
    rw [hlocal]
  obtain ⟨u, hu, he⟩ := BitMachineStackEmbedding.outputs
    (Function.Embedding.refl Stack) S bLabel bControl
    (fun v => v.1.copy) (by intro v; rfl)
    (some (aLabel .afterCopy)) P program (by intro l; rfl) c
    (2 * context.length + 3) hh
  change run u (BitMachineStackEmbedding.cfg
      (Function.Embedding.refl Stack) S bLabel bControl
      (some (aLabel .afterCopy)) c) = _ at he
  have hstart : BitMachineStackEmbedding.cfg
      (Function.Embedding.refl Stack) S bLabel bControl
      (some (aLabel .afterCopy)) c =
      ⟨some (bLabel .scan), bControl ((), none), S⟩ := by
    simp [BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
      bank_id, c]
  rw [hstart, hlocal] at he
  refine ⟨u, hu, ?_⟩
  simpa [BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    bank_id] using he

theorem after_copy_step (S : Stack → List Bool) :
    run 1 ⟨some (aLabel .afterCopy), bControl ((), none), S⟩ =
      ⟨some (pLabel (.inl .scan)),
        pControl (CurrentAdditive.GaussListContext.PreservingV2Program.copyControl
          ((), none)), S⟩ := by
  rfl

def selectedLocal (source : List Bool) (word : List Bool)
    (suffix : List (List Bool)) :
    CurrentAdditive.GaussListContext.PreservingV2Program.Stack → List Bool :=
  ![SourceListEncoding.fields suffix, [], [], [], [],
    List.replicate word.length true, word, [], source, []]

theorem extract_phase (pre : List (List Bool)) (cell : List Bool)
    (suffix : List (List Bool)) (S : Stack → List Bool)
    (hbank : ∀ j, S (cellSlot j) =
      CurrentAdditive.GaussListContext.PreservingV2Program.initialBank
        (SourceListEncoding.encode (pre ++ cell :: suffix)) pre.length j) :
    ∃ t ≤ 2 * (SourceListEncoding.encode (pre ++ cell :: suffix)).length + 5 +
       (4 * (pre ++ cell :: suffix).length.bits.length + 6 +
         CurrentAdditive.GaussListContext.IndexedFieldProgram.fieldCost
           (pre ++ [cell])),
      run t
        ⟨some (pLabel (.inl .scan)),
          pControl (CurrentAdditive.GaussListContext.PreservingV2Program.copyControl
            ((), none)), S⟩ =
        ⟨some (aLabel .afterGet),
          pControl (CurrentAdditive.GaussListContext.PreservingV2Program.v2Control
            (CurrentAdditive.GaussListContext.IndexedV2Program.indexControl
              (SourceListMachineFields.coreControl
                (some true, false), none))),
          BitMachineStackEmbedding.bank cellSlot S
            (selectedLocal (SourceListEncoding.encode (pre ++ cell :: suffix))
              cell suffix)⟩ := by
  open CurrentAdditive.GaussListContext.PreservingV2Program in
    obtain ⟨t, ht, hr⟩ := select_preserving pre cell suffix
  let source := SourceListEncoding.encode (pre ++ cell :: suffix)
  let c := CurrentAdditive.GaussListContext.PreservingV2Program.initial
    source pre.length
  have hhalt : (((advance
      CurrentAdditive.GaussListContext.PreservingV2Program.program)^[t]) c).l = none := by
    change (CurrentAdditive.GaussListContext.PreservingV2Program.run t c).l = none
    rw [hr]
  obtain ⟨u, hu, he⟩ := BitMachineStackEmbedding.outputs
    cellSlot S pLabel pControl (fun v => v.1.get)
    (by intro v; rfl) (some (aLabel .afterGet))
    CurrentAdditive.GaussListContext.PreservingV2Program.program program
    (by intro l; rfl) c t hhalt
  change run u (BitMachineStackEmbedding.cfg cellSlot S pLabel pControl
      (some (aLabel .afterGet)) c) = _ at he
  have hstart : BitMachineStackEmbedding.cfg cellSlot S pLabel pControl
      (some (aLabel .afterGet)) c =
      ⟨some (pLabel (.inl .scan)),
        pControl (CurrentAdditive.GaussListContext.PreservingV2Program.copyControl
          ((), none)), S⟩ := by
    simp only [BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg]
    congr 1
    exact BitMachineStackEmbedding.bank_eq_self cellSlot S _
      (fun j => (hbank j).symm)
  change ((advance CurrentAdditive.GaussListContext.PreservingV2Program.program)^[t]) c = _ at hr
  rw [hstart, hr] at he
  refine ⟨u, hu.trans ht, ?_⟩
  simpa only [BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    selectedLocal] using he

theorem after_get_step (v : Control) (S : Stack → List Bool) :
    run 1 ⟨some (aLabel .afterGet), v, S⟩ =
      ⟨some (aLabel (.preclear 0)), v, S⟩ := by rfl

def preclearLabel : Fin 15 → Label
  | ⟨n, hn⟩ => if h : n < 14 then aLabel (.preclear ⟨n, h⟩)
      else aLabel .finishPreclear

theorem preclearBank_injective : Function.Injective preclearBank := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [preclearBank]

theorem preclearBank_cover (k : Stack) (hl : 15 ≤ k.val)
    (hu : k.val < 30) (hne : k ≠ 21) :
    ∃ i : Fin 14, preclearBank i = k := by
  fin_cases k <;> simp_all [preclearBank] <;> decide

theorem preclearBank_omits21 : ∀ i : Fin 14, preclearBank i ≠ 21 := by
  intro i
  fin_cases i <;> decide

theorem preclearLabel_step (i : Fin 14) :
    preclearLabel i.castSucc = aLabel (.preclear i) ∧
    preclearLabel i.succ = aLabel (nextPreclear i) := by
  fin_cases i <;> simp [preclearLabel, nextPreclear]

theorem preclearLabel_finish :
    preclearLabel (Fin.last 14) = aLabel .finishPreclear := by
  simp [preclearLabel]

theorem preclear_run (v : Base) (S : Stack → List Bool) :
    run ((∑ i : Fin 14, (S (preclearBank i)).length) + 15)
      ⟨some (aLabel (.preclear 0)), (v, none), S⟩ =
      ⟨some (aLabel .afterPreclear), (v, none),
        BitMachineClearBank.cleared preclearBank S⟩ := by
  change ((advance program)^[(∑ i : Fin 14, (S (preclearBank i)).length) + 14 + 1])
      ⟨some (preclearLabel 0), (v, none), S⟩ = _
  apply BitMachineClearBank.clear_bank_run program id
    (aLabel .afterPreclear) 14 preclearBank preclearBank_injective
    preclearLabel
  · intro i
    obtain ⟨hi, hn⟩ := preclearLabel_step i
    rw [hi, hn]
    rfl
  · rw [preclearLabel_finish]
    rfl

theorem zeroSlot_range (j : Fin Z.stackCount) :
    15 ≤ (zeroSlot j).val ∧ (zeroSlot j).val < 30 := by
  have h := (zeroPerm (zeroSmall j)).isLt
  change 15 ≤ 15 + (zeroPerm (zeroSmall j)).val ∧
    15 + (zeroPerm (zeroSmall j)).val < 30
  omega

theorem cleared_zero_input (S : Stack → List Bool) (cell : List Bool)
    (hcell : S 21 = cell) :
    ∀ j : Fin Z.stackCount,
      (BitMachineClearBank.cleared preclearBank S) (zeroSlot j) =
        (Z.init cell).stk j := by
  intro j
  by_cases hj : j = Z.input
  · subst j
    rw [zero_input_slot]
    rw [BitMachineClearBank.cleared_foreign preclearBank S 21
      preclearBank_omits21]
    simpa [BitMachine.Machine.init] using hcell
  · have hne : zeroSlot j ≠ 21 := by
      intro he
      have hi := zeroSlot.injective (he.trans zero_input_slot.symm)
      exact hj hi
    obtain ⟨i, hi⟩ := preclearBank_cover (zeroSlot j)
      (zeroSlot_range j).1 (zeroSlot_range j).2 hne
    rw [← hi, BitMachineClearBank.cleared_bank]
    simp [BitMachine.Machine.init, hj]

theorem selectedLocal_cell (source cell : List Bool)
    (suffix : List (List Bool)) (S : Stack → List Bool) :
    (BitMachineStackEmbedding.bank cellSlot S
      (selectedLocal source cell suffix)) 21 = cell := by
  have h := BitMachineStackEmbedding.bank_at cellSlot S
    (selectedLocal source cell suffix) (6 : CurrentAdditive.GaussListContext.PreservingV2Program.Stack)
  simpa [cellSlot, selectedLocal] using h

theorem after_preclear_step (S : Stack → List Bool) (v : Control) :
    run 1 ⟨some (aLabel .afterPreclear), v, S⟩ =
      ⟨some (zLabel Z.start), zControl Z.initial, S⟩ := by rfl

theorem zero_phase (cell : List Bool) (S : Stack → List Bool)
    (hbank : ∀ j, S (zeroSlot j) = (Z.init cell).stk j) :
    ∃ t ≤ CurrentAdditive.GaussRawZeroCheck.clock cell,
      run t ⟨some (zLabel Z.start), zControl Z.initial, S⟩ =
        ⟨some (aLabel .afterZero),
          zControl (Z.run (CurrentAdditive.GaussRawZeroCheck.clock cell)
            (Z.init cell)).var,
          BitMachineStackEmbedding.bank zeroSlot S
            (Z.run (CurrentAdditive.GaussRawZeroCheck.clock cell)
              (Z.init cell)).stk⟩ := by
  let c := Z.init cell
  have hout := BitMachine.outputsWithin_at_bound Z
    (CurrentAdditive.GaussRawZeroCheck.outputs cell)
  have hhalt : (((advance Z.program)^[CurrentAdditive.GaussRawZeroCheck.clock cell]) c).l = none := by
    exact hout.1
  obtain ⟨u, hu, he⟩ := BitMachineStackEmbedding.outputs
    zeroSlot S zLabel zControl (fun v => v.1.zero)
    (by intro v; rfl) (some (aLabel .afterZero))
    Z.program program (by intro l; rfl) c
    (CurrentAdditive.GaussRawZeroCheck.clock cell) hhalt
  change run u (BitMachineStackEmbedding.cfg zeroSlot S zLabel zControl
      (some (aLabel .afterZero)) c) = _ at he
  have hstart : BitMachineStackEmbedding.cfg zeroSlot S zLabel zControl
      (some (aLabel .afterZero)) c =
      ⟨some (zLabel Z.start), zControl Z.initial, S⟩ := by
    simp only [BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg]
    congr 1
    exact BitMachineStackEmbedding.bank_eq_self zeroSlot S _
      (fun j => (hbank j).symm)
  rw [hstart] at he
  refine ⟨u, hu, ?_⟩
  simp only [BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    hhalt] at he
  simpa only [c] using he

theorem after_zero_step (b : Bool) (v : Fin Z.controlCount)
    (S : Stack → List Bool) (hout : S (zeroSlot Z.output) = [b]) :
    run 1 ⟨some (aLabel .afterZero), zControl v, S⟩ =
      ⟨some (aLabel (.clear 0)), zControl v,
        Function.update (Function.update S (zeroSlot Z.output) [])
          9 ((!b) :: S 9)⟩ := by
  have h9 : (9 : Stack) ≠ zeroSlot Z.output := by
    intro h
    have hv := congrArg Fin.val h
    simp [zeroSlot] at hv
    omega
  simp [run, advance, TM2.step, TM2.stepAux, aLabel, program, hout,
    Function.update_apply, h9, zControl]

def clearLabel : Fin 16 → Label
  | ⟨n, hn⟩ => if h : n < 15 then aLabel (.clear ⟨n, h⟩)
      else aLabel .finishClear

theorem clearBank_injective : Function.Injective clearBank := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [clearBank]

theorem clearBank_cover (k : Stack) (hl : 15 ≤ k.val)
    (hu : k.val < 30) : ∃ i : Fin 15, clearBank i = k := by
  fin_cases k <;> simp_all [clearBank] <;> decide

theorem clearLabel_step (i : Fin 15) :
    clearLabel i.castSucc = aLabel (.clear i) ∧
    clearLabel i.succ = aLabel (nextClear i) := by
  fin_cases i <;> simp [clearLabel, nextClear]

theorem clearLabel_finish :
    clearLabel (Fin.last 15) = aLabel .finishClear := by
  simp [clearLabel]

theorem clear_run (v : Base) (S : Stack → List Bool) :
    run ((∑ i : Fin 15, (S (clearBank i)).length) + 16)
      ⟨some (aLabel (.clear 0)), (v, none), S⟩ =
      ⟨some (aLabel .done), (v, none),
        BitMachineClearBank.cleared clearBank S⟩ := by
  change ((advance program)^[(∑ i : Fin 15, (S (clearBank i)).length) + 15 + 1])
      ⟨some (clearLabel 0), (v, none), S⟩ = _
  apply BitMachineClearBank.clear_bank_run program id
    (aLabel .done) 15 clearBank clearBank_injective clearLabel
  · intro i
    obtain ⟨hi, hn⟩ := clearLabel_step i
    rw [hi, hn]
    rfl
  · rw [clearLabel_finish]
    rfl

theorem done_step (v : Control) (S : Stack → List Bool) :
    run 1 ⟨some (aLabel .done), v, S⟩ = ⟨none, v, S⟩ := by rfl

def cellCost (pre : List (List Bool)) (cell : List Bool)
    (suffix : List (List Bool)) : Nat :=
  let source := SourceListEncoding.encode (pre ++ cell :: suffix)
  2 * source.length + 5 +
    (4 * (pre ++ cell :: suffix).length.bits.length + 6 +
      CurrentAdditive.GaussListContext.IndexedFieldProgram.fieldCost
        (pre ++ [cell]))

noncomputable def selectedAfter (S : Stack → List Bool)
    (pre : List (List Bool)) (cell : List Bool)
    (suffix : List (List Bool)) : Stack → List Bool :=
  BitMachineStackEmbedding.bank cellSlot S
    (selectedLocal (SourceListEncoding.encode (pre ++ cell :: suffix))
      cell suffix)

theorem callback_selected (pre : List (List Bool)) (cell : List Bool)
    (suffix : List (List Bool)) (S : Stack → List Bool)
    (hcontext : S 12 = List.replicate pre.length true)
    (htemp : S 24 = [])
    (hbank : ∀ j,
      (SourceClausePreservingBroadcast.result 12 24 [23]
        (List.replicate pre.length true) S) (cellSlot j) =
        CurrentAdditive.GaussListContext.PreservingV2Program.initialBank
          (SourceListEncoding.encode (pre ++ cell :: suffix)) pre.length j) :
    let B := SourceClausePreservingBroadcast.result 12 24 [23]
      (List.replicate pre.length true) S
    let C := selectedAfter B pre cell suffix
    let D := BitMachineClearBank.cleared preclearBank C
    let E := BitMachineStackEmbedding.bank zeroSlot D
      (Z.run (CurrentAdditive.GaussRawZeroCheck.clock cell)
        (Z.init cell)).stk
    let b := !((CurrentAdditive.GaussRawZeroCheck.numeratorWord cell).any id)
    let F := Function.update (Function.update E (zeroSlot Z.output) [])
      9 ((!b) :: E 9)
    ∃ t ≤ (2 * pre.length + 3) + 1 + cellCost pre cell suffix + 1 +
        ((∑ i : Fin 14, (C (preclearBank i)).length) + 15) + 1 +
        CurrentAdditive.GaussRawZeroCheck.clock cell + 1 +
        ((∑ i : Fin 15, (F (clearBank i)).length) + 16) + 1,
      ∃ v : Control,
        run t ⟨some (bLabel .scan), bControl ((), none), S⟩ =
          ⟨none, v, BitMachineClearBank.cleared clearBank F⟩ := by
  dsimp only
  let B := SourceClausePreservingBroadcast.result 12 24 [23]
    (List.replicate pre.length true) S
  let C := selectedAfter B pre cell suffix
  let D := BitMachineClearBank.cleared preclearBank C
  let E := BitMachineStackEmbedding.bank zeroSlot D
    (Z.run (CurrentAdditive.GaussRawZeroCheck.clock cell)
      (Z.init cell)).stk
  let b := !((CurrentAdditive.GaussRawZeroCheck.numeratorWord cell).any id)
  let F := Function.update (Function.update E (zeroSlot Z.output) [])
    9 ((!b) :: E 9)
  obtain ⟨a, ha, hcopy⟩ := broadcast_phase
    (List.replicate pre.length true) S hcontext htemp
  have hafter := after_copy_step B
  obtain ⟨c, hc, hselect⟩ := extract_phase pre cell suffix B hbank
  change run c _ = ⟨some (aLabel .afterGet), _, C⟩ at hselect
  have hget := after_get_step
    (pControl (CurrentAdditive.GaussListContext.PreservingV2Program.v2Control
      (CurrentAdditive.GaussListContext.IndexedV2Program.indexControl
        (SourceListMachineFields.coreControl (some true, false), none)))) C
  have hclear := preclear_run
    (pControl (CurrentAdditive.GaussListContext.PreservingV2Program.v2Control
      (CurrentAdditive.GaussListContext.IndexedV2Program.indexControl
        (SourceListMachineFields.coreControl (some true, false), none)))).1 C
  have hpre := after_preclear_step D
    (pControl (CurrentAdditive.GaussListContext.PreservingV2Program.v2Control
      (CurrentAdditive.GaussListContext.IndexedV2Program.indexControl
        (SourceListMachineFields.coreControl (some true, false), none))))
  have hcell : C 21 = cell := selectedLocal_cell _ cell suffix B
  have hzeroInit := cleared_zero_input C cell hcell
  obtain ⟨z, hz, hzero⟩ := zero_phase cell D hzeroInit
  change run z _ = ⟨some (aLabel .afterZero), _, E⟩ at hzero
  have houtput : E (zeroSlot Z.output) = [b] := by
    change BitMachineStackEmbedding.bank zeroSlot D
      (Z.run (CurrentAdditive.GaussRawZeroCheck.clock cell)
        (Z.init cell)).stk (zeroSlot Z.output) = [b]
    rw [BitMachineStackEmbedding.bank_at]
    have hout := (BitMachine.outputsWithin_at_bound Z
      (CurrentAdditive.GaussRawZeroCheck.outputs cell)).2
    simpa [b, CurrentAdditive.GaussRawZeroCheck.result] using hout
  have hflag := after_zero_step b
    (Z.run (CurrentAdditive.GaussRawZeroCheck.clock cell)
      (Z.init cell)).var E houtput
  change run 1 _ = ⟨some (aLabel (.clear 0)), _, F⟩ at hflag
  have hclean := clear_run
    (zControl (Z.run (CurrentAdditive.GaussRawZeroCheck.clock cell)
      (Z.init cell)).var).1 F
  have hdone := done_step
    (zControl (Z.run (CurrentAdditive.GaussRawZeroCheck.clock cell)
      (Z.init cell)).var) (BitMachineClearBank.cleared clearBank F)
  have h01 := (run_add hcopy 1).trans hafter
  have h02 := (run_add h01 c).trans hselect
  have h03 := (run_add h02 1).trans hget
  have h04 := (run_add h03 _).trans hclear
  have h05 := (run_add h04 1).trans hpre
  have h06 := (run_add h05 z).trans hzero
  have h07 := (run_add h06 1).trans hflag
  have h08 := (run_add h07 _).trans hclean
  have h09 := (run_add h08 1).trans hdone
  have ha' : a ≤ 2 * pre.length + 3 := by simpa using ha
  have hc' : c ≤ cellCost pre cell suffix := by exact hc
  have hbound :
      a + 1 + c + 1 +
        ((∑ i : Fin 14, (C (preclearBank i)).length) + 15) + 1 + z + 1 +
        ((∑ i : Fin 15, (F (clearBank i)).length) + 16) + 1 ≤
      (2 * pre.length + 3) + 1 + cellCost pre cell suffix + 1 +
        ((∑ i : Fin 14, (C (preclearBank i)).length) + 15) + 1 +
        CurrentAdditive.GaussRawZeroCheck.clock cell + 1 +
        ((∑ i : Fin 15, (F (clearBank i)).length) + 16) + 1 := by
    omega
  refine ⟨a + 1 + c + 1 +
    ((∑ i : Fin 14, (C (preclearBank i)).length) + 15) + 1 + z + 1 +
    ((∑ i : Fin 15, (F (clearBank i)).length) + 16) + 1,
    by simpa only [B, C, F] using hbound,
    zControl (Z.run (CurrentAdditive.GaussRawZeroCheck.clock cell)
      (Z.init cell)).var, ?_⟩
  simpa only [F] using h09

theorem cellSlot_outside (k : Stack)
    (hk : k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 12 ∨ k = 13 ∨
      k = 30 ∨ k = 31) :
    ¬ ∃ j, cellSlot j = k := by
  rintro ⟨j, hj⟩
  rcases hk with h | h | h | h | h | h | h <;>
    subst k <;> fin_cases j <;> simp_all [cellSlot]

theorem zeroSlot_outside (k : Stack)
    (hk : k.val < 15 ∨ 30 ≤ k.val) :
    ¬ ∃ j, zeroSlot j = k := by
  rintro ⟨j, hj⟩
  have hr := zeroSlot_range j
  have hv := congrArg Fin.val hj
  omega

theorem preclearBank_outside (k : Stack)
    (hk : k.val < 15 ∨ 30 ≤ k.val) :
    ∀ i, preclearBank i ≠ k := by
  intro i hi
  have hval : 15 ≤ (preclearBank i).val ∧
      (preclearBank i).val < 30 := by
    fin_cases i <;> decide
  have hv := congrArg Fin.val hi
  omega

theorem clearBank_outside (k : Stack)
    (hk : k.val < 15 ∨ 30 ≤ k.val) :
    ∀ i, clearBank i ≠ k := by
  intro i hi
  have hval : 15 ≤ (clearBank i).val ∧
      (clearBank i).val < 30 := by
    fin_cases i <;> decide
  have hv := congrArg Fin.val hi
  omega

theorem final_preserves_foreign (pre : List (List Bool))
    (cell : List Bool) (suffix : List (List Bool))
    (S : Stack → List Bool) (k : Stack)
    (hk : k = 8 ∨ k = 10 ∨ k = 12 ∨ k = 13 ∨ k = 30 ∨ k = 31) :
    let B := SourceClausePreservingBroadcast.result 12 24 [23]
      (List.replicate pre.length true) S
    let C := selectedAfter B pre cell suffix
    let D := BitMachineClearBank.cleared preclearBank C
    let E := BitMachineStackEmbedding.bank zeroSlot D
      (Z.run (CurrentAdditive.GaussRawZeroCheck.clock cell)
        (Z.init cell)).stk
    let b := !((CurrentAdditive.GaussRawZeroCheck.numeratorWord cell).any id)
    let F := Function.update (Function.update E (zeroSlot Z.output) [])
      9 ((!b) :: E 9)
    (h12 : S 12 = List.replicate pre.length true) →
      BitMachineClearBank.cleared clearBank F k = S k := by
  intro B C D E b F h12
  have hval : k.val < 15 ∨ 30 ≤ k.val := by
    rcases hk with h | h | h | h | h | h <;> subst k <;> decide
  have h9 : k ≠ 9 := by
    rcases hk with h | h | h | h | h | h <;> subst k <;> decide
  have hout : k ≠ zeroSlot Z.output := by
    intro he
    exact zeroSlot_outside k hval ⟨Z.output, he.symm⟩
  have hB : B k = S k := by
    by_cases hc : k = 12
    · subst k
      simpa [B, h12] using
        SourceClausePreservingBroadcast.source_restored
          (12 : Stack) 24 [23] (by decide)
          (List.replicate pre.length true) S
    · have h24 : k ≠ 24 := by
        intro he
        have hv := congrArg Fin.val he
        omega
      have h23 : k ∉ ([23] : List Stack) := by
        intro he
        have hv : k = 23 := by simpa using he
        have hv' := congrArg Fin.val hv
        omega
      exact SourceClausePreservingBroadcast.other_preserved
        (12 : Stack) 24 [23] _ S k hc h24 h23
  change BitMachineClearBank.cleared clearBank F k = S k
  rw [BitMachineClearBank.cleared_foreign clearBank F k
      (clearBank_outside k hval)]
  have hF : F k = E k := by
    simp [F, Function.update_of_ne, h9, hout]
  rw [hF]
  change BitMachineStackEmbedding.bank zeroSlot D
    (Z.run (CurrentAdditive.GaussRawZeroCheck.clock cell)
      (Z.init cell)).stk k = S k
  rw [BitMachineStackEmbedding.bank_outside zeroSlot D _ k
    (zeroSlot_outside k hval)]
  change BitMachineClearBank.cleared preclearBank C k = S k
  rw [BitMachineClearBank.cleared_foreign preclearBank C k
    (preclearBank_outside k hval)]
  change BitMachineStackEmbedding.bank cellSlot B
    (selectedLocal (SourceListEncoding.encode (pre ++ cell :: suffix))
      cell suffix) k = S k
  rw [BitMachineStackEmbedding.bank_outside cellSlot B _ k
    (cellSlot_outside k (by
      rcases hk with h | h | h | h | h | h <;> subst k <;> simp))]
  exact hB

theorem final_output (pre : List (List Bool))
    (cell : List Bool) (suffix : List (List Bool))
    (S : Stack → List Bool) :
    let B := SourceClausePreservingBroadcast.result 12 24 [23]
      (List.replicate pre.length true) S
    let C := selectedAfter B pre cell suffix
    let D := BitMachineClearBank.cleared preclearBank C
    let E := BitMachineStackEmbedding.bank zeroSlot D
      (Z.run (CurrentAdditive.GaussRawZeroCheck.clock cell)
        (Z.init cell)).stk
    let b := !((CurrentAdditive.GaussRawZeroCheck.numeratorWord cell).any id)
    let F := Function.update (Function.update E (zeroSlot Z.output) [])
      9 ((!b) :: E 9)
    (BitMachineClearBank.cleared clearBank F) 9 =
      ((CurrentAdditive.GaussRawZeroCheck.numeratorWord cell).any id) :: S 9 := by
  intro B C D E b F
  have h9val : (9 : Stack).val < 15 ∨ 30 ≤ (9 : Stack).val := by decide
  have hB : B 9 = S 9 := by
    exact SourceClausePreservingBroadcast.other_preserved
      (12 : Stack) 24 [23] _ S 9 (by decide)
        (by decide) (by decide)
  have hC : C 9 = B 9 := by
    change BitMachineStackEmbedding.bank cellSlot B
      (selectedLocal (SourceListEncoding.encode (pre ++ cell :: suffix))
        cell suffix) 9 = B 9
    exact BitMachineStackEmbedding.bank_outside cellSlot B _ 9
      (cellSlot_outside 9 (by simp))
  have hD : D 9 = C 9 := by
    exact BitMachineClearBank.cleared_foreign preclearBank C 9
      (preclearBank_outside 9 h9val)
  have hE : E 9 = D 9 := by
    exact BitMachineStackEmbedding.bank_outside zeroSlot D _ 9
      (zeroSlot_outside 9 h9val)
  have hF : F 9 = ((!b) :: E 9) := by simp [F]
  rw [BitMachineClearBank.cleared_foreign clearBank F 9
    (clearBank_outside 9 h9val), hF, hE, hD, hC, hB]
  simp [b]

theorem final_scratch (pre : List (List Bool))
    (cell : List Bool) (suffix : List (List Bool))
    (S : Stack → List Bool) :
    let B := SourceClausePreservingBroadcast.result 12 24 [23]
      (List.replicate pre.length true) S
    let C := selectedAfter B pre cell suffix
    let D := BitMachineClearBank.cleared preclearBank C
    let E := BitMachineStackEmbedding.bank zeroSlot D
      (Z.run (CurrentAdditive.GaussRawZeroCheck.clock cell)
        (Z.init cell)).stk
    let b := !((CurrentAdditive.GaussRawZeroCheck.numeratorWord cell).any id)
    let F := Function.update (Function.update E (zeroSlot Z.output) [])
      9 ((!b) :: E 9)
    ∀ i : Fin 15,
      (BitMachineClearBank.cleared clearBank F) (clearBank i) = [] := by
  intro B C D E b F i
  exact BitMachineClearBank.cleared_bank clearBank F i

theorem broadcast_cell_bank (pre : List (List Bool))
    (cell : List Bool) (suffix : List (List Bool))
    (S : Stack → List Bool)
    (hrow : S 6 = SourceListEncoding.encode (pre ++ cell :: suffix))
    (hscratch : ∀ k : Stack, 15 ≤ k.val → k.val < 30 → S k = []) :
    ∀ j : CurrentAdditive.GaussListContext.PreservingV2Program.Stack,
      (SourceClausePreservingBroadcast.result 12 24 [23]
        (List.replicate pre.length true) S) (cellSlot j) =
      CurrentAdditive.GaussListContext.PreservingV2Program.initialBank
        (SourceListEncoding.encode (pre ++ cell :: suffix)) pre.length j := by
  have h15 := hscratch 15 (by decide) (by decide)
  have h16 := hscratch 16 (by decide) (by decide)
  have h17 := hscratch 17 (by decide) (by decide)
  have h18 := hscratch 18 (by decide) (by decide)
  have h19 := hscratch 19 (by decide) (by decide)
  have h20 := hscratch 20 (by decide) (by decide)
  have h21 := hscratch 21 (by decide) (by decide)
  have h22 := hscratch 22 (by decide) (by decide)
  have h23 := hscratch 23 (by decide) (by decide)
  have h24 := hscratch 24 (by decide) (by decide)
  intro j
  fin_cases j <;>
    simp [cellSlot,
      CurrentAdditive.GaussListContext.PreservingV2Program.initialBank,
      SourceClausePreservingBroadcast.result,
      BitMachineBroadcast.prepend, hrow, h15, h16, h17, h18,
      h19, h20, h21, h22, h23, h24]

noncomputable def finalState (pre : List (List Bool))
    (cell : List Bool) (suffix : List (List Bool))
    (S : Stack → List Bool) : Stack → List Bool :=
  let B := SourceClausePreservingBroadcast.result 12 24 [23]
    (List.replicate pre.length true) S
  let C := selectedAfter B pre cell suffix
  let D := BitMachineClearBank.cleared preclearBank C
  let E := BitMachineStackEmbedding.bank zeroSlot D
    (Z.run (CurrentAdditive.GaussRawZeroCheck.clock cell)
      (Z.init cell)).stk
  let b := !((CurrentAdditive.GaussRawZeroCheck.numeratorWord cell).any id)
  let F := Function.update (Function.update E (zeroSlot Z.output) [])
    9 ((!b) :: E 9)
  BitMachineClearBank.cleared clearBank F

noncomputable def callbackCost (pre : List (List Bool))
    (cell : List Bool) (suffix : List (List Bool))
    (S : Stack → List Bool) : Nat :=
  let B := SourceClausePreservingBroadcast.result 12 24 [23]
    (List.replicate pre.length true) S
  let C := selectedAfter B pre cell suffix
  let D := BitMachineClearBank.cleared preclearBank C
  let E := BitMachineStackEmbedding.bank zeroSlot D
    (Z.run (CurrentAdditive.GaussRawZeroCheck.clock cell)
      (Z.init cell)).stk
  let b := !((CurrentAdditive.GaussRawZeroCheck.numeratorWord cell).any id)
  let F := Function.update (Function.update E (zeroSlot Z.output) [])
    9 ((!b) :: E 9)
  (2 * pre.length + 3) + 1 + cellCost pre cell suffix + 1 +
    ((∑ i : Fin 14, (C (preclearBank i)).length) + 15) + 1 +
    CurrentAdditive.GaussRawZeroCheck.clock cell + 1 +
    ((∑ i : Fin 15, (F (clearBank i)).length) + 16) + 1

theorem callback_run_clean (pre : List (List Bool))
    (cell : List Bool) (suffix : List (List Bool))
    (S : Stack → List Bool)
    (hrow : S 6 = SourceListEncoding.encode (pre ++ cell :: suffix))
    (hcontext : S 12 = List.replicate pre.length true)
    (hscratch : ∀ k : Stack, 15 ≤ k.val → k.val < 30 → S k = []) :
    ∃ t ≤ callbackCost pre cell suffix S,
      ∃ v : Control,
        run t ⟨some (bLabel .scan), bControl ((), none), S⟩ =
          ⟨none, v, finalState pre cell suffix S⟩ ∧
        (finalState pre cell suffix S) 9 =
          ((CurrentAdditive.GaussRawZeroCheck.numeratorWord cell).any id) :: S 9 ∧
        (∀ i : Fin 15, (finalState pre cell suffix S) (clearBank i) = []) ∧
        (∀ k : Stack,
          k = 8 ∨ k = 10 ∨ k = 12 ∨ k = 13 ∨ k = 30 ∨ k = 31 →
          (finalState pre cell suffix S) k = S k) := by
  have h24 := hscratch 24 (by decide) (by decide)
  have hb := broadcast_cell_bank pre cell suffix S hrow hscratch
  obtain ⟨t, ht, v, hr⟩ := callback_selected pre cell suffix S
    hcontext h24 hb
  refine ⟨t, ?_, v, ?_, ?_, ?_, ?_⟩
  · simpa only [callbackCost] using ht
  · simpa only [finalState] using hr
  · exact final_output pre cell suffix S
  · exact final_scratch pre cell suffix S
  · intro k hk
    exact final_preserves_foreign pre cell suffix S k hk hcontext

end CurrentAdditive.GaussRowZeroCallback
