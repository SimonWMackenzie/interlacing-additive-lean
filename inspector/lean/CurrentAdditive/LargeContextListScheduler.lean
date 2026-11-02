import CurrentAdditive.LargeContextPreservingScan
import EthInapproximability.CurrentPaper.BitMachineClearBank

/-!
Fixed finite-control repeated indexed scan with a contextual callback.  Bank 8
holds the immutable canonical V2 input, bank 10 the unary zero-based index,
bank 13 the remaining unary item count, bank 9 an append-only output chosen by
the callback, and banks 12/14 are caller context and getter scratch.  The
callback sees the selected word on bank 6.  Each iteration physically runs
the counted-V2 getter; the administrative code clears all its temporary banks
before incrementing the index and repeating.  This file defines the program
and local step facts; full correctness requires a concrete callback run.
-/

namespace CurrentAdditive.LargeContextListScheduler

open EthInapproximability.CurrentPaper
open CurrentAdditive.LargeContextPreservingScan
open CurrentAdditive.GaussListContext
open Turing Turing.TM2.Stmt BitMachineEncoding

variable {L V : Type} [DecidableEq L] [Fintype L]
    [DecidableEq V] [Fintype V]

abbrev Stack := CurrentAdditive.LargeContextPreservingScan.Stack

inductive Admin where
  | check | afterGetter | afterCallback | clear (j : Fin 10)
  | finishClear | increment
  deriving DecidableEq, Fintype

abbrev Label (L : Type) := LargeContextPreservingScan.Label ⊕ (L ⊕ Admin)
abbrev Control (V : Type) :=
  (LargeContextPreservingScan.Control × V) × Option Bool
abbrev Config (L V : Type) := TM2.Cfg (fun _ : Stack => Bool) (Label L) (Control V)

def getterControl (callbackInit : V)
    (v : LargeContextPreservingScan.Control) : Control V :=
  ((v, callbackInit), none)

def callbackControl (getterInit : LargeContextPreservingScan.Control)
    (v : V) : Control V :=
  ((getterInit, v), none)

def cleanBank : Fin 10 → Stack :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 11, 14]

def nextClear (j : Fin 10) : Admin :=
  if h : j.val + 1 < 10 then .clear ⟨j.val + 1, h⟩
  else .finishClear

def clearLabel : Fin 11 → Label L :=
  fun j => if h : j.val < 10 then .inr (.inr (.clear ⟨j.val, h⟩))
    else .inr (.inr .finishClear)

def program (callback : L → TM2.Stmt (fun _ : Stack => Bool) L V)
    (callbackStart : L) (callbackInit : V) :
    Label L → TM2.Stmt (fun _ : Stack => Bool) (Label L) (Control V)
  | .inl l => BitMachineStackEmbedding.stmt
      (Function.Embedding.refl Stack) Sum.inl
      (getterControl callbackInit) (fun v => v.1.1)
      (some (.inr (.inr .afterGetter)))
      (LargeContextPreservingScan.program l)
  | .inr (.inl l) => BitMachineStackEmbedding.stmt
      (Function.Embedding.refl Stack) (fun l => .inr (.inl l))
      (callbackControl (CylinderContextScanStep.copyControl ((), none)))
      (fun v => v.1.2)
      (some (.inr (.inr .afterCallback))) (callback l)
  | .inr (.inr .check) =>
      pop 13 (fun v b => (v.1, b))
        (branch (fun v => v.2.isSome)
          (load (fun _ => getterControl callbackInit
            (CylinderContextScanStep.copyControl ((), none)))
            (goto (fun _ => .inl (.inl (.inl .scan)))))
          halt)
  | .inr (.inr .afterGetter) =>
      load (fun _ => callbackControl
        (CylinderContextScanStep.copyControl ((), none)) callbackInit)
        (goto (fun _ => .inr (.inl callbackStart)))
  | .inr (.inr .afterCallback) =>
      goto (fun _ => .inr (.inr (.clear 0)))
  | .inr (.inr (.clear j)) =>
      BitMachineClearBank.clearStep (cleanBank j)
        (.inr (.inr (.clear j))) (.inr (.inr (nextClear j)))
  | .inr (.inr .finishClear) =>
      BitMachineClearBank.finishStep id (.inr (.inr .increment))
  | .inr (.inr .increment) =>
      push 10 (fun _ => true) (goto (fun _ => .inr (.inr .check)))

def run (callback : L → TM2.Stmt (fun _ : Stack => Bool) L V)
    (callbackStart : L) (callbackInit : V) (t : Nat)
    (c : Config L V) : Config L V :=
  ((advance (program callback callbackStart callbackInit))^[t]) c

theorem run_add (callback : L → TM2.Stmt (fun _ : Stack => Bool) L V)
    (callbackStart : L) (callbackInit : V)
    {c c' : Config L V} {n : Nat}
    (h : run callback callbackStart callbackInit n c = c') (m : Nat) :
    run callback callbackStart callbackInit (n + m) c =
      run callback callbackStart callbackInit m c' := by
  rw [Nat.add_comm, run, Function.iterate_add_apply]
  exact congrArg (run callback callbackStart callbackInit m) h

def initialBank (source output context : List Bool) (count : Nat)
    (extra : Stack → List Bool) :
    Stack → List Bool :=
  Function.update
    (Function.update
      (Function.update
        (Function.update extra 8 source) 9 output) 12 context)
    13 (List.replicate count true)

def initial (source output context : List Bool) (count : Nat)
    (extra : Stack → List Bool) (callbackInit : V) : Config L V :=
  ⟨some (.inr (.inr .check)),
   getterControl callbackInit
     (CylinderContextScanStep.copyControl ((), none)),
   initialBank source output context count extra⟩

theorem program_finite :
    Finite Stack ∧ Finite (Label L) ∧ Finite (Control V) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

theorem check_positive (callback : L → TM2.Stmt (fun _ : Stack => Bool) L V)
    (callbackStart : L) (callbackInit : V) (S : Stack → List Bool)
    (v : Control V) (fuel : Nat) :
    advance (program callback callbackStart callbackInit)
      ⟨some (.inr (.inr .check)), v,
        Function.update S 13 (true :: List.replicate fuel true)⟩ =
      ⟨some (.inl (.inl (.inl .scan))),
       getterControl callbackInit
         (CylinderContextScanStep.copyControl ((), none)),
       Function.update S 13 (List.replicate fuel true)⟩ := by
  simp [program, advance, TM2.step, TM2.stepAux]

theorem check_zero (callback : L → TM2.Stmt (fun _ : Stack => Bool) L V)
    (callbackStart : L) (callbackInit : V) (S : Stack → List Bool)
    (v : Control V) :
    advance (program callback callbackStart callbackInit)
      ⟨some (.inr (.inr .check)), v, Function.update S 13 []⟩ =
      ⟨none, (v.1, none), Function.update S 13 []⟩ := by
  simp [program, advance, TM2.step, TM2.stepAux]

theorem cleanBank_injective : Function.Injective cleanBank := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [cleanBank]

theorem clearLabel_step (i : Fin 10) :
    clearLabel (L := L) i.castSucc =
      .inr (.inr (.clear i)) ∧
    clearLabel (L := L) i.succ =
      .inr (.inr (nextClear i)) := by
  fin_cases i <;> simp [clearLabel, nextClear]

theorem clearLabel_finish :
    clearLabel (L := L) (Fin.last 10) =
      .inr (.inr .finishClear) := by
  simp [clearLabel]

theorem cleanup_run (callback : L → TM2.Stmt (fun _ : Stack => Bool) L V)
    (callbackStart : L) (callbackInit : V)
    (v : LargeContextPreservingScan.Control × V)
    (S : Stack → List Bool) :
    run callback callbackStart callbackInit
      ((∑ i : Fin 10, (S (cleanBank i)).length) + 11)
      ⟨some (.inr (.inr (.clear 0))), (v, none), S⟩ =
      ⟨some (.inr (.inr .increment)), (v, none),
       BitMachineClearBank.cleared cleanBank S⟩ := by
  change ((advance (program callback callbackStart callbackInit))^[
      (∑ i : Fin 10, (S (cleanBank i)).length) + 10 + 1])
        ⟨some (clearLabel (L := L) 0), (v, none), S⟩ = _
  apply BitMachineClearBank.clear_bank_run
    (program callback callbackStart callbackInit) id
    (.inr (.inr .increment)) 10 cleanBank cleanBank_injective
    (clearLabel (L := L))
  · intro i
    obtain ⟨hi, hn⟩ := clearLabel_step (L := L) i
    rw [hi, hn]
    rfl
  · rw [clearLabel_finish]
    rfl

theorem getter_run (callback : L → TM2.Stmt (fun _ : Stack => Bool) L V)
    (callbackStart : L) (callbackInit : V)
    (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (foreign : Stack → List Bool) :
    let source := SourceListEncoding.encode (pre ++ word :: suffix)
    let selected := LargeContextPreservingScan.frame foreign
      (⟨none,
       CylinderContextScanStep.getterControl
         (PreservingV2Program.v2Control
           (IndexedV2Program.indexControl
             (SourceListMachineFields.coreControl (some true, false), none))),
       CylinderContextScanStep.selectedBank source
         (SourceListEncoding.fields suffix) word pre.length⟩ :
        CylinderContextScanStep.Config)
    ∃ t ≤ 2 * pre.length + 5 +
        (2 * source.length + 5 +
          (4 * (pre ++ word :: suffix).length.bits.length + 6 +
            IndexedFieldProgram.fieldCost (pre ++ [word]))) + 1,
      run callback callbackStart callbackInit t
        ⟨some (.inl (.inl (.inl .scan))),
         getterControl callbackInit
           (CylinderContextScanStep.copyControl ((), none)),
         (LargeContextPreservingScan.frame foreign
           (CylinderContextScanStep.initial source pre.length)).stk⟩ =
        ⟨some (.inr (.inr .afterGetter)),
         getterControl callbackInit selected.var,
         selected.stk⟩ := by
  dsimp only
  obtain ⟨t, ht, hr⟩ := LargeContextPreservingScan.lookup_halt
    pre word suffix foreign
  let c := LargeContextPreservingScan.frame foreign
    (CylinderContextScanStep.initial
      (SourceListEncoding.encode (pre ++ word :: suffix)) pre.length)
  obtain ⟨u, hu, he⟩ := BitMachineStackEmbedding.outputs
    (Function.Embedding.refl Stack) c.stk Sum.inl
    (getterControl callbackInit) (fun v => v.1.1)
    (by intro v; rfl) (some (.inr (.inr .afterGetter)))
    LargeContextPreservingScan.program
    (program callback callbackStart callbackInit)
    (by intro l; rfl) c t
    (by change (LargeContextPreservingScan.run t c).l = none; rw [hr])
  change run callback callbackStart callbackInit u
      (BitMachineStackEmbedding.cfg
        (Function.Embedding.refl Stack) c.stk Sum.inl
        (getterControl callbackInit)
        (some (.inr (.inr .afterGetter))) c) = _ at he
  change ((advance LargeContextPreservingScan.program)^[t]) c = _ at hr
  rw [hr] at he
  unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    BitMachineInline.cfg at he
  have hid (F T : Stack → List Bool) :
      BitMachineStackEmbedding.bank (Function.Embedding.refl Stack) F T = T := by
    funext j
    exact BitMachineStackEmbedding.bank_at _ _ _ _
  simp only [hid] at he
  refine ⟨u, hu.trans ht, ?_⟩
  simpa [c, LargeContextPreservingScan.frame,
    BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg] using he

theorem callback_run (callback : L → TM2.Stmt (fun _ : Stack => Bool) L V)
    (callbackStart : L) (callbackInit vOut : V)
    (getterState : LargeContextPreservingScan.Control)
    (S SOut : Stack → List Bool) (bound : Nat)
    (hcallback : ((advance callback)^[bound])
      (⟨some callbackStart, callbackInit, S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) L V) =
      ⟨none, vOut, SOut⟩) :
    ∃ t ≤ bound + 1,
      run callback callbackStart callbackInit t
        ⟨some (.inr (.inr .afterGetter)),
         getterControl callbackInit getterState, S⟩ =
        ⟨some (.inr (.inr .afterCallback)),
         callbackControl
           (CylinderContextScanStep.copyControl ((), none)) vOut,
         SOut⟩ := by
  let c : TM2.Cfg (fun _ : Stack => Bool) L V :=
    ⟨some callbackStart, callbackInit, S⟩
  obtain ⟨u, hu, he⟩ := BitMachineStackEmbedding.outputs
    (Function.Embedding.refl Stack) S (fun l => .inr (.inl l))
    (callbackControl (CylinderContextScanStep.copyControl ((), none)))
    (fun v => v.1.2) (by intro v; rfl)
    (some (.inr (.inr .afterCallback))) callback
    (program callback callbackStart callbackInit)
    (by intro l; rfl) c bound
    (by change (((advance callback)^[bound]) c).l = none;
        rw [hcallback])
  have hid (F T : Stack → List Bool) :
      BitMachineStackEmbedding.bank (Function.Embedding.refl Stack) F T = T := by
    funext j
    exact BitMachineStackEmbedding.bank_at _ _ _ _
  change run callback callbackStart callbackInit u
      (BitMachineStackEmbedding.cfg (Function.Embedding.refl Stack) S
        (fun l => .inr (.inl l))
        (callbackControl (CylinderContextScanStep.copyControl ((), none)))
        (some (.inr (.inr .afterCallback))) c) = _ at he
  rw [hcallback] at he
  simp only [BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg, hid] at he
  have hstep : advance (program callback callbackStart callbackInit)
      ⟨some (.inr (.inr .afterGetter)),
       getterControl callbackInit getterState, S⟩ =
      ⟨some (.inr (.inl callbackStart)),
       callbackControl
         (CylinderContextScanStep.copyControl ((), none)) callbackInit,
       S⟩ := by rfl
  refine ⟨u + 1, by omega, ?_⟩
  rw [show u + 1 = 1 + u by omega,
    run_add callback callbackStart callbackInit
      (n := 1) (by exact hstep) u]
  simpa only [c] using he

#print axioms callback_run

theorem cycle_from_getter
    (callback : L → TM2.Stmt (fun _ : Stack => Bool) L V)
    (callbackStart : L) (callbackInit vOut : V)
    (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (foreign : Stack → List Bool)
    (SOut : Stack → List Bool) (callbackBound : Nat)
    (hcallback :
      let source := SourceListEncoding.encode (pre ++ word :: suffix)
      let selected := LargeContextPreservingScan.frame foreign
        (⟨none,
         CylinderContextScanStep.getterControl
           (PreservingV2Program.v2Control
             (IndexedV2Program.indexControl
               (SourceListMachineFields.coreControl (some true, false), none))),
         CylinderContextScanStep.selectedBank source
           (SourceListEncoding.fields suffix) word pre.length⟩ :
          CylinderContextScanStep.Config)
      ((advance callback)^[callbackBound])
        (⟨some callbackStart, callbackInit, selected.stk⟩ :
          TM2.Cfg (fun _ : Stack => Bool) L V) =
        ⟨none, vOut, SOut⟩) :
    let source := SourceListEncoding.encode (pre ++ word :: suffix)
    let getterBound := 2 * pre.length + 5 +
      (2 * source.length + 5 +
        (4 * (pre ++ word :: suffix).length.bits.length + 6 +
          IndexedFieldProgram.fieldCost (pre ++ [word]))) + 1
    let cleanupBound :=
      (∑ i : Fin 10, (SOut (cleanBank i)).length) + 11
    ∃ t ≤ getterBound + (callbackBound + 1) + 1 + cleanupBound + 1,
      run callback callbackStart callbackInit t
        ⟨some (.inl (.inl (.inl .scan))),
         getterControl callbackInit
           (CylinderContextScanStep.copyControl ((), none)),
         (LargeContextPreservingScan.frame foreign
           (CylinderContextScanStep.initial source pre.length)).stk⟩ =
        ⟨some (.inr (.inr .check)),
         callbackControl
           (CylinderContextScanStep.copyControl ((), none)) vOut,
         Function.update
           (BitMachineClearBank.cleared cleanBank SOut) 10
           (true :: (BitMachineClearBank.cleared cleanBank SOut) 10)⟩ := by
  dsimp only at hcallback ⊢
  obtain ⟨a, ha, hget⟩ := getter_run callback callbackStart
    callbackInit pre word suffix foreign
  obtain ⟨b, hb, hcb⟩ := callback_run callback callbackStart
    callbackInit vOut _ _ SOut callbackBound hcallback
  have hafter : advance (program callback callbackStart callbackInit)
      ⟨some (.inr (.inr .afterCallback)),
       callbackControl
         (CylinderContextScanStep.copyControl ((), none)) vOut,
       SOut⟩ =
      ⟨some (.inr (.inr (.clear 0))),
       callbackControl
         (CylinderContextScanStep.copyControl ((), none)) vOut,
       SOut⟩ := by rfl
  have hclean := cleanup_run callback callbackStart callbackInit
    (CylinderContextScanStep.copyControl ((), none), vOut) SOut
  have hinc : advance (program callback callbackStart callbackInit)
      ⟨some (.inr (.inr .increment)),
       callbackControl
         (CylinderContextScanStep.copyControl ((), none)) vOut,
       BitMachineClearBank.cleared cleanBank SOut⟩ =
      ⟨some (.inr (.inr .check)),
       callbackControl
         (CylinderContextScanStep.copyControl ((), none)) vOut,
       Function.update
         (BitMachineClearBank.cleared cleanBank SOut) 10
         (true :: (BitMachineClearBank.cleared cleanBank SOut) 10)⟩ := by
    rfl
  have h12 := (run_add callback callbackStart callbackInit hget b).trans hcb
  have h123 := (run_add callback callbackStart callbackInit h12 1).trans
    (show run callback callbackStart callbackInit 1 _ = _ from hafter)
  have h1234 := (run_add callback callbackStart callbackInit h123 _).trans
    hclean
  have hfinal := (run_add callback callbackStart callbackInit h1234 1).trans
    (show run callback callbackStart callbackInit 1 _ = _ from hinc)
  refine ⟨a + b + 1 +
    ((∑ i : Fin 10, (SOut (cleanBank i)).length) + 11) + 1,
    by omega, ?_⟩
  exact hfinal

#print axioms cycle_from_getter

def foreignBank (output context : List Bool) (fuel : Nat)
    (extra : Stack → List Bool) :
    Stack → List Bool :=
  Function.update
    (Function.update
      (Function.update extra 9 output) 12 context)
    13 (List.replicate fuel true)

/-- The callback's larger-bank registers are copied into each framed state. -/
theorem foreignBank_extra (output context : List Bool) (fuel : Nat)
    (extra : Stack → List Bool) (j : Stack) (hj : 15 ≤ j.val) :
    foreignBank output context fuel extra j = extra j := by
  have h9 : j ≠ 9 := by intro h; subst j; omega
  have h12 : j ≠ 12 := by intro h; subst j; omega
  have h13 : j ≠ 13 := by intro h; subst j; omega
  simp [foreignBank, Function.update_of_ne, h9, h12, h13]

theorem frame_extra (source output context : List Bool)
    (index fuel : Nat) (extra : Stack → List Bool)
    (j : Stack) (hj : 15 ≤ j.val) :
    (LargeContextPreservingScan.frame
      (foreignBank output context fuel extra)
      (CylinderContextScanStep.initial source index)).stk j = extra j := by
  rw [LargeContextPreservingScan.frame_foreign]
  · exact foreignBank_extra output context fuel extra j hj
  · rintro ⟨k, hk⟩
    have hsmall : (LargeContextPreservingScan.locate k).val < 15 := by
      fin_cases k <;> decide
    have heq := congrArg Fin.val hk
    omega

theorem cleanup_extra (S : Stack → List Bool)
    (j : Stack) (hj : 15 ≤ j.val) :
    BitMachineClearBank.cleared cleanBank S j = S j := by
  apply BitMachineClearBank.cleared_foreign
  intro i hi
  have hsmall : (cleanBank i).val < 15 := by
    fin_cases i <;> decide
  have heq := congrArg Fin.val hi
  omega

theorem cleanup_and_increment_extra (S : Stack → List Bool)
    (j : Stack) (hj : 15 ≤ j.val) :
    Function.update (BitMachineClearBank.cleared cleanBank S) 10
      (true :: (BitMachineClearBank.cleared cleanBank S) 10) j = S j := by
  have h10 : j ≠ 10 := by intro h; subst j; omega
  rw [Function.update_of_ne h10]
  exact cleanup_extra S j hj

theorem bank13_outside :
    ¬ ∃ k : CylinderContextScanStep.Stack,
      LargeContextPreservingScan.locate k = (13 : Stack) := by
  rintro ⟨k, hk⟩
  fin_cases k <;> cases hk

theorem frame_fuel (source output context : List Bool)
    (index fuel : Nat) (extra : Stack → List Bool) :
    (LargeContextPreservingScan.frame
      (foreignBank output context (fuel + 1) extra)
      (CylinderContextScanStep.initial source index)).stk =
      Function.update
        (LargeContextPreservingScan.frame
          (foreignBank output context fuel extra)
          (CylinderContextScanStep.initial source index)).stk
        13 (true :: List.replicate fuel true) := by
  funext j
  by_cases hj : j = 13
  · subst j
    rw [LargeContextPreservingScan.frame_foreign _ _ _ bank13_outside]
    rw [show fuel + 1 = Nat.succ fuel by omega]
    simp [foreignBank, List.replicate_succ]
  · by_cases himage : ∃ k : CylinderContextScanStep.Stack,
        LargeContextPreservingScan.locate k = j
    · obtain ⟨k, rfl⟩ := himage
      rw [LargeContextPreservingScan.frame_bank,
        Function.update_of_ne]
      · exact (LargeContextPreservingScan.frame_bank _ _ k).symm
      · intro h
        exact bank13_outside ⟨k, h⟩
    · rw [LargeContextPreservingScan.frame_foreign _ _ _ himage,
        Function.update_of_ne hj,
        LargeContextPreservingScan.frame_foreign _ _ _ himage]
      simp [foreignBank, Function.update_of_ne, hj]

theorem frame_fuel_same (source output context : List Bool)
    (index fuel : Nat) (extra : Stack → List Bool) :
    Function.update
      (LargeContextPreservingScan.frame
        (foreignBank output context fuel extra)
        (CylinderContextScanStep.initial source index)).stk
      13 (List.replicate fuel true) =
    (LargeContextPreservingScan.frame
      (foreignBank output context fuel extra)
      (CylinderContextScanStep.initial source index)).stk := by
  have h :
      (LargeContextPreservingScan.frame
        (foreignBank output context fuel extra)
        (CylinderContextScanStep.initial source index)).stk 13 =
        List.replicate fuel true := by
    rw [LargeContextPreservingScan.frame_foreign _ _ _ bank13_outside]
    simp [foreignBank]
  rw [← h]
  exact Function.update_eq_self 13 _

#print axioms frame_fuel
#print axioms frame_extra
#print axioms cleanup_extra
#print axioms cleanup_and_increment_extra

theorem check_to_getter
    (callback : L → TM2.Stmt (fun _ : Stack => Bool) L V)
    (callbackStart : L) (callbackInit : V)
    (source output context : List Bool) (index fuel : Nat)
    (extra : Stack → List Bool)
    (v : Control V) :
    advance (program callback callbackStart callbackInit)
      ⟨some (.inr (.inr .check)), v,
       (LargeContextPreservingScan.frame
         (foreignBank output context (fuel + 1) extra)
         (CylinderContextScanStep.initial source index)).stk⟩ =
      ⟨some (.inl (.inl (.inl .scan))),
       getterControl callbackInit
         (CylinderContextScanStep.copyControl ((), none)),
       (LargeContextPreservingScan.frame
         (foreignBank output context fuel extra)
         (CylinderContextScanStep.initial source index)).stk⟩ := by
  rw [frame_fuel]
  have h := check_positive callback callbackStart callbackInit
    (LargeContextPreservingScan.frame
      (foreignBank output context fuel extra)
      (CylinderContextScanStep.initial source index)).stk
    v fuel
  rw [h, frame_fuel_same]

#print axioms check_to_getter

#print axioms getter_run

#print axioms cleanup_run

#print axioms program_finite
#print axioms check_positive
#print axioms check_zero

end CurrentAdditive.LargeContextListScheduler
