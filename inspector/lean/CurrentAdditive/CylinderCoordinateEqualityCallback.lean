import CurrentAdditive.CylinderEqualityListRun
import CurrentAdditive.LargeContextListSchedulerFixedBound
import CurrentAdditive.CylinderTupleCoordinate

/-!
Physical coordinate selection followed by one context-preserving equality
cell.  The source tuple is the selected word on bank 6; the fixed coordinate
address is unary on bank 15 and the desired symbol word is on bank 16.  The
indexed V2 getter produces the tuple's coordinate word on bank 17, then the
checked equality appender writes one bit at the tail of bank 9.  Banks 8, 10,
12, and 13 retain the outer list scheduler's source/index/context/fuel.
-/

namespace CurrentAdditive.CylinderCoordinateEqualityCallback

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.GaussListContext

abbrev Stack := Fin 32
abbrev GLabel := CylinderContextScanStep.Label
abbrev ELabel := CylinderEqualityAppendCallback.Label
abbrev GControl := CylinderContextScanStep.Control
abbrev EControl := CylinderEqualityAppendCallback.Control
abbrev Core := GControl × EControl
abbrev Control := Core × Option Bool

inductive Admin where
  | handoff | clean (i : Fin 15) | finishClean | done
  deriving DecidableEq, Fintype

abbrev Label := GLabel ⊕ (ELabel ⊕ Admin)
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def getterStack : Fin 12 ↪ Stack where
  toFun k := ![18, 19, 20, 21, 22, 23, 17, 24, 6, 31, 15, 25] k
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all

def equalityStack : Fin 15 ↪ Stack where
  toFun k := ![0, 1, 2, 3, 4, 5, 17, 27, 8, 9, 10, 28, 16, 13, 29] k
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all

def getterControl (v : GControl) : Control :=
  ((v, CylinderEqualityAppendCallback.bcontrol ((), none)), none)

def equalityControl (v : EControl) : Control :=
  ((CylinderContextScanStep.copyControl ((), none), v), none)

def cleanBank (i : Fin 15) : Stack := ⟨17 + i.val, by omega⟩

def nextClean (i : Fin 15) : Admin :=
  if h : i.val + 1 < 15 then .clean ⟨i.val + 1, h⟩
  else .finishClean

def cleanLabel (i : Fin 16) : Label :=
  if h : i.val < 15 then .inr (.inr (.clean ⟨i.val, h⟩))
  else .inr (.inr .finishClean)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineStackEmbedding.stmt getterStack Sum.inl
      getterControl (fun v => v.1.1) (some (.inr (.inr .handoff)))
      (CylinderContextScanStep.program l)
  | .inr (.inl l) => BitMachineStackEmbedding.stmt equalityStack
      (fun x => .inr (.inl x)) equalityControl (fun v => v.1.2)
      (some (.inr (.inr (.clean 0))))
      (CylinderEqualityAppendCallback.program l)
  | .inr (.inr .handoff) =>
      .load (fun _ => equalityControl
        (CylinderEqualityAppendCallback.bcontrol ((), none)))
        (.goto (fun _ => .inr (.inl (.copyContext .scan))))
  | .inr (.inr (.clean i)) =>
      BitMachineClearBank.clearStep (cleanBank i)
        (.inr (.inr (.clean i))) (.inr (.inr (nextClean i)))
  | .inr (.inr .finishClean) =>
      BitMachineClearBank.finishStep id (.inr (.inr .done))
  | .inr (.inr .done) => .halt

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

theorem finite_program : Finite Stack ∧ Finite Label ∧ Finite Control :=
  ⟨inferInstance, inferInstance, inferInstance⟩

noncomputable def getterFrame (foreign : Stack → List Bool)
    (c : CylinderContextScanStep.Config) : Config :=
  BitMachineStackEmbedding.cfg getterStack foreign Sum.inl
    getterControl (some (.inr (.inr .handoff))) c

noncomputable def equalityFrame (foreign : Stack → List Bool)
    (c : TM2.Cfg (fun _ : Fin 15 => Bool) ELabel EControl) : Config :=
  BitMachineStackEmbedding.cfg equalityStack foreign
    (fun x => .inr (.inl x)) equalityControl
    (some (.inr (.inr (.clean 0)))) c

theorem run_add {c c' : Config} {n : Nat}
    (h : run n c = c') (m : Nat) : run (n + m) c = run m c' := by
  rw [Nat.add_comm, run, Function.iterate_add_apply]
  exact congrArg (run m) h

theorem getter_run (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (foreign : Stack → List Bool) :
    let source := SourceListEncoding.encode (pre ++ word :: suffix)
    ∃ t ≤ 2 * pre.length + 5 +
        (2 * source.length + 5 +
          (4 * (pre ++ word :: suffix).length.bits.length + 6 +
            IndexedFieldProgram.fieldCost (pre ++ [word]))),
      run t (getterFrame foreign
        (CylinderContextScanStep.initial source pre.length)) =
        getterFrame foreign
          ⟨none,
           CylinderContextScanStep.getterControl
             (PreservingV2Program.v2Control
               (IndexedV2Program.indexControl
                 (SourceListMachineFields.coreControl (some true, false), none))),
           CylinderContextScanStep.selectedBank source
             (SourceListEncoding.fields suffix) word pre.length⟩ := by
  dsimp only
  obtain ⟨t, ht, hr⟩ := CylinderContextScanStep.scan_step pre word suffix
  obtain ⟨u, hu, he⟩ := BitMachineStackEmbedding.outputs
    getterStack foreign Sum.inl getterControl (fun v => v.1.1)
    (by intro v; rfl) (some (.inr (.inr .handoff)))
    CylinderContextScanStep.program program (by intro l; rfl)
    (CylinderContextScanStep.initial
      (SourceListEncoding.encode (pre ++ word :: suffix)) pre.length)
    t (by change (CylinderContextScanStep.run t _).l = none; rw [hr])
  change run u (getterFrame foreign _) = getterFrame foreign
    (CylinderContextScanStep.run t _) at he
  rw [hr] at he
  exact ⟨u, hu.trans ht, he⟩

theorem cleanBank_injective : Function.Injective cleanBank := by
  intro a b h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp [cleanBank] at hv
  omega

theorem cleanLabel_step (i : Fin 15) :
    cleanLabel i.castSucc = .inr (.inr (.clean i)) ∧
    cleanLabel i.succ = .inr (.inr (nextClean i)) := by
  fin_cases i <;> simp [cleanLabel, nextClean]

theorem cleanLabel_finish :
    cleanLabel (Fin.last 15) = .inr (.inr .finishClean) := by
  simp [cleanLabel]

theorem cleanup_run (v : Core) (S : Stack → List Bool) :
    run ((∑ i : Fin 15, (S (cleanBank i)).length) + 16)
      ⟨some (.inr (.inr (.clean 0))), (v, none), S⟩ =
      ⟨some (.inr (.inr .done)), (v, none),
        BitMachineClearBank.cleared cleanBank S⟩ := by
  change ((advance program)^[(∑ i : Fin 15,
      (S (cleanBank i)).length) + 15 + 1])
      ⟨some (cleanLabel 0), (v, none), S⟩ = _
  apply BitMachineClearBank.clear_bank_run program id
    (.inr (.inr .done)) 15 cleanBank cleanBank_injective cleanLabel
  · intro i
    obtain ⟨hi, hn⟩ := cleanLabel_step i
    rw [hi, hn]
    rfl
  · rw [cleanLabel_finish]
    rfl

theorem equality_run_frame (foreign : Stack → List Bool)
    (left right out : List Bool)
    (hleft : foreign 17 = left) (hright : foreign 16 = right)
    (hout : foreign 9 = out) (h28 : foreign 28 = [])
    (h27 : foreign 27 = []) (h29 : foreign 29 = []) :
    let c : TM2.Cfg (fun _ : Fin 15 => Bool) ELabel EControl :=
      ⟨some (.copyContext .scan),
       CylinderEqualityAppendCallback.bcontrol ((), none),
       fun k => foreign (equalityStack k)⟩
    ∃ t ≤ CylinderEqualityAppendCallback.callbackBound left right out,
      ∃ (vFinal : EControl) (SFinal : Fin 15 → List Bool),
      run t (equalityFrame foreign c) =
        equalityFrame foreign ⟨none, vFinal, SFinal⟩ ∧
      SFinal 9 = out ++ [decide (left = right)] ∧
      (∀ k : Fin 15,
        k = 8 ∨ k = 10 ∨ k = 12 ∨ k = 13 →
          SFinal k = foreign (equalityStack k)) := by
  dsimp only
  let S : Fin 15 → List Bool := fun k => foreign (equalityStack k)
  have h6 : S 6 = left := by simpa [S, equalityStack] using hleft
  have h12 : S 12 = right := by simpa [S, equalityStack] using hright
  have h9 : S 9 = out := by simpa [S, equalityStack] using hout
  have h11 : S 11 = [] := by simpa [S, equalityStack] using h28
  have h7 : S 7 = [] := by simpa [S, equalityStack] using h27
  have h14 : S 14 = [] := by simpa [S, equalityStack] using h29
  obtain ⟨t, ht, v, T, hr, ho, hp⟩ :=
    CylinderEqualityAppendCallback.run_selected left right out S
      h6 h12 h9 h11 h7 h14
  have hh :
      ((advance CylinderEqualityAppendCallback.program)^[t]
        (⟨some (.copyContext .scan),
          CylinderEqualityAppendCallback.bcontrol ((), none), S⟩ :
          TM2.Cfg (fun _ : Fin 15 => Bool) ELabel EControl)).l = none := by
    change (CylinderEqualityAppendCallback.run t _).l = none
    rw [hr]
  obtain ⟨u, hu, he⟩ := BitMachineStackEmbedding.outputs
    equalityStack foreign (fun x => .inr (.inl x))
    equalityControl (fun x => x.1.2) (by intro v; rfl)
    (some (.inr (.inr (.clean 0))))
    CylinderEqualityAppendCallback.program program (by intro l; rfl)
    (⟨some (.copyContext .scan),
      CylinderEqualityAppendCallback.bcontrol ((), none), S⟩ :
      TM2.Cfg (fun _ : Fin 15 => Bool) ELabel EControl) t hh
  change run u (equalityFrame foreign _) =
    equalityFrame foreign (CylinderEqualityAppendCallback.run t _) at he
  rw [hr] at he
  exact ⟨u, hu.trans ht, v, T, he, ho, hp⟩

noncomputable def selectedFrame (foreign : Stack → List Bool)
    (source suffix word : List Bool) (index : Nat) : Config :=
  getterFrame foreign
    ⟨none,
     CylinderContextScanStep.getterControl
       (PreservingV2Program.v2Control
         (IndexedV2Program.indexControl
           (SourceListMachineFields.coreControl (some true, false), none))),
     CylinderContextScanStep.selectedBank source suffix word index⟩

theorem selectedFrame_word (foreign : Stack → List Bool)
    (source suffix word : List Bool) (index : Nat) :
    (selectedFrame foreign source suffix word index).stk 17 = word := by
  let c : CylinderContextScanStep.Config :=
    ⟨none,
     CylinderContextScanStep.getterControl
       (PreservingV2Program.v2Control
         (IndexedV2Program.indexControl
           (SourceListMachineFields.coreControl (some true, false), none))),
     CylinderContextScanStep.selectedBank source suffix word index⟩
  have h := BitMachineStackEmbedding.bank_at getterStack foreign
    c.stk (6 : Fin 12)
  simpa [selectedFrame, getterFrame, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, c, getterStack,
    CylinderContextScanStep.selectedBank] using h

theorem selectedFrame_foreign (foreign : Stack → List Bool)
    (source suffix word : List Bool) (index : Nat)
    (k : Stack) (hk : ¬ ∃ i : Fin 12, getterStack i = k) :
    (selectedFrame foreign source suffix word index).stk k =
      foreign k := by
  let c : CylinderContextScanStep.Config :=
    ⟨none,
     CylinderContextScanStep.getterControl
       (PreservingV2Program.v2Control
         (IndexedV2Program.indexControl
           (SourceListMachineFields.coreControl (some true, false), none))),
     CylinderContextScanStep.selectedBank source suffix word index⟩
  have h := BitMachineStackEmbedding.bank_outside getterStack foreign
    c.stk k hk
  simpa [selectedFrame, getterFrame, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, c] using h

theorem handoff_step (S : Stack → List Bool) (v : Control) :
    run 1 ⟨some (.inr (.inr .handoff)), v, S⟩ =
      equalityFrame S
        ⟨some (.copyContext .scan),
         CylinderEqualityAppendCallback.bcontrol ((), none),
         fun k => S (equalityStack k)⟩ := by
  have hb := BitMachineStackEmbedding.bank_restrict equalityStack S
  simp [run, advance, TM2.step, TM2.stepAux, program,
    equalityFrame, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg, hb]

def getterBound (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) : Nat :=
  let source := SourceListEncoding.encode (pre ++ word :: suffix)
  2 * pre.length + 5 +
    (2 * source.length + 5 +
      (4 * (pre ++ word :: suffix).length.bits.length + 6 +
        IndexedFieldProgram.fieldCost (pre ++ [word])))

theorem physical_coordinate_pair (pre : List (List Bool))
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
        (∑ i : Fin 15, (SBefore (cleanBank i)).length) + 17 ∧
      run t start = ⟨none, vFinal, SFinal⟩ ∧
      SFinal 9 = out ++ [decide (word = right)] ∧
      SFinal = BitMachineClearBank.cleared cleanBank SBefore ∧
      (∀ i : Fin 15, SFinal (cleanBank i) = []) ∧
      (∀ k : Stack,
        k = 8 ∨ k = 10 ∨ k = 12 ∨ k = 13 ∨ k = 15 ∨ k = 16 →
          SFinal k = start.stk k) := by
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
      before.stk, ?_, htotal, h9final, rfl, ?_, ?_⟩
  · change a ≤ getterBound pre word suffix at ha
    omega
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

#print axioms finite_program
#print axioms getter_run
#print axioms cleanup_run
#print axioms equality_run_frame
#print axioms handoff_step
#print axioms physical_coordinate_pair

end CurrentAdditive.CylinderCoordinateEqualityCallback
