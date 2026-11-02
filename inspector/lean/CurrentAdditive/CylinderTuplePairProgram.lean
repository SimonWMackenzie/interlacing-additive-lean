import CurrentAdditive.ContextPreservingScan
import CurrentAdditive.CylinderEqualMachine
import CurrentAdditive.CylinderPairEvaluationBridge

/-!
Physical callback core for one cylinder assignment.  The counted tuple is
selected from its actual V2 word on bank 8 using the unary coordinate address
on bank 10.  The selected symbol lands on bank 6.  Bank 12 holds the feature
symbol; a literal bitwise comparator appends its Boolean answer to bank 9.
This fixed program is one pair callback, not the complete feature conjunction
or matrix scheduler.
-/

namespace CurrentAdditive.CylinderTuplePairProgram

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.CylinderContextScanStep

abbrev Stack := Fin 15

inductive Admin where
  | compare | done
  deriving DecidableEq, Fintype

abbrev Label := CylinderContextScanStep.Label ⊕
  (CurrentAdditive.CylinderEqualMachine.Label ⊕ Admin)

abbrev Control := CylinderContextScanStep.Control ×
  CurrentAdditive.CylinderEqualMachine.Control

abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def compareStack : Fin 3 ↪ Stack where
  toFun k := ![6, 12, 9] k
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

def getterControl (v : CylinderContextScanStep.Control) : Control :=
  (v, (true, none, none))

def comparatorControl (v : CurrentAdditive.CylinderEqualMachine.Control) :
    Control :=
  (CylinderContextScanStep.copyControl ((), none), v)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineStackEmbedding.stmt
      CurrentAdditive.ContextPreservingScan.locate Sum.inl getterControl
      Prod.fst (some (.inr (.inr .compare)))
      (CylinderContextScanStep.program l)
  | .inr (.inl l) => BitMachineStackEmbedding.stmt
      compareStack (fun l => .inr (.inl l)) comparatorControl
      Prod.snd (some (.inr (.inr .done)))
      (CurrentAdditive.CylinderEqualMachine.program l)
  | .inr (.inr .compare) =>
      load (fun _ => comparatorControl (true, none, none))
        (goto (fun _ => .inr (.inl .scan)))
  | .inr (.inr .done) => halt

def run (t : Nat) (c : Config) : Config :=
  ((advance program)^[t]) c

theorem finite_program : Finite Stack ∧ Finite Label ∧ Finite Control :=
  ⟨inferInstance, inferInstance, inferInstance⟩

def initialBank (tuple : List Bool) (i : Nat) (y : List Bool) :
    Stack → List Bool :=
  fun k => if h : k.val < 12 then
    (CylinderContextScanStep.initialBank tuple i) ⟨k.val, h⟩
  else if k = 12 then y else []

def initial (tuple : List Bool) (i : Nat) (y : List Bool) : Config :=
  ⟨some (.inl (.inl .scan)),
    getterControl (CylinderContextScanStep.copyControl ((), none)),
    initialBank tuple i y⟩

noncomputable def getterFrame (foreign : Stack → List Bool)
    (c : CylinderContextScanStep.Config) : Config :=
  BitMachineStackEmbedding.cfg
    CurrentAdditive.ContextPreservingScan.locate foreign Sum.inl
    getterControl (some (.inr (.inr .compare))) c

theorem getter_run (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (foreign : Stack → List Bool) :
    let source := SourceListEncoding.encode (pre ++ word :: suffix)
    ∃ t ≤ 2 * pre.length + 5 +
        (2 * source.length + 5 +
          (4 * (pre ++ word :: suffix).length.bits.length + 6 +
            CurrentAdditive.GaussListContext.IndexedFieldProgram.fieldCost
              (pre ++ [word]))),
      run t (getterFrame foreign
        (CylinderContextScanStep.initial source pre.length)) =
        getterFrame foreign
          ⟨none,
           CylinderContextScanStep.getterControl
             (CurrentAdditive.GaussListContext.PreservingV2Program.v2Control
               (CurrentAdditive.GaussListContext.IndexedV2Program.indexControl
                 (SourceListMachineFields.coreControl (some true, false), none))),
           CylinderContextScanStep.selectedBank source
             (SourceListEncoding.fields suffix) word pre.length⟩ := by
  dsimp only
  obtain ⟨t, ht, hr⟩ := CylinderContextScanStep.scan_step pre word suffix
  obtain ⟨u, hu, he⟩ := BitMachineStackEmbedding.outputs
    CurrentAdditive.ContextPreservingScan.locate foreign Sum.inl
    getterControl Prod.fst (by intro v; rfl)
    (some (.inr (.inr .compare)))
    CylinderContextScanStep.program program (by intro l; rfl)
    (CylinderContextScanStep.initial
      (SourceListEncoding.encode (pre ++ word :: suffix)) pre.length)
    t (by change (CylinderContextScanStep.run t _).l = none; rw [hr])
  change run u (getterFrame foreign _) = getterFrame foreign
    (CylinderContextScanStep.run t _) at he
  rw [hr] at he
  exact ⟨u, by omega, he⟩

noncomputable def compareFrame (foreign : Stack → List Bool)
    (c : CurrentAdditive.CylinderEqualMachine.Config) : Config :=
  BitMachineStackEmbedding.cfg compareStack foreign
    (fun l => .inr (.inl l)) comparatorControl
    (some (.inr (.inr .done))) c

theorem compareFrame_ready (S : Stack → List Bool)
    (left right out : List Bool)
    (hleft : S 6 = left) (hright : S 12 = right)
    (hout : S 9 = out) :
    compareFrame S
      (CurrentAdditive.CylinderEqualMachine.cfg (some .scan)
        (true, none, none) left right out) =
      ⟨some (.inr (.inl .scan)),
       comparatorControl (true, none, none), S⟩ := by
  unfold compareFrame BitMachineStackEmbedding.cfg
    BitMachineStackEmbedding.stackCfg BitMachineInline.cfg
  congr 1
  funext j
  let c := CurrentAdditive.CylinderEqualMachine.cfg (some .scan)
    (true, none, none) left right out
  by_cases h6 : j = 6
  · subst j
    have h := BitMachineStackEmbedding.bank_at compareStack S c.stk (0 : Fin 3)
    simpa [compareStack, c, CurrentAdditive.CylinderEqualMachine.cfg,
      CurrentAdditive.CylinderEqualMachine.bank, hleft] using h
  by_cases h12 : j = 12
  · subst j
    have h := BitMachineStackEmbedding.bank_at compareStack S c.stk (1 : Fin 3)
    simpa [compareStack, c, CurrentAdditive.CylinderEqualMachine.cfg,
      CurrentAdditive.CylinderEqualMachine.bank, hright] using h
  by_cases h9 : j = 9
  · subst j
    have h := BitMachineStackEmbedding.bank_at compareStack S c.stk (2 : Fin 3)
    simpa [compareStack, c, CurrentAdditive.CylinderEqualMachine.cfg,
      CurrentAdditive.CylinderEqualMachine.bank, hout] using h
  exact BitMachineStackEmbedding.bank_outside compareStack S c.stk j (by
    rintro ⟨k, hk⟩
    fin_cases k <;> simp_all [compareStack])

theorem getterFrame_selected_banks (source suffix word : List Bool)
    (index : Nat) (foreign : Stack → List Bool) :
    let S := (getterFrame foreign
      ⟨none,
       CylinderContextScanStep.getterControl
         (CurrentAdditive.GaussListContext.PreservingV2Program.v2Control
           (CurrentAdditive.GaussListContext.IndexedV2Program.indexControl
             (SourceListMachineFields.coreControl (some true, false), none))),
       CylinderContextScanStep.selectedBank source suffix word index⟩).stk
    S 6 = word ∧ S 12 = foreign 12 ∧ S 9 = foreign 9 := by
  dsimp only
  let c : CylinderContextScanStep.Config :=
    ⟨none,
     CylinderContextScanStep.getterControl
       (CurrentAdditive.GaussListContext.PreservingV2Program.v2Control
         (CurrentAdditive.GaussListContext.IndexedV2Program.indexControl
           (SourceListMachineFields.coreControl (some true, false), none))),
     CylinderContextScanStep.selectedBank source suffix word index⟩
  have h6 := BitMachineStackEmbedding.bank_at
    CurrentAdditive.ContextPreservingScan.locate foreign c.stk (6 : Fin 12)
  have h12 := BitMachineStackEmbedding.bank_outside
    CurrentAdditive.ContextPreservingScan.locate foreign c.stk (12 : Stack)
    (by rintro ⟨k, hk⟩; fin_cases k <;> cases hk)
  have h9 := BitMachineStackEmbedding.bank_outside
    CurrentAdditive.ContextPreservingScan.locate foreign c.stk (9 : Stack)
    (by rintro ⟨k, hk⟩; fin_cases k <;> cases hk)
  constructor
  · simpa [getterFrame, BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, c,
      CylinderContextScanStep.selectedBank,
      CurrentAdditive.ContextPreservingScan.locate] using h6
  constructor
  · simpa [getterFrame, BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, c] using h12
  · simpa [getterFrame, BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, c] using h9

theorem handoff_to_comparator (source suffix word : List Bool)
    (index : Nat) (foreign : Stack → List Bool)
    (right out : List Bool) (hright : foreign 12 = right)
    (hout : foreign 9 = out) :
    let c : CylinderContextScanStep.Config :=
      ⟨none,
       CylinderContextScanStep.getterControl
         (CurrentAdditive.GaussListContext.PreservingV2Program.v2Control
           (CurrentAdditive.GaussListContext.IndexedV2Program.indexControl
             (SourceListMachineFields.coreControl (some true, false), none))),
       CylinderContextScanStep.selectedBank source suffix word index⟩
    let S := (getterFrame foreign c).stk
    advance program (getterFrame foreign c) =
      compareFrame S
        (CurrentAdditive.CylinderEqualMachine.cfg (some .scan)
          (true, none, none) word right out) := by
  dsimp only
  let c : CylinderContextScanStep.Config :=
    ⟨none,
     CylinderContextScanStep.getterControl
       (CurrentAdditive.GaussListContext.PreservingV2Program.v2Control
         (CurrentAdditive.GaussListContext.IndexedV2Program.indexControl
           (SourceListMachineFields.coreControl (some true, false), none))),
     CylinderContextScanStep.selectedBank source suffix word index⟩
  let S := (getterFrame foreign c).stk
  obtain ⟨hleft, hright', hout'⟩ :=
    getterFrame_selected_banks source suffix word index foreign
  have hready := compareFrame_ready S word right out hleft
    (hright'.trans hright) (hout'.trans hout)
  rw [hready]
  have hshape : getterFrame foreign c =
      ⟨some (.inr (.inr .compare)), getterControl c.var, S⟩ := by
    simp [getterFrame, BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg, c, S]
  rw [hshape]
  rfl

theorem compare_run_frame (left right out : List Bool)
    (foreign : Stack → List Bool) :
    ∃ t ≤ min left.length right.length + 1,
      (run t (compareFrame foreign
        (CurrentAdditive.CylinderEqualMachine.cfg (some .scan)
          (true, none, none) left right out))).l =
        some (.inr (.inr .done)) ∧
      (run t (compareFrame foreign
        (CurrentAdditive.CylinderEqualMachine.cfg (some .scan)
          (true, none, none) left right out))).stk 9 =
        decide (left = right) :: out := by
  obtain ⟨t, ht, hh, ho⟩ :=
    CurrentAdditive.CylinderEqualMachine.compare_run true left right out
  obtain ⟨u, hu, he⟩ := BitMachineStackEmbedding.outputs
    compareStack foreign (fun l => .inr (.inl l))
    comparatorControl Prod.snd (by intro v; rfl)
    (some (.inr (.inr .done)))
    CurrentAdditive.CylinderEqualMachine.program program
    (by intro l; rfl)
    (CurrentAdditive.CylinderEqualMachine.cfg (some .scan)
      (true, none, none) left right out) t hh
  change run u (compareFrame foreign _) = compareFrame foreign
    (CurrentAdditive.CylinderEqualMachine.run t _) at he
  refine ⟨u, hu.trans ht, ?_, ?_⟩
  · rw [he]
    simp [compareFrame, BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg, hh]
  · rw [he]
    have hbank := BitMachineStackEmbedding.bank_at compareStack foreign
      (CurrentAdditive.CylinderEqualMachine.run t
        (CurrentAdditive.CylinderEqualMachine.cfg (some .scan)
          (true, none, none) left right out)).stk (2 : Fin 3)
    simpa [compareFrame, ho] using hbank

theorem run_add {c c' : Config} {n : Nat} (h : run n c = c')
    (m : Nat) : run (n + m) c = run m c' := by
  rw [Nat.add_comm, run, Function.iterate_add_apply]
  exact congrArg (run m) h

theorem done_step (c : Config)
    (h : c.l = some (.inr (.inr .done))) :
    (run 1 c).l = none ∧ (run 1 c).stk 9 = c.stk 9 := by
  rcases c with ⟨l, v, S⟩
  cases l with
  | none => cases h
  | some l =>
      cases h
      simp [run, advance, TM2.step, TM2.stepAux, program]

theorem physical_tuple_pair (pre : List (List Bool))
    (word : List Bool) (suffix : List (List Bool))
    (right out : List Bool) (foreign : Stack → List Bool)
    (hright : foreign 12 = right) (hout : foreign 9 = out) :
    let source := SourceListEncoding.encode (pre ++ word :: suffix)
    let start := getterFrame foreign
      (CylinderContextScanStep.initial source pre.length)
    ∃ t ≤ 2 * pre.length + 5 +
        (2 * source.length + 5 +
          (4 * (pre ++ word :: suffix).length.bits.length + 6 +
            CurrentAdditive.GaussListContext.IndexedFieldProgram.fieldCost
              (pre ++ [word]))) +
        1 + (min word.length right.length + 1) + 1,
      (run t start).l = none ∧
      (run t start).stk 9 = decide (word = right) :: out := by
  dsimp only
  let source := SourceListEncoding.encode (pre ++ word :: suffix)
  let c : CylinderContextScanStep.Config :=
    ⟨none,
     CylinderContextScanStep.getterControl
       (CurrentAdditive.GaussListContext.PreservingV2Program.v2Control
         (CurrentAdditive.GaussListContext.IndexedV2Program.indexControl
           (SourceListMachineFields.coreControl (some true, false), none))),
     CylinderContextScanStep.selectedBank source
       (SourceListEncoding.fields suffix) word pre.length⟩
  let selected := getterFrame foreign c
  obtain ⟨a, ha, hget⟩ := getter_run pre word suffix foreign
  change run a _ = selected at hget
  have hhandoff := handoff_to_comparator source
    (SourceListEncoding.fields suffix) word pre.length foreign
    right out hright hout
  change advance program selected = compareFrame selected.stk
    (CurrentAdditive.CylinderEqualMachine.cfg (some .scan)
      (true, none, none) word right out) at hhandoff
  obtain ⟨b, hb, hlabel, houtput⟩ :=
    compare_run_frame word right out selected.stk
  let ready := compareFrame selected.stk
    (CurrentAdditive.CylinderEqualMachine.cfg (some .scan)
      (true, none, none) word right out)
  have hprefix : run (a + 1) (getterFrame foreign
      (CylinderContextScanStep.initial source pre.length)) = ready := by
    rw [run_add hget 1]
    simpa [run, ready] using hhandoff
  have htotal : run (a + 1 + b) (getterFrame foreign
      (CylinderContextScanStep.initial source pre.length)) = run b ready :=
    run_add hprefix b
  let finish := run b ready
  have hfinish : (run 1 finish).l = none ∧
      (run 1 finish).stk 9 = finish.stk 9 :=
    done_step finish hlabel
  refine ⟨a + 1 + b + 1, by omega, ?_, ?_⟩
  · rw [run_add htotal 1]
    exact hfinish.1
  · rw [run_add htotal 1, hfinish.2]
    exact houtput

def pairForeign (right out : List Bool) : Stack → List Bool :=
  fun k => if k = 12 then right else if k = 9 then out else []

theorem actual_retained_tuple_pair {q : Nat}
    (entry : (Fin q → Nat) × ℚ) (i : Fin q) (y : Nat)
    (out : List Bool) :
    let xs := List.ofFn (fun j : Fin q => (entry.1 j).bits)
    let tuple := SourceListEncoding.encode xs
    ∃ t ≤ 2 * i.val + 5 +
        (2 * tuple.length + 5 +
          (4 * xs.length.bits.length + 6 +
            CurrentAdditive.GaussListContext.IndexedFieldProgram.fieldCost
              (xs.take i.val ++ [(entry.1 i).bits]))) +
        1 + (min (entry.1 i).bits.length y.bits.length + 1) + 1,
      (run t (getterFrame (pairForeign y.bits out)
        (CylinderContextScanStep.initial tuple i.val))).l = none ∧
      (run t (getterFrame (pairForeign y.bits out)
        (CylinderContextScanStep.initial tuple i.val))).stk 9 =
        decide (SequentialCode.generatedFeatureValue entry.1
          [(i.val, y)] = 1) :: out := by
  dsimp only
  let xs := List.ofFn (fun j : Fin q => (entry.1 j).bits)
  have hi : i.val < xs.length := by simp [xs, i.isLt]
  have hsplit : xs = xs.take i.val ++
      (entry.1 i).bits :: xs.drop (i.val + 1) := by
    calc
      xs = xs.take i.val ++ xs.drop i.val :=
        (List.take_append_drop i.val xs).symm
      _ = xs.take i.val ++ (entry.1 i).bits :: xs.drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons hi]
        simp [xs]
  have hpre : (xs.take i.val).length = i.val := by
    simp [List.length_take, hi.le]
  obtain ⟨t, ht, hl, ho⟩ := physical_tuple_pair
    (xs.take i.val) (entry.1 i).bits (xs.drop (i.val + 1))
    y.bits out (pairForeign y.bits out)
    (by simp [pairForeign]) (by simp [pairForeign])
  refine ⟨t, ?_, ?_, ?_⟩
  · simpa [← hsplit, hpre, xs] using ht
  · simpa [← hsplit, hpre, xs] using hl
  · have hp := CurrentAdditive.CylinderPairEvaluationBridge.pair_value_eq
      q entry.1 i y
    simpa [← hsplit, hpre, xs, hp] using ho

#print axioms finite_program
#print axioms getter_run
#print axioms compare_run_frame
#print axioms physical_tuple_pair
#print axioms actual_retained_tuple_pair

end CurrentAdditive.CylinderTuplePairProgram
