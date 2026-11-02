import CurrentAdditive.CylinderEqualityAppendCallback

/-!
Instantiates the checked counted-V2 whole-list scheduler with a concrete
context-preserving equality callback.  This is a physical row of direct word
equalities; a cylinder feature still requires coordinate selection and
conjunction over a feature's pairs.
-/

namespace CurrentAdditive.CylinderEqualityListRun

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.ContextListScheduler
open CurrentAdditive.GaussListContext
open CurrentAdditive.CylinderEqualityAppendCallback

def piece (context word : List Bool) : List Bool :=
  [decide (word = context)]

noncomputable def selected (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (output context : List Bool) :
    ContextPreservingScan.Config :=
  let source := SourceListEncoding.encode (pre ++ word :: suffix)
  ContextPreservingScan.frame
    (foreignBank output context suffix.length)
    ⟨none,
     CylinderContextScanStep.getterControl
       (PreservingV2Program.v2Control
         (IndexedV2Program.indexControl
           (SourceListMachineFields.coreControl (some true, false), none))),
     CylinderContextScanStep.selectedBank source
       (SourceListEncoding.fields suffix) word pre.length⟩

theorem selected_banks (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (output context : List Bool) :
    (selected pre word suffix output context).stk 6 = word ∧
    (selected pre word suffix output context).stk 12 = context ∧
    (selected pre word suffix output context).stk 9 = output ∧
    (selected pre word suffix output context).stk 11 = [] ∧
    (selected pre word suffix output context).stk 7 = [] ∧
    (selected pre word suffix output context).stk 14 = [] := by
  constructor
  · simpa [selected, CylinderContextScanStep.selectedBank] using
      ContextPreservingScan.frame_bank
        (foreignBank output context suffix.length)
        (⟨none,
         CylinderContextScanStep.getterControl
           (PreservingV2Program.v2Control
             (IndexedV2Program.indexControl
               (SourceListMachineFields.coreControl (some true, false), none))),
         CylinderContextScanStep.selectedBank
           (SourceListEncoding.encode (pre ++ word :: suffix))
           (SourceListEncoding.fields suffix) word pre.length⟩ :
          CylinderContextScanStep.Config) 6
  constructor
  · simpa [selected, foreignBank] using
      (ContextPreservingScan.context_preserved
        (foreignBank output context suffix.length)
        (⟨none,
         CylinderContextScanStep.getterControl
           (PreservingV2Program.v2Control
             (IndexedV2Program.indexControl
               (SourceListMachineFields.coreControl (some true, false), none))),
         CylinderContextScanStep.selectedBank
           (SourceListEncoding.encode (pre ++ word :: suffix))
           (SourceListEncoding.fields suffix) word pre.length⟩ :
          CylinderContextScanStep.Config)).1
  constructor
  · simpa [selected, foreignBank] using
      ContextPreservingScan.output_preserved
        (foreignBank output context suffix.length)
        (⟨none,
         CylinderContextScanStep.getterControl
           (PreservingV2Program.v2Control
             (IndexedV2Program.indexControl
               (SourceListMachineFields.coreControl (some true, false), none))),
         CylinderContextScanStep.selectedBank
           (SourceListEncoding.encode (pre ++ word :: suffix))
           (SourceListEncoding.fields suffix) word pre.length⟩ :
          CylinderContextScanStep.Config)
  constructor
  · simpa [selected, CylinderContextScanStep.selectedBank] using
      ContextPreservingScan.frame_bank
        (foreignBank output context suffix.length)
        (⟨none,
         CylinderContextScanStep.getterControl
           (PreservingV2Program.v2Control
             (IndexedV2Program.indexControl
               (SourceListMachineFields.coreControl (some true, false), none))),
         CylinderContextScanStep.selectedBank
           (SourceListEncoding.encode (pre ++ word :: suffix))
           (SourceListEncoding.fields suffix) word pre.length⟩ :
          CylinderContextScanStep.Config) 11
  constructor
  · simpa [selected, CylinderContextScanStep.selectedBank] using
      ContextPreservingScan.frame_bank
        (foreignBank output context suffix.length)
        (⟨none,
         CylinderContextScanStep.getterControl
           (PreservingV2Program.v2Control
             (IndexedV2Program.indexControl
               (SourceListMachineFields.coreControl (some true, false), none))),
         CylinderContextScanStep.selectedBank
           (SourceListEncoding.encode (pre ++ word :: suffix))
           (SourceListEncoding.fields suffix) word pre.length⟩ :
          CylinderContextScanStep.Config) 7
  · have h := ContextPreservingScan.frame_bank
        (foreignBank output context suffix.length)
        (⟨none,
         CylinderContextScanStep.getterControl
           (PreservingV2Program.v2Control
             (IndexedV2Program.indexControl
               (SourceListMachineFields.coreControl (some true, false), none))),
         CylinderContextScanStep.selectedBank
           (SourceListEncoding.encode (pre ++ word :: suffix))
           (SourceListEncoding.fields suffix) word pre.length⟩ :
          CylinderContextScanStep.Config) 9
    simpa [selected, ContextPreservingScan.locate,
      CylinderContextScanStep.selectedBank] using h

theorem selected_run (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (initialOutput context : List Bool) :
    let output := initialOutput ++ joined (piece context) pre
    let S := (selected pre word suffix output context).stk
    ∃ t ≤ callbackBound word context output,
      ∃ (vFinal : Control) (SFinal : Fin 15 → List Bool),
      run t ⟨some (.copyContext .scan), bcontrol ((), none), S⟩ =
        ⟨none, vFinal, SFinal⟩ ∧
      SFinal 9 = initialOutput ++
        joined (piece context) (pre ++ [word]) ∧
      (∀ k : Fin 15,
        k = 8 ∨ k = 10 ∨ k = 12 ∨ k = 13 → SFinal k = S k) := by
  dsimp only
  let output := initialOutput ++ joined (piece context) pre
  let S := (selected pre word suffix output context).stk
  obtain ⟨h6,h12,h9,h11,h7,h14⟩ :=
    selected_banks pre word suffix output context
  obtain ⟨t,ht,v,T,hr,ho,hpres⟩ :=
    run_selected word context output S h6 h12 h9 h11 h7 h14
  refine ⟨t,ht,v,T,hr,?_,hpres⟩
  simpa [output, piece, joined_append_one, List.append_assoc]
    using ho

def canonicalBank (source output context : List Bool)
    (index fuel : Nat) : Fin 15 → List Bool :=
  ![[], [], [], [], [], [], [], [], source, output,
    List.replicate index true, [], context,
    List.replicate fuel true, []]

theorem canonical_frame (source output context : List Bool)
    (index fuel : Nat) :
    (ContextPreservingScan.frame (foreignBank output context fuel)
      (CylinderContextScanStep.initial source index)).stk =
      canonicalBank source output context index fuel := by
  let c := CylinderContextScanStep.initial source index
  let f := foreignBank output context fuel
  funext j
  by_cases hj : ∃ i : Fin 12, ContextPreservingScan.locate i = j
  · obtain ⟨i, rfl⟩ := hj
    change (ContextPreservingScan.frame f c).stk
      (ContextPreservingScan.locate i) =
      canonicalBank source output context index fuel
        (ContextPreservingScan.locate i)
    rw [ContextPreservingScan.frame_bank]
    fin_cases i <;>
      simp [c, canonicalBank, ContextPreservingScan.locate,
        CylinderContextScanStep.initial,
        CylinderContextScanStep.initialBank]
  · have hforeign : j = 9 ∨ j = 12 ∨ j = 13 := by
      have hrange : ∀ j : Fin 15,
          j ≠ 9 → j ≠ 12 → j ≠ 13 →
          ∃ i : Fin 12, ContextPreservingScan.locate i = j := by
        decide
      by_contra hn
      have h9 : j ≠ 9 := by intro h; exact hn (Or.inl h)
      have h12 : j ≠ 12 := by intro h; exact hn (Or.inr (Or.inl h))
      have h13 : j ≠ 13 := by intro h; exact hn (Or.inr (Or.inr h))
      exact hj (hrange j h9 h12 h13)
    change (ContextPreservingScan.frame f c).stk j =
      canonicalBank source output context index fuel j
    rw [ContextPreservingScan.frame_foreign f c j hj]
    rcases hforeign with h | h | h <;> subst j <;>
      simp [f, canonicalBank, foreignBank]

theorem post_clean (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (initialOutput context : List Bool)
    (SOut : Fin 15 → List Bool)
    (hout : SOut 9 = initialOutput ++
      joined (piece context) (pre ++ [word]))
    (hpres : ∀ k : Fin 15,
      k = 8 ∨ k = 10 ∨ k = 12 ∨ k = 13 →
      SOut k = (selected pre word suffix
        (initialOutput ++ joined (piece context) pre) context).stk k) :
    Function.update
      (BitMachineClearBank.cleared cleanBank SOut) 10
      (true :: (BitMachineClearBank.cleared cleanBank SOut) 10) =
    (ContextPreservingScan.frame
      (foreignBank
        (initialOutput ++ joined (piece context) (pre ++ [word]))
        context suffix.length)
      (CylinderContextScanStep.initial
        (SourceListEncoding.encode (pre ++ word :: suffix))
        (pre.length + 1))).stk := by
  rw [canonical_frame]
  let source := SourceListEncoding.encode (pre ++ word :: suffix)
  have hsel8 : (selected pre word suffix
      (initialOutput ++ joined (piece context) pre) context).stk 8 =
      source := by
    simpa [selected, source, CylinderContextScanStep.selectedBank] using
      ContextPreservingScan.frame_bank
        (foreignBank (initialOutput ++ joined (piece context) pre)
          context suffix.length)
        (⟨none,
         CylinderContextScanStep.getterControl
           (PreservingV2Program.v2Control
             (IndexedV2Program.indexControl
               (SourceListMachineFields.coreControl (some true, false), none))),
         CylinderContextScanStep.selectedBank source
           (SourceListEncoding.fields suffix) word pre.length⟩ :
          CylinderContextScanStep.Config) 8
  have hsel10 : (selected pre word suffix
      (initialOutput ++ joined (piece context) pre) context).stk 10 =
      List.replicate pre.length true := by
    simpa [selected, source, CylinderContextScanStep.selectedBank] using
      ContextPreservingScan.frame_bank
        (foreignBank (initialOutput ++ joined (piece context) pre)
          context suffix.length)
        (⟨none,
         CylinderContextScanStep.getterControl
           (PreservingV2Program.v2Control
             (IndexedV2Program.indexControl
               (SourceListMachineFields.coreControl (some true, false), none))),
         CylinderContextScanStep.selectedBank source
           (SourceListEncoding.fields suffix) word pre.length⟩ :
          CylinderContextScanStep.Config) 10
  have hsel12 := (selected_banks pre word suffix
    (initialOutput ++ joined (piece context) pre) context).2.1
  have hsel13 : (selected pre word suffix
      (initialOutput ++ joined (piece context) pre) context).stk 13 =
      List.replicate suffix.length true := by
    have hf := ContextPreservingScan.frame_foreign
      (foreignBank (initialOutput ++ joined (piece context) pre)
        context suffix.length)
      (⟨none,
       CylinderContextScanStep.getterControl
         (PreservingV2Program.v2Control
           (IndexedV2Program.indexControl
             (SourceListMachineFields.coreControl (some true, false), none))),
       CylinderContextScanStep.selectedBank source
         (SourceListEncoding.fields suffix) word pre.length⟩ :
        CylinderContextScanStep.Config) 13 (by decide)
    simpa [selected, source, foreignBank] using hf
  have h8 : SOut 8 = source := (hpres 8 (by simp)).trans hsel8
  have h10 : SOut 10 = List.replicate pre.length true :=
    (hpres 10 (by simp)).trans hsel10
  have h12 : SOut 12 = context := (hpres 12 (by simp)).trans hsel12
  have h13 : SOut 13 = List.replicate suffix.length true :=
    (hpres 13 (by simp)).trans hsel13
  have hclean_iff : ∀ k : Fin 15,
      (∃ i : Fin 10, cleanBank i = k) ↔
      k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨
      k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 11 ∨ k = 14 := by
    decide
  funext j
  fin_cases j <;>
    simp [BitMachineClearBank.cleared, hclean_iff,
      canonicalBank, source, hout, h8, h10, h12, h13,
      List.replicate_succ]

private structure CellRun (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (initialOutput context : List Bool) where
  time : Nat
  control : Control
  state : Fin 15 → List Bool
  bound : time ≤ callbackBound word context
    (initialOutput ++ joined (piece context) pre)
  run :
    CylinderEqualityAppendCallback.run time
      ⟨some (.copyContext .scan), bcontrol ((), none),
        (selected pre word suffix
          (initialOutput ++ joined (piece context) pre) context).stk⟩ =
      ⟨none, control, state⟩
  output : state 9 = initialOutput ++
    joined (piece context) (pre ++ [word])
  preserve : ∀ k : Fin 15,
    k = 8 ∨ k = 10 ∨ k = 12 ∨ k = 13 →
    state k = (selected pre word suffix
      (initialOutput ++ joined (piece context) pre) context).stk k

private noncomputable def chosenRun (pre : List (List Bool))
    (word : List Bool) (suffix : List (List Bool))
    (initialOutput context : List Bool) :
    CellRun pre word suffix initialOutput context := by
  classical
  let h := selected_run pre word suffix initialOutput context
  let t := Classical.choose h
  let ht := Classical.choose_spec h
  let v := Classical.choose ht.2
  let hv := Classical.choose_spec ht.2
  let S := Classical.choose hv
  let hS := Classical.choose_spec hv
  exact ⟨t, v, S, ht.1, hS.1, hS.2.1, hS.2.2⟩

noncomputable def equalityContract (initialOutput context : List Bool) :
    CallbackContract CylinderEqualityAppendCallback.program
      (.copyContext .scan) (bcontrol ((), none))
      (piece context) initialOutput context where
  time := fun pre word suffix =>
    (chosenRun pre word suffix initialOutput context).time
  control := fun pre word suffix =>
    (chosenRun pre word suffix initialOutput context).control
  state := fun pre word suffix =>
    (chosenRun pre word suffix initialOutput context).state
  callback_run := by
    intro pre word suffix
    exact (chosenRun pre word suffix initialOutput context).run
  post := by
    intro pre word suffix
    exact post_clean pre word suffix initialOutput context
      (chosenRun pre word suffix initialOutput context).state
      (chosenRun pre word suffix initialOutput context).output
      (chosenRun pre word suffix initialOutput context).preserve

theorem equality_list_run (words : List (List Bool))
    (initialOutput context : List Bool)
    (v : ContextListScheduler.Control Control) :
    ∃ t ≤ ContextListScheduler.remainingBudget
        CylinderEqualityAppendCallback.program
        (.copyContext .scan) (bcontrol ((), none))
        (piece context) initialOutput context
        (equalityContract initialOutput context) [] words,
      ∃ vFinal : ContextListScheduler.Control Control,
      ContextListScheduler.run CylinderEqualityAppendCallback.program
        (.copyContext .scan) (bcontrol ((), none)) t
        ⟨some (.inr (.inr .check)), v,
         (ContextPreservingScan.frame
           (foreignBank initialOutput context words.length)
           (CylinderContextScanStep.initial
             (SourceListEncoding.encode words) 0)).stk⟩ =
        ⟨none, vFinal,
         (ContextPreservingScan.frame
           (foreignBank (initialOutput ++ joined (piece context) words)
             context 0)
           (CylinderContextScanStep.initial
             (SourceListEncoding.encode words) words.length)).stk⟩ := by
  simpa only [List.nil_append, joined, List.flatMap_nil,
    List.append_nil, List.length_nil]
    using ContextListScheduler.run_remaining
      CylinderEqualityAppendCallback.program
      (.copyContext .scan) (bcontrol ((), none))
      (piece context) initialOutput context
      (equalityContract initialOutput context) [] words v

noncomputable def cycleCap (words : List (List Bool))
    (initialOutput context : List Bool) : Nat :=
  (Finset.univ : Finset (Fin words.length)).sup (fun i =>
    ContextListScheduler.cycleBudget
      CylinderEqualityAppendCallback.program
      (.copyContext .scan) (bcontrol ((), none))
      (piece context) initialOutput context
      (equalityContract initialOutput context)
      (words.take i.val) words[i] (words.drop (i.val + 1)))

theorem cycle_le_cap (words : List (List Bool))
    (initialOutput context : List Bool)
    (a : List (List Bool)) (word : List Bool)
    (b : List (List Bool)) (h : a ++ word :: b = words) :
    ContextListScheduler.cycleBudget
      CylinderEqualityAppendCallback.program
      (.copyContext .scan) (bcontrol ((), none))
      (piece context) initialOutput context
      (equalityContract initialOutput context) a word b ≤
      cycleCap words initialOutput context := by
  have hi : a.length < words.length := by
    rw [← h]
    simp
  let i : Fin words.length := ⟨a.length, hi⟩
  have htake : words.take i.val = a := by
    simp [i, ← h]
  have hword : words[i] = word := by
    simp [i, ← h]
  have hdrop : words.drop (i.val + 1) = b := by
    simp [i, ← h]
  have hs := Finset.le_sup
    (s := (Finset.univ : Finset (Fin words.length)))
    (f := fun j : Fin words.length =>
      ContextListScheduler.cycleBudget
        CylinderEqualityAppendCallback.program
        (.copyContext .scan) (bcontrol ((), none))
        (piece context) initialOutput context
        (equalityContract initialOutput context)
        (words.take j.val) words[j] (words.drop (j.val + 1)))
    (Finset.mem_univ i)
  simpa [cycleCap, htake, hword, hdrop] using hs

theorem equality_list_run_fixed (words : List (List Bool))
    (initialOutput context : List Bool)
    (v : ContextListScheduler.Control Control) :
    ∃ t ≤ (words.length + 1) *
        (cycleCap words initialOutput context + 1),
      ∃ vFinal : ContextListScheduler.Control Control,
      ContextListScheduler.run CylinderEqualityAppendCallback.program
        (.copyContext .scan) (bcontrol ((), none)) t
        ⟨some (.inr (.inr .check)), v,
         (ContextPreservingScan.frame
           (foreignBank initialOutput context words.length)
           (CylinderContextScanStep.initial
             (SourceListEncoding.encode words) 0)).stk⟩ =
        ⟨none, vFinal,
         (ContextPreservingScan.frame
           (foreignBank (initialOutput ++ joined (piece context) words)
             context 0)
           (CylinderContextScanStep.initial
             (SourceListEncoding.encode words) words.length)).stk⟩ := by
  simpa only [List.nil_append, joined, List.flatMap_nil,
    List.append_nil, List.length_nil]
    using ContextListScheduler.run_remaining_fixed_input
      CylinderEqualityAppendCallback.program
      (.copyContext .scan) (bcontrol ((), none))
      (piece context) initialOutput context
      (equalityContract initialOutput context)
      words (cycleCap words initialOutput context)
      (cycle_le_cap words initialOutput context)
      [] words rfl v

#print axioms selected_banks
#print axioms selected_run
#print axioms post_clean
#print axioms equality_list_run
#print axioms equality_list_run_fixed

end CurrentAdditive.CylinderEqualityListRun
