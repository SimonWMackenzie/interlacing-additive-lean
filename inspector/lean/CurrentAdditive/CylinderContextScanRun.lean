import CurrentAdditive.CylinderContextScanStep

set_option maxHeartbeats 1000000

namespace CurrentAdditive.CylinderContextScanStep

open EthInapproximability.CurrentPaper
open CurrentAdditive.GaussListContext
open Turing BitMachineEncoding

def copiedBank (source : List Bool) (index : Nat) : Stack → List Bool :=
  ![[], [], [], [], [], [], [], List.replicate index true,
    source, [], List.replicate index true, []]

theorem copy_result (source : List Bool) (index : Nat) :
    SourceClausePreservingBroadcast.result
      (10 : Stack) (11 : Stack) [7] (List.replicate index true)
      (initialBank source index) = copiedBank source index := by
  funext j
  fin_cases j <;> simp [SourceClausePreservingBroadcast.result,
    BitMachineBroadcast.prepend, initialBank, copiedBank]

noncomputable def copyFrame (S : Stack → List Bool)
    (c : TM2.Cfg (fun _ : Stack => Bool)
      SourceClausePreservingBroadcast.Label (Unit × Option Bool)) : Config :=
  BitMachineStackEmbedding.cfg (Function.Embedding.refl Stack) S Sum.inl
    copyControl (some (.inr (.inr .afterCopy))) c

theorem copyFrame_foreign (S : Stack → List Bool)
    (c : TM2.Cfg (fun _ : Stack => Bool)
      SourceClausePreservingBroadcast.Label (Unit × Option Bool)) :
    copyFrame S c =
      ⟨match c.l with
        | none => some (.inr (.inr .afterCopy))
        | some l => some (.inl l),
       copyControl c.var, c.stk⟩ := by
  unfold copyFrame BitMachineStackEmbedding.cfg
    BitMachineStackEmbedding.stackCfg BitMachineInline.cfg
  have hbank : BitMachineStackEmbedding.bank
      (Function.Embedding.refl Stack) S c.stk = c.stk := by
    funext j
    exact BitMachineStackEmbedding.bank_at _ _ _ _
  rw [hbank]
  cases c with
  | mk l v stk =>
      simp
      cases l <;> rfl

theorem copy_run (source : List Bool) (index : Nat) :
    ∃ t ≤ 2 * index + 3,
      run t (initial source index) =
        ⟨some (.inr (.inr .afterCopy)), copyControl ((), none),
         copiedBank source index⟩ := by
  have hlocal := SourceClausePreservingBroadcast.run_halt
    (10 : Stack) (11 : Stack) [7]
    (by decide) (by decide) (by decide) (by decide)
    (List.replicate index true) (initialBank source index)
    (by simp [initialBank]) (by simp [initialBank])
  simp only [List.length_replicate] at hlocal
  let P := SourceClausePreservingBroadcast.program
    (10 : Stack) (11 : Stack) [7]
  let c : TM2.Cfg (fun _ : Stack => Bool)
      SourceClausePreservingBroadcast.Label (Unit × Option Bool) :=
    ⟨some .scan, ((), none), initialBank source index⟩
  have hhalt : (((advance P)^[2 * index + 3]) c).l = none := by
    exact congrArg (fun cfg => cfg.l) hlocal
  obtain ⟨u, hu, he⟩ := BitMachineStackEmbedding.outputs
    (Function.Embedding.refl Stack) (initialBank source index)
    Sum.inl copyControl Prod.fst (by intro v; rfl)
    (some (.inr (.inr .afterCopy))) P program (by intro l; rfl)
    c (2 * index + 3) hhalt
  have hframe : copyFrame (initialBank source index) c =
      initial source index := by
    rw [copyFrame_foreign]
    rfl
  change run u (copyFrame _ _) = copyFrame _ _ at he
  rw [hframe, hlocal, copyFrame_foreign, copy_result] at he
  exact ⟨u, hu, he⟩

noncomputable def getterFrame (S : Stack → List Bool)
    (c : PreservingV2Program.Config) : Config :=
  BitMachineStackEmbedding.cfg getterStack S
    (fun l => .inr (.inl l)) getterControl
    (some (.inr (.inr .done))) c

private theorem getter_bank (S : Stack → List Bool)
    (T : PreservingV2Program.Stack → List Bool) (j : Stack) :
    BitMachineStackEmbedding.bank getterStack S T j =
      if h : j.val < 10 then T ⟨j.val, h⟩ else S j := by
  by_cases h : j.val < 10
  · have hj : j = getterStack ⟨j.val, h⟩ := Fin.ext rfl
    rw [dif_pos h]
    calc
      BitMachineStackEmbedding.bank getterStack S T j =
          BitMachineStackEmbedding.bank getterStack S T
            (getterStack ⟨j.val, h⟩) := congrArg _ hj
      _ = T ⟨j.val, h⟩ := BitMachineStackEmbedding.bank_at _ _ _ _
  · rw [dif_neg h]
    apply BitMachineStackEmbedding.bank_outside
    rintro ⟨k, hk⟩
    have hv := congrArg Fin.val hk
    simp [getterStack] at hv
    omega

theorem getterFrame_initial (source : List Bool) (index : Nat) :
    getterFrame (copiedBank source index)
      (PreservingV2Program.initial source index) =
      ⟨some (.inr (.inl (.inl .scan))),
       getterControl (PreservingV2Program.copyControl ((), none)),
       copiedBank source index⟩ := by
  unfold getterFrame BitMachineStackEmbedding.cfg
    BitMachineStackEmbedding.stackCfg BitMachineInline.cfg
  simp only [PreservingV2Program.initial]
  congr 1
  funext j
  rw [getter_bank]
  fin_cases j <;> simp [copiedBank,
    PreservingV2Program.initialBank]

theorem afterCopy_step (source : List Bool) (index : Nat) :
    advance program
      ⟨some (.inr (.inr .afterCopy)), copyControl ((), none),
       copiedBank source index⟩ =
      getterFrame (copiedBank source index)
        (PreservingV2Program.initial source index) := by
  rw [getterFrame_initial]
  rfl

def selectedBank (source suffix word : List Bool) (index : Nat) :
    Stack → List Bool :=
  ![suffix, [], [], [], [], List.replicate word.length true, word,
    [], source, [], List.replicate index true, []]

theorem getterFrame_selected (source suffix word : List Bool) (index : Nat) :
    getterFrame (copiedBank source index)
      ⟨none,
       PreservingV2Program.v2Control (IndexedV2Program.indexControl
         (SourceListMachineFields.coreControl (some true, false), none)),
       ![suffix, [], [], [], [], List.replicate word.length true,
         word, [], source, []]⟩ =
      ⟨some (.inr (.inr .done)),
       getterControl (PreservingV2Program.v2Control
         (IndexedV2Program.indexControl
           (SourceListMachineFields.coreControl (some true, false), none))),
       selectedBank source suffix word index⟩ := by
  unfold getterFrame BitMachineStackEmbedding.cfg
    BitMachineStackEmbedding.stackCfg BitMachineInline.cfg
  congr 1
  funext j
  rw [getter_bank]
  fin_cases j <;> simp [selectedBank, copiedBank]

theorem done_step (source suffix word : List Bool) (index : Nat) :
    advance program
      ⟨some (.inr (.inr .done)),
       getterControl (PreservingV2Program.v2Control
         (IndexedV2Program.indexControl
           (SourceListMachineFields.coreControl (some true, false), none))),
       selectedBank source suffix word index⟩ =
      ⟨none,
       getterControl (PreservingV2Program.v2Control
         (IndexedV2Program.indexControl
           (SourceListMachineFields.coreControl (some true, false), none))),
       selectedBank source suffix word index⟩ := by
  rfl

theorem run_succ {c c' : Config} (h : advance program c = c') (n : Nat) :
    run (n + 1) c = run n c' := by
  exact (Function.iterate_succ_apply _ _ _).trans (congrArg (run n) h)

theorem run_add {c c' : Config} {n : Nat} (h : run n c = c') (m : Nat) :
    run (n + m) c = run m c' := by
  rw [Nat.add_comm, run, Function.iterate_add_apply]
  exact congrArg (run m) h

theorem scan_step (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) :
    let source := SourceListEncoding.encode (pre ++ word :: suffix)
    ∃ t ≤ 2 * pre.length + 5 +
        (2 * source.length + 5 +
          (4 * (pre ++ word :: suffix).length.bits.length + 6 +
            IndexedFieldProgram.fieldCost (pre ++ [word]))),
      run t (initial source pre.length) =
        ⟨none,
         getterControl (PreservingV2Program.v2Control
           (IndexedV2Program.indexControl
             (SourceListMachineFields.coreControl (some true, false), none))),
         selectedBank source (SourceListEncoding.fields suffix)
           word pre.length⟩ := by
  dsimp only
  let source := SourceListEncoding.encode (pre ++ word :: suffix)
  obtain ⟨a, ha, hc⟩ := copy_run source pre.length
  obtain ⟨b, hb, hs⟩ := PreservingV2Program.select_preserving
    pre word suffix
  obtain ⟨u, hu, he⟩ := BitMachineStackEmbedding.outputs
    getterStack (copiedBank source pre.length)
    (fun l => .inr (.inl l)) getterControl Prod.snd
    (by intro v; rfl) (some (.inr (.inr .done)))
    PreservingV2Program.program program (by intro l; rfl)
    (PreservingV2Program.initial source pre.length) b
    (by change (PreservingV2Program.run b _).l = none; rw [hs])
  change run u (getterFrame _ _) =
    getterFrame _ (PreservingV2Program.run b _) at he
  rw [hs, getterFrame_selected] at he
  have hmid := (run_add hc 1).trans
    (run_succ (afterCopy_step source pre.length) 0)
  have hfin := (run_add ((run_add hmid u).trans he) 1).trans
    (run_succ (done_step source (SourceListEncoding.fields suffix)
      word pre.length) 0)
  refine ⟨a + 1 + u + 1, ?_, ?_⟩
  · dsimp [source] at ha ⊢
    omega
  · exact hfin

#print axioms scan_step

end CurrentAdditive.CylinderContextScanStep
