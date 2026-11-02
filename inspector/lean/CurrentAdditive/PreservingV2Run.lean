import CurrentAdditive.PreservingV2Program

set_option maxHeartbeats 1000000

namespace CurrentAdditive.GaussListContext.PreservingV2Program

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding

def copiedBank (source : List Bool) (index : Nat) :
    Stack → List Bool :=
  ![source, [], [], [], [], [], [], List.replicate index true,
    source, []]

theorem copy_result (source : List Bool) (index : Nat) :
    SourceClausePreservingBroadcast.result
      (8 : Stack) (9 : Stack) [0] source
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
    ∃ t ≤ 2 * source.length + 3,
      run t (initial source index) =
        ⟨some (.inr (.inr .afterCopy)), copyControl ((), none),
         copiedBank source index⟩ := by
  have hlocal := SourceClausePreservingBroadcast.run_halt
    (8 : Stack) (9 : Stack) [0]
    (by decide) (by decide) (by decide) (by decide)
    source (initialBank source index)
    (by simp [initialBank]) (by simp [initialBank])
  let P := SourceClausePreservingBroadcast.program
    (8 : Stack) (9 : Stack) [0]
  let c : TM2.Cfg (fun _ : Stack => Bool)
      SourceClausePreservingBroadcast.Label (Unit × Option Bool) :=
    ⟨some .scan, ((), none), initialBank source index⟩
  have hhalt :
      (((advance P)^[2 * source.length + 3]) c).l = none := by
    exact congrArg (fun cfg => cfg.l) hlocal
  obtain ⟨u, hu, he⟩ := BitMachineStackEmbedding.outputs
    (Function.Embedding.refl Stack) (initialBank source index)
    Sum.inl copyControl Prod.fst (by intro v; rfl)
    (some (.inr (.inr .afterCopy)))
    P
    program (by intro l; rfl)
    c
    (2 * source.length + 3) hhalt
  have hframe : copyFrame (initialBank source index)
      (⟨some .scan, ((), none), initialBank source index⟩ :
        TM2.Cfg (fun _ : Stack => Bool)
          SourceClausePreservingBroadcast.Label (Unit × Option Bool)) =
      initial source index := by
    rw [copyFrame_foreign]
    rfl
  change run u (copyFrame _ _) = copyFrame _ _ at he
  rw [hframe, hlocal, copyFrame_foreign, copy_result] at he
  exact ⟨u, hu, he⟩

noncomputable def v2Frame (S : Stack → List Bool)
    (c : IndexedV2Program.Config) : Config :=
  BitMachineStackEmbedding.cfg v2Stack S (fun l => .inr (.inl l))
    v2Control (some (.inr (.inr .done))) c

private theorem v2_bank (S : Stack → List Bool)
    (T : IndexedV2Program.Stack → List Bool) (j : Stack) :
    BitMachineStackEmbedding.bank v2Stack S T j =
      if h : j.val < 8 then T ⟨j.val, h⟩ else S j := by
  by_cases h : j.val < 8
  · have hj : j = v2Stack ⟨j.val, h⟩ := Fin.ext rfl
    rw [dif_pos h]
    calc
      BitMachineStackEmbedding.bank v2Stack S T j =
          BitMachineStackEmbedding.bank v2Stack S T
            (v2Stack ⟨j.val, h⟩) := congrArg _ hj
      _ = T ⟨j.val, h⟩ := BitMachineStackEmbedding.bank_at _ _ _ _
  · rw [dif_neg h]
    apply BitMachineStackEmbedding.bank_outside
    rintro ⟨k, hk⟩
    have hv := congrArg Fin.val hk
    simp [v2Stack] at hv
    omega

theorem v2Frame_initial (source : List Bool) (index : Nat) :
    v2Frame (copiedBank source index)
      (IndexedV2Program.initial source index) =
      ⟨some (.inr (.inl (.inl .scan))),
       v2Control (IndexedV2Program.headerControl (none, none)),
       copiedBank source index⟩ := by
  unfold v2Frame BitMachineStackEmbedding.cfg
    BitMachineStackEmbedding.stackCfg BitMachineInline.cfg
  simp only [IndexedV2Program.initial]
  congr 1
  funext j
  rw [v2_bank]
  fin_cases j <;> simp [copiedBank,
    IndexedFieldProgram.initialBank]

theorem afterCopy_step (source : List Bool) (index : Nat) :
    advance program
      ⟨some (.inr (.inr .afterCopy)), copyControl ((), none),
       copiedBank source index⟩ =
      v2Frame (copiedBank source index)
        (IndexedV2Program.initial source index) := by
  rw [v2Frame_initial]
  rfl

theorem v2Frame_selected (source : List Bool) (index : Nat)
    (suffix word : List Bool) :
    v2Frame (copiedBank source index)
      ⟨none,
       IndexedV2Program.indexControl
         (SourceListMachineFields.coreControl (some true, false), none),
       IndexedFieldProgram.contents suffix
         (List.replicate word.length true) word 0⟩ =
      ⟨some (.inr (.inr .done)),
       v2Control (IndexedV2Program.indexControl
         (SourceListMachineFields.coreControl (some true, false), none)),
       ![suffix, [], [], [], [], List.replicate word.length true, word,
         [], source, []]⟩ := by
  unfold v2Frame BitMachineStackEmbedding.cfg
    BitMachineStackEmbedding.stackCfg BitMachineInline.cfg
  congr 1
  funext j
  rw [v2_bank]
  fin_cases j <;> simp [copiedBank, IndexedFieldProgram.contents]

theorem done_step (source suffix word : List Bool) :
    advance program
      ⟨some (.inr (.inr .done)),
       v2Control (IndexedV2Program.indexControl
         (SourceListMachineFields.coreControl (some true, false), none)),
       ![suffix, [], [], [], [], List.replicate word.length true, word,
         [], source, []]⟩ =
      ⟨none,
       v2Control (IndexedV2Program.indexControl
         (SourceListMachineFields.coreControl (some true, false), none)),
       ![suffix, [], [], [], [], List.replicate word.length true, word,
         [], source, []]⟩ := by
  rfl

theorem run_succ {c c' : Config} (h : advance program c = c') (n : Nat) :
    run (n + 1) c = run n c' := by
  exact (Function.iterate_succ_apply _ _ _).trans (congrArg (run n) h)

theorem run_add {c c' : Config} {n : Nat} (h : run n c = c') (m : Nat) :
    run (n + m) c = run m c' := by
  rw [Nat.add_comm, run, Function.iterate_add_apply]
  exact congrArg (run m) h

theorem select_preserving (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) :
    let source := SourceListEncoding.encode (pre ++ word :: suffix)
    ∃ t ≤ 2 * source.length + 5 +
        (4 * (pre ++ word :: suffix).length.bits.length + 6 +
          IndexedFieldProgram.fieldCost (pre ++ [word])),
      run t (initial source pre.length) =
      ⟨none,
       v2Control (IndexedV2Program.indexControl
         (SourceListMachineFields.coreControl (some true, false), none)),
       ![SourceListEncoding.fields suffix, [], [], [], [],
         List.replicate word.length true, word, [], source, []]⟩ := by
  dsimp only
  let source := SourceListEncoding.encode (pre ++ word :: suffix)
  obtain ⟨a, ha, hc⟩ := copy_run source pre.length
  obtain ⟨b, hb, hs⟩ := IndexedV2Program.select_v2 pre word suffix
  obtain ⟨u, hu, he⟩ := BitMachineStackEmbedding.outputs
    v2Stack (copiedBank source pre.length)
    (fun l => .inr (.inl l)) v2Control Prod.snd
    (by intro v; rfl) (some (.inr (.inr .done)))
    IndexedV2Program.program program (by intro l; rfl)
    (IndexedV2Program.initial source pre.length) b
    (by change (IndexedV2Program.run b _).l = none; rw [hs])
  change run u (v2Frame _ _) =
    v2Frame _ (IndexedV2Program.run b _) at he
  rw [hs, v2Frame_selected] at he
  have hmid := (run_add hc 1).trans
    (run_succ (afterCopy_step source pre.length) 0)
  have hfin := (run_add ((run_add hmid u).trans he) 1).trans
    (run_succ (done_step source (SourceListEncoding.fields suffix) word) 0)
  refine ⟨a + 1 + u + 1, ?_, ?_⟩
  · dsimp [source] at ha ⊢
    omega
  · exact hfin

#print axioms select_preserving

#print axioms copy_run

end CurrentAdditive.GaussListContext.PreservingV2Program
