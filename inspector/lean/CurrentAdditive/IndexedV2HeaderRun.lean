import CurrentAdditive.IndexedV2Program

set_option maxHeartbeats 1000000

namespace CurrentAdditive.GaussListContext.IndexedV2Program

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding EncodedCommunication

noncomputable def headerFrame (S : Stack → List Bool)
    (c : SourceListMachineFields.HeaderConfig) : Config :=
  BitMachineStackEmbedding.cfg headerStack S Sum.inl
    headerControl (some (.inr (.inr .afterHeader))) c

noncomputable def indexFrame (c : IndexedFieldProgram.Config) : Config :=
  BitMachineStackEmbedding.cfg (Function.Embedding.refl Stack)
    c.stk (fun l => .inr (.inl l)) indexControl
    (some (.inr (.inr .done))) c

private theorem header_bank (S : Stack → List Bool)
    (T : Fin 3 → List Bool) (j : Stack) :
    BitMachineStackEmbedding.bank headerStack S T j =
      if h : j.val < 3 then T ⟨j.val, h⟩ else S j := by
  by_cases h : j.val < 3
  · have hj : j = headerStack ⟨j.val, h⟩ := Fin.ext rfl
    rw [dif_pos h]
    calc
      BitMachineStackEmbedding.bank headerStack S T j =
          BitMachineStackEmbedding.bank headerStack S T
            (headerStack ⟨j.val, h⟩) := congrArg _ hj
      _ = T ⟨j.val, h⟩ := BitMachineStackEmbedding.bank_at _ _ _ _
  · rw [dif_neg h]
    apply BitMachineStackEmbedding.bank_outside
    rintro ⟨k, hk⟩
    have hv := congrArg Fin.val hk
    simp [headerStack] at hv
    omega

theorem headerFrame_initial (input : List Bool) (index : Nat) :
    headerFrame (IndexedFieldProgram.initialBank input index)
      (ProtocolBinaryHeader.cfg (some .scan) (none, none) input [] []) =
    initial input index := by
  unfold headerFrame initial BitMachineStackEmbedding.cfg
    BitMachineStackEmbedding.stackCfg BitMachineInline.cfg
  simp only [ProtocolBinaryHeader.cfg]
  congr 1
  funext j
  rw [header_bank]
  fin_cases j <;> simp [IndexedFieldProgram.initialBank,
    ProtocolBinaryHeader.stackContents]

theorem headerFrame_success (n : Nat) (source : List Bool)
    (index : Nat) (v : ProtocolBinaryHeader.Control) :
    headerFrame (IndexedFieldProgram.initialBank
      (natField n ++ source) index)
      (ProtocolBinaryHeader.cfg none v source [] (true :: n.bits)) =
    ⟨some (.inr (.inr .afterHeader)), headerControl v,
     ![source, [], true :: n.bits, [], [], [], [], List.replicate index true]⟩ := by
  unfold headerFrame BitMachineStackEmbedding.cfg
    BitMachineStackEmbedding.stackCfg BitMachineInline.cfg
  simp only [ProtocolBinaryHeader.cfg]
  congr 1
  funext j
  rw [header_bank]
  fin_cases j <;> simp [IndexedFieldProgram.initialBank,
    ProtocolBinaryHeader.stackContents]

theorem header_run (n : Nat) (source : List Bool) (index : Nat) :
    ∃ t ≤ 3 * n.bits.length + 2, ∃ v : ProtocolBinaryHeader.Control,
      run t (initial (natField n ++ source) index) =
      ⟨some (.inr (.inr .afterHeader)), headerControl v,
       ![source, [], true :: n.bits, [], [], [], [], List.replicate index true]⟩ := by
  obtain ⟨v, he⟩ := SourceListMachineFields.header_natField n source
  obtain ⟨u, hu, hr⟩ := BitMachineStackEmbedding.outputs
    headerStack (IndexedFieldProgram.initialBank (natField n ++ source) index)
    Sum.inl headerControl (fun v => v.1) (by intro v; rfl)
    (some (.inr (.inr .afterHeader))) ProtocolBinaryHeader.program
    program (by intro l; rfl)
    (ProtocolBinaryHeader.cfg (some .scan) (none, none)
      (natField n ++ source) [] []) (3 * n.bits.length + 2)
    (by change (ProtocolBinaryHeader.run _ _).l = none; rw [he]; rfl)
  change run u (headerFrame _ _) =
    headerFrame _ (ProtocolBinaryHeader.run _ _) at hr
  rw [headerFrame_initial, he, headerFrame_success] at hr
  exact ⟨u, hu, v, hr⟩

def headerContents (source count : List Bool) (index : Nat) :
    Stack → List Bool :=
  ![source, [], count, [], [], [], [], List.replicate index true]

theorem run_succ {c c' : Config} (h : advance program c = c') (n : Nat) :
    run (n + 1) c = run n c' := by
  exact (Function.iterate_succ_apply _ _ _).trans (congrArg (run n) h)

theorem run_add {c c' : Config} {n : Nat} (h : run n c = c') (m : Nat) :
    run (n + m) c = run m c' := by
  rw [Nat.add_comm, run, Function.iterate_add_apply]
  exact congrArg (run m) h

theorem afterHeader_good (source count : List Bool)
    (index : Nat) (v : Control) :
    advance program
      ⟨some (.inr (.inr .afterHeader)), v,
       headerContents source (true :: count) index⟩ =
      ⟨some (.inr (.inr .clearHeaderCount)),
       (v.1, v.2.1, some true), headerContents source count index⟩ := by
  simp [advance, Turing.TM2.step, program, headerContents]
  funext j
  fin_cases j <;> rfl

theorem clearCount_cons (source : List Bool) (b : Bool)
    (tail : List Bool) (index : Nat) (v : Control) :
    advance program
      ⟨some (.inr (.inr .clearHeaderCount)), v,
       headerContents source (b :: tail) index⟩ =
      ⟨some (.inr (.inr .clearHeaderCount)),
       (v.1, v.2.1, some b), headerContents source tail index⟩ := by
  simp [advance, Turing.TM2.step, program, headerContents]
  funext j
  fin_cases j <;> rfl

theorem clearCount_nil (source : List Bool)
    (index : Nat) (v : Control) :
    advance program
      ⟨some (.inr (.inr .clearHeaderCount)), v,
       headerContents source [] index⟩ =
      ⟨some (.inr (.inr .startIndex)),
       (v.1, v.2.1, none), headerContents source [] index⟩ := by
  simp [advance, Turing.TM2.step, program, headerContents]

theorem indexFrame_ready (source : List Bool) (index : Nat) :
    indexFrame (IndexedFieldProgram.ready source index) =
      ⟨some (.inr (.inl (.inl (.inl .scan)))),
       indexControl (IndexedFieldProgram.fieldControl
         SourceListMachineFields.initialControl),
       IndexedFieldProgram.contents source [] [] index⟩ := by
  simp [indexFrame, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    IndexedFieldProgram.ready]
  exact BitMachineStackEmbedding.bank_restrict
    (Function.Embedding.refl Stack) _

theorem startIndex_step (source : List Bool) (index : Nat) (v : Control) :
    advance program
      ⟨some (.inr (.inr .startIndex)), v,
       headerContents source [] index⟩ =
      indexFrame (IndexedFieldProgram.ready source index) := by
  rw [indexFrame_ready]
  simp [advance, Turing.TM2.step, program, headerContents,
    IndexedFieldProgram.contents, indexControl]

theorem clearCount_run (source count : List Bool)
    (index : Nat) (v : Control) :
    ∃ w : Control,
      run (count.length + 1)
        ⟨some (.inr (.inr .clearHeaderCount)), v,
         headerContents source count index⟩ =
      ⟨some (.inr (.inr .startIndex)), w,
       headerContents source [] index⟩ := by
  induction count generalizing v with
  | nil =>
      refine ⟨(v.1, v.2.1, none), ?_⟩
      simpa using run_succ (clearCount_nil source index v) 0
  | cons b tail ih =>
      obtain ⟨w, hw⟩ := ih (v.1, v.2.1, some b)
      refine ⟨w, ?_⟩
      rw [List.length_cons, show tail.length + 1 + 1 =
        (tail.length + 1) + 1 by omega,
        run_succ (clearCount_cons source b tail index v), hw]

theorem header_to_index (n : Nat) (source : List Bool)
    (index : Nat) (v : ProtocolBinaryHeader.Control) :
    run (n.bits.length + 3)
      ⟨some (.inr (.inr .afterHeader)), headerControl v,
       headerContents source (true :: n.bits) index⟩ =
      indexFrame (IndexedFieldProgram.ready source index) := by
  obtain ⟨w, hw⟩ := clearCount_run source n.bits index
    (v, IndexedFieldProgram.fieldControl
      SourceListMachineFields.initialControl, some true)
  rw [show n.bits.length + 3 = (n.bits.length + 1 + 1) + 1 by omega,
    run_succ (afterHeader_good source n.bits index (headerControl v))]
  exact (run_add hw 1).trans (run_succ
    (startIndex_step source index w) 0)

theorem indexFrame_selected (source word : List Bool) :
    indexFrame
      ⟨none,
       (SourceListMachineFields.coreControl (some true, false), none),
       IndexedFieldProgram.contents source
         (List.replicate word.length true) word 0⟩ =
      ⟨some (.inr (.inr .done)),
       indexControl
         (SourceListMachineFields.coreControl (some true, false), none),
       IndexedFieldProgram.contents source
         (List.replicate word.length true) word 0⟩ := by
  simp [indexFrame, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg]
  exact BitMachineStackEmbedding.bank_restrict
    (Function.Embedding.refl Stack) _

theorem done_step (source word : List Bool) :
    advance program
      ⟨some (.inr (.inr .done)),
       indexControl
         (SourceListMachineFields.coreControl (some true, false), none),
       IndexedFieldProgram.contents source
         (List.replicate word.length true) word 0⟩ =
      ⟨none,
       indexControl
         (SourceListMachineFields.coreControl (some true, false), none),
       IndexedFieldProgram.contents source
         (List.replicate word.length true) word 0⟩ := by
  rfl

theorem indexFrame_foreign (S : Stack → List Bool)
    (c : IndexedFieldProgram.Config) :
    BitMachineStackEmbedding.cfg (Function.Embedding.refl Stack) S
      (fun l => .inr (.inl l)) indexControl
      (some (.inr (.inr .done))) c = indexFrame c := by
  unfold indexFrame BitMachineStackEmbedding.cfg
    BitMachineStackEmbedding.stackCfg
  congr 1
  funext j
  calc
    BitMachineStackEmbedding.bank (Function.Embedding.refl Stack) S c.stk j =
      c.stk j := BitMachineStackEmbedding.bank_at _ _ _ _
    _ = BitMachineStackEmbedding.bank (Function.Embedding.refl Stack)
      c.stk c.stk j := (BitMachineStackEmbedding.bank_at _ _ _ _).symm

theorem index_run (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) :
    ∃ t ≤ IndexedFieldProgram.fieldCost (pre ++ [word]) + 1,
      run t (indexFrame (IndexedFieldProgram.ready
        (SourceListEncoding.fields (pre ++ word :: suffix)) pre.length)) =
      ⟨none,
       indexControl
         (SourceListMachineFields.coreControl (some true, false), none),
       IndexedFieldProgram.contents (SourceListEncoding.fields suffix)
         (List.replicate word.length true) word 0⟩ := by
  obtain ⟨t, ht, hr⟩ := IndexedFieldProgram.select_fields pre word suffix
  obtain ⟨u, hu, he⟩ := BitMachineStackEmbedding.outputs
    (Function.Embedding.refl Stack)
    (IndexedFieldProgram.ready
      (SourceListEncoding.fields (pre ++ word :: suffix)) pre.length).stk
    (fun l => .inr (.inl l)) indexControl (fun v => v.2.1)
    (by intro v; rfl) (some (.inr (.inr .done)))
    IndexedFieldProgram.program program (by intro l; rfl)
    (IndexedFieldProgram.ready
      (SourceListEncoding.fields (pre ++ word :: suffix)) pre.length) t
    (by change (IndexedFieldProgram.run t _).l = none; rw [hr])
  change run u (indexFrame _) =
    BitMachineStackEmbedding.cfg (Function.Embedding.refl Stack)
      (IndexedFieldProgram.ready
        (SourceListEncoding.fields (pre ++ word :: suffix)) pre.length).stk
      (fun l => .inr (.inl l)) indexControl
      (some (.inr (.inr .done))) (IndexedFieldProgram.run t _) at he
  rw [indexFrame_foreign] at he
  rw [hr, indexFrame_selected] at he
  refine ⟨u + 1, by omega, ?_⟩
  exact (run_add he 1).trans (run_succ
    (done_step (SourceListEncoding.fields suffix) word) 0)

theorem select_v2 (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) :
    ∃ t ≤ 4 * (pre ++ word :: suffix).length.bits.length + 6 +
        IndexedFieldProgram.fieldCost (pre ++ [word]),
      run t (initial
        (SourceListEncoding.encode (pre ++ word :: suffix)) pre.length) =
      ⟨none,
       indexControl
         (SourceListMachineFields.coreControl (some true, false), none),
       IndexedFieldProgram.contents (SourceListEncoding.fields suffix)
         (List.replicate word.length true) word 0⟩ := by
  let xs := pre ++ word :: suffix
  obtain ⟨a, ha, v, har⟩ := header_run xs.length
    (SourceListEncoding.fields xs) pre.length
  obtain ⟨b, hb, hbr⟩ := index_run pre word suffix
  have hmid := (run_add har (xs.length.bits.length + 3)).trans
    (header_to_index xs.length (SourceListEncoding.fields xs) pre.length v)
  have hfinal := (run_add hmid b).trans hbr
  refine ⟨a + (xs.length.bits.length + 3) + b, ?_, ?_⟩
  · dsimp [xs] at *
    omega
  · simpa only [SourceListEncoding.encode, xs] using hfinal

#print axioms select_v2

#print axioms header_run

end CurrentAdditive.GaussListContext.IndexedV2Program
