import CurrentAdditive.IndexedFieldProgram

set_option maxHeartbeats 1000000

namespace CurrentAdditive.GaussListContext.IndexedFieldProgram

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding EncodedCommunication

noncomputable def fieldFrame (S : Stack → List Bool)
    (c : SourceListMachineFields.Config) : Config :=
  BitMachineStackEmbedding.cfg fieldStack S Sum.inl fieldControl
    (some (.inr .afterField)) c

def contents (source count payload : List Bool) (index : Nat) : Stack → List Bool :=
  ![source, [], [], [], [], count, payload, List.replicate index true]

def ready (source : List Bool) (index : Nat) : Config :=
  ⟨some (.inl (.inl .scan)),
    fieldControl SourceListMachineFields.initialControl,
    contents source [] [] index⟩

private theorem bank_get (S : Stack → List Bool)
    (T : SourceListMachineFields.Stack → List Bool) (j : Stack) :
    BitMachineStackEmbedding.bank fieldStack S T j =
      if h : j.val < 7 then T ⟨j.val, h⟩ else S j := by
  by_cases h : j.val < 7
  · have hj : j = fieldStack ⟨j.val, h⟩ := Fin.ext rfl
    rw [dif_pos h]
    calc
      BitMachineStackEmbedding.bank fieldStack S T j =
          BitMachineStackEmbedding.bank fieldStack S T
            (fieldStack ⟨j.val, h⟩) := congrArg _ hj
      _ = T ⟨j.val, h⟩ := BitMachineStackEmbedding.bank_at _ _ _ _
  · have hj : j = 7 := Fin.ext (by omega)
    rw [dif_neg h, hj]
    apply BitMachineStackEmbedding.bank_outside
    rintro ⟨k, hk⟩
    have hv := congrArg Fin.val hk
    simp [fieldStack] at hv
    omega

theorem frame_ready (word suffix : List Bool) (index : Nat) :
    fieldFrame (contents (natField word.length ++ (word ++ suffix)) [] [] index)
      (SourceListMachineFields.cfg (some (.inl .scan))
        SourceListMachineFields.initialControl
        {input := natField word.length ++ (word ++ suffix)}) =
      ready (natField word.length ++ (word ++ suffix)) index := by
  unfold fieldFrame ready BitMachineStackEmbedding.cfg
    BitMachineStackEmbedding.stackCfg BitMachineInline.cfg
  simp only [SourceListMachineFields.cfg]
  congr 1
  funext j
  rw [bank_get]
  fin_cases j <;> simp [contents, SourceListMachineFields.Data.stacks]

theorem frame_success (word suffix : List Bool) (index : Nat) :
    fieldFrame (contents (natField word.length ++ (word ++ suffix)) [] [] index)
      (SourceListMachineFields.success word suffix) =
      ⟨some (.inr .afterField),
        fieldControl (SourceListMachineFields.coreControl (some true, false)),
        contents suffix (List.replicate word.length true) word index⟩ := by
  unfold fieldFrame BitMachineStackEmbedding.cfg
    BitMachineStackEmbedding.stackCfg BitMachineInline.cfg
  simp only [SourceListMachineFields.success, SourceListMachineFields.cfg]
  congr 1
  funext j
  rw [bank_get]
  fin_cases j <;> simp [contents, SourceListMachineFields.Data.stacks]

theorem field_embedded (S : Stack → List Bool)
    (word suffix : List Bool) :
    ∃ t ≤ 20 * (word.length + 1) * (word.length.bits.length + 1),
      run t (fieldFrame S (SourceListMachineFields.cfg
        (some (.inl .scan)) SourceListMachineFields.initialControl
        {input := natField word.length ++ (word ++ suffix)})) =
      fieldFrame S (SourceListMachineFields.success word suffix) := by
  obtain ⟨t, ht, he⟩ := SourceListMachineFields.field_encoded word suffix
  obtain ⟨u, hu, hr⟩ := BitMachineStackEmbedding.outputs
    fieldStack S Sum.inl fieldControl Prod.fst (by intro v; rfl)
    (some (.inr .afterField)) SourceListMachineFields.program
    program (by intro l; rfl)
    (SourceListMachineFields.cfg (some (.inl .scan))
      SourceListMachineFields.initialControl
      {input := natField word.length ++ (word ++ suffix)}) t
    (by change (SourceListMachineFields.run t _).l = none
        rw [he]; rfl)
  change run u (fieldFrame S _) =
    fieldFrame S (SourceListMachineFields.run t _) at hr
  rw [he] at hr
  exact ⟨u, hu.trans ht, hr⟩

theorem fieldFrame_success (S : Stack → List Bool)
    (word suffix : List Bool) :
    fieldFrame S (SourceListMachineFields.success word suffix) =
      ⟨some (.inr .afterField),
        fieldControl (SourceListMachineFields.coreControl (some true, false)),
        BitMachineStackEmbedding.bank fieldStack S
          (SourceListMachineFields.success word suffix).stk⟩ := rfl

theorem run_succ {c c' : Config} (h : advance program c = c') (n : Nat) :
    run (n + 1) c = run n c' := by
  exact (Function.iterate_succ_apply _ _ _).trans (congrArg (run n) h)

theorem run_add {c c' : Config} {n : Nat} (h : run n c = c') (m : Nat) :
    run (n + m) c = run m c' := by
  rw [Nat.add_comm, run, Function.iterate_add_apply]
  exact congrArg (run m) h

theorem start_step (source : List Bool) (index : Nat) :
    advance program (initial source index) = ready source index := by
  simp [advance, Turing.TM2.step, program, initial, ready,
    contents, fieldControl, SourceListMachineFields.initialControl]
  funext j
  fin_cases j <;> rfl

theorem afterField_zero (source payload : List Bool) :
    advance program
      ⟨some (.inr .afterField),
       fieldControl (SourceListMachineFields.coreControl (some true, false)),
       contents source (List.replicate payload.length true) payload 0⟩ =
      ⟨none,
       (SourceListMachineFields.coreControl (some true, false), none),
       contents source (List.replicate payload.length true) payload 0⟩ := by
  simp [advance, Turing.TM2.step, program, contents, fieldControl,
    SourceListMachineFields.coreControl]

theorem afterField_succ (source payload : List Bool) (index : Nat) :
    advance program
      ⟨some (.inr .afterField),
       fieldControl (SourceListMachineFields.coreControl (some true, false)),
       contents source (List.replicate payload.length true) payload (index + 1)⟩ =
      ⟨some (.inr .clearPayload),
       (SourceListMachineFields.coreControl (some true, false), some true),
       contents source (List.replicate payload.length true) payload index⟩ := by
  simp [advance, Turing.TM2.step, program, contents, fieldControl,
    SourceListMachineFields.coreControl, List.replicate_succ]
  funext j
  fin_cases j <;> rfl

theorem clearPayload_cons (source count : List Bool) (b : Bool)
    (tail : List Bool) (index : Nat) (v : Control) :
    advance program ⟨some (.inr .clearPayload), v,
      contents source count (b :: tail) index⟩ =
      ⟨some (.inr .clearPayload), (v.1, some b),
       contents source count tail index⟩ := by
  simp [advance, Turing.TM2.step, program, contents]
  funext j
  fin_cases j <;> rfl

theorem clearPayload_nil (source count : List Bool)
    (index : Nat) (v : Control) :
    advance program ⟨some (.inr .clearPayload), v,
      contents source count [] index⟩ =
      ⟨some (.inr .clearCount), (v.1, none),
       contents source count [] index⟩ := by
  simp [advance, Turing.TM2.step, program, contents]

theorem clearCount_cons (source : List Bool) (b : Bool)
    (tail : List Bool) (index : Nat) (v : Control) :
    advance program ⟨some (.inr .clearCount), v,
      contents source (b :: tail) [] index⟩ =
      ⟨some (.inr .clearCount), (v.1, some b),
       contents source tail [] index⟩ := by
  simp [advance, Turing.TM2.step, program, contents]
  funext j
  fin_cases j <;> rfl

theorem clearCount_nil (source : List Bool)
    (index : Nat) (v : Control) :
    advance program ⟨some (.inr .clearCount), v,
      contents source [] [] index⟩ =
      ⟨some (.inr .again), (v.1, none),
       contents source [] [] index⟩ := by
  simp [advance, Turing.TM2.step, program, contents]

theorem again_step (source : List Bool) (index : Nat) (v : Control) :
    advance program ⟨some (.inr .again), v,
      contents source [] [] index⟩ = ready source index := by
  simp [advance, Turing.TM2.step, program, ready, contents,
    fieldControl, SourceListMachineFields.initialControl]

theorem clearPayload_run (source count payload : List Bool)
    (index : Nat) (v : Control) :
    ∃ w : Control,
      run (payload.length + 1)
        ⟨some (.inr .clearPayload), v,
         contents source count payload index⟩ =
      ⟨some (.inr .clearCount), w,
       contents source count [] index⟩ := by
  induction payload generalizing v with
  | nil =>
      refine ⟨(v.1, none), ?_⟩
      simpa using run_succ (clearPayload_nil source count index v) 0
  | cons b tail ih =>
      obtain ⟨w, hw⟩ := ih (v.1, some b)
      refine ⟨w, ?_⟩
      rw [List.length_cons, show tail.length + 1 + 1 =
        (tail.length + 1) + 1 by omega,
        run_succ (clearPayload_cons source count b tail index v), hw]

theorem clearCount_run (source count : List Bool)
    (index : Nat) (v : Control) :
    ∃ w : Control,
      run (count.length + 1)
        ⟨some (.inr .clearCount), v,
         contents source count [] index⟩ =
      ⟨some (.inr .again), w,
       contents source [] [] index⟩ := by
  induction count generalizing v with
  | nil =>
      refine ⟨(v.1, none), ?_⟩
      simpa using run_succ (clearCount_nil source index v) 0
  | cons b tail ih =>
      obtain ⟨w, hw⟩ := ih (v.1, some b)
      refine ⟨w, ?_⟩
      rw [List.length_cons, show tail.length + 1 + 1 =
        (tail.length + 1) + 1 by omega,
        run_succ (clearCount_cons source b tail index v), hw]

theorem skip_run (source payload : List Bool) (index : Nat) :
    run (2 * payload.length + 4)
      ⟨some (.inr .afterField),
       fieldControl (SourceListMachineFields.coreControl (some true, false)),
       contents source (List.replicate payload.length true) payload (index + 1)⟩ =
    ready source index := by
  obtain ⟨w, hw⟩ := clearPayload_run source
    (List.replicate payload.length true) payload index
    (SourceListMachineFields.coreControl (some true, false), some true)
  obtain ⟨z, hz⟩ := clearCount_run source
    (List.replicate payload.length true) index w
  have hlen : (List.replicate payload.length true).length = payload.length := by simp
  rw [show 2 * payload.length + 4 =
    ((payload.length + 1) + ((List.replicate payload.length true).length + 1) + 1) + 1 by omega,
    run_succ (afterField_succ source payload index)]
  exact (run_add hw _).trans ((run_add hz 1).trans
    (run_succ (again_step source index z) 0))

def fieldCost (xs : List (List Bool)) : Nat :=
  xs.foldr (fun word total =>
    20 * (word.length + 1) * (word.length.bits.length + 1) +
      2 * word.length + 5 + total) 0

theorem select_fields (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) :
    ∃ t ≤ fieldCost (pre ++ [word]),
      run t (ready (SourceListEncoding.fields (pre ++ word :: suffix))
        pre.length) =
      ⟨none,
       (SourceListMachineFields.coreControl (some true, false), none),
       contents (SourceListEncoding.fields suffix)
         (List.replicate word.length true) word 0⟩ := by
  induction pre with
  | nil =>
      obtain ⟨t, ht, hr⟩ := field_embedded
        (contents (natField word.length ++
          (word ++ SourceListEncoding.fields suffix)) [] [] 0)
        word (SourceListEncoding.fields suffix)
      rw [frame_ready, frame_success] at hr
      refine ⟨t + 1, ?_, ?_⟩
      · simp [fieldCost]; omega
      · simpa [SourceListEncoding.fields, List.append_assoc, run_add] using
          (run_add hr 1).trans (run_succ
            (afterField_zero (SourceListEncoding.fields suffix) word) 0)
  | cons first rest ih =>
      obtain ⟨t, ht, hr⟩ := field_embedded
        (contents (natField first.length ++
          (first ++ SourceListEncoding.fields (rest ++ word :: suffix)))
          [] [] (rest.length + 1))
        first (SourceListEncoding.fields (rest ++ word :: suffix))
      rw [frame_ready, frame_success] at hr
      obtain ⟨u, hu, hs⟩ := ih
      refine ⟨t + (2 * first.length + 4) + u, ?_, ?_⟩
      · simp [fieldCost] at *
        omega
      · have hstep := (run_add hr (2 * first.length + 4)).trans
          (skip_run (SourceListEncoding.fields (rest ++ word :: suffix))
            first rest.length)
        have hresult := (run_add hstep u).trans hs
        have hshape :
            SourceListEncoding.fields (first :: rest ++ word :: suffix) =
              natField first.length ++
                (first ++ SourceListEncoding.fields (rest ++ word :: suffix)) := by
          change (natField first.length ++ first) ++
              SourceListEncoding.fields (rest ++ word :: suffix) = _
          rw [List.append_assoc]
        rw [hshape]
        simpa only [List.length_cons] using hresult

#print axioms field_embedded
#print axioms select_fields

end CurrentAdditive.GaussListContext.IndexedFieldProgram
