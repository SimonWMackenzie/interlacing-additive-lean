import EthInapproximability.CurrentPaper.SourceListMachineFields
import EthInapproximability.CurrentPaper.BitMachineIteration
import EthInapproximability.CurrentPaper.BitMachineBroadcast
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-!
# One charged streaming step on an ordered source list

Source: frozen v8 `06-eth.tex`, ordered sparsification and gap-reduction
outputs. Only the current length-framed payload enters the supplied finite
machine. The unread suffix and reversed output accumulator are untouched by
that call. All local working stacks are physically cleared before returning.
-/

namespace EthInapproximability.CurrentPaper.SourceListMachineItem

open Turing TM2.Stmt BitMachine BitMachineEncoding
open scoped BigOperators

open SourceListMachineFields hiding cfg run run_add program outer

inductive Admin (n : Nat) where
  | afterField | movePayload | restorePayload | startLocal | moveOutput
  | clear (i : Fin (n+1)) | clearCount | done
  deriving DecidableEq, Fintype

variable (M : Machine)

abbrev Stack := Fin M.stackCount ⊕ Fin 8
abbrev Label := Fin M.labelCount ⊕ (SourceListMachineFields.Label ⊕ Admin M.stackCount)
abbrev Control := (SourceListMachineFields.Control × Fin M.controlCount) × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack M => Bool) (Label M) (Control M)

def outer (l : Admin M.stackCount) : Label M := .inr (.inr l)
def fieldLabel (l : SourceListMachineFields.Label) : Label M := .inr (.inl l)

def fieldStack : Fin 7 ↪ Stack M where
  toFun := fun k => .inr ⟨k.val, by omega⟩
  inj' := by
    intro a b h
    apply Fin.ext
    exact congrArg (fun k : Fin 8 => k.val) (Sum.inr.inj h)

def localStack : Fin M.stackCount ↪ Stack M := ⟨Sum.inl, Sum.inl_injective⟩
def fieldControl (v : SourceListMachineFields.Control) : Control M := ((v,M.initial),none)
def localControl (v : Fin M.controlCount) : Control M := ((SourceListMachineFields.initialControl,v),none)

def program : Label M → TM2.Stmt (fun _ : Stack M => Bool) (Label M) (Control M)
  | .inl l => BitMachineStackEmbedding.stmt (localStack M) Sum.inl
      (localControl M) (fun v => v.1.2) (some (outer M .moveOutput)) (M.program l)
  | .inr (.inl l) => BitMachineStackEmbedding.stmt (fieldStack M) (fieldLabel M)
      (fieldControl M) (fun v => v.1.1) (some (outer M .afterField)) (SourceListMachineFields.program l)
  | .inr (.inr .afterField) =>
      branch (fun v => v.1.1.2.1 == some true)
        (goto (fun _ => outer M .movePayload))
        (load (fun v => (v.1,some false)) halt)
  | .inr (.inr .movePayload) => BitMachineBroadcast.scanStep (.inr 6) (.inr 1)
      (outer M .movePayload) (outer M .restorePayload)
  | .inr (.inr .restorePayload) => BitMachineBroadcast.restoreStep (.inr 1) [.inl M.input]
      (outer M .restorePayload) (outer M .startLocal)
  | .inr (.inr .startLocal) =>
      load (fun _ => localControl M M.initial) (goto (fun _ => .inl M.start))
  | .inr (.inr .moveOutput) => BitMachineBroadcast.scanStep (.inl M.output) (.inr 7)
      (outer M .moveOutput) (outer M (.clear 0))
  | .inr (.inr (.clear i)) =>
      if h : i.val < M.stackCount then
        pop (.inl ⟨i.val,h⟩) (fun v b => (v.1,b))
          (branch (fun v => v.2.isSome)
            (load (fun v => (v.1,none)) (goto (fun _ => outer M (.clear i))))
            (load (fun v => (v.1,none))
              (goto (fun _ => outer M (.clear ⟨i.val+1,by omega⟩)))))
      else load (fun _ => localControl M M.initial) (goto (fun _ => outer M .clearCount))
  | .inr (.inr .clearCount) => BitMachineClearBank.clearStep (.inr 5)
      (outer M .clearCount) (outer M .done)
  | .inr (.inr .done) => load
      (fun _ => ((SourceListMachineFields.initialControl,M.initial),some true)) halt

theorem moveOutput_program : program M (outer M .moveOutput) =
    BitMachineBroadcast.scanStep (.inl M.output) (.inr 7)
      (outer M .moveOutput) (outer M (.clear 0)) := rfl

theorem movePayload_program : program M (outer M .movePayload) =
    BitMachineBroadcast.scanStep (.inr 6) (.inr 1)
      (outer M .movePayload) (outer M .restorePayload) := rfl

theorem restorePayload_program : program M (outer M .restorePayload) =
    BitMachineBroadcast.restoreStep (.inr 1) [.inl M.input]
      (outer M .restorePayload) (outer M .startLocal) := rfl

theorem clearCount_program : program M (outer M .clearCount) =
    BitMachineClearBank.clearStep (.inr 5) (outer M .clearCount) (outer M .done) := rfl

def cfg (l : Option (Label M)) (v : Control M) (S : Fin M.stackCount → List Bool)
    (T : Fin 8 → List Bool) : Config M := ⟨l,v,Sum.elim S T⟩

def foreign (source count saved payload accumulator : List Bool) : Fin 8 → List Bool :=
  ![source,saved,[],[],[],count,payload,accumulator]

def run (t : Nat) (c : Config M) := BitMachineBroadcast.run (program M) t c

theorem run_add {c d : Config M} {t : Nat} (h : run M t c = d) (u : Nat) :
    run M (t+u) c = run M u d := by
  rw [Nat.add_comm t u]
  simp only [run,BitMachineBroadcast.run,Function.iterate_add_apply] at h ⊢
  rw [h]

theorem run_step {c d : Config M} (h : advance (program M) c = d) (t : Nat) :
    run M (t+1) c = run M t d := by
  simp only [run,BitMachineBroadcast.run,Function.iterate_succ_apply,h]

theorem field_bank (source accumulator : List Bool) (d : SourceListMachineFields.Data) :
    BitMachineStackEmbedding.bank (fieldStack M)
      (Sum.elim (fun _ => []) (foreign source [] [] [] accumulator)) d.stacks =
      Sum.elim (fun _ => []) ![d.input,d.saved,d.counter,d.work,d.reversed,d.count,d.payload,accumulator] := by
  funext k
  cases k with
  | inl k =>
      rw [BitMachineStackEmbedding.bank_outside]
      · rfl
      · simp [fieldStack]
  | inr k =>
      fin_cases k
      all_goals first
      | exact BitMachineStackEmbedding.bank_at (fieldStack M) _ d.stacks (0 : Fin 7)
      | exact BitMachineStackEmbedding.bank_at (fieldStack M) _ d.stacks (1 : Fin 7)
      | exact BitMachineStackEmbedding.bank_at (fieldStack M) _ d.stacks (2 : Fin 7)
      | exact BitMachineStackEmbedding.bank_at (fieldStack M) _ d.stacks (3 : Fin 7)
      | exact BitMachineStackEmbedding.bank_at (fieldStack M) _ d.stacks (4 : Fin 7)
      | exact BitMachineStackEmbedding.bank_at (fieldStack M) _ d.stacks (5 : Fin 7)
      | exact BitMachineStackEmbedding.bank_at (fieldStack M) _ d.stacks (6 : Fin 7)
      | (rw [BitMachineStackEmbedding.bank_outside]; rfl; intro ⟨i,hi⟩;
          have := congrArg Fin.val (Sum.inr.inj hi); simp [fieldStack] at this; omega)

theorem field_encoded (payload suffix accumulator : List Bool) :
    ∃ t ≤ 20*(payload.length+1)*(payload.length.bits.length+1),
      run M t
        (cfg M (some (fieldLabel M (.inl .scan))) (fieldControl M SourceListMachineFields.initialControl)
          (fun _ => []) (foreign (EncodedCommunication.natField payload.length ++ (payload++suffix))
            [] [] [] accumulator)) =
        cfg M (some (outer M .afterField))
          (fieldControl M (SourceListMachineFields.coreControl (some true,false)))
          (fun _ => []) (foreign suffix (List.replicate payload.length true) [] payload accumulator) := by
  obtain ⟨t,ht,he⟩ := SourceListMachineFields.field_encoded payload suffix
  have hh : (SourceListMachineFields.run t (SourceListMachineFields.cfg (some (.inl .scan)) SourceListMachineFields.initialControl
      {input := EncodedCommunication.natField payload.length ++ (payload++suffix)})).l = none := by
    rw [he]; rfl
  obtain ⟨u,hu,hr⟩ := BitMachineStackEmbedding.outputs (fieldStack M)
    (Sum.elim (fun _ => []) (foreign [] [] [] [] accumulator))
    (fieldLabel M) (fieldControl M) (fun v => v.1.1) (fun _ => rfl)
    (some (outer M .afterField)) SourceListMachineFields.program (program M) (fun _ => rfl)
    (SourceListMachineFields.cfg (some (.inl .scan)) SourceListMachineFields.initialControl
      {input := EncodedCommunication.natField payload.length ++ (payload++suffix)}) t hh
  change run M u _ = BitMachineStackEmbedding.cfg _ _ _ _ _ (SourceListMachineFields.run t _) at hr
  rw [he] at hr
  refine ⟨u,hu.trans ht,?_⟩
  simpa only [BitMachineStackEmbedding.cfg,BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg,SourceListMachineFields.cfg,SourceListMachineFields.success,field_bank,Option.map_some,cfg] using hr

theorem afterField_good (source count payload accumulator : List Bool) :
    advance (program M)
      (cfg M (some (outer M .afterField))
        (fieldControl M (SourceListMachineFields.coreControl (some true,false))) (fun _ => [])
        (foreign source count [] payload accumulator)) =
      cfg M (some (outer M .movePayload))
        (fieldControl M (SourceListMachineFields.coreControl (some true,false))) (fun _ => [])
        (foreign source count [] payload accumulator) := rfl

theorem movePayload_run (source count payload accumulator : List Bool)
    (v : Control M) (S : Fin M.stackCount → List Bool) :
    run M (payload.length+1)
      (cfg M (some (outer M .movePayload)) v S (foreign source count [] payload accumulator)) =
      cfg M (some (outer M .restorePayload)) (v.1,none) S
        (foreign source count payload.reverse [] accumulator) := by
  let bank := Sum.elim S (foreign source count [] payload accumulator)
  have hstart : bank = BitMachineBroadcast.contents (.inr 6) (.inr 1)
      bank payload [] := by
    funext k
    cases k with
    | inl k => rfl
    | inr k => fin_cases k <;> rfl
  have hend : BitMachineBroadcast.contents (.inr 6) (.inr 1)
      bank [] payload.reverse =
      Sum.elim S (foreign source count payload.reverse [] accumulator) := by
    funext k
    cases k with
    | inl k => rfl
    | inr k =>
        fin_cases k <;>
          simp only [BitMachineBroadcast.contents,Function.update_apply,Sum.elim_inr] <;>
          rfl
  have hcore := BitMachineBroadcast.scan_run (program M)
    (Sum.inr (6 : Fin 8) : Stack M) (.inr 1) (by simp)
    (outer M .movePayload) (outer M .restorePayload) (movePayload_program M)
    v.1 v.2 payload [] bank
  have h0 : cfg M (some (outer M .movePayload)) v S
      (foreign source count [] payload accumulator) =
      ⟨some (outer M .movePayload),v,
        BitMachineBroadcast.contents (.inr 6) (.inr 1) bank payload []⟩ :=
    congrArg (fun B : Stack M → List Bool => (⟨some (outer M .movePayload),v,B⟩ : Config M)) hstart
  have h1 : (⟨some (outer M .restorePayload),(v.1,none),
      BitMachineBroadcast.contents (.inr 6) (.inr 1) bank []
        (payload.reverse ++ [])⟩ : Config M) =
      cfg M (some (outer M .restorePayload)) (v.1,none) S
        (foreign source count payload.reverse [] accumulator) := by
    simpa only [List.append_nil] using
      congrArg (fun B : Stack M → List Bool =>
        (⟨some (outer M .restorePayload),(v.1,none),B⟩ : Config M)) hend
  exact (congrArg (run M (payload.length+1)) h0).trans (hcore.trans h1)

theorem restorePayload_run (source count saved accumulator : List Bool)
    (v : Control M) (S : Fin M.stackCount → List Bool) :
    run M (saved.length+1)
      (cfg M (some (outer M .restorePayload)) v S (foreign source count saved [] accumulator)) =
      cfg M (some (outer M .startLocal)) (v.1,none)
        (Function.update S M.input (saved.reverse ++ S M.input))
        (foreign source count [] [] accumulator) := by
  have h := BitMachineBroadcast.restore_run (program M)
    (Sum.inr (1 : Fin 8) : Stack M) [.inl M.input] (by simp) (by simp)
    (outer M .restorePayload) (outer M .startLocal) (restorePayload_program M) v.1 v.2 saved
    (Sum.elim S (foreign source count saved [] accumulator))
  have hi : Function.update (Sum.elim S (foreign source count saved [] accumulator)) (.inr 1) saved =
      Sum.elim S (foreign source count saved [] accumulator) := by
    funext k
    cases k with
    | inl k => rfl
    | inr k => fin_cases k <;> rfl
  have hf : Function.update
      (BitMachineBroadcast.prepend [.inl M.input] saved.reverse
        (Sum.elim S (foreign source count saved [] accumulator))) (.inr 1) [] =
      Sum.elim (Function.update S M.input (saved.reverse ++ S M.input))
        (foreign source count [] [] accumulator) := by
    funext k
    cases k with
    | inl k =>
      by_cases hk : k = M.input <;>
        simp only [Function.update_apply,BitMachineBroadcast.prepend,List.mem_singleton,
          Sum.inl.injEq,reduceCtorEq,Sum.elim_inl,hk,↓reduceIte]
    | inr k => fin_cases k <;> rfl
  rw [hi,hf] at h
  exact h

theorem prepare_run (source count payload accumulator : List Bool) (v : Control M) :
    run M (2*payload.length+3)
      (cfg M (some (outer M .movePayload)) v (fun _ => [])
        (foreign source count [] payload accumulator)) =
      cfg M (some (.inl M.start)) (localControl M M.initial)
        (M.init payload).stk (foreign source count [] [] accumulator) := by
  have h1 := movePayload_run M source count payload accumulator v (fun _ => [])
  have h2 := restorePayload_run M source count payload.reverse accumulator (v.1,none) (fun _ => [])
  simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at h2
  have h3 : advance (program M)
      (cfg M (some (outer M .startLocal)) (v.1,none)
        (Function.update (fun _ => []) M.input payload) (foreign source count [] [] accumulator)) =
      cfg M (some (.inl M.start)) (localControl M M.initial)
        (M.init payload).stk (foreign source count [] [] accumulator) := by
    simp only [advance,cfg,outer,program,TM2.step,TM2.stepAux,Option.getD_some]
    congr 1
    funext k
    cases k with
    | inl k => by_cases hk : k = M.input <;> simp [Function.update_apply,Machine.init,hk]
    | inr k => rfl
  have hr := (run_add M ((run_add M h1 _).trans h2) 1).trans (run_step M h3 0)
  have ht : payload.length + 1 + (payload.length + 1) + 1 =
      2 * payload.length + 3 := by omega
  rw [ht] at hr
  simpa only [run,BitMachineBroadcast.run,Function.iterate_zero_apply] using hr

theorem local_bank (S : Fin M.stackCount → List Bool) (T : Fin 8 → List Bool) :
    BitMachineStackEmbedding.bank (localStack M) (Sum.elim S T) S = Sum.elim S T := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro k
  rfl

theorem component_run (input output source count accumulator : List Bool) (bound : Nat)
    (h : M.OutputsWithin input output bound) :
    ∃ t ≤ bound, ∃ c : M.Config,
      c.l = none ∧ c.stk M.output = output ∧
      run M t (cfg M (some (.inl M.start)) (localControl M M.initial) (M.init input).stk
        (foreign source count [] [] accumulator)) =
      cfg M (some (outer M .moveOutput)) (localControl M c.var) c.stk
        (foreign source count [] [] accumulator) ∧
      ∀ k, (c.stk k).length ≤ input.length + bound*M.pushBound := by
  obtain ⟨n,hn,hh,ho⟩ := h
  let c := M.run n (M.init input)
  obtain ⟨t,ht,hr⟩ := BitMachineStackEmbedding.outputs (localStack M)
    (Sum.elim c.stk (foreign source count [] [] accumulator)) Sum.inl
    (localControl M) (fun v => v.1.2) (fun _ => rfl)
    (some (outer M .moveOutput)) M.program (program M) (fun _ => rfl) (M.init input) n hh
  have hb (R : Fin M.stackCount → List Bool) :
      BitMachineStackEmbedding.bank (localStack M)
        (Sum.elim c.stk (foreign source count [] [] accumulator)) R =
        Sum.elim R (foreign source count [] [] accumulator) := by
    funext k
    cases k with
    | inl k => exact BitMachineStackEmbedding.bank_at (localStack M) _ R k
    | inr k => rw [BitMachineStackEmbedding.bank_outside]; rfl; simp [localStack]
  refine ⟨t,ht.trans hn,c,hh,ho,?_,?_⟩
  · change run M t _ = BitMachineStackEmbedding.cfg _ _ _ _ _ c at hr
    simp only [BitMachineStackEmbedding.cfg,BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg,hb] at hr
    have hc : c.l = none := hh
    rw [hc] at hr
    exact hr
  · intro k
    have hk := run_length M (M.init input) k n
    have hi : ((M.init input).stk k).length ≤ input.length := by
      simp only [Machine.init]
      split <;> simp
    have hmul : n * M.pushBound ≤ bound * M.pushBound :=
      Nat.mul_le_mul_right _ hn
    exact hk.trans (Nat.add_le_add hi hmul)

theorem moveOutput_run (source count output accumulator : List Bool)
    (v : Control M) (S : Fin M.stackCount → List Bool) (hS : S M.output = output) :
    run M (output.length+1)
      (cfg M (some (outer M .moveOutput)) v S (foreign source count [] [] accumulator)) =
      cfg M (some (outer M (.clear 0))) (v.1,none) (Function.update S M.output [])
        (foreign source count [] [] (output.reverse++accumulator)) := by
  let bank := Sum.elim (Function.update S M.output []) (foreign source count [] [] [])
  have hstart : Sum.elim S (foreign source count [] [] accumulator) =
      BitMachineBroadcast.contents (.inl M.output) (.inr 7)
      bank output accumulator := by
    funext k
    cases k with
    | inl k =>
        by_cases hk : k = M.output
        · subst k
          simp only [BitMachineBroadcast.contents,Function.update_apply,bank,hS,
            Sum.elim_inl,Sum.inl.injEq,reduceCtorEq,↓reduceIte]
        · simp only [BitMachineBroadcast.contents,Function.update_apply,bank,hk,
            Sum.elim_inl,Sum.inl.injEq,reduceCtorEq,↓reduceIte]
    | inr k => fin_cases k <;> simp only [BitMachineBroadcast.contents,
        Function.update_apply,bank,Sum.elim_inr,reduceCtorEq,↓reduceIte] <;> rfl
  have hend : BitMachineBroadcast.contents (.inl M.output) (.inr 7)
      bank [] (output.reverse ++ accumulator) =
      Sum.elim (Function.update S M.output [])
        (foreign source count [] [] (output.reverse++accumulator)) := by
    funext k
    cases k with
    | inl k =>
        by_cases hk : k = M.output
        · subst k
          simp only [BitMachineBroadcast.contents,Function.update_apply,bank,
            Sum.elim_inl,Sum.inl.injEq,reduceCtorEq,↓reduceIte]
        · simp only [BitMachineBroadcast.contents,Function.update_apply,bank,hk,
            Sum.elim_inl,Sum.inl.injEq,reduceCtorEq,↓reduceIte]
    | inr k => fin_cases k <;> simp only [BitMachineBroadcast.contents,
        Function.update_apply,bank,Sum.elim_inr,reduceCtorEq,↓reduceIte] <;> rfl
  have h := BitMachineBroadcast.scan_run (program M)
    (Sum.inl M.output : Stack M) (.inr 7) (by simp)
    (outer M .moveOutput) (outer M (.clear 0)) (moveOutput_program M) v.1 v.2 output accumulator
    bank
  change BitMachineBroadcast.run (program M) (output.length+1)
      ⟨some (outer M .moveOutput),v,
        Sum.elim S (foreign source count [] [] accumulator)⟩ =
    ⟨some (outer M (.clear 0)),(v.1,none),
      Sum.elim (Function.update S M.output [])
        (foreign source count [] [] (output.reverse++accumulator))⟩
  calc
    _ = BitMachineBroadcast.run (program M) (output.length+1)
      ⟨some (outer M .moveOutput),v,
        BitMachineBroadcast.contents (.inl M.output) (.inr 7) bank output accumulator⟩ := by
        rw [hstart]
    _ = ⟨some (outer M (.clear 0)),(v.1,none),
      BitMachineBroadcast.contents (.inl M.output) (.inr 7) bank []
        (output.reverse ++ accumulator)⟩ := h
    _ = _ := by rw [hend]

theorem clear_run (v : SourceListMachineFields.Control × Fin M.controlCount)
    (S : Fin M.stackCount → List Bool) (source count accumulator : List Bool) :
    run M ((∑ k, (S k).length)+M.stackCount+1)
      (cfg M (some (outer M (.clear 0))) (v,none) S (foreign source count [] [] accumulator)) =
      cfg M (some (outer M .clearCount)) (localControl M M.initial) (fun _ => [])
        (foreign source count [] [] accumulator) := by
  have h := BitMachineClearBank.clear_bank_run (program M)
    (fun _ => (SourceListMachineFields.initialControl,M.initial))
    (outer M .clearCount) M.stackCount (fun k => (Sum.inl k : Stack M)) Sum.inl_injective
    (fun i => outer M (.clear i))
    (fun i => by simp only [outer,program,Fin.val_castSucc,i.isLt,↓reduceDIte]; rfl)
    (by simp only [outer,program,Fin.val_last,lt_self_iff_false,↓reduceDIte]; rfl)
    v (Sum.elim S (foreign source count [] [] accumulator))
  have he : BitMachineClearBank.cleared (fun k => (Sum.inl k : Stack M))
      (Sum.elim S (foreign source count [] [] accumulator)) =
      Sum.elim (fun _ => []) (foreign source count [] [] accumulator) := by
    funext k
    cases k with
    | inl k => simp [BitMachineClearBank.cleared]
    | inr k => simp [BitMachineClearBank.cleared]
  change run M _ _ = _
  simp only [run,BitMachineBroadcast.run,cfg,Sum.elim_inl,he,localControl] at h ⊢
  exact h

end EthInapproximability.CurrentPaper.SourceListMachineItem
