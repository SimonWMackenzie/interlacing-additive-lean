import CurrentAdditive.GaussPivotPairEmit32
import CurrentAdditive.CodeDAppendAtEnd15

/-!
The checked Fin15 append controller runs inside a fixed Fin32 program. A
source-preserving copy routes the old pivot-list body from bank 23 to the
append output bank 27, and another routes the framed new pivot pair from
bank 28 to payload bank 26. Scratch 31 is emptied after each copy. The
append controller then writes the exact body with one new pair at its end.
-/

namespace CurrentAdditive.GaussPivotAppend32

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open Turing BitMachineEncoding

abbrev Stack := Fin 32
abbrev Control := Unit × Option Bool

inductive Label where
  | copyBody (l : SourceClausePreservingBroadcast.Label)
  | copyBodyDirect (l : SourceClausePreservingBroadcast.Label)
  | copyPayload (l : SourceClausePreservingBroadcast.Label)
  | append (l : CurrentAdditive.CodeDAppendAtEnd15.Label)
  | done
  deriving DecidableEq, Fintype

abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def appendSlot : CurrentAdditive.CodeDAppendAtEnd15.Stack ↪ Stack where
  toFun j := ![0, 1, 2, 3, 8, 26, 9, 10, 11, 27, 12, 24, 13, 14, 31] j
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .copyBody l => BitMachineInline.stmt Label.copyBody id id
      (some (.copyPayload .scan))
      (SourceClausePreservingBroadcast.program (23 : Stack) 31 [27] l)
  | .copyBodyDirect l => BitMachineInline.stmt Label.copyBodyDirect id id
      (some (.append .saveScan))
      (SourceClausePreservingBroadcast.program (23 : Stack) 31 [27] l)
  | .copyPayload l => BitMachineInline.stmt Label.copyPayload id id
      (some (.append .saveScan))
      (SourceClausePreservingBroadcast.program (28 : Stack) 31 [26] l)
  | .append l => BitMachineStackEmbedding.stmt appendSlot Label.append
      id id (some .done) (CurrentAdditive.CodeDAppendAtEnd15.program l)
  | .done => .halt

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c c' : Config} {n : Nat} (h : run n c = c') (u : Nat) :
    run (n + u) c = run u c' := by
  rw [Nat.add_comm, run, Function.iterate_add_apply]
  exact congrArg (run u) h

def afterBody (body : List Bool) (S : Stack → List Bool) :
    Stack → List Bool :=
  SourceClausePreservingBroadcast.result (23 : Stack) 31 [27] body S

def afterPayload (body payload : List Bool) (S : Stack → List Bool) :
    Stack → List Bool :=
  SourceClausePreservingBroadcast.result (28 : Stack) 31 [26]
    payload (afterBody body S)

theorem copy_body (body : List Bool) (S : Stack → List Bool)
    (hbody : S 23 = body) (htemp : S 31 = []) :
    ∃ t ≤ 2 * body.length + 3,
      run t ⟨some (.copyBody .scan), ((), none), S⟩ =
        ⟨some (.copyPayload .scan), ((), none), afterBody body S⟩ := by
  have hcore := SourceClausePreservingBroadcast.run_halt
    (23 : Stack) 31 [27] (by decide) (by simp) (by simp)
    (by simp) body S hbody htemp
  obtain ⟨u, hu, hr⟩ := BitMachineInline.outputs
    Label.copyBody id id (by intro v; rfl)
    (some (.copyPayload .scan))
    (SourceClausePreservingBroadcast.program (23 : Stack) 31 [27])
    program (by intro l; rfl)
    (⟨some .scan, ((), none), S⟩ :
      TM2.Cfg (fun _ : Stack => Bool)
        SourceClausePreservingBroadcast.Label Control)
    (2 * body.length + 3) (by rw [hcore])
  refine ⟨u, hu, ?_⟩
  change run u _ = _ at hr
  rw [hcore] at hr
  simpa [afterBody, BitMachineInline.cfg] using hr

theorem copy_body_direct (body : List Bool) (S : Stack → List Bool)
    (hbody : S 23 = body) (htemp : S 31 = []) :
    ∃ t ≤ 2*body.length+3,
      run t ⟨some (.copyBodyDirect .scan),((),none),S⟩ =
        ⟨some (.append .saveScan),((),none),afterBody body S⟩ := by
  have hcore := SourceClausePreservingBroadcast.run_halt
    (23 : Stack) 31 [27] (by decide) (by simp) (by simp)
    (by simp) body S hbody htemp
  obtain ⟨u,hu,hr⟩ := BitMachineInline.outputs
    Label.copyBodyDirect id id (by intro v; rfl)
    (some (.append .saveScan))
    (SourceClausePreservingBroadcast.program (23 : Stack) 31 [27])
    program (by intro l; rfl)
    (⟨some .scan,((),none),S⟩ :
      TM2.Cfg (fun _ : Stack => Bool)
        SourceClausePreservingBroadcast.Label Control)
    (2*body.length+3) (by rw [hcore])
  refine ⟨u,hu,?_⟩
  change run u _ = _ at hr
  rw [hcore] at hr
  simpa [afterBody, BitMachineInline.cfg] using hr

theorem copy_payload (body payload : List Bool)
    (S : Stack → List Bool) (hpay : S 28 = payload) :
    ∃ t ≤ 2 * payload.length + 3,
      run t ⟨some (.copyPayload .scan), ((), none), afterBody body S⟩ =
        ⟨some (.append .saveScan), ((), none),
          afterPayload body payload S⟩ := by
  have hpay' : (afterBody body S) 28 = payload := by
    unfold afterBody
    rw [SourceClausePreservingBroadcast.other_preserved
      (23 : Stack) 31 [27] body S 28
      (by decide) (by decide) (by simp)]
    exact hpay
  have htemp' : (afterBody body S) 31 = [] :=
    SourceClausePreservingBroadcast.temp_empty _ _ _ _ _
  have hcore := SourceClausePreservingBroadcast.run_halt
    (28 : Stack) 31 [26] (by decide) (by simp) (by simp)
    (by simp) payload (afterBody body S) hpay' htemp'
  obtain ⟨u, hu, hr⟩ := BitMachineInline.outputs
    Label.copyPayload id id (by intro v; rfl)
    (some (.append .saveScan))
    (SourceClausePreservingBroadcast.program (28 : Stack) 31 [26])
    program (by intro l; rfl)
    (⟨some .scan, ((), none), afterBody body S⟩ :
      TM2.Cfg (fun _ : Stack => Bool)
        SourceClausePreservingBroadcast.Label Control)
    (2 * payload.length + 3) (by rw [hcore])
  refine ⟨u, hu, ?_⟩
  change run u _ = _ at hr
  rw [hcore] at hr
  simpa [afterPayload, BitMachineInline.cfg] using hr

def localBank (S : Stack → List Bool) :
    CurrentAdditive.CodeDAppendAtEnd15.Stack → List Bool :=
  fun j => S (appendSlot j)

noncomputable def appendFrame (S : Stack → List Bool)
    (c : CurrentAdditive.CodeDAppendAtEnd15.Config) : Config :=
  BitMachineStackEmbedding.cfg appendSlot S Label.append id
    (some .done) c

theorem appendFrame_start (S : Stack → List Bool) :
    appendFrame S
      ⟨some .saveScan, ((), none), localBank S⟩ =
      ⟨some (.append .saveScan), ((), none), S⟩ := by
  unfold appendFrame
  simp only [BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg]
  congr 1
  exact BitMachineStackEmbedding.bank_restrict appendSlot S

theorem local_initial_eq (S : Stack → List Bool)
    (body payload : List Bool)
    (h27 : S 27 = body) (h26 : S 26 = payload) :
    CurrentAdditive.CodeDAppendAtEnd15.initialBank
      (localBank S) body payload = localBank S := by
  funext j
  fin_cases j <;>
    simp [CurrentAdditive.CodeDAppendAtEnd15.initialBank,
      localBank, appendSlot, h27, h26]

theorem physical_append_stage (body payload : List Bool)
    (S : Stack → List Bool)
    (h27 : S 27 = body) (h26 : S 26 = payload)
    (h24 : S 24 = []) (h31 : S 31 = []) :
    ∃ t ≤ 4 * body.length + 2 * payload.length + 7,
      (run t ⟨some (.append .saveScan), ((), none), S⟩).l =
        some .done ∧
      (run t ⟨some (.append .saveScan), ((), none), S⟩).stk 27 =
        body ++ payload := by
  let B := localBank S
  have h11 : B 11 = [] := by simpa [B, localBank, appendSlot] using h24
  have h14 : B 14 = [] := by simpa [B, localBank, appendSlot] using h31
  have hinit := local_initial_eq S body payload h27 h26
  have hcore := CurrentAdditive.CodeDAppendAtEnd15.append_run
    B body payload h11 h14
  rw [hinit] at hcore
  let T := Function.update
    (Function.update (Function.update B 9 []) 5 []) 9
    (body ++ payload)
  have hcore' : CurrentAdditive.CodeDAppendAtEnd15.run
      (4 * body.length + 2 * payload.length + 6)
      ⟨some .saveScan, ((), none), B⟩ =
      ⟨some .done, ((), none), T⟩ := hcore
  have hhalt : CurrentAdditive.CodeDAppendAtEnd15.run
      (4 * body.length + 2 * payload.length + 7)
      ⟨some .saveScan, ((), none), B⟩ =
      ⟨none, ((), none), T⟩ := by
    rw [show 4 * body.length + 2 * payload.length + 7 =
      (4 * body.length + 2 * payload.length + 6) + 1 by omega]
    rw [CurrentAdditive.CodeDAppendAtEnd15.run]
    rw [Nat.add_comm, Function.iterate_add_apply]
    change CurrentAdditive.CodeDAppendAtEnd15.run 1
      (CurrentAdditive.CodeDAppendAtEnd15.run
        (4 * body.length + 2 * payload.length + 6)
        ⟨some .saveScan, ((), none), B⟩) = _
    rw [hcore']
    rfl
  have hh : (CurrentAdditive.CodeDAppendAtEnd15.run
      (4 * body.length + 2 * payload.length + 7)
      ⟨some .saveScan, ((), none), B⟩).l = none := by
    rw [hhalt]
  obtain ⟨u, hu, hr⟩ := BitMachineStackEmbedding.outputs
    appendSlot S Label.append id id (by intro v; rfl)
    (some .done) CurrentAdditive.CodeDAppendAtEnd15.program
    program (by intro l; rfl)
    (⟨some .saveScan, ((), none), B⟩ :
      CurrentAdditive.CodeDAppendAtEnd15.Config)
    (4 * body.length + 2 * payload.length + 7) hh
  have hstart : run u ⟨some (.append .saveScan), ((), none), S⟩ =
      appendFrame S ⟨none, ((), none), T⟩ := by
    change run u (appendFrame S _) =
      appendFrame S (CurrentAdditive.CodeDAppendAtEnd15.run _ _) at hr
    rw [hhalt] at hr
    simpa only [B, appendFrame_start] using hr
  refine ⟨u, hu, ?_, ?_⟩
  · rw [hstart]
    rfl
  · rw [hstart]
    change (appendFrame S ⟨none, ((), none), T⟩).stk
      (appendSlot (9 : CurrentAdditive.CodeDAppendAtEnd15.Stack)) = _
    simp only [appendFrame, BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
      BitMachineStackEmbedding.bank_at]
    simp [T]

theorem fields_append_one (xs : List (List Bool)) (p : List Bool) :
    SourceListEncoding.fields (xs ++ [p]) =
      SourceListEncoding.fields xs ++ natField p.length ++ p := by
  induction xs with
  | nil => simp [SourceListEncoding.fields]
  | cons x xs ih =>
      simp only [List.cons_append, SourceListEncoding.fields]
      rw [ih]
      simp [List.append_assoc]

theorem semantic_append {m k : Nat}
    (ps : List (Fin m × Fin k)) (p : Fin m × Fin k) :
    SourceListEncoding.fields (ps.map CurrentAdditive.GaussControlTrace.pivotPacket) ++
      CurrentAdditive.GaussPivotFieldsAppend.payload p =
    SourceListEncoding.fields
      ((ps ++ [p]).map CurrentAdditive.GaussControlTrace.pivotPacket) := by
  simp only [List.map_append, List.map_singleton]
  rw [fields_append_one]
  simp [CurrentAdditive.GaussPivotFieldsAppend.payload, List.append_assoc]

theorem physical_extend (body payload : List Bool)
    (S : Stack → List Bool)
    (h23 : S 23 = body) (h26 : S 26 = payload)
    (h27 : S 27 = []) (h24 : S 24 = []) (h31 : S 31 = []) :
    ∃ t ≤ (2*body.length+3) +
        (4*body.length+2*payload.length+7),
      (run t ⟨some (.copyBodyDirect .scan),((),none),S⟩).l =
        some .done ∧
      (run t ⟨some (.copyBodyDirect .scan),((),none),S⟩).stk 27 =
        body++payload := by
  let S1 := afterBody body S
  have hS127 : S1 27 = body := by
    have h := SourceClausePreservingBroadcast.target_written
      (23 : Stack) 31 [27] (by simp) (by simp) (by decide)
      body S 27 (by simp)
    simpa [S1,afterBody,h27] using h
  have hS126 : S1 26 = payload := by
    have h := SourceClausePreservingBroadcast.other_preserved
      (23 : Stack) 31 [27] body S 26
      (by decide) (by decide) (by simp)
    simpa [S1,afterBody] using h.trans h26
  have hS124 : S1 24 = [] := by
    have h := SourceClausePreservingBroadcast.other_preserved
      (23 : Stack) 31 [27] body S 24
      (by decide) (by decide) (by simp)
    simpa [S1,afterBody] using h.trans h24
  have hS131 : S1 31 = [] :=
    SourceClausePreservingBroadcast.temp_empty _ _ _ _ _
  obtain ⟨a,ha,hcopy⟩ := copy_body_direct body S h23 h31
  obtain ⟨b,hb,hlabel,hout⟩ :=
    physical_append_stage body payload S1 hS127 hS126 hS124 hS131
  refine ⟨a+b,by omega,?_,?_⟩
  · rw [run_add hcopy b]
    exact hlabel
  · rw [run_add hcopy b]
    exact hout

#print axioms copy_body
#print axioms copy_payload
#print axioms physical_append_stage
#print axioms semantic_append
#print axioms physical_extend

end CurrentAdditive.GaussPivotAppend32
