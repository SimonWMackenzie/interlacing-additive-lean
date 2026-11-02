import CurrentAdditive.GaussWorkerReset32

/-!
Physical final join of the new V2 pivot-list count header and the extended
framed-pair body. Bank 30 holds the canonical count header, bank 27 the body,
and bank 7 is the prepared pivot-list field. The program first clears the old
contents of bank 7, copies the header there, then invokes the fixed Fin15
append controller to concatenate the body. No packet bytes are preloaded.
-/

namespace CurrentAdditive.GaussPivotJoin32

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open Turing BitMachineEncoding

abbrev Stack := Fin 32
abbrev Control := Unit × Option Bool

inductive Label where
  | clear7
  | copy (l : SourceClausePreservingBroadcast.Label)
  | append (l : CurrentAdditive.CodeDAppendAtEnd15.Label)
  | done
  deriving DecidableEq, Fintype

abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def appendSlot : CurrentAdditive.CodeDAppendAtEnd15.Stack ↪ Stack where
  toFun j := ![0,1,2,3,8,27,9,10,11,7,12,24,13,14,31] j
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .clear7 => BitMachineClearBank.clearStep (7 : Stack)
      .clear7 (.copy .scan)
  | .copy l => BitMachineInline.stmt Label.copy id id
      (some (.append .saveScan))
      (SourceClausePreservingBroadcast.program (30 : Stack) 31 [7] l)
  | .append l => BitMachineStackEmbedding.stmt appendSlot Label.append
      id id (some .done) (CurrentAdditive.CodeDAppendAtEnd15.program l)
  | .done => .halt

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c c' : Config} {n : Nat} (h : run n c = c') (u : Nat) :
    run (n+u) c = run u c' := by
  rw [Nat.add_comm, run, Function.iterate_add_apply]
  exact congrArg (run u) h

def afterClear (S : Stack → List Bool) : Stack → List Bool :=
  Function.update S 7 []

theorem physical_clear7 (S : Stack → List Bool) :
    run ((S 7).length+1) ⟨some .clear7,((),none),S⟩ =
      ⟨some (.copy .scan),((),none),afterClear S⟩ := by
  have h := BitMachineClearBank.clear_one_run program (7 : Stack)
    .clear7 (.copy .scan) rfl () S
  simpa [run,afterClear] using h

def afterCopy (header : List Bool) (S : Stack → List Bool) :
    Stack → List Bool :=
  SourceClausePreservingBroadcast.result (30 : Stack) 31 [7] header S

theorem physical_copy (header : List Bool) (S : Stack → List Bool)
    (hheader : S 30 = header) (h31 : S 31 = []) :
    ∃ t ≤ 2*header.length+3,
      run t ⟨some (.copy .scan),((),none),S⟩ =
        ⟨some (.append .saveScan),((),none),afterCopy header S⟩ := by
  have hcore := SourceClausePreservingBroadcast.run_halt
    (30 : Stack) 31 [7] (by decide) (by simp)
    (by simp) (by simp) header S hheader h31
  obtain ⟨u,hu,hr⟩ := BitMachineInline.outputs
    Label.copy id id (by intro v; rfl)
    (some (.append .saveScan))
    (SourceClausePreservingBroadcast.program (30 : Stack) 31 [7])
    program (by intro l; rfl)
    (⟨some .scan,((),none),S⟩ :
      TM2.Cfg (fun _ : Stack => Bool)
        SourceClausePreservingBroadcast.Label Control)
    (2*header.length+3) (by rw [hcore])
  refine ⟨u,hu,?_⟩
  change run u _ = _ at hr
  rw [hcore] at hr
  simpa [afterCopy, BitMachineInline.cfg] using hr

def localBank (S : Stack → List Bool) :
    CurrentAdditive.CodeDAppendAtEnd15.Stack → List Bool :=
  fun j => S (appendSlot j)

noncomputable def appendFrame (S : Stack → List Bool)
    (c : CurrentAdditive.CodeDAppendAtEnd15.Config) : Config :=
  BitMachineStackEmbedding.cfg appendSlot S Label.append id
    (some .done) c

theorem appendFrame_start (S : Stack → List Bool) :
    appendFrame S ⟨some .saveScan,((),none),localBank S⟩ =
      ⟨some (.append .saveScan),((),none),S⟩ := by
  unfold appendFrame
  simp only [BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg]
  congr 1
  exact BitMachineStackEmbedding.bank_restrict appendSlot S

theorem local_initial_eq (S : Stack → List Bool)
    (header body : List Bool)
    (h7 : S 7 = header) (h27 : S 27 = body) :
    CurrentAdditive.CodeDAppendAtEnd15.initialBank
      (localBank S) header body = localBank S := by
  funext j
  fin_cases j <;>
    simp [CurrentAdditive.CodeDAppendAtEnd15.initialBank,
      localBank, appendSlot, h7, h27]

theorem physical_append (header body : List Bool)
    (S : Stack → List Bool)
    (h7 : S 7 = header) (h27 : S 27 = body)
    (h24 : S 24 = []) (h31 : S 31 = []) :
    ∃ t ≤ 4*header.length+2*body.length+7,
      (run t ⟨some (.append .saveScan),((),none),S⟩).l =
        some .done ∧
      (run t ⟨some (.append .saveScan),((),none),S⟩).stk 7 =
        header++body ∧
      ∀ j : Fin 3,
        (run t ⟨some (.append .saveScan),((),none),S⟩).stk
          (⟨j.val+4, by omega⟩ : Stack) =
        S (⟨j.val+4, by omega⟩ : Stack) := by
  let B := localBank S
  have h11 : B 11 = [] := by simpa [B,localBank,appendSlot] using h24
  have h14 : B 14 = [] := by simpa [B,localBank,appendSlot] using h31
  have hinit := local_initial_eq S header body h7 h27
  have hcore := CurrentAdditive.CodeDAppendAtEnd15.append_run
    B header body h11 h14
  rw [hinit] at hcore
  let T := Function.update
    (Function.update (Function.update B 9 []) 5 []) 9
      (header++body)
  have hcore' : CurrentAdditive.CodeDAppendAtEnd15.run
      (4*header.length+2*body.length+6)
      ⟨some .saveScan,((),none),B⟩ =
      ⟨some .done,((),none),T⟩ := hcore
  have hhalt : CurrentAdditive.CodeDAppendAtEnd15.run
      (4*header.length+2*body.length+7)
      ⟨some .saveScan,((),none),B⟩ =
      ⟨none,((),none),T⟩ := by
    rw [show 4*header.length+2*body.length+7 =
      (4*header.length+2*body.length+6)+1 by omega]
    rw [CurrentAdditive.CodeDAppendAtEnd15.run]
    rw [Nat.add_comm, Function.iterate_add_apply]
    change CurrentAdditive.CodeDAppendAtEnd15.run 1
      (CurrentAdditive.CodeDAppendAtEnd15.run
        (4*header.length+2*body.length+6)
        ⟨some .saveScan,((),none),B⟩) = _
    rw [hcore']
    rfl
  have hh : (CurrentAdditive.CodeDAppendAtEnd15.run
      (4*header.length+2*body.length+7)
      ⟨some .saveScan,((),none),B⟩).l = none := by
    rw [hhalt]
  obtain ⟨u,hu,hr⟩ := BitMachineStackEmbedding.outputs
    appendSlot S Label.append id id (by intro v; rfl)
    (some .done) CurrentAdditive.CodeDAppendAtEnd15.program
    program (by intro l; rfl)
    (⟨some .saveScan,((),none),B⟩ :
      CurrentAdditive.CodeDAppendAtEnd15.Config)
    (4*header.length+2*body.length+7) hh
  have hstart : run u ⟨some (.append .saveScan),((),none),S⟩ =
      appendFrame S ⟨none,((),none),T⟩ := by
    change run u (appendFrame S _) =
      appendFrame S (CurrentAdditive.CodeDAppendAtEnd15.run _ _) at hr
    rw [hhalt] at hr
    simpa only [B,appendFrame_start] using hr
  refine ⟨u,hu,?_,?_,?_⟩
  · rw [hstart]
    rfl
  · rw [hstart]
    change (appendFrame S ⟨none,((),none),T⟩).stk
      (appendSlot (9 : CurrentAdditive.CodeDAppendAtEnd15.Stack)) = _
    simp only [appendFrame, BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
      BitMachineStackEmbedding.bank_at]
    simp [T]
  · intro j
    rw [hstart]
    let k : Stack := ⟨j.val+4, by omega⟩
    have hk : ¬ ∃ q, appendSlot q = k := by
      rintro ⟨q,hq⟩
      fin_cases j <;> fin_cases q <;> simp_all [k,appendSlot]
    change (BitMachineStackEmbedding.bank appendSlot S T) k = S k
    exact BitMachineStackEmbedding.bank_outside appendSlot S T k hk

theorem physical_join (header body : List Bool)
    (S : Stack → List Bool)
    (h30 : S 30 = header) (h27 : S 27 = body)
    (h24 : S 24 = []) (h31 : S 31 = []) :
    ∃ t ≤ (S 7).length+1 + (2*header.length+3) +
        (4*header.length+2*body.length+7),
      (run t ⟨some .clear7,((),none),S⟩).l = some .done ∧
      (run t ⟨some .clear7,((),none),S⟩).stk 7 =
        header++body ∧
      ∀ j : Fin 3,
        (run t ⟨some .clear7,((),none),S⟩).stk
          (⟨j.val+4, by omega⟩ : Stack) =
        S (⟨j.val+4, by omega⟩ : Stack) := by
  let S1 := afterClear S
  have hS130 : S1 30 = header := by simpa [S1,afterClear] using h30
  have hS131 : S1 31 = [] := by simpa [S1,afterClear] using h31
  obtain ⟨b,hb,hcopy⟩ := physical_copy header S1 hS130 hS131
  let S2 := afterCopy header S1
  have hS27 : S2 7 = header := by
    have h := SourceClausePreservingBroadcast.target_written
      (30 : Stack) 31 [7] (by simp) (by simp) (by decide)
      header S1 7 (by simp)
    simpa [S2,afterCopy,S1,afterClear] using h
  have hS227 : S2 27 = body := by
    have h := SourceClausePreservingBroadcast.other_preserved
      (30 : Stack) 31 [7] header S1 27
      (by decide) (by decide) (by simp)
    simpa [S2,afterCopy,S1,afterClear] using h.trans h27
  have hS224 : S2 24 = [] := by
    have h := SourceClausePreservingBroadcast.other_preserved
      (30 : Stack) 31 [7] header S1 24
      (by decide) (by decide) (by simp)
    simpa [S2,afterCopy,S1,afterClear] using h.trans h24
  have hS231 : S2 31 = [] :=
    SourceClausePreservingBroadcast.temp_empty _ _ _ _ _
  have hS2pres : ∀ j : Fin 3,
      S2 (⟨j.val+4, by omega⟩ : Stack) =
        S (⟨j.val+4, by omega⟩ : Stack) := by
    intro j
    let k : Stack := ⟨j.val+4, by omega⟩
    have hk30 : k ≠ 30 := by
      intro he
      have hv := congrArg Fin.val he
      have hj := j.isLt
      change j.val+4 = 30 at hv
      omega
    have hk31 : k ≠ 31 := by
      intro he
      have hv := congrArg Fin.val he
      have hj := j.isLt
      change j.val+4 = 31 at hv
      omega
    have hk7 : k ≠ 7 := by
      intro he
      have hv := congrArg Fin.val he
      have hj := j.isLt
      change j.val+4 = 7 at hv
      omega
    have h := SourceClausePreservingBroadcast.other_preserved
      (30 : Stack) 31 [7] header S1 k
      hk30 hk31 (by simpa using hk7)
    simpa [k,S2,afterCopy,S1,afterClear,hk7] using h
  obtain ⟨c,hc,hlabel,hout,hpres⟩ :=
    physical_append header body S2 hS27 hS227 hS224 hS231
  have hclear := physical_clear7 S
  refine ⟨((S 7).length+1)+b+c,by omega,?_,?_,?_⟩
  · rw [run_add ((run_add hclear b).trans hcopy) c]
    exact hlabel
  · rw [run_add ((run_add hclear b).trans hcopy) c]
    exact hout
  · intro j
    rw [run_add ((run_add hclear b).trans hcopy) c]
    exact (hpres j).trans (hS2pres j)

theorem packet_parts {m k : Nat} (ps : List (Fin m × Fin k)) :
    natField ps.length ++
      SourceListEncoding.fields
        (ps.map CurrentAdditive.GaussControlTrace.pivotPacket) =
      CurrentAdditive.GaussControlTrace.pivotsPacket ps := by
  simp [CurrentAdditive.GaussControlTrace.pivotsPacket,
    SourceListEncoding.encode]

theorem physical_join_pivots {m k : Nat}
    (ps : List (Fin m × Fin k)) (S : Stack → List Bool)
    (h30 : S 30 = natField ps.length)
    (h27 : S 27 = SourceListEncoding.fields
      (ps.map CurrentAdditive.GaussControlTrace.pivotPacket))
    (h24 : S 24 = []) (h31 : S 31 = []) :
    ∃ t ≤ (S 7).length+1 + (2*(natField ps.length).length+3) +
        (4*(natField ps.length).length+2*
          (SourceListEncoding.fields
            (ps.map CurrentAdditive.GaussControlTrace.pivotPacket)).length+7),
      (run t ⟨some .clear7,((),none),S⟩).l = some .done ∧
      (run t ⟨some .clear7,((),none),S⟩).stk 7 =
        CurrentAdditive.GaussControlTrace.pivotsPacket ps ∧
      ∀ j : Fin 3,
        (run t ⟨some .clear7,((),none),S⟩).stk
          (⟨j.val+4, by omega⟩ : Stack) =
        S (⟨j.val+4, by omega⟩ : Stack) := by
  obtain ⟨t,ht,hl,ho,hpres⟩ := physical_join
    (natField ps.length)
    (SourceListEncoding.fields
      (ps.map CurrentAdditive.GaussControlTrace.pivotPacket))
    S h30 h27 h24 h31
  refine ⟨t,ht,hl,ho.trans (packet_parts ps),hpres⟩

#print axioms physical_clear7
#print axioms physical_copy
#print axioms physical_append
#print axioms physical_join
#print axioms physical_join_pivots

end CurrentAdditive.GaussPivotJoin32
