import EthInapproximability.CurrentPaper.BitMachineStackEmbedding
import EthInapproximability.CurrentPaper.BitMachineCopy
import EthInapproximability.CurrentPaper.ETHParameterScaleMachineInput

/-!
Physical preparation of the three nonlogarithmic scale-bound candidates and
the unary-two fold seed. The raw words remain in the bank. The remaining
three logarithmic candidates are a separate physical controller.
-/

namespace EthInapproximability.CurrentPaper.ScaleRawTailScratch

noncomputable section

open Turing TM2.Stmt BitMachineEncoding BitMachineStackEmbedding

variable {Private : Type*} [DecidableEq Private]

abbrev Stack (Private : Type*) := Fin 6 ⊕ (Fin 13 ⊕ Private)

def raw (j : Fin 6) : Stack Private := .inl j
def candidate (j : Fin 13) : Stack Private := .inr (.inl j)

-- `ETHParameterScaleMachineInput.words` orders the raw words as
-- sourceConstant, nextDepth, cost, rows, columns, edges.
def rawTail (j : Fin 3) : Fin 6 := ⟨2-j.val,by omega⟩
def candidateTail (j : Fin 3) : Fin 13 := ⟨j.val+3,by omega⟩
def scratch : Stack Private := candidate 7
def seed : Stack Private := candidate 6

def copyEmbed (j : Fin 3) : Fin 3 ↪ Stack Private where
  toFun := ![raw (rawTail j), candidate (candidateTail j), scratch]
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> try rfl
    all_goals simp [raw,rawTail,candidate,candidateTail,scratch,
      Fin.ext_iff] at h <;> omega

inductive Label where
  | copy (j : Fin 3) (l : BitMachineCopy.Label)
  | seedFirst
  | seedSecond
  deriving DecidableEq, Fintype

abbrev Config (Private : Type*) := TM2.Cfg (fun _ : Stack Private => Bool) Label (Option Bool)

def afterCopy : Fin 3 → Label
  | 0 => .copy 1 .scan
  | 1 => .copy 2 .scan
  | 2 => .seedFirst

def program : Label → TM2.Stmt (fun _ : Stack Private => Bool) Label (Option Bool)
  | .copy j l => stmt (copyEmbed j) (.copy j) id id (some (afterCopy j))
      (BitMachineCopy.program l)
  | .seedFirst => push seed (fun _ => true) (goto (fun _ => .seedSecond))
  | .seedSecond => push seed (fun _ => true) (load (fun _ => none) halt)

def run (t : ℕ) (c : Config Private) : Config Private :=
  ((advance (program (Private := Private)))^[t]) c

theorem copy_phase (j : Fin 3) (S : Stack Private → List Bool)
    (htarget : S (candidate (candidateTail j)) = [])
    (hscratch : S scratch = []) :
    ∃ t ≤ 2 * (S (raw (rawTail j))).length + 2,
      run t ⟨some (.copy j .scan),none,S⟩ =
        ⟨some (afterCopy j),none,
          Function.update S (candidate (candidateTail j)) (S (raw (rawTail j)))⟩ := by
  let q := S (raw (rawTail j))
  let localStart := BitMachineCopy.cfg (some .scan) none q [] []
  let localEnd := BitMachineCopy.cfg none none q q []
  have hr : BitMachineCopy.run (2*q.length+2) localStart = localEnd := by
    simpa only [List.append_nil] using BitMachineCopy.run_correct none q []
  have hh : (BitMachineCopy.run (2*q.length+2) localStart).l = none := by rw [hr]; rfl
  obtain ⟨t,ht,he⟩ := BitMachineStackEmbedding.outputs (copyEmbed j) S
    (.copy j) id id (by intro x; rfl) (some (afterCopy j))
    BitMachineCopy.program (program (Private := Private)) (by intro l; rfl)
    localStart (2*q.length+2) hh
  change run t (BitMachineStackEmbedding.cfg _ _ _ _ _ localStart) =
    BitMachineStackEmbedding.cfg _ _ _ _ _ (BitMachineCopy.run _ localStart) at he
  rw [hr] at he
  have hbank : bank (copyEmbed j) S localStart.stk = S := by
    apply bank_eq_self
    intro k
    fin_cases k <;> simp [localStart,BitMachineCopy.cfg,
      BitMachineCopy.stackContents,copyEmbed,q,htarget,hscratch]
  have hlocal : localEnd.stk = Function.update localStart.stk 1 q := by
    funext k
    fin_cases k <;> simp [localStart,localEnd,BitMachineCopy.cfg,
      BitMachineCopy.stackContents]
  have hbank' : bank (copyEmbed j) S localEnd.stk =
      Function.update S (candidate (candidateTail j)) q := by
    rw [hlocal,bank_update,hbank]
    rfl
  refine ⟨t,ht,?_⟩
  change run t ⟨some (.copy j .scan),none,
      bank (copyEmbed j) S localStart.stk⟩ =
    ⟨some (afterCopy j),none,bank (copyEmbed j) S localEnd.stk⟩ at he
  rw [hbank,hbank'] at he
  exact he

theorem seed_run (S : Stack Private → List Bool) :
    run 2 ⟨some .seedFirst,none,S⟩ =
      ⟨none,none,Function.update S seed (true :: true :: S seed)⟩ := by
  simp [run,Function.iterate_succ_apply,advance,program,TM2.step,TM2.stepAux]

def copiedBank (S : Stack Private → List Bool) : Stack Private → List Bool :=
  Function.update
    (Function.update
      (Function.update S (candidate 3) (S (raw 2)))
      (candidate 4) (S (raw 1)))
    (candidate 5) (S (raw 0))

def outputBank (S : Stack Private → List Bool) : Stack Private → List Bool :=
  Function.update (copiedBank S) seed [true,true]

theorem outputBank_raw (S : Stack Private → List Bool) (j : Fin 6) :
    outputBank S (raw j) = S (raw j) := by
  simp [outputBank,copiedBank,raw,candidate,seed]

theorem outputBank_private (S : Stack Private → List Bool) (p : Private) :
    outputBank S (.inr (.inr p)) = S (.inr (.inr p)) := by
  simp [outputBank,copiedBank,candidate,seed]

theorem outputBank_prefix (S : Stack Private → List Bool) (j : Fin 3) :
    outputBank S (candidate (j.castLE (by decide : 3 ≤ 13))) =
      S (candidate (j.castLE (by decide : 3 ≤ 13))) := by
  fin_cases j <;> simp [outputBank,copiedBank,candidate,seed]

theorem outputBank_suffix (S : Stack Private → List Bool) (j : Fin 13)
    (h : 7 ≤ j.val) : outputBank S (candidate j) = S (candidate j) := by
  have h3 : candidate (Private := Private) j ≠ candidate 3 := by
    intro he
    have hv : j = 3 := by simpa [candidate] using he
    have := congrArg Fin.val hv
    omega
  have h4 : candidate (Private := Private) j ≠ candidate 4 := by
    intro he
    have hv : j = 4 := by simpa [candidate] using he
    have := congrArg Fin.val hv
    omega
  have h5 : candidate (Private := Private) j ≠ candidate 5 := by
    intro he
    have hv : j = 5 := by simpa [candidate] using he
    have := congrArg Fin.val hv
    omega
  have h6 : candidate (Private := Private) j ≠ seed := by
    intro he
    have hv : j = 6 := by simpa [candidate,seed] using he
    have := congrArg Fin.val hv
    omega
  simp only [outputBank,copiedBank,Function.update_of_ne h6,
    Function.update_of_ne h5,Function.update_of_ne h4,
    Function.update_of_ne h3]

theorem outputBank_values (S : Stack Private → List Bool) :
    outputBank S (candidate 3) = S (raw 2) ∧
    outputBank S (candidate 4) = S (raw 1) ∧
    outputBank S (candidate 5) = S (raw 0) ∧
    outputBank S seed = [true,true] := by
  simp [outputBank,copiedBank,candidate,seed]

theorem outputBank_words (i : Parameters.Input) (S : Stack Private → List Bool)
    (hwords : ∀ j : Fin 6, S (raw j) =
      ETHParameterScaleMachineInput.words i j) :
    outputBank S (candidate 3) = List.replicate i.cost true ∧
    outputBank S (candidate 4) = List.replicate i.nextDepth true ∧
    outputBank S (candidate 5) = List.replicate i.sourceConstant true ∧
    outputBank S seed = [true,true] := by
  obtain ⟨h3,h4,h5,h6⟩ := outputBank_values S
  refine ⟨?_,?_,?_,h6⟩
  · simpa [ETHParameterScaleMachineInput.words] using h3.trans (hwords 2)
  · simpa [ETHParameterScaleMachineInput.words] using h4.trans (hwords 1)
  · simpa [ETHParameterScaleMachineInput.words] using h5.trans (hwords 0)

private theorem run_add {c d : Config Private} {t : ℕ}
    (h : run t c = d) (u : ℕ) : run (t+u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run,Function.iterate_add_apply] at h ⊢
  rw [h]

/-- The three raw nonlogarithmic words are copied physically and the
unary-two maximum seed is physically pushed. Candidate cells 0..2 and all
private cells are framed, as are the six raw source words. -/
theorem raw_tail_run (S : Stack Private → List Bool)
    (h3 : S (candidate 3) = [])
    (h4 : S (candidate 4) = [])
    (h5 : S (candidate 5) = [])
    (h6 : S seed = [])
    (h7 : S scratch = []) :
    ∃ t ≤ (2 * (S (raw 2)).length + 2) +
      (2 * (S (raw 1)).length + 2) +
      (2 * (S (raw 0)).length + 2) + 2,
      run t ⟨some (.copy 0 .scan),none,S⟩ =
        ⟨none,none,outputBank S⟩ := by
  let S1 := Function.update S (candidate 3) (S (raw 2))
  let S2 := Function.update S1 (candidate 4) (S (raw 1))
  let S3 := Function.update S2 (candidate 5) (S (raw 0))
  obtain ⟨t0,ht0,e0⟩ := copy_phase (Private := Private) 0 S h3 h7
  have h4' : S1 (candidate 4) = [] := by simpa [S1,candidate] using h4
  have h7' : S1 scratch = [] := by simpa [S1,candidate,scratch] using h7
  have hraw1 : S1 (raw 1) = S (raw 1) := by simp [S1,raw,candidate]
  obtain ⟨t1,ht1,e1⟩ := copy_phase (Private := Private) 1 S1 h4' h7'
  have h5' : S2 (candidate 5) = [] := by simpa [S2,S1,candidate] using h5
  have h7'' : S2 scratch = [] := by simpa [S2,S1,candidate,scratch] using h7
  have hraw0 : S2 (raw 0) = S (raw 0) := by simp [S2,S1,raw,candidate]
  obtain ⟨t2,ht2,e2⟩ := copy_phase (Private := Private) 2 S2 h5' h7''
  have e0' : run t0 ⟨some (.copy 0 .scan),none,S⟩ =
      ⟨some (.copy 1 .scan),none,S1⟩ := by simpa [afterCopy,S1] using e0
  have e1' : run t1 ⟨some (.copy 1 .scan),none,S1⟩ =
      ⟨some (.copy 2 .scan),none,S2⟩ := by simpa [afterCopy,S2,hraw1] using e1
  have e2' : run t2 ⟨some (.copy 2 .scan),none,S2⟩ =
      ⟨some .seedFirst,none,S3⟩ := by simpa [afterCopy,S3,hraw0] using e2
  have h01 := run_add e0' t1
  rw [e1'] at h01
  have h012 := run_add h01 t2
  rw [e2'] at h012
  have h012s := run_add h012 2
  rw [seed_run] at h012s
  refine ⟨t0+t1+t2+2,?_,?_⟩
  · change t0 ≤ 2 * (S (raw 2)).length + 2 at ht0
    change t1 ≤ 2 * (S1 (raw 1)).length + 2 at ht1
    change t2 ≤ 2 * (S2 (raw 0)).length + 2 at ht2
    rw [hraw1] at ht1
    rw [hraw0] at ht2
    omega
  · have h6' : S3 seed = [] := by simpa [S3,S2,S1,seed,candidate] using h6
    simp only [h6'] at h012s
    simpa only [outputBank,copiedBank,S3,S2,S1,Nat.add_assoc] using h012s


end
end EthInapproximability.CurrentPaper.ScaleRawTailScratch
