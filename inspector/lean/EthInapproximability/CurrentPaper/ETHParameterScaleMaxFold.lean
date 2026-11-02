import EthInapproximability.CurrentPaper.ETHParameterScaleMachineInput
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-!
Physical fixed six-candidate maximum for the single-scale formula.
Source: locked v8 `F-parameter-choices.tex`, `eq:paper-parameter-scale`; six candidate
semantics are `ETHParameterScaleMachineInput.candidates`.
-/

namespace EthInapproximability.CurrentPaper.ScaleMaxFoldScratch

open Turing BitMachineEncoding BitMachineStackEmbedding
open ETHParameterScaleMachineMax ETHParameterScaleMachineInput

noncomputable section

set_option maxHeartbeats 1000000

abbrev Stack := Fin 13
abbrev Label := Fin 6
abbrev Control := ETHParameterScaleMachineMax.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def candidate (i : Parameters.Input) : Fin 6 → ℕ :=
  ![Nat.clog 2 (i.edges+2), Nat.clog 2 i.columns,
    Nat.clog 2 i.rows, i.cost, i.nextDepth, i.sourceConstant]

theorem candidate_list (i : Parameters.Input) :
    (List.ofFn (candidate i)) = candidates i := rfl

def acc (j : Fin 7) : Stack := ⟨6+j.val, by omega⟩
def cand (j : Label) : Stack := j.castLE (by decide : 6 ≤ 13)

def slots (j : Label) : Fin 3 ↪ Stack where
  toFun := ![acc ⟨j.val, by omega⟩, cand j,
    acc ⟨j.val+1, by omega⟩]
  inj' := by
    intro x y h
    fin_cases x <;> fin_cases y <;> try rfl
    all_goals
      have hv := congrArg Fin.val h
      simp [acc,cand] at hv
      try omega

def next (j : Label) : Option Label :=
  if h : j.val+1 < 6 then some ⟨j.val+1,h⟩ else none

def program (j : Label) :
    TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  stmt (slots j) (fun _ : Unit => j) id id (next j)
    (ETHParameterScaleMachineMax.consumeProgram ())

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

def inputBank (i : Parameters.Input) : Stack → List Bool :=
  ![List.replicate (candidate i 0) true,
    List.replicate (candidate i 1) true,
    List.replicate (candidate i 2) true,
    List.replicate (candidate i 3) true,
    List.replicate (candidate i 4) true,
    List.replicate (candidate i 5) true,
    List.replicate 2 true, [], [], [], [], [], []]

def finalBank (i : Parameters.Input) : Stack → List Bool :=
  ![[], [], [], [], [], [], [], [], [], [], [], [],
    List.replicate (Parameters.scaleBound i) true]

def foldVal (i : Parameters.Input) (j : Fin 7) : ℕ :=
  ((candidates i).take j.val).foldl max 2

theorem foldVal_succ (i : Parameters.Input) (j : Label) :
    foldVal i ⟨j.val+1,by omega⟩ =
      max (foldVal i ⟨j.val,by omega⟩) (candidate i j) := by
  fin_cases j <;> rfl

theorem foldVal_final (i : Parameters.Input) :
    foldVal i 6 = Parameters.scaleBound i := by
  simpa only [foldVal,candidates,List.take_length]
    using (candidate_fold_eq_scaleBound i)

def stateBank (i : Parameters.Input) (j : Fin 7) :
    Stack → List Bool := fun k =>
  if h : k.val < 6 then
    if k.val < j.val then [] else
      List.replicate (candidate i ⟨k.val,h⟩) true
  else if k.val = 6+j.val then
    List.replicate (foldVal i j) true
  else []

theorem stateBank_initial (i : Parameters.Input) :
    stateBank i 0 = inputBank i := by
  funext k
  fin_cases k <;> rfl

theorem stateBank_final (i : Parameters.Input) :
    stateBank i 6 = finalBank i := by
  funext k
  fin_cases k <;> simp [stateBank,finalBank,foldVal_final]

theorem stateBank_source (i : Parameters.Input) (j : Label) :
    stateBank i ⟨j.val,by omega⟩ (slots j 0) =
      List.replicate (foldVal i ⟨j.val,by omega⟩) true := by
  simp [stateBank,slots,acc]

theorem stateBank_candidate (i : Parameters.Input) (j : Label) :
    stateBank i ⟨j.val,by omega⟩ (slots j 1) =
      List.replicate (candidate i j) true := by
  simp [stateBank,slots,cand]

theorem stateBank_target (i : Parameters.Input) (j : Label) :
    stateBank i ⟨j.val,by omega⟩ (slots j 2) = [] := by
  simp [stateBank,slots,acc]

def phaseBank (j : Label) (S : Stack → List Bool) (a b : List Bool) :
    Stack → List Bool :=
  Function.update
    (Function.update
      (Function.update S (slots j 0) []) (slots j 1) [])
    (slots j 2) (List.replicate (max a.length b.length) true)

theorem phaseBank_stateBank (i : Parameters.Input) (j : Label) :
    phaseBank j (stateBank i ⟨j.val,by omega⟩)
      (List.replicate (foldVal i ⟨j.val,by omega⟩) true)
      (List.replicate (candidate i j) true) =
    stateBank i ⟨j.val+1,by omega⟩ := by
  funext k
  fin_cases j <;> fin_cases k <;>
    simp [phaseBank,stateBank,slots,acc,cand] <;> rfl

theorem phase_run (j : Label) (S : Stack → List Bool)
    (v : Control) (a b : List Bool)
    (ha : S (slots j 0) = a) (hb : S (slots j 1) = b)
    (hout : S (slots j 2) = []) :
    ∃ t ≤ max a.length b.length+1,
      run t ⟨some j,v,S⟩ =
        ⟨next j,(none,none),phaseBank j S a b⟩ := by
  let c := ETHParameterScaleMachineMax.consumeCfg (some ()) v a b []
  have hloc : ∀ k : Fin 3, c.stk k = S (slots j k) := by
    intro k
    fin_cases k <;>
      simp [c,ETHParameterScaleMachineMax.consumeCfg,ha,hb,hout]
  have hstart :
      BitMachineStackEmbedding.cfg (slots j) S (fun _ : Unit => j)
        id (next j) c = (⟨some j,v,S⟩ : Config) := by
    simp only [BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg,BitMachineInline.cfg,c,
      ETHParameterScaleMachineMax.consumeCfg]
    congr 1
    exact bank_eq_self (slots j) S _ hloc
  have hmax := ETHParameterScaleMachineMax.consume_run a b [] v
  have hhalt :
      (((advance ETHParameterScaleMachineMax.consumeProgram)^[max a.length b.length+1]) c).l =
        none := by
    change (ETHParameterScaleMachineMax.consumeRun
      (max a.length b.length+1) c).l = none
    rw [hmax]
    rfl
  obtain ⟨t,ht,hrun⟩ := BitMachineStackEmbedding.outputs
    (slots j) S (fun _ : Unit => j) id id (by intro x; rfl)
    (next j) ETHParameterScaleMachineMax.consumeProgram program
    (by intro l; cases l; rfl) c (max a.length b.length+1) hhalt
  rw [hstart] at hrun
  change run t ⟨some j,v,S⟩ = _ at hrun
  have hmax' :
      (((advance ETHParameterScaleMachineMax.consumeProgram)^[max a.length b.length+1]) c) =
        ETHParameterScaleMachineMax.consumeCfg none (none,none) [] []
          (List.replicate (max a.length b.length) true) := by
    simpa only [c,ETHParameterScaleMachineMax.consumeRun,List.append_nil]
      using hmax
  rw [hmax'] at hrun
  refine ⟨t,ht,?_⟩
  calc
    _ = BitMachineStackEmbedding.cfg (slots j) S (fun _ : Unit => j)
      id (next j)
      (ETHParameterScaleMachineMax.consumeCfg none (none,none) [] []
        (List.replicate (max a.length b.length) true)) := hrun
    _ = ⟨next j,(none,none),phaseBank j S a b⟩ := by
      simp only [BitMachineStackEmbedding.cfg,
        BitMachineStackEmbedding.stackCfg,BitMachineInline.cfg,
        ETHParameterScaleMachineMax.consumeCfg]
      congr 1
      have hlocal :
          (![[],[],List.replicate (max a.length b.length) true] :
            Fin 3 → List Bool) =
          Function.update
            (Function.update (Function.update
              (fun k : Fin 3 => S (slots j k)) 0 []) 1 []) 2
            (List.replicate (max a.length b.length) true) := by
        funext k
        fin_cases k <;> simp
      rw [hlocal,bank_update,bank_update,bank_update,bank_restrict]
      rfl

def phaseCost (i : Parameters.Input) (j : Label) : ℕ :=
  foldVal i ⟨j.val+1,by omega⟩ + 1

theorem phase_state_run (i : Parameters.Input) (j : Label) :
    ∃ t ≤ phaseCost i j,
      run t ⟨some j,(none,none),stateBank i ⟨j.val,by omega⟩⟩ =
        ⟨next j,(none,none),stateBank i ⟨j.val+1,by omega⟩⟩ := by
  let a := List.replicate (foldVal i ⟨j.val,by omega⟩) true
  let b := List.replicate (candidate i j) true
  obtain ⟨t,ht,hr⟩ := phase_run j
    (stateBank i ⟨j.val,by omega⟩) (none,none) a b
    (stateBank_source i j) (stateBank_candidate i j)
    (stateBank_target i j)
  refine ⟨t,?_,?_⟩
  · simpa only [phaseCost,a,b,List.length_replicate,
      foldVal_succ] using ht
  · simpa only [a,b,phaseBank_stateBank] using hr

private theorem run_add {c d : Config} {t : ℕ}
    (h : run t c = d) (u : ℕ) : run (t+u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run,Function.iterate_add_apply] at h ⊢
  rw [h]

def totalCost (i : Parameters.Input) : ℕ :=
  (phaseCost i 0 + phaseCost i 1 + phaseCost i 2) +
    (phaseCost i 3 + phaseCost i 4 + phaseCost i 5)

/-- Six actual embedded maximum runs on one Fin13 bank. All candidate
cells and old accumulators are physically consumed, and no candidate value
is loaded into the finite control. -/
theorem six_phase_run (i : Parameters.Input) :
    ∃ t ≤ totalCost i,
      run t ⟨some (0 : Label),(none,none),inputBank i⟩ =
        ⟨none,(none,none),finalBank i⟩ := by
  obtain ⟨t0,h0,e0⟩ := phase_state_run i 0
  obtain ⟨t1,h1,e1⟩ := phase_state_run i 1
  obtain ⟨t2,h2,e2⟩ := phase_state_run i 2
  obtain ⟨t3,h3,e3⟩ := phase_state_run i 3
  obtain ⟨t4,h4,e4⟩ := phase_state_run i 4
  obtain ⟨t5,h5,e5⟩ := phase_state_run i 5
  have e0' : run t0 ⟨some (0 : Label),(none,none),stateBank i 0⟩ =
      ⟨some (1 : Label),(none,none),stateBank i 1⟩ := by simpa [next] using e0
  have e1' : run t1 ⟨some (1 : Label),(none,none),stateBank i 1⟩ =
      ⟨some (2 : Label),(none,none),stateBank i 2⟩ := by simpa [next] using e1
  have e2' : run t2 ⟨some (2 : Label),(none,none),stateBank i 2⟩ =
      ⟨some (3 : Label),(none,none),stateBank i 3⟩ := by simpa [next] using e2
  have e3' : run t3 ⟨some (3 : Label),(none,none),stateBank i 3⟩ =
      ⟨some (4 : Label),(none,none),stateBank i 4⟩ := by simpa [next] using e3
  have e4' : run t4 ⟨some (4 : Label),(none,none),stateBank i 4⟩ =
      ⟨some (5 : Label),(none,none),stateBank i 5⟩ := by simpa [next] using e4
  have e5' : run t5 ⟨some (5 : Label),(none,none),stateBank i 5⟩ =
      ⟨none,(none,none),stateBank i 6⟩ := by simpa [next] using e5
  have h01 := run_add e0' t1
  rw [e1'] at h01
  have h012 := run_add h01 t2
  rw [e2'] at h012
  have h0123 := run_add h012 t3
  rw [e3'] at h0123
  have h01234 := run_add h0123 t4
  rw [e4'] at h01234
  have h012345 := run_add h01234 t5
  rw [e5'] at h012345
  refine ⟨t0+t1+t2+t3+t4+t5,?_,?_⟩
  · dsimp only [totalCost]
    omega
  · simpa only [stateBank_initial,stateBank_final,
      Nat.add_assoc] using h012345


end
end EthInapproximability.CurrentPaper.ScaleMaxFoldScratch
