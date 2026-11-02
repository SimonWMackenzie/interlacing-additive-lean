import EthInapproximability.CurrentPaper.ClockInputPreparation
import EthInapproximability.CurrentPaper.BitMachineClearBank
import EthInapproximability.CurrentPaper.SlowClockPrefixLoop

/-!
# One physical step of the consecutive bounded-cutoff loop

Source: frozen v8 `05-iteration.tex`, the prefix clock. Three permanent
stacks hold the active flag, unary budget, and accepted binary counter.
Every transient cell is physically cleared before and after a call. The
active branch constructs and probes the next input; its returned bit
controls an actual successor operation or disables subsequent probes.
-/

namespace EthInapproximability.CurrentPaper.ClockStepMachine

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open Turing TM2.Stmt BitMachineEncoding BitMachineStackEmbedding
open scoped BigOperators

variable (M : BitMachine.Machine)

abbrev Stack := ClockInputPreparation.Stack M
def tempCount := Fintype.card (ClockInputPreparation.Temp M)

def tempKey (i : Fin (tempCount M)) : Stack M :=
  .inr ((Fintype.equivFin (ClockInputPreparation.Temp M)).symm i)

theorem tempKey_injective : Function.Injective (tempKey M) := by
  intro i j h
  exact (Fintype.equivFin _).symm.injective (Sum.inr_injective h)

def probeEmbed : CutoffProbeMachine.Stack M ↪ Stack M :=
  ⟨ClockInputPreparation.probeKey M, by intro i j h; cases h; rfl⟩

def incrementEmbed : Fin 2 ↪ Stack M where
  toFun i := if i = 0 then .inl 2 else ClockInputPreparation.scratchKey M
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [ClockInputPreparation.scratchKey]

inductive Label (M : BitMachine.Machine) where
  | clearBefore : Fin (tempCount M + 1) → Label M
  | active
  | prepare : ClockInputPreparation.Label → Label M
  | probeStart
  | probe : CutoffProbeMachine.Label M → Label M
  | test
  | increment : BinarySuccessorMachine.Label → Label M
  | clearAfterStart
  | clearAfter : Fin (tempCount M + 1) → Label M
  | done
  deriving DecidableEq, Fintype

inductive Tag (M : BitMachine.Machine) where
  | idle
  | prepare : ClockInputPreparation.Control → Tag M
  | probe : CutoffProbeMachine.Control M → Tag M
  | increment : Option Bool → Tag M
  deriving DecidableEq, Fintype

abbrev Control := Tag M × Option Bool

def prepControl (v : ClockInputPreparation.Control) : Control M := (.prepare v, none)
def probeControl (v : CutoffProbeMachine.Control M) : Control M := (.probe v, none)
def incrementControl (v : Option Bool) : Control M := (.increment v, none)

def readPrep : Control M → ClockInputPreparation.Control
  | (.prepare v, _) => v
  | _ => .copying none
def readProbe : Control M → CutoffProbeMachine.Control M
  | (.probe v, _) => v
  | _ => ((CutoffProbeMachine.sim M).initial, CutoffProbeMachine.testInitial)
def readIncrement : Control M → Option Bool
  | (.increment v, _) => v
  | _ => none

def program : Label M → TM2.Stmt (fun _ : Stack M => Bool) (Label M) (Control M)
  | .clearBefore i => if h : i.val < tempCount M then
      BitMachineClearBank.clearStep (tempKey M ⟨i.val,h⟩) (.clearBefore i)
        (.clearBefore ⟨i.val+1, by omega⟩)
    else BitMachineClearBank.finishStep (fun _ => .idle) .active
  | .active => peek (.inl 0) (fun v b => (v.1,b))
      (branch (fun v => v.2.getD false)
        (load (fun _ => prepControl M (.copying none))
          (goto (fun _ => .prepare (.copyStart .count))))
        halt)
  | .prepare l => BitMachineInline.stmt Label.prepare (prepControl M) (readPrep M)
      (some .probeStart) (ClockInputPreparation.program M l)
  | .probeStart => load
      (fun _ => probeControl M ((CutoffProbeMachine.sim M).initial,CutoffProbeMachine.testInitial))
      (goto (fun _ => .probe (.inl (CutoffProbeMachine.sim M).start)))
  | .probe l => stmt (probeEmbed M) Label.probe (probeControl M) (readProbe M)
      (some .test) (CutoffProbeMachine.program M l)
  | .test => peek (ClockInputPreparation.probeKey M (.inr (.inr 2)))
      (fun v b => (v.1,b))
      (branch (fun v => v.2.getD false)
        (load (fun _ => incrementControl M none) (goto (fun _ => .increment .carry)))
        (pop (.inl 0) (fun v _ => v)
          (push (.inl 0) (fun _ => false) (goto (fun _ => .clearAfterStart)))))
  | .increment l => stmt (incrementEmbed M) Label.increment (incrementControl M) (readIncrement M)
      (some .clearAfterStart) (BinarySuccessorMachine.program l)
  | .clearAfterStart => load (fun _ => (.idle,none)) (goto (fun _ => .clearAfter 0))
  | .clearAfter i => if h : i.val < tempCount M then
      BitMachineClearBank.clearStep (tempKey M ⟨i.val,h⟩) (.clearAfter i)
        (.clearAfter ⟨i.val+1, by omega⟩)
    else BitMachineClearBank.finishStep (fun _ => .idle) .done
  | .done => halt

abbrev Config := TM2.Cfg (fun _ : Stack M => Bool) (Label M) (Control M)

def run (t : ℕ) (c : Config M) := ((advance (program M))^[t]) c

theorem run_add (t u : ℕ) (c : Config M) : run M (t+u) c = run M u (run M t c) := by
  rw [Nat.add_comm]
  exact Function.iterate_add_apply _ _ _ _

theorem cleared_eq (S : Stack M → List Bool) :
    BitMachineClearBank.cleared (tempKey M) S =
      ClockInputPreparation.readyBank M (S (.inl 0)) (S (.inl 1)) (S (.inl 2)) := by
  funext i
  cases i with
  | inl i =>
      rw [BitMachineClearBank.cleared_foreign _ _ _ (by simp [tempKey])]
      fin_cases i <;> rfl
  | inr i =>
      have hi : tempKey M ((Fintype.equivFin _) i) = .inr i := by simp [tempKey]
      rw [← hi, BitMachineClearBank.cleared_bank]
      rfl

theorem clear_before (S : Stack M → List Bool) :
    run M ((∑ i, (S (tempKey M i)).length) + tempCount M + 1)
      ⟨some (.clearBefore 0), (.idle,none), S⟩ =
      ⟨some .active, (.idle,none),
        ClockInputPreparation.readyBank M (S (.inl 0)) (S (.inl 1)) (S (.inl 2))⟩ := by
  have h := BitMachineClearBank.clear_bank_run (program M) (fun _ => .idle) .active
    (tempCount M) (tempKey M) (tempKey_injective M) Label.clearBefore
    (by intro i; simp only [program, Fin.val_castSucc, i.isLt, dite_true]; rfl)
    (by simp [program]) (.idle : Tag M) S
  simpa only [run, cleared_eq] using h

theorem clear_after (S : Stack M → List Bool) :
    run M ((∑ i, (S (tempKey M i)).length) + tempCount M + 1)
      ⟨some (.clearAfter 0), (.idle,none), S⟩ =
      ⟨some .done, (.idle,none),
        ClockInputPreparation.readyBank M (S (.inl 0)) (S (.inl 1)) (S (.inl 2))⟩ := by
  have h := BitMachineClearBank.clear_bank_run (program M) (fun _ => .idle) .done
    (tempCount M) (tempKey M) (tempKey_injective M) Label.clearAfter
    (by intro i; simp only [program, Fin.val_castSucc, i.isLt, dite_true]; rfl)
    (by simp [program]) (.idle : Tag M) S
  simpa only [run, cleared_eq] using h

theorem prepare_phase (active budget count : List Bool) :
    ∃ t ≤ 20 * (count.length + budget.length + 2), ∃ c : ClockInputPreparation.Next.Config,
      run M t ⟨some (.prepare (.copyStart .count)), prepControl M (.copying none),
        ClockInputPreparation.readyBank M active budget count⟩ =
        ⟨some .probeStart, prepControl M (.packing none),
          ClockInputPreparation.preparedBank M active budget count c⟩ := by
  obtain ⟨t,ht,c,hc,_⟩ := ClockInputPreparation.preparation_run M active budget count
  let initial : ClockInputPreparation.Config M :=
    ⟨some (.copyStart .count), .copying none, ClockInputPreparation.readyBank M active budget count⟩
  have hh : (ClockInputPreparation.run M t initial).l = none := by rw [hc]
  obtain ⟨u,hu,he⟩ := BitMachineInline.outputs Label.prepare (prepControl M) (readPrep M)
    (fun _ => rfl) (some .probeStart) (ClockInputPreparation.program M) (program M)
    (fun _ => rfl) initial t hh
  change run M u (BitMachineInline.cfg _ _ _ initial) =
    BitMachineInline.cfg _ _ _ (ClockInputPreparation.run M t initial) at he
  rw [hc] at he
  exact ⟨u,hu.trans ht,c,he⟩

def test (budget count : List Bool) : Bool :=
  let c := M.run budget.length (M.init (CutoffInputEncoding.nextInput count))
  decide (c.l = none) && decide (CutoffBitMachine.decodedNat (c.stk M.output) ≤ budget.length)

theorem probe_phase (active budget count : List Bool) (prepared : ClockInputPreparation.Next.Config) :
    ∃ t ≤ CutoffProbeMachine.polynomialConstant M *
        (2 * budget.length + (CutoffInputEncoding.nextInput count).length + 2)^2,
      ∃ c : CutoffProbeMachine.Config M,
        run M t ⟨some (.probe (.inl (CutoffProbeMachine.sim M).start)),
          probeControl M ((CutoffProbeMachine.sim M).initial,CutoffProbeMachine.testInitial),
          ClockInputPreparation.preparedBank M active budget count prepared⟩ =
          ⟨some .test, probeControl M c.var,
            bank (probeEmbed M) (ClockInputPreparation.preparedBank M active budget count prepared) c.stk⟩ ∧
        (c.stk (.inr (.inr 2))).head? = some (test M budget count) := by
  obtain ⟨t,c,ht,hc,hh,ho,_,_⟩ := CutoffProbeMachine.probe_packed M budget.length
    (CutoffInputEncoding.nextInput count)
  let S := ClockInputPreparation.preparedBank M active budget count prepared
  let initial := CutoffProbeMachine.start M
    (BoundedBitMachine.packed budget.length (CutoffInputEncoding.nextInput count))
    (List.replicate budget.length true)
  have hh' : (CutoffProbeMachine.run M t initial).l = none := by rw [hc]; exact hh
  obtain ⟨u,hu,he⟩ := BitMachineStackEmbedding.outputs (probeEmbed M) S
    Label.probe (probeControl M) (readProbe M) (fun _ => rfl) (some .test)
    (CutoffProbeMachine.program M) (program M) (fun _ => rfl) initial t hh'
  change run M u (BitMachineStackEmbedding.cfg _ _ _ _ _ initial) =
    BitMachineStackEmbedding.cfg _ _ _ _ _ (CutoffProbeMachine.run M t initial) at he
  rw [hc] at he
  have hi : bank (probeEmbed M) S initial.stk = S := by
    apply bank_eq_self
    intro i
    exact (ClockInputPreparation.prepared_probe M active budget count prepared i).symm
  change run M u ⟨some (.probe (.inl (CutoffProbeMachine.sim M).start)),
      probeControl M ((CutoffProbeMachine.sim M).initial,CutoffProbeMachine.testInitial),
      bank (probeEmbed M) S initial.stk⟩ = BitMachineStackEmbedding.cfg _ _ _ _ _ c at he
  rw [hi] at he
  refine ⟨u,hu.trans ht,c,?_,ho⟩
  simpa only [BitMachineStackEmbedding.cfg, stackCfg, BitMachineInline.cfg, hh] using he

theorem increment_phase (S : Stack M → List Bool)
    (hs : S (ClockInputPreparation.scratchKey M) = []) :
    ∃ t ≤ 2 * (S (.inl 2)).length + 2,
      run M t ⟨some (.increment .carry), incrementControl M none, S⟩ =
        ⟨some .clearAfterStart, incrementControl M none,
          Function.update S (.inl 2) (BinarySuccessorMachine.successor (S (.inl 2)))⟩ := by
  let q := S (.inl 2)
  let initial := BinarySuccessorMachine.cfg (some .carry) none q []
  let final := BinarySuccessorMachine.cfg none none (BinarySuccessorMachine.successor q) []
  let bound := 2 * BinarySuccessorMachine.carryCount q + 2
  have hr : BinarySuccessorMachine.run bound initial = final := by
    simpa only [List.length_nil, add_zero, List.reverse_nil, List.nil_append]
      using BinarySuccessorMachine.run_correct none q []
  have hh : (BinarySuccessorMachine.run bound initial).l = none := by rw [hr]; rfl
  obtain ⟨t,ht,he⟩ := BitMachineStackEmbedding.outputs (incrementEmbed M) S Label.increment
    (incrementControl M) (readIncrement M) (fun _ => rfl) (some .clearAfterStart)
    BinarySuccessorMachine.program (program M) (fun _ => rfl) initial bound hh
  change run M t (BitMachineStackEmbedding.cfg _ _ _ _ _ initial) =
    BitMachineStackEmbedding.cfg _ _ _ _ _ (BinarySuccessorMachine.run bound initial) at he
  rw [hr] at he
  have hi : bank (incrementEmbed M) S initial.stk = S := by
    apply bank_eq_self
    intro i
    fin_cases i <;> simp [initial, BinarySuccessorMachine.cfg, incrementEmbed, q, hs]
  have hf : final.stk = Function.update initial.stk 0 (BinarySuccessorMachine.successor q) := by
    funext i
    fin_cases i <;> simp [initial, final, BinarySuccessorMachine.cfg]
  have hf' : bank (incrementEmbed M) S final.stk =
      Function.update S (.inl 2) (BinarySuccessorMachine.successor q) := by
    rw [hf,bank_update,hi]
    rfl
  change run M t ⟨some (.increment .carry), incrementControl M none,
      bank (incrementEmbed M) S initial.stk⟩ =
        ⟨some .clearAfterStart, incrementControl M none, bank (incrementEmbed M) S final.stk⟩ at he
  rw [hi,hf'] at he
  refine ⟨t,?_,he⟩
  change t ≤ 2 * q.length + 2
  have h := BinarySuccessorMachine.carryCount_le_length q
  dsimp only [bound] at ht
  omega

def bankPushBound : ℕ := ∑ l : Label M, BitMachine.pushBound (program M l)

theorem step_stack_length (c : Config M) (j : Stack M) :
    ((advance (program M) c).stk j).length ≤ (c.stk j).length + bankPushBound M := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => simp [advance,TM2.step]
  | some l =>
      have h := BitMachine.stepAux_length (program M l) v S j
      have hb : BitMachine.pushBound (program M l) ≤ bankPushBound M :=
        Finset.single_le_sum (f := fun l => BitMachine.pushBound (program M l))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
      exact h.trans (Nat.add_le_add_left hb _)

theorem run_stack_length (t : ℕ) (c : Config M) (j : Stack M) :
    ((run M t c).stk j).length ≤ (c.stk j).length + t * bankPushBound M := by
  induction t with
  | zero => simp [run]
  | succ t ih =>
      have h := (step_stack_length M (run M t c) j).trans (Nat.add_le_add_right ih _)
      simpa [run,Function.iterate_succ_apply',Nat.succ_mul,Nat.add_assoc] using h

def result (active budget count : List Bool) : Stack M → List Bool :=
  if active.head?.getD false then
    if test M budget count then
      ClockInputPreparation.readyBank M active budget (BinarySuccessorMachine.successor count)
    else ClockInputPreparation.readyBank M (false :: active.tail) budget count
  else ClockInputPreparation.readyBank M active budget count

theorem probe_bank_permanent (S : Stack M → List Bool)
    (T : CutoffProbeMachine.Stack M → List Bool) (i : Fin 3) :
    bank (probeEmbed M) S T (.inl i) = S (.inl i) := by
  apply bank_outside
  simp [probeEmbed, ClockInputPreparation.probeKey]

theorem probe_bank_scratch (S : Stack M → List Bool)
    (T : CutoffProbeMachine.Stack M → List Bool) :
    bank (probeEmbed M) S T (ClockInputPreparation.scratchKey M) =
      S (ClockInputPreparation.scratchKey M) := by
  apply bank_outside
  simp [probeEmbed, ClockInputPreparation.probeKey, ClockInputPreparation.scratchKey]

theorem test_true_step (S : Stack M → List Bool) (v : CutoffProbeMachine.Control M)
    (h : (S (ClockInputPreparation.probeKey M (.inr (.inr 2)))).head? = some true) :
    run M 1 ⟨some .test, probeControl M v, S⟩ =
      ⟨some (.increment .carry), incrementControl M none, S⟩ := by
  simp [run,advance,program,TM2.step,TM2.stepAux,h]

theorem test_false_step (S : Stack M → List Bool) (v : CutoffProbeMachine.Control M)
    (h : (S (ClockInputPreparation.probeKey M (.inr (.inr 2)))).head? = some false) :
    run M 1 ⟨some .test, probeControl M v, S⟩ =
      ⟨some .clearAfterStart, (.probe v,some false),
        Function.update S (.inl 0) (false :: (S (.inl 0)).tail)⟩ := by
  simp [run,advance,program,TM2.step,TM2.stepAux,h,probeControl]

def activeBound : ℕ := 100 + 9 * CutoffProbeMachine.polynomialConstant M

theorem active_run (active budget count : List Bool) (ha : active.head?.getD false = true) :
    ∃ t ≤ activeBound M * (count.length + budget.length + 2)^2,
      ∃ (v : Control M) (S : Stack M → List Bool),
        run M t ⟨some .active, (.idle,none), ClockInputPreparation.readyBank M active budget count⟩ =
          ⟨some .clearAfterStart,v,S⟩ ∧
        (∀ i : Fin 3, S (.inl i) = result M active budget count (.inl i)) := by
  obtain ⟨t₁,ht₁,c,h₁⟩ := prepare_phase M active budget count
  obtain ⟨t₂,ht₂,p,h₂,ho⟩ := probe_phase M active budget count c
  let P := ClockInputPreparation.preparedBank M active budget count c
  let S := bank (probeEmbed M) P p.stk
  have hs : S (ClockInputPreparation.scratchKey M) = [] := by
    dsimp only [S,P]
    rw [probe_bank_scratch, ClockInputPreparation.prepared_scratch]
  have hp : ∀ i : Fin 3, S (.inl i) = ![active,budget,count] i := by
    intro i
    dsimp only [S,P]
    rw [probe_bank_permanent, ClockInputPreparation.prepared_permanent]
  have ho' : (S (ClockInputPreparation.probeKey M (.inr (.inr 2)))).head? =
      some (test M budget count) := by
    dsimp only [S]
    rw [show ClockInputPreparation.probeKey M (.inr (.inr 2)) = probeEmbed M (.inr (.inr 2)) from rfl,
      bank_at]
    exact ho
  have hactive : run M 1 ⟨some .active, (.idle,none),
      ClockInputPreparation.readyBank M active budget count⟩ =
      ⟨some (.prepare (.copyStart .count)), prepControl M (.copying none),
        ClockInputPreparation.readyBank M active budget count⟩ := by
    simp [run,advance,program,TM2.step,TM2.stepAux,ClockInputPreparation.readyBank,ha]
  have hstart : run M 1 ⟨some .probeStart, prepControl M (.packing none), P⟩ =
      ⟨some (.probe (.inl (CutoffProbeMachine.sim M).start)),
        probeControl M ((CutoffProbeMachine.sim M).initial,CutoffProbeMachine.testInitial),P⟩ := rfl
  have hbase : run M (1+t₁+1+t₂)
      ⟨some .active, (.idle,none), ClockInputPreparation.readyBank M active budget count⟩ =
      ⟨some .test,probeControl M p.var,S⟩ := by
    rw [run_add,run_add,run_add,hactive,h₁,hstart,h₂]
  have hlen : (CutoffInputEncoding.nextInput count).length ≤ 2*count.length+4 := by
    simp only [CutoffInputEncoding.nextInput,CutoffInputEncoding.word,List.length_append,
      CutoffInputEncoding.digits_length,List.length_cons,List.length_nil]
    have h := CutoffInputEncoding.successor_length_le count
    omega
  have ht₂' : t₂ ≤ 9 * CutoffProbeMachine.polynomialConstant M *
      (count.length+budget.length+2)^2 := by
    have hb : 2*budget.length+(CutoffInputEncoding.nextInput count).length+2 ≤
        3*(count.length+budget.length+2) := by omega
    have hh := Nat.pow_le_pow_left hb 2
    have hmul := Nat.mul_le_mul_left (CutoffProbeMachine.polynomialConstant M) hh
    nlinarith
  have hquad : count.length+budget.length+2 ≤ (count.length+budget.length+2)^2 := by nlinarith
  cases htest : test M budget count with
  | false =>
      rw [htest] at ho'
      refine ⟨1+t₁+1+t₂+1,?_,(.probe p.var,some false),
        Function.update S (.inl 0) (false::(S (.inl 0)).tail),?_,?_⟩
      · dsimp only [activeBound]; nlinarith
      · rw [run_add,hbase,test_false_step M S p.var ho']
      · intro i
        fin_cases i <;> simp [result,ha,htest,hp,ClockInputPreparation.readyBank]
  | true =>
      rw [htest] at ho'
      obtain ⟨t₃,ht₃,h₃⟩ := increment_phase M S hs
      have hcount : S (.inl 2) = count := hp 2
      rw [hcount] at ht₃ h₃
      refine ⟨1+t₁+1+t₂+1+t₃,?_,incrementControl M none,
        Function.update S (.inl 2) (BinarySuccessorMachine.successor count),?_,?_⟩
      · dsimp only [activeBound]; nlinarith
      · rw [run_add,run_add,hbase,test_true_step M S p.var ho',h₃]
      · intro i
        fin_cases i <;> simp [result,ha,htest,hp,ClockInputPreparation.readyBank]

theorem finish_run (v : Control M) (S : Stack M → List Bool) :
    run M ((∑ i, (S (tempKey M i)).length) + tempCount M + 3)
      ⟨some .clearAfterStart,v,S⟩ =
      ⟨none,(.idle,none),ClockInputPreparation.readyBank M (S (.inl 0)) (S (.inl 1)) (S (.inl 2))⟩ := by
  have ht : (∑ i, (S (tempKey M i)).length) + tempCount M + 3 =
      1 + ((∑ i, (S (tempKey M i)).length) + tempCount M + 1) + 1 := by omega
  rw [ht,run_add,run_add]
  change run M 1 (run M ((∑ i, (S (tempKey M i)).length) + tempCount M + 1)
    ⟨some (.clearAfter 0),(.idle,none),S⟩) = _
  rw [clear_after]
  rfl

theorem result_eq_ready (active budget count : List Bool) :
    ClockInputPreparation.readyBank M
      (result M active budget count (.inl 0)) (result M active budget count (.inl 1))
      (result M active budget count (.inl 2)) = result M active budget count := by
  unfold result
  split
  · split <;> rfl
  · rfl

def readyBound : ℕ :=
  (tempCount M * bankPushBound M + 1) * activeBound M + tempCount M + 3

theorem ready_run (active budget count : List Bool) :
    ∃ t ≤ readyBound M * (count.length + budget.length + 2)^2, ∃ v : Control M,
      run M t ⟨some .active,(.idle,none),ClockInputPreparation.readyBank M active budget count⟩ =
        ⟨none,v,result M active budget count⟩ := by
  cases ha : active.head?.getD false with
  | false =>
      refine ⟨1,?_,(.idle,active.head?),?_⟩
      · have hbase : 1 ≤ (count.length+budget.length+2)^2 := Nat.one_le_pow _ _ (by omega)
        have hbound : 1 ≤ readyBound M := by unfold readyBound; omega
        exact hbase.trans (Nat.le_mul_of_pos_left _ hbound)
      · simp [run,advance,program,TM2.step,TM2.stepAux,ClockInputPreparation.readyBank,
          result,ha]
  | true =>
      obtain ⟨t,ht,v,S,hr,hp⟩ := active_run M active budget count ha
      have hs : ∀ i : Fin (tempCount M), (S (tempKey M i)).length ≤ t * bankPushBound M := by
        intro i
        have h := run_stack_length M t
          ⟨some .active,(.idle,none),ClockInputPreparation.readyBank M active budget count⟩
          (tempKey M i)
        rw [hr] at h
        simpa only [ClockInputPreparation.readyBank,tempKey,Sum.elim_inr,List.length_nil,zero_add]
          using h
      have hsum : (∑ i : Fin (tempCount M), (S (tempKey M i)).length) ≤
          tempCount M * (t * bankPushBound M) := by
        calc
          _ ≤ ∑ _i : Fin (tempCount M), t * bankPushBound M := Finset.sum_le_sum (fun i _ => hs i)
          _ = _ := by simp
      refine ⟨t + ((∑ i, (S (tempKey M i)).length) + tempCount M + 3),?_,(.idle,none),?_⟩
      · have hbase : 1 ≤ (count.length+budget.length+2)^2 := Nat.one_le_pow _ _ (by omega)
        have hmul := Nat.mul_le_mul_left (tempCount M * bankPushBound M + 1) ht
        have hconst := Nat.mul_le_mul_left (tempCount M+3) hbase
        dsimp only [readyBound]
        nlinarith
      · rw [run_add,hr,finish_run,hp 0,hp 1,hp 2,result_eq_ready]

def totalWords (S : Stack M → List Bool) : ℕ := ∑ i, (S i).length

theorem word_le_total (S : Stack M → List Bool) (i : Stack M) :
    (S i).length ≤ totalWords M S :=
  Finset.single_le_sum (f := fun i => (S i).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

theorem tempWords_le_total (S : Stack M → List Bool) :
    (∑ i : Fin (tempCount M), (S (tempKey M i)).length) ≤ totalWords M S := by
  let e : Fin (tempCount M) ↪ Stack M := ⟨tempKey M,tempKey_injective M⟩
  have he : (∑ i : Fin (tempCount M), (S (tempKey M i)).length) =
      ∑ i ∈ Finset.univ.map e, (S i).length := by rw [Finset.sum_map]; rfl
  rw [he]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

def rawBound : ℕ := 4 * readyBound M + tempCount M + 2

theorem raw_run (S : Stack M → List Bool) :
    ∃ t ≤ rawBound M * (totalWords M S + 1)^2, ∃ v : Control M,
      run M t ⟨some (.clearBefore 0),(.idle,none),S⟩ =
        ⟨none,v,result M (S (.inl 0)) (S (.inl 1)) (S (.inl 2))⟩ := by
  obtain ⟨t,ht,v,hr⟩ := ready_run M (S (.inl 0)) (S (.inl 1)) (S (.inl 2))
  refine ⟨((∑ i, (S (tempKey M i)).length) + tempCount M + 1) + t,?_,v,?_⟩
  · have hs := tempWords_le_total M S
    have hb := word_le_total M S (.inl 1)
    have hc := word_le_total M S (.inl 2)
    have harg : (S (.inl 2)).length+(S (.inl 1)).length+2 ≤ 2*(totalWords M S+1) := by omega
    have hpow := Nat.pow_le_pow_left harg 2
    have hmul := Nat.mul_le_mul_left (readyBound M) hpow
    have hbase : totalWords M S+1 ≤ (totalWords M S+1)^2 := by nlinarith
    have hconst : 1 ≤ (totalWords M S+1)^2 := Nat.one_le_pow _ _ (by omega)
    have hscale := Nat.mul_le_mul_left (tempCount M+1) hconst
    dsimp only [rawBound]
    nlinarith
  · rw [run_add,clear_before,hr]

theorem result_word_length (active budget count : List Bool) (L : ℕ)
    (ha : active.length ≤ L) (hb : budget.length ≤ L) (hc : count.length ≤ L)
    (i : Stack M) : (result M active budget count i).length ≤ L+1 := by
  have hs := CutoffInputEncoding.successor_length_le count
  have ht : active.tail.length ≤ active.length := by cases active <;> simp
  unfold result
  split
  · split <;> cases i with
    | inl i => fin_cases i <;> simp [ClockInputPreparation.readyBank] <;> omega
    | inr i => simp [ClockInputPreparation.readyBank]
  · cases i with
    | inl i => fin_cases i <;> simp [ClockInputPreparation.readyBank] <;> omega
    | inr i => simp [ClockInputPreparation.readyBank]

end
end EthInapproximability.CurrentPaper.ClockStepMachine
