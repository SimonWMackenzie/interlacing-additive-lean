import EthInapproximability.CurrentPaper.ClockIterationInput
import EthInapproximability.CurrentPaper.BitMachineIteration
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-!
# A fixed ordinary-input driver for clock-state iteration

Source: frozen v8 `05-iteration.tex`. The input word supplies unary fuel.
The initial bank packet is written by a physical finite program, followed
by the existing physically charged iteration controller. The output is the
entire final state packet; extraction of its counter is a separate call.
-/

namespace EthInapproximability.CurrentPaper.ClockIterationDriver

noncomputable section

open Turing TM2.Stmt BitMachineEncoding BitMachineStackEmbedding

variable (A : BitMachine.Machine) (K : ℕ)

abbrev Stack := BitMachineIteration.Stack A

inductive Label (A : BitMachine.Machine) (K : ℕ) where
  | prepare : ClockIterationInput.Label K → Label A K
  | start
  | loop : BitMachineIteration.Label A → Label A K
  deriving DecidableEq, Fintype

abbrev Control := Option Bool ⊕ BitMachineIteration.Control A

def readPrepare : Control A → Option Bool
  | .inl b => b
  | .inr _ => none
def readLoop : Control A → BitMachineIteration.Control A
  | .inl _ => (A.initial,none)
  | .inr v => v

def prepareEmbed : Fin 3 ↪ Stack A where
  toFun i := if i=0 then .inr 0 else if i=1 then .inr 1 else .inl A.input
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

def program : Label A K → TM2.Stmt (fun _ : Stack A => Bool) (Label A K) (Control A)
  | .prepare l => stmt (prepareEmbed A) Label.prepare Sum.inl (readPrepare A)
      (some .start) (ClockIterationInput.program K l)
  | .start => load (fun _ => .inr (A.initial,none)) (goto (fun _ => .loop (.inr .testFuel)))
  | .loop l => BitMachineInline.stmt Label.loop Sum.inr (readLoop A) none
      (BitMachineIteration.program A l)

abbrev Config := TM2.Cfg (fun _ : Stack A => Bool) (Label A K) (Control A)

def run (t : ℕ) (c : Config A K) := ((advance (program A K))^[t]) c

theorem run_add (t u : ℕ) (c : Config A K) : run A K (t+u) c = run A K u (run A K t c) := by
  rw [Nat.add_comm]
  exact Function.iterate_add_apply _ _ _ _

def initial (input : List Bool) : Config A K :=
  rawInit (.inr 0) (.prepare (.suffix 0)) (.inl none) input

theorem preparation (input : List Bool) :
    ∃ t ≤ 2*input.length+K+5,
      run A K t (initial A K input) =
        ⟨some .start,.inl none,(BitMachineIteration.ready A (ClockIterationInput.packet K input) input).stk⟩ := by
  let c := ClockIterationInput.cfg (K := K) (some (.suffix 0)) none input [] []
  let d := ClockIterationInput.cfg (K := K) none none input [] (ClockIterationInput.packet K input)
  have hr : ClockIterationInput.run (2*input.length+K+5) c = d :=
    ClockIterationInput.run_correct K input
  have hh : (ClockIterationInput.run (2*input.length+K+5) c).l = none := by rw [hr]; rfl
  obtain ⟨t,ht,he⟩ := BitMachineStackEmbedding.outputs (prepareEmbed A) (initial A K input).stk
    Label.prepare Sum.inl (readPrepare A) (fun _ => rfl) (some .start)
    (ClockIterationInput.program K) (program A K) (fun _ => rfl) c (2*input.length+K+5) hh
  change run A K t (BitMachineStackEmbedding.cfg _ _ _ _ _ c) =
    BitMachineStackEmbedding.cfg _ _ _ _ _ (ClockIterationInput.run _ c) at he
  rw [hr] at he
  have hi : bank (prepareEmbed A) (initial A K input).stk c.stk = (initial A K input).stk := by
    apply bank_eq_self
    intro i
    fin_cases i <;> simp [c,ClockIterationInput.cfg,prepareEmbed,initial,rawInit]
  have hd : bank (prepareEmbed A) (initial A K input).stk d.stk =
      (BitMachineIteration.ready A (ClockIterationInput.packet K input) input).stk := by
    funext i
    cases i with
    | inl i =>
        by_cases h : i=A.input
        · subst i
          change bank (prepareEmbed A) (initial A K input).stk d.stk (prepareEmbed A 2) = _
          rw [bank_at]
          simp [d,ClockIterationInput.cfg,BitMachineIteration.ready,BitMachineIteration.adminCfg,
            BitMachine.Machine.init]
        · rw [bank_outside _ _ _ _ (by
            intro ⟨j,hj⟩; fin_cases j <;> simp_all [prepareEmbed])]
          simp [initial,rawInit,BitMachineIteration.ready,BitMachineIteration.adminCfg,
            BitMachine.Machine.init,h]
    | inr i =>
        fin_cases i
        · change bank (prepareEmbed A) (initial A K input).stk d.stk (prepareEmbed A 0) = _
          rw [bank_at]
          rfl
        · change bank (prepareEmbed A) (initial A K input).stk d.stk (prepareEmbed A 1) = _
          rw [bank_at]
          rfl
  change run A K t ⟨some (.prepare (.suffix 0)),.inl none,
      bank (prepareEmbed A) (initial A K input).stk c.stk⟩ =
      ⟨some .start,.inl none,bank (prepareEmbed A) (initial A K input).stk d.stk⟩ at he
  rw [hi,hd] at he
  exact ⟨t,ht,he⟩

theorem driver_run (input : List Bool) (states : ℕ → List Bool) (L T : ℕ)
    (hzero : states 0 = ClockIterationInput.packet K input)
    (hstep : ∀ j < input.length, A.OutputsWithin (states j) (states (j+1)) T)
    (hlen : ∀ j < input.length, (states j).length ≤ L) :
    ∃ t ≤ 2*input.length+K+7+input.length*BitMachineIteration.roundBound A L T,
      (run A K t (initial A K input)).l = none ∧
      (run A K t (initial A K input)).stk (.inl A.input) = states input.length := by
  obtain ⟨t₁,ht₁,h₁⟩ := preparation A K input
  obtain ⟨t₂,ht₂,h₂⟩ := BitMachineIteration.iteration_run A states input L T hstep hlen
  have hh : (BitMachineIteration.run A t₂ (BitMachineIteration.ready A (states 0) input)).l = none := by
    rw [h₂]; rfl
  obtain ⟨u,hu,he⟩ := BitMachineInline.outputs Label.loop Sum.inr (readLoop A) (fun _ => rfl) none
    (BitMachineIteration.program A) (program A K) (fun _ => rfl)
    (BitMachineIteration.ready A (states 0) input) t₂ hh
  change run A K u (BitMachineInline.cfg _ _ _ _) =
    BitMachineInline.cfg _ _ _ (BitMachineIteration.run A t₂ _) at he
  rw [h₂,hzero] at he
  have hstart : run A K 1
      ⟨some .start,.inl none,(BitMachineIteration.ready A (ClockIterationInput.packet K input) input).stk⟩ =
      BitMachineInline.cfg Label.loop Sum.inr none
        (BitMachineIteration.ready A (ClockIterationInput.packet K input) input) := rfl
  have hr : run A K (t₁+1+u) (initial A K input) =
      BitMachineInline.cfg Label.loop Sum.inr none (BitMachineIteration.finished A (states input.length)) := by
    rw [run_add,run_add,h₁,hstart,he]
  refine ⟨t₁+1+u,by omega,?_,?_⟩ <;> rw [hr]
  · rfl
  · simp [BitMachineInline.cfg,BitMachineIteration.finished,BitMachine.Machine.init]

noncomputable def machine : BitMachine.Machine :=
  ofFinite (.inr 0) (.inl A.input) (.prepare (.suffix 0)) (.inl none) (program A K)

theorem outputs (input : List Bool) (states : ℕ → List Bool) (L T : ℕ)
    (hzero : states 0 = ClockIterationInput.packet K input)
    (hstep : ∀ j < input.length, A.OutputsWithin (states j) (states (j+1)) T)
    (hlen : ∀ j < input.length, (states j).length ≤ L) :
    (machine A K).OutputsWithin input (states input.length)
      (2*input.length+K+7+input.length*BitMachineIteration.roundBound A L T) := by
  obtain ⟨t,ht,hh,ho⟩ := driver_run A K input states L T hzero hstep hlen
  apply outputsWithin_of_raw_run (Sum.inr (0 : Fin 2) : Stack A) (.inl A.input)
    (Label.prepare (.suffix 0) : Label A K) (Sum.inl none : Control A)
    (program A K) input (states input.length) t _ ht
  · exact hh
  · exact ho

end
end EthInapproximability.CurrentPaper.ClockIterationDriver
