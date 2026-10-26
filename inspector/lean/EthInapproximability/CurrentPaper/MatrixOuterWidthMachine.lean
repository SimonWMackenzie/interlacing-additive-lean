import EthInapproximability.CurrentPaper.MatrixOuterWidthMachineCoefficient
import EthInapproximability.CurrentPaper.ExactParameterMachineSquare
import EthInapproximability.CurrentPaper.MatrixUnaryPower
import EthInapproximability.CurrentPaper.BitMachineComposition
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding
import EthInapproximability.CurrentPaper.Parameters

/-!
# Physical outer-width producer

Locked v8 `F-parameter-choices.tex`, `eq:paper-explicit-parameter-list`:
`q = 2^(1000*lambda^2)`. One unary lambda word enters the fixed
square machine. The fixed coefficient stage writes 1000 and physically
multiplies the unary square. The fixed power machine then writes unary q.
Both inter-machine transfers are literal Boolean-stack transitions.
-/

namespace EthInapproximability.CurrentPaper.MatrixOuterWidthMachine

open Turing BitMachineEncoding BitMachineComposition

def unary (n : ℕ) : List Bool := List.replicate n true
def exponent (lambda : ℕ) : ℕ := 1000*lambda^2
def width (lambda : ℕ) : ℕ := 2 ^ exponent lambda

noncomputable def squareMachine : BitMachine.Machine :=
  ExactParameterMachineSquare.squareMachine
noncomputable def coefficientMachine : BitMachine.Machine :=
  MatrixOuterWidthMachineCoefficient.machine
noncomputable def powerMachine : BitMachine.Machine := MatrixUnaryPower.machine

noncomputable def productMachine : BitMachine.Machine :=
  composition squareMachine coefficientMachine
noncomputable def machine : BitMachine.Machine :=
  composition productMachine powerMachine

abbrev Stack := Fin machine.stackCount
abbrev Label := Fin machine.labelCount
abbrev Control := Fin machine.controlCount
abbrev Config := machine.Config

noncomputable def inputStack : Stack := machine.input
noncomputable def outputStack : Stack := machine.output
noncomputable def startCfg (lambda : ℕ) : Config := machine.init (unary lambda)

theorem startCfg_input (lambda : ℕ) :
    (startCfg lambda).stk inputStack = unary lambda := by
  simp [startCfg, inputStack, BitMachine.Machine.init]

theorem startCfg_other_empty (lambda : ℕ) (k : Stack)
    (hk : k ≠ inputStack) : (startCfg lambda).stk k = [] := by
  change k ≠ machine.input at hk
  simp [startCfg, BitMachine.Machine.init, hk]

def squareTime (lambda : ℕ) : ℕ :=
  2*lambda+2 + 2*(2*lambda+1)+2 + 2*(2*lambda+2)^2
def coefficientTime (lambda : ℕ) : ℕ :=
  MatrixOuterWidthMachineCoefficient.time (lambda^2)
def totalTime (lambda : ℕ) : ℕ :=
  squareTime lambda + 2*(lambda^2)+2 + coefficientTime lambda +
    2*exponent lambda+2 + 16*width lambda

theorem outputs (lambda : ℕ) :
    machine.OutputsWithin (unary lambda) (unary (width lambda))
      (totalTime lambda) := by
  have hs := ExactParameterMachineSquare.square_outputs lambda
  have hc := MatrixOuterWidthMachineCoefficient.outputs (lambda^2)
  have hsc := composition_outputsWithin squareMachine coefficientMachine hs hc
  have hp := MatrixUnaryPower.outputs (unary (exponent lambda))
  have hscp := composition_outputsWithin productMachine powerMachine hsc hp
  simpa only [machine, productMachine, squareMachine, coefficientMachine,
    powerMachine, totalTime, squareTime, coefficientTime, exponent, width,
    unary, MatrixOuterWidthMachineCoefficient.unary,
    List.length_replicate] using hscp

/-- Exact literal terminal configuration: the final bank is unary q,
and its label is halted. No exponent or duplicate lambda is preloaded. -/
theorem width_run (lambda : ℕ) :
    ∃ t ≤ totalTime lambda, ∃ cf : Config,
      machine.run t (startCfg lambda) = cf ∧
      cf.l = none ∧ cf.stk outputStack = unary (width lambda) := by
  obtain ⟨t, ht, hh, ho⟩ := outputs lambda
  exact ⟨t, ht, _, rfl, hh, ho⟩

theorem totalTime_output_poly (lambda : ℕ) :
    let H := lambda+width lambda+1
    totalTime lambda ≤ 5000*H^2 := by
  let Q := width lambda
  let H := lambda+Q+1
  have hH : 1 ≤ H := by dsimp [H]; omega
  have hl : lambda ≤ H := by dsimp [H]; omega
  have hQ : Q ≤ H := by dsimp [H]; omega
  have hpow : lambda^2 ≤ H^2 := Nat.pow_le_pow_left hl 2
  have hHpow : H ≤ H^2 := by nlinarith
  have h1 : 1 ≤ H^2 := by nlinarith
  have hf : totalTime lambda = 4014*lambda^2+22*lambda+23+16*Q := by
    dsimp [totalTime, squareTime, coefficientTime,
      MatrixOuterWidthMachineCoefficient.time,
      MatrixAddressMachine.exactTime, exponent]
    ring
  rw [hf]
  nlinarith [hpow, hHpow, h1, hl, hQ]

theorem width_run_output_poly (lambda : ℕ) :
    let H := lambda+width lambda+1
    ∃ t ≤ 5000*H^2, ∃ cf : Config,
      machine.run t (startCfg lambda) = cf ∧
      cf.l = none ∧ cf.stk outputStack = unary (width lambda) := by
  obtain ⟨t, ht, cf, hr, hh, ho⟩ := width_run lambda
  exact ⟨t, ht.trans (totalTime_output_poly lambda), cf, hr, hh, ho⟩

noncomputable def embeddedProgram {K : Type*} [DecidableEq K]
    (ι : Stack ↪ K) : Label → TM2.Stmt (fun _ : K => Bool) Label Control :=
  fun l => BitMachineStackEmbedding.stmt ι id id id none (machine.program l)

/-- Every non-selected ambient bank is preserved, including nonempty
protected-source, parameter, and interlace banks. -/
theorem embedded_width_run {K : Type*} [DecidableEq K]
    (ι : Stack ↪ K) (foreign : K → List Bool) (lambda : ℕ) :
    let H := lambda+width lambda+1
    ∃ t ≤ 5000*H^2, ∃ cf : Config,
      ((advance (embeddedProgram ι))^[t])
        (BitMachineStackEmbedding.cfg ι foreign id id none (startCfg lambda)) =
          BitMachineStackEmbedding.cfg ι foreign id id none cf ∧
      cf.l = none ∧ cf.stk outputStack = unary (width lambda) := by
  obtain ⟨u, hu, cf, hr, hh, ho⟩ := width_run lambda
  have hhalt : (((advance machine.program)^[u]) (startCfg lambda)).l = none := by
    change (machine.run u (startCfg lambda)).l = none
    rw [hr]
    exact hh
  obtain ⟨t, ht, hem⟩ := BitMachineStackEmbedding.outputs
    ι foreign id id id (fun _ => rfl) none machine.program
    (embeddedProgram ι) (fun _ => rfl) (startCfg lambda) u hhalt
  refine ⟨t, (ht.trans hu).trans (totalTime_output_poly lambda), cf, ?_, hh, ho⟩
  change ((advance (embeddedProgram ι))^[t])
    (BitMachineStackEmbedding.cfg ι foreign id id none (startCfg lambda)) =
      BitMachineStackEmbedding.cfg ι foreign id id none
        (machine.run u (startCfg lambda)) at hem
  rw [hr] at hem
  exact hem

theorem width_eq_parameters (i : Parameters.Input) :
    width (Parameters.scale i) = Parameters.outerWidth i := rfl

end EthInapproximability.CurrentPaper.MatrixOuterWidthMachine
