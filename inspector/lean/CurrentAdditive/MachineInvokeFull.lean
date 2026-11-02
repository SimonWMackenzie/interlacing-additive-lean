import CurrentAdditive.MachineInvokeClear

/-! Complete source-preserving invocation with charged copy, run, output and cleanup. -/

namespace CurrentAdditive.MinimumRatioContext.MachineInvokeFull

open Turing EthInapproximability.CurrentPaper
open MachineInvokeCore MachineInvokeClear BitMachineEncoding
open BitMachineStackEmbedding

def p01 {M : BitMachine.Machine} {N : ℕ} (C : Slots M N) :=
  BitMachineRawSequence.program (inputProgram C) (machineProgram C)
    M.start (none : Option Bool) M.initial

def p012 {M : BitMachine.Machine} {N : ℕ} (C : Slots M N) :=
  BitMachineRawSequence.program (p01 C) (outputProgram C)
    BitMachineCopy.Label.scan (none, M.initial) (none : Option Bool)

def program {M : BitMachine.Machine} {N : ℕ} (C : Slots M N) :=
  BitMachineRawSequence.program (p012 C) (MachineInvokeClear.program C)
    (MachineInvokeClear.clearLabel M.stackCount 0)
    ((none, M.initial), none) ((), none)

theorem cleanup_eq {M : BitMachine.Machine} {N : ℕ} (C : Slots M N)
    (S : StackN N → List Bool) (bits result : List Bool) (T : ℕ)
    (hblank : ∀ k, S (C.machine k) = []) :
    BitMachineClearBank.cleared C.machine
      (Function.update
        (ExactParameterMachineFrame.terminalBank M C.machine S bits T)
        C.target result) =
      Function.update S C.target result := by
  let U := ExactParameterMachineFrame.terminalBank M C.machine S bits T
  funext k
  by_cases ht : k = C.target
  · subst k
    rw [BitMachineClearBank.cleared_foreign C.machine
      (Function.update U C.target result) C.target
      (by intro i; exact (C.target_machine i).symm)]
    simp
  · by_cases hi : ∃ i, C.machine i = k
    · obtain ⟨i, he⟩ := hi
      subst k
      rw [BitMachineClearBank.cleared_bank]
      simp [ht, hblank i]
    · rw [BitMachineClearBank.cleared_foreign C.machine
        (Function.update U C.target result) k
        (by intro i; exact fun h => hi ⟨i, h⟩)]
      have hU : U k = S k :=
        ExactParameterMachineFrame.foreign_at M C.machine S bits T k hi
      simp [ht, hU]

abbrev Label01 (M : BitMachine.Machine) :=
  BitMachineRawSequence.Label BitMachineCopy.Label (Fin M.labelCount)

abbrev Label012 (M : BitMachine.Machine) :=
  BitMachineRawSequence.Label (Label01 M) BitMachineCopy.Label

abbrev LabelFull (M : BitMachine.Machine) :=
  BitMachineRawSequence.Label (Label012 M)
    (MachineInvokeClear.Label M.stackCount)

abbrev ControlFull (M : BitMachine.Machine) :=
  (((Option Bool × Fin M.controlCount) × Option Bool) ×
    MachineInvokeClear.Control)

def start {M : BitMachine.Machine} {N : ℕ} (_C : Slots M N) :
    LabelFull M :=
  BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))

def control {M : BitMachine.Machine} {N : ℕ} (_C : Slots M N) :
    ControlFull M :=
  (((none, M.initial), none), ((), none))

noncomputable def timeBound {M : BitMachine.Machine} {N : ℕ} (C : Slots M N)
    (S : StackN N → List Bool) (bits result : List Bool) (T : ℕ) : ℕ :=
  (2 * bits.length + 2) + T + (2 * result.length + 2) +
  MachineInvokeClear.time C
    (Function.update
      (ExactParameterMachineFrame.terminalBank M C.machine S bits T)
      C.target result) + 3

/-- One literal program copies a preserved source into a checked embedded machine,
executes that machine, copies its answer to a fresh target, and physically
clears every embedded stack. The final equality covers the entire ambient bank. -/
theorem invoke_run {M : BitMachine.Machine} {N : ℕ} (C : Slots M N)
    (S : StackN N → List Bool) (bits result : List Bool) (T : ℕ)
    (hsource : S C.source = bits)
    (htarget : S C.target = [])
    (hscratch : S C.scratch = [])
    (hblank : ∀ k, S (C.machine k) = [])
    (hM : M.OutputsWithin bits result T) :
    ∃ u ≤ timeBound C S bits result T,
      ((advance (program C))^[u])
        (⟨some (start C), control C, S⟩ :
          TM2.Cfg (fun _ : StackN N => Bool) _ _) =
        ⟨none, control C, Function.update S C.target result⟩ := by
  let I := Function.update S (C.machine M.input) bits
  let U := ExactParameterMachineFrame.terminalBank M C.machine S bits T
  let V := Function.update U C.target result
  obtain ⟨u0, hu0, h0⟩ := input_run C S bits hsource hblank hscratch
  have h1 := machine_run C S bits result T hblank hM
  obtain ⟨u2, hu2, h2⟩ := output_run C S bits result T htarget hscratch hM
  have h3 := MachineInvokeClear.run C V
  rw [cleanup_eq C S bits result T hblank] at h3
  obtain ⟨u01, hu01, h01⟩ := BitMachineRawSequence.runs
    (inputProgram C) (machineProgram C) .scan M.start
    none none M.initial (M.run T (M.init bits)).var
    S I U u0 T
    (by simpa only [I] using h0)
    (by simpa only [I, U] using h1)
  obtain ⟨u012, hu012, h012⟩ := BitMachineRawSequence.runs
    (p01 C) (outputProgram C)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    BitMachineCopy.Label.scan
    (none, M.initial) (none, (M.run T (M.init bits)).var)
    none none
    S U V u01 u2
    (by simpa only [p01] using h01)
    (by simpa only [U, V] using h2)
  obtain ⟨u, hu, hr⟩ := BitMachineRawSequence.runs
    (p012 C) (MachineInvokeClear.program C)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
    (MachineInvokeClear.clearLabel M.stackCount 0)
    ((none, M.initial), none)
    ((none, M.initial), none)
    ((), none) ((), none)
    S V (Function.update S C.target result)
    u012 (MachineInvokeClear.time C V)
    (by simpa only [p012] using h012)
    (by simpa only [V] using h3)
  have hbound : u ≤ (2 * bits.length + 2) + T +
      (2 * result.length + 2) + MachineInvokeClear.time C V + 3 := by
    omega
  exact ⟨u, by simpa only [timeBound, V] using hbound,
    by simpa only [program, start, control] using hr⟩

/-- The cleanup cost is bounded by the length growth of the invoked literal
machine; no final scratch contents are supplied as an input. -/
theorem clear_time_le {M : BitMachine.Machine} {N : ℕ} (C : Slots M N)
    (S : StackN N → List Bool) (bits result : List Bool) (T : ℕ) :
    MachineInvokeClear.time C
      (Function.update
        (ExactParameterMachineFrame.terminalBank M C.machine S bits T)
        C.target result) ≤
      M.stackCount * (bits.length + T * M.pushBound) +
        M.stackCount + 2 := by
  have hlen (i : Fin M.stackCount) :
      ((Function.update
        (ExactParameterMachineFrame.terminalBank M C.machine S bits T)
        C.target result) (C.machine i)).length ≤
        bits.length + T * M.pushBound := by
    have hne : C.machine i ≠ C.target := (C.target_machine i).symm
    rw [Function.update_of_ne hne]
    rw [ExactParameterMachineFrame.terminalBank, bank_at]
    have hr := BitMachine.run_length M (M.init bits) i T
    have hi : ((M.init bits).stk i).length ≤ bits.length := by
      simp only [BitMachine.Machine.init]
      split <;> simp
    exact hr.trans (Nat.add_le_add_right hi _)
  unfold MachineInvokeClear.time
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun i (_ : i ∈ Finset.univ) => hlen i)
  simpa only [Finset.sum_const_zero, Finset.sum_const, Finset.card_fin,
    nsmul_eq_mul] using Nat.add_le_add_right hsum (M.stackCount + 2)

def uniformBound (M : BitMachine.Machine) (bits : List Bool) (T : ℕ) : ℕ :=
  (2 * bits.length + 2) + T +
  (2 * (bits.length + T * M.pushBound) + 2) +
  (M.stackCount * (bits.length + T * M.pushBound) +
    M.stackCount + 2) + 3

theorem invoke_run_uniform {M : BitMachine.Machine} {N : ℕ}
    (C : Slots M N) (S : StackN N → List Bool)
    (bits result : List Bool) (T : ℕ)
    (hsource : S C.source = bits)
    (htarget : S C.target = [])
    (hscratch : S C.scratch = [])
    (hblank : ∀ k, S (C.machine k) = [])
    (hM : M.OutputsWithin bits result T) :
    ∃ u ≤ uniformBound M bits T,
      ((advance (program C))^[u])
        (⟨some (start C), control C, S⟩ :
          TM2.Cfg (fun _ : StackN N => Bool) _ _) =
        ⟨none, control C, Function.update S C.target result⟩ := by
  obtain ⟨u, hu, hr⟩ := invoke_run C S bits result T
    hsource htarget hscratch hblank hM
  have houtput := BitMachine.output_length_bound M hM
  have hclear := clear_time_le C S bits result T
  refine ⟨u, ?_, hr⟩
  unfold timeBound at hu
  unfold uniformBound
  omega

#print axioms cleanup_eq
#print axioms invoke_run
#print axioms invoke_run_uniform

end CurrentAdditive.MinimumRatioContext.MachineInvokeFull
