import EthInapproximability.CurrentPaper.BitMachineIteration
import EthInapproximability.CurrentPaper.BinarySuccessorMachine

/-!
# Counting a unary word into a canonical binary word

Source: frozen v8 `B-effectivity-details.tex`, the compact prime descriptor.
The loop is the already proved physical iteration controller, instantiated
with the actual variable-width binary-successor machine. Its input is the
unary fuel stack; the evolving binary word begins empty. All intermediate
lengths, subroutine cleanup and output movement are charged.
-/

namespace EthInapproximability.CurrentPaper.UnaryBinaryEncoding

open Turing BitMachineEncoding BitMachineIteration

noncomputable abbrev counter := BinarySuccessorMachine.machine

theorem successor_length (q : List Bool) :
    (BinarySuccessorMachine.successor q).length ≤ q.length+1 := by
  induction q with
  | nil => rfl
  | cons b q ih => cases b <;> simp only [BinarySuccessorMachine.successor, List.length_cons] <;> omega

theorem bits_length_le (n : ℕ) : n.bits.length ≤ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [← BinarySuccessorMachine.successor_bits]
      exact (successor_length n.bits).trans (Nat.add_le_add_right ih 1)

noncomputable def machine : BitMachine.Machine :=
  ofFinite (Sum.inr (0 : Fin 2) : Stack counter) (.inl counter.input) (.inr .testFuel)
    (counter.initial,none) (program counter)

theorem initial_cfg (input : List Bool) :
    rawInit (Sum.inr (0 : Fin 2) : Stack counter) (Sum.inr .testFuel : Label counter)
      (counter.initial,none) input = ready counter [] input := by
  simp only [rawInit, ready, adminCfg, BitMachine.Machine.init]
  congr 1
  funext j
  cases j with
  | inl j => simp
  | inr j => fin_cases j <;> rfl

theorem raw_outputs (input : List Bool) :
    machine.OutputsWithin input input.length.bits
      (input.length*roundBound counter input.length (2*input.length+2)+1) := by
  obtain ⟨t,ht,hh,ho⟩ := iteration_output counter (fun n => n.bits) input input.length
    (2*input.length+2) (by
      intro j hj
      have h := BinarySuccessorMachine.outputs_all j.bits
      rw [BinarySuccessorMachine.successor_bits] at h
      apply BitMachine.outputsWithin_mono _ h
      have hlen := bits_length_le j
      omega) (by intro j hj; exact (bits_length_le j).trans (by omega))
  apply outputsWithin_of_raw_run (.inr 0) (.inl counter.input) (.inr .testFuel)
    (counter.initial,none) (program counter) input input.length.bits t _ ht
  · simpa only [initial_cfg, show (0 : ℕ).bits=[] by rfl, run] using hh
  · simpa only [initial_cfg, show (0 : ℕ).bits=[] by rfl, run] using ho

noncomputable def coefficient : ℕ :=
  2+(counter.stackCount+2)*(1+2*counter.pushBound)+counter.stackCount+5

theorem time_bound (n : ℕ) : n*roundBound counter n (2*n+2)+1 ≤ coefficient*(n+1)^2 := by
  have hr : roundBound counter n (2*n+2) ≤ coefficient*(n+1) := by
    have he : coefficient*(n+1) = roundBound counter n (2*n+2)+
        n*(counter.stackCount+5)+counter.stackCount+3 := by
      dsimp [roundBound, coefficient]
      ring
    omega
  have hc : 1 ≤ coefficient := by dsimp [coefficient]; omega
  have hm := Nat.mul_le_mul_left n hr
  have hp := Nat.mul_le_mul_left coefficient (show 1 ≤ n+1 by omega)
  nlinarith

theorem outputs (input : List Bool) :
    machine.OutputsWithin input input.length.bits (coefficient*(input.length+1)^2) :=
  BitMachine.outputsWithin_mono _ (raw_outputs input) (time_bound input.length)

theorem polytime : BitMachine.Polytime (fun input => input.length.bits) :=
  ⟨machine,coefficient,2,outputs⟩

end EthInapproximability.CurrentPaper.UnaryBinaryEncoding
