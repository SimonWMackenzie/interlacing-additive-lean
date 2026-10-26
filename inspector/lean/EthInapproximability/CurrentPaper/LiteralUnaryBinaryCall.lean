import EthInapproximability.CurrentPaper.BinarySuccessorLiteral
import EthInapproximability.CurrentPaper.UnaryBinaryEncoding

/-! # Computably indexed unary-to-binary counter

The same physical iteration proof is instantiated at the explicit Fin2/Fin3
successor, with no chosen finite equivalence in the controller. The full-bank
endpoint records cleanup and the exact destination register.
-/

namespace EthInapproximability.CurrentPaper.LiteralUnaryBinaryCall

open Turing BitMachineEncoding BitMachineIteration

def counter := BinarySuccessorLiteral.machine

def coefficient : ℕ :=
  2+(counter.stackCount+2)*(1+2*counter.pushBound)+counter.stackCount+5

theorem time_bound (n : ℕ) :
    n*roundBound counter n (2*n+2)+1 ≤ coefficient*(n+1)^2 := by
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

theorem raw_run (input : List Bool) :
    ∃ t ≤ coefficient * (input.length + 1)^2,
      run counter t (ready counter [] input) =
        finished counter input.length.bits := by
  obtain ⟨t, ht, hr⟩ := iteration_run counter (fun j => j.bits) input input.length
    (2 * input.length + 2) (by
      intro j hj
      have h := BinarySuccessorLiteral.outputs_all j.bits
      rw [BinarySuccessorMachine.successor_bits] at h
      apply BitMachine.outputsWithin_mono _ h
      have hlen := UnaryBinaryEncoding.bits_length_le j
      omega) (by
      intro j hj
      exact (UnaryBinaryEncoding.bits_length_le j).trans (by omega))
  exact ⟨t, ht.trans (time_bound input.length), hr⟩

theorem initial_bank (input : List Bool) :
    (ready counter [] input).stk =
      fun k : Stack counter => if k = .inr 0 then input else [] := by
  funext k
  cases k with
  | inl k => simp [ready, adminCfg, BitMachine.Machine.init]
  | inr k => fin_cases k <;> rfl

theorem final_bank (word : List Bool) :
    (finished counter word).stk =
      fun k : Stack counter => if k = .inl counter.input then word else [] := by
  funext k
  cases k with
  | inl k => simp [finished, BitMachine.Machine.init]
  | inr k => fin_cases k <;> rfl

end EthInapproximability.CurrentPaper.LiteralUnaryBinaryCall
