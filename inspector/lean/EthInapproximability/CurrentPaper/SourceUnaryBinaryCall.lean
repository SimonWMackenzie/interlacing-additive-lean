import EthInapproximability.CurrentPaper.UnaryBinaryEncoding

/-!
# Full-bank endpoint of unary-to-binary conversion

Source: frozen v8 `06-eth.tex`, actual variable-label writing. Unlike an
output-only statement, this exposes every local stack after the conversion:
the binary result occupies the counter input register and all other local
stacks are empty. Foreign stacks can therefore be framed by the proved
selected-stack compiler without assuming cleanup.
-/

namespace EthInapproximability.CurrentPaper.SourceUnaryBinaryCall

open Turing BitMachineEncoding BitMachineIteration

noncomputable abbrev counter := UnaryBinaryEncoding.counter

theorem raw_run (input : List Bool) :
    ∃ t ≤ UnaryBinaryEncoding.coefficient * (input.length + 1) ^ 2,
      run counter t (ready counter [] input) = finished counter input.length.bits := by
  obtain ⟨t, ht, hr⟩ := iteration_run counter (fun j => j.bits) input input.length
    (2 * input.length + 2) (by
      intro j hj
      have h := BinarySuccessorMachine.outputs_all j.bits
      rw [BinarySuccessorMachine.successor_bits] at h
      apply BitMachine.outputsWithin_mono _ h
      have hlen := UnaryBinaryEncoding.bits_length_le j
      omega) (by
      intro j hj
      exact (UnaryBinaryEncoding.bits_length_le j).trans (by omega))
  exact ⟨t, ht.trans (UnaryBinaryEncoding.time_bound input.length), hr⟩

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

end EthInapproximability.CurrentPaper.SourceUnaryBinaryCall
