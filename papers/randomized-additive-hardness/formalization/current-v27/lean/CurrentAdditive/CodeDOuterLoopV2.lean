import CurrentAdditive.CodeDStageContractV2
import EthInapproximability.CurrentPaper.BitMachineIteration

/-!
The physical outer-loop boundary for fixed D.  `BitMachineIteration.program`
is an actual finite Boolean-stack program with a literal unary fuel stack,
two charged data transfers, and cleanup after each call.  The theorem below
specifies the exact per-round packet that a still-to-be-built physical stage
machine must produce.  Its `OutputsWithin` hypotheses are open obligations,
not a claimed Code D implementation or a polynomial clock certificate.
-/

namespace CurrentAdditive.CodeDOuterLoopV2

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineBankCodec
open EthInapproximability.CurrentPaper.BitMachineIteration
open CodeDCodec CodeDTargetV2

def stateAt (D : Nat) (alphabet : Array (Nat × ℚ)) (j : Nat) : List Bool :=
  encode (codePacket D j (alphabetBytes alphabet)
    ((targetBytes D alphabet j).getD []) [] [] [])

theorem stateAt_decodes (D : Nat) (alphabet : Array (Nat × ℚ))
    (j : Nat) :
    decode 12 (stateAt D alphabet j) =
      some (codePacket D j (alphabetBytes alphabet)
        ((targetBytes D alphabet j).getD []) [] [] []) := by
  simp [stateAt]

theorem stateAt_has_actual_source (D : Nat)
    (alphabet : Array (Nat × ℚ))
    (halphabet : SequentialSourceCode.SourcePositive alphabet)
    (j : Nat) :
    ∃ out, (decode 12 (stateAt D alphabet j)).map (fun S => S 3) =
        some (CodeDCanonicalSourceV2.encodedSource out) ∧
      SequentialSourceCode.sequentialMaterialized D alphabet j = some out := by
  obtain ⟨out, hout, _⟩ :=
    SequentialSourceCode.sequentialMaterialized_total D alphabet halphabet j
  refine ⟨out, ?_, hout⟩
  simp [stateAt_decodes, targetBytes, hout]

theorem conditional_outer_run (M : BitMachine.Machine)
    (D : Nat) (alphabet : Array (Nat × ℚ))
    (q L T : Nat)
    (hstep : ∀ j < q,
      M.OutputsWithin (stateAt D alphabet j) (stateAt D alphabet (j + 1)) T)
    (hlen : ∀ j < q, (stateAt D alphabet j).length ≤ L) :
    ∃ t ≤ q * roundBound M L T + 1,
      run M t (ready M (stateAt D alphabet 0) (List.replicate q true)) =
        finished M (stateAt D alphabet q) := by
  simpa using iteration_run M (stateAt D alphabet)
    (List.replicate q true) L T
      (by intro j hj; exact hstep j (by simpa using hj))
      (by intro j hj; exact hlen j (by simpa using hj))

#print axioms stateAt_has_actual_source
#print axioms conditional_outer_run

end CurrentAdditive.CodeDOuterLoopV2
