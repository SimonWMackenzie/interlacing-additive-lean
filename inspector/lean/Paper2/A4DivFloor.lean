import EthInapproximability.CurrentPaper.ExactParameterMachineSecondOrder
import EthInapproximability.CurrentPaper.EncodedComplexity

/-!
# Unit 4 (Paper A), N-4 (1b): one fixed FLOOR-division machine on a six-bank packet

Owner lane `owner:a-unit4-shell-4` (private, 26 September 2026).

The admitted literal unary divider `MatrixUnaryDivision.program` (repeated counted subtraction
on Boolean stacks; `division_total_run`, every `n`, `m`, including `m = 0`) is called through
the admitted generic packet wrapper `BitMachineBankWrapper.machine` on the admitted packet
`ExactParameterMachineSecondOrder.packedInput n m` (six fields: `1^n`, `1^m`, four empty), and
the quotient field `4` is projected by the admitted `BankFieldProjection.machine 4`, the handoff
charged by `BitMachineComposition.composition_outputsWithin`. This mirrors the admitted
`ExactParameterMachineSecondOrder.ceilMachine` without the ceiling step. **No ledger row is
closed.**
-/

namespace Paper2.Unit4Shell.DivFloor

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

/-- The terminal bank of the divider. -/
def outBank (n m : ℕ) : BitMachineBankCodec.Bank 6 :=
  (MatrixUnaryDivision.cfg none false [] (List.replicate m true) []
    (List.replicate (n % m) true) (List.replicate (n / m) true) []).stk

/-- The divider called on a packed six-bank input. -/
noncomputable def divMachine : BitMachine.Machine :=
  BitMachineBankWrapper.machine MatrixUnaryDivision.program MatrixUnaryDivision.Label.start false

/-- THE fixed floor-division machine. -/
noncomputable def machine : BitMachine.Machine :=
  BitMachineComposition.composition divMachine (BankFieldProjection.machine (4 : Fin 6))

theorem packedInput_eq (n m : ℕ) :
    ExactParameterMachineSecondOrder.packedInput n m =
      EncodedComplexity.pair (List.replicate n true)
        (EncodedComplexity.pair (List.replicate m true) [false, false, false, false]) := by
  simp [ExactParameterMachineSecondOrder.packedInput, BitMachineBankCodec.encode_eq_list,
    List.ofFn_succ, ExactParameterMachineCeil.inputBank, MatrixUnaryDivision.cfg,
    EncodedComplexity.pair, EncodedCommunication.field]

theorem packedInput_length (n m : ℕ) :
    (ExactParameterMachineSecondOrder.packedInput n m).length = 2 * n + 2 * m + 6 := by
  rw [packedInput_eq]
  simp [EncodedComplexity.pair_length, EncodedCommunication.field_length]
  omega

theorem outBank_length (n m : ℕ) :
    (BitMachineBankCodec.encode (outBank n m)).length =
      2 * m + 2 * (n % m) + 2 * (n / m) + 6 := by
  simp [outBank, BitMachineBankCodec.encode_eq_list, List.ofFn_succ, MatrixUnaryDivision.cfg,
    EncodedCommunication.field_length]
  omega

theorem div_outputs (n m : ℕ) :
    divMachine.OutputsWithin (ExactParameterMachineSecondOrder.packedInput n m)
      (BitMachineBankCodec.encode (outBank n m))
      ((2 * 6 + 1) * ((ExactParameterMachineSecondOrder.packedInput n m).length + 1) +
        MatrixUnaryDivision.totalTime n m +
        2 * (BitMachineBankCodec.encode (outBank n m)).length + 4) := by
  let F : BitMachineBankCodec.Bank 6 → BitMachineBankCodec.Bank 6 := fun _ => outBank n m
  have hlocal : ∀ S, BitMachineBankCodec.decode 6
      (ExactParameterMachineSecondOrder.packedInput n m) = some S →
      ∃ (t : ℕ) (c : Turing.TM2.Cfg (fun _ : Fin 6 => Bool) MatrixUnaryDivision.Label Bool),
        t ≤ MatrixUnaryDivision.totalTime n m ∧
        ((BitMachineEncoding.advance MatrixUnaryDivision.program)^[t])
          ⟨some MatrixUnaryDivision.Label.start, false, S⟩ = c ∧ c.l = none ∧ c.stk = F S := by
    intro S hS
    have hdecode : S = ExactParameterMachineCeil.inputBank n m := by
      simpa only [ExactParameterMachineSecondOrder.packedInput,
        BitMachineBankCodec.decode_encode, Option.some.injEq] using hS.symm
    subst S
    refine ⟨MatrixUnaryDivision.totalTime n m, MatrixUnaryDivision.cfg none false []
      (List.replicate m true) [] (List.replicate (n % m) true) (List.replicate (n / m) true) [],
      le_rfl, ?_, rfl, rfl⟩
    simpa [MatrixUnaryDivision.run, ExactParameterMachineCeil.inputBank] using
      MatrixUnaryDivision.division_total_run n m
  have hsize : ∀ S, BitMachineBankCodec.decode 6
      (ExactParameterMachineSecondOrder.packedInput n m) = some S →
      (BitMachineBankCodec.encode (F S)).length ≤
        (BitMachineBankCodec.encode (outBank n m)).length := fun _ _ => le_rfl
  have h := BitMachineBankWrapper.outputs MatrixUnaryDivision.program
    MatrixUnaryDivision.Label.start false F (ExactParameterMachineSecondOrder.packedInput n m)
    (MatrixUnaryDivision.totalTime n m) (BitMachineBankCodec.encode (outBank n m)).length
    hlocal hsize
  simpa only [divMachine, BitMachineBankWrapper.result, ExactParameterMachineSecondOrder.packedInput,
    BitMachineBankCodec.decode_encode, F] using h

/-- **Floor division.** ONE fixed machine: `packedInput n m ↦ 1^(n / m)` (Lean's `/`, so
`m = 0` gives `0`), within `114 n + 69 m + 237` steps. Does not close a ledger row. -/
theorem outputs (n m : ℕ) :
    machine.OutputsWithin (ExactParameterMachineSecondOrder.packedInput n m)
      (List.replicate (n / m) true) (114 * n + 69 * m + 237) := by
  have h1 := div_outputs n m
  have h2 := BankFieldProjection.outputs (4 : Fin 6) (BitMachineBankCodec.encode (outBank n m))
  have hres : BankFieldProjection.result (4 : Fin 6) (BitMachineBankCodec.encode (outBank n m)) =
      List.replicate (n / m) true := by
    simp [outBank, MatrixUnaryDivision.cfg]
  rw [hres] at h2
  have hC := BitMachineComposition.composition_outputsWithin divMachine
    (BankFieldProjection.machine (4 : Fin 6)) h1 h2
  apply BitMachine.outputsWithin_mono _ hC
  have hin := packedInput_length n m
  have hout := outBank_length n m
  have ht := MatrixUnaryDivision.totalTime_bound n m
  have hmod : n % m ≤ n := Nat.mod_le n m
  have hdiv : n / m ≤ n := Nat.div_le_self n m
  rw [hin, hout]
  omega

#print axioms div_outputs
#print axioms outputs

end Paper2.Unit4Shell.DivFloor
