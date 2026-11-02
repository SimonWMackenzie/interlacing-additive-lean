import EthInapproximability.CurrentPaper.ExactParameterMachineCeil
import EthInapproximability.CurrentPaper.ExactParameterMachineLog
import EthInapproximability.CurrentPaper.MatrixUnaryPower
import EthInapproximability.CurrentPaper.BitMachineBankWrapper
import EthInapproximability.CurrentPaper.BitMachineBankSerialize
import EthInapproximability.CurrentPaper.BankFieldProjection
import EthInapproximability.CurrentPaper.BitMachineComposition
import EthInapproximability.CurrentPaper.ExactParameters

/-!
# Physical second-order sampler parameter from a prepared bank packet

The input is the canonical six-field packet whose first two Boolean banks
contain unary `n` and positive unary `m`. The fixed program parses it,
physically computes the ceiling quotient, projects bank 4, counts its
ceiling logarithm, and constructs the unary power of two. Each between-stage
copy/reversal is charged by `BitMachineComposition`.

The preceding source compiler must still *write* this canonical packet from
its `3*r` and `s` banks. This module does not count that preparation as free.
-/

namespace EthInapproximability.CurrentPaper.ExactParameterMachineSecondOrder

open BitMachineEncoding BitMachineComposition

def packedInput (n m : ℕ) : List Bool :=
  BitMachineBankCodec.encode (ExactParameterMachineCeil.inputBank n m)

def packedOutput (n m : ℕ) : List Bool :=
  BitMachineBankCodec.encode (ExactParameterMachineCeil.outputBank n m)

/-- Physical bank-to-packet preparation from six preloaded stacks. The first
two contain unary `n,m`; the other four are empty. This consumes the six
word banks but preserves the independent source stack and clears the saved
reversal stack. It does not construct the preloaded bank from the edge count. -/
theorem prepare_packet_run (n m : ℕ) (source : List Bool) :
    ∃ (t : ℕ) (S' : BitMachineBankSerialize.Bank 6),
      t ≤ 2 * (packedInput n m).length + 2 ∧
      BitMachineBankSerialize.run t
        (BitMachineBankSerialize.cfg (some (.emit 0)) none
          (ExactParameterMachineCeil.inputBank n m) source [] []) =
        BitMachineBankSerialize.cfg none none S' source [] (packedInput n m) := by
  obtain ⟨t, S', ht, hr⟩ := BitMachineBankSerialize.serialize
    (ExactParameterMachineCeil.inputBank n m) source []
  have he : BitMachineBankSerialize.encode
      (List.ofFn (ExactParameterMachineCeil.inputBank n m)) = packedInput n m := by
    unfold packedInput
    rw [BitMachineBankCodec.encode_eq_list]
    rfl
  exact ⟨t, S', by simpa only [he] using ht,
    by simpa only [he, List.append_nil] using hr⟩

noncomputable def ceilMachine : BitMachine.Machine :=
  BitMachineBankWrapper.machine ExactParameterMachineCeil.program
    (BitMachineRawSequence.leftLabel MatrixUnaryDivision.Label.start) (false, false)

def ceilBudget (n m : ℕ) : ℕ :=
  13 * ((packedInput n m).length + 1) +
    (MatrixUnaryDivision.totalTime n m + 2) +
    2 * (packedOutput n m).length + 4

/-- The quotient is computed on physical unary stacks, then the complete
six-bank terminal configuration is serialized. -/
theorem ceil_outputs (n m : ℕ) :
    ceilMachine.OutputsWithin (packedInput n m) (packedOutput n m)
      (ceilBudget n m) := by
  let F : BitMachineBankCodec.Bank 6 → BitMachineBankCodec.Bank 6 :=
    fun _ => ExactParameterMachineCeil.outputBank n m
  have hlocal : ∀ S, BitMachineBankCodec.decode 6 (packedInput n m) = some S →
      ∃ (t : ℕ) (c : Turing.TM2.Cfg (fun _ : Fin 6 => Bool)
        (BitMachineRawSequence.Label MatrixUnaryDivision.Label (Fin 1))
        (BitMachineRawSequence.Control Bool Bool)),
        t ≤ MatrixUnaryDivision.totalTime n m + 2 ∧
        ((BitMachineEncoding.advance ExactParameterMachineCeil.program)^[t])
          ⟨some (BitMachineRawSequence.leftLabel MatrixUnaryDivision.Label.start),
            (false, false), S⟩ = c ∧ c.l = none ∧ c.stk = F S := by
    intro S hS
    have hdecode : S = ExactParameterMachineCeil.inputBank n m := by
      simpa only [packedInput, BitMachineBankCodec.decode_encode,
        Option.some.injEq] using hS.symm
    subst S
    obtain ⟨t, ht, hr⟩ := ExactParameterMachineCeil.run_quotient n m
    refine ⟨t, ⟨none, (false, n % m ≠ 0),
      ExactParameterMachineCeil.outputBank n m⟩, ht, hr, rfl, rfl⟩
  have hsize : ∀ S, BitMachineBankCodec.decode 6 (packedInput n m) = some S →
      (BitMachineBankCodec.encode (F S)).length ≤ (packedOutput n m).length := by
    intro S _
    exact le_refl _
  have h := BitMachineBankWrapper.outputs ExactParameterMachineCeil.program
    (BitMachineRawSequence.leftLabel MatrixUnaryDivision.Label.start)
    (false, false) F (packedInput n m)
    (MatrixUnaryDivision.totalTime n m + 2) (packedOutput n m).length
    hlocal hsize
  simpa only [ceilMachine, ceilBudget, packedOutput,
    BitMachineBankWrapper.result, packedInput,
    BitMachineBankCodec.decode_encode, F] using h

noncomputable def machine : BitMachine.Machine :=
  composition
    (composition
      (composition ceilMachine (BankFieldProjection.machine (4 : Fin 6)))
      ExactParameterMachineLog.machine)
    MatrixUnaryPower.machine

noncomputable def budget (n m : ℕ) : ℕ :=
  let packet := packedOutput n m
  let q := n ⌈/⌉ m
  let e := Nat.clog 2 q
  ceilBudget n m + 2 * packet.length + 2 +
    ((2 * 6 + 4) * (packet.length + 1)) +
    2 * q + 2 +
    ((UnaryBinaryEncoding.coefficient + 6) * (q + 1) ^ 2) +
    2 * e + 2 + 16 * 2 ^ e

/-- A fixed single-input machine returns the exact unary least-power-of-two
second order from a canonical packet of two prepared unary operands. -/
theorem outputs (n m : ℕ) (hm : 0 < m) :
    machine.OutputsWithin (packedInput n m)
      (List.replicate (2 ^ Nat.clog 2 (n ⌈/⌉ m)) true) (budget n m) := by
  let q := n ⌈/⌉ m
  let e := Nat.clog 2 q
  have hceil := ceil_outputs n m
  have hproj := BankFieldProjection.outputs (4 : Fin 6) (packedOutput n m)
  have hword : BankFieldProjection.result (4 : Fin 6) (packedOutput n m) =
      List.replicate q true := by
    simp [BankFieldProjection.result, packedOutput,
      ExactParameterMachineCeil.output_ceil n m hm, q]
  rw [hword] at hproj
  have hlog := ExactParameterMachineLog.outputs q
  have hpower := MatrixUnaryPower.outputs (List.replicate e true)
  have hfirst := composition_outputsWithin ceilMachine
    (BankFieldProjection.machine (4 : Fin 6)) hceil hproj
  have hsecond := composition_outputsWithin
    (composition ceilMachine (BankFieldProjection.machine (4 : Fin 6)))
    ExactParameterMachineLog.machine hfirst hlog
  have hthird := composition_outputsWithin
    (composition (composition ceilMachine (BankFieldProjection.machine (4 : Fin 6)))
      ExactParameterMachineLog.machine)
    MatrixUnaryPower.machine hsecond hpower
  simpa only [machine, budget, List.length_replicate, q, e] using hthird

/-- The manuscript's `t₂` call site, without unfolding the large padding
cutoff or claiming that the input packet has already been prepared. -/
theorem source_outputs (s : ℕ) (hs : 0 < s) :
    machine.OutputsWithin
      (packedInput (3 * ExactParameters.dimensionLog s) s)
      (List.replicate (ExactParameters.secondOrder s) true)
      (budget (3 * ExactParameters.dimensionLog s) s) := by
  simpa only [ExactParameters.secondOrder, ExactParameters.secondExponent,
    ExactParameters.secondTarget] using
    outputs (3 * ExactParameters.dimensionLog s) s hs

theorem padded_source_outputs (edges : ℕ) :
    let s := ExactSourcePadding.paddedExponent edges
    machine.OutputsWithin
      (packedInput (3 * ExactParameters.dimensionLog s) s)
      (List.replicate (ExactParameters.secondOrder s) true)
      (budget (3 * ExactParameters.dimensionLog s) s) := by
  have hs : 0 < ExactSourcePadding.paddedExponent edges := by
    have hc := ExactSourcePadding.cutoff edges
    omega
  exact source_outputs _ hs

end EthInapproximability.CurrentPaper.ExactParameterMachineSecondOrder
