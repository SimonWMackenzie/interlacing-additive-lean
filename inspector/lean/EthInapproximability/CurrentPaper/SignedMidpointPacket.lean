import EthInapproximability.CurrentPaper.SignedMidpointSemantics
import EthInapproximability.CurrentPaper.BitMachineBankWrapper
import EthInapproximability.CurrentPaper.BankFieldProjection
import EthInapproximability.CurrentPaper.BitMachineComposition

/-!
# Ordinary-input packet for the signed midpoint comparator

Source: frozen v8 `06-eth.tex`, actual final midpoint comparison. A canonical
five-field packet physically contains the approximation's signed output and
the unary cap on separate fields. The generic bank wrapper parses the whole
packet, runs the fixed comparator program, and serializes its final bank;
the fixed-field projector then extracts its one-bit decision. The pointwise
theorem below applies to canonical packets. It does not yet prove an
all-input polynomial-time ordinary comparator or construct the cap `2Y+k`.
-/

namespace EthInapproximability.CurrentPaper.SignedMidpointPacket

open Turing BitMachineEncoding

def inputBank (answer cap : List Bool) : Fin 5 → List Bool :=
  ![answer, cap, [], [], []]

def packet (answer cap : List Bool) : List Bool :=
  BitMachineBankCodec.encode (inputBank answer cap)

def start : SignedMidpointMachine.Label := .inl .sign
def initial : SignedMidpointMachine.Control :=
  (none, (none, false), none, none)

def finalBank (S : Fin 5 → List Bool) : Fin 5 → List Bool :=
  (SignedMidpointMachine.run (SignedMidpointSemantics.fuel (S 0) (S 1))
    (⟨some start, initial, S⟩ : SignedMidpointMachine.Config)).stk

def finalPacket (answer cap : List Bool) : List Bool :=
  BitMachineBankCodec.encode (finalBank (inputBank answer cap))

noncomputable def rawMachine : BitMachine.Machine :=
  ofFinite (0 : Fin 5) 4 start initial SignedMidpointMachine.program

theorem finalBank_word_length (S : Fin 5 → List Bool) (j : Fin 5) :
    ((finalBank S) j).length ≤ (S j).length +
      SignedMidpointSemantics.fuel (S 0) (S 1) * rawMachine.pushBound := by
  let c : SignedMidpointMachine.Config := ⟨some start, initial, S⟩
  let ek := Fintype.equivFin (Fin 5)
  let el := Fintype.equivFin SignedMidpointMachine.Label
  let ev := Fintype.equivFin SignedMidpointMachine.Control
  have h := BitMachine.run_length rawMachine
    (renameCfg ek el ev c) (ek j) (SignedMidpointSemantics.fuel (S 0) (S 1))
  have hr := ofFinite_run (0 : Fin 5) 4 start initial SignedMidpointMachine.program c
    (SignedMidpointSemantics.fuel (S 0) (S 1))
  change (rawMachine.run _ (renameCfg ek el ev c)) = _ at hr
  rw [hr] at h
  simp only [renameCfg] at h
  have hj : ek.symm (ek j) = j := ek.symm_apply_apply j
  change ((finalBank S) (ek.symm (ek j))).length ≤
    (S (ek.symm (ek j))).length +
      SignedMidpointSemantics.fuel (S 0) (S 1) * rawMachine.pushBound at h
  rw [hj] at h
  exact h

theorem finalPacket_length (answer cap : List Bool) :
    (finalPacket answer cap).length ≤
      (packet answer cap).length +
        10 * SignedMidpointSemantics.fuel answer cap * rawMachine.pushBound := by
  let S := inputBank answer cap
  have hs : (∑ j : Fin 5, ((finalBank S) j).length) ≤
      ∑ j : Fin 5, ((S j).length +
        SignedMidpointSemantics.fuel (S 0) (S 1) * rawMachine.pushBound) := by
    apply Finset.sum_le_sum
    intro j _
    exact finalBank_word_length S j
  simp only [Fin.sum_univ_five] at hs
  simp only [finalPacket, packet, BitMachineBankCodec.encode_length]
  dsimp [S, inputBank] at hs ⊢
  simp only [Fin.sum_univ_five] at ⊢
  simp only [Nat.mul_assoc] at ⊢
  simp at hs ⊢
  omega

theorem fuel_le_packet (answer cap : List Bool) :
    SignedMidpointSemantics.fuel answer cap ≤
      20 * ((packet answer cap).length + 1) ^ 2 + 2 := by
  have ha := BitMachineBankCodec.word_length_le_encode (inputBank answer cap) (0 : Fin 5)
  have hc := BitMachineBankCodec.word_length_le_encode (inputBank answer cap) (1 : Fin 5)
  change answer.length ≤ (packet answer cap).length at ha
  change cap.length ≤ (packet answer cap).length at hc
  have hm := Nat.mul_le_mul (Nat.succ_le_succ ha) (Nat.succ_le_succ hc)
  unfold SignedMidpointSemantics.fuel
  nlinarith

noncomputable def machine : BitMachine.Machine :=
  BitMachineBankWrapper.machine SignedMidpointMachine.program start initial

theorem final_decision (a : ℤ) (cap : List Bool) :
    BankFieldProjection.result (4 : Fin 5)
      (finalPacket (EncodedETHTail.encodeInteger a) cap) =
        [decide (2 * a < (cap.length : ℤ))] := by
  rw [finalPacket, BankFieldProjection.result_encode]
  exact SignedMidpointSemantics.result_encodeInteger a cap

/-- An ordinary finite Boolean-stack machine actually parses, runs and
serializes the canonical packet. The displayed time charges both framing
directions and the complete five-stack comparator run. -/
theorem outputs_packet (a : ℤ) (cap : List Bool) :
    machine.OutputsWithin
      (packet (EncodedETHTail.encodeInteger a) cap)
      (finalPacket (EncodedETHTail.encodeInteger a) cap)
      ((2 * 5 + 1) * ((packet (EncodedETHTail.encodeInteger a) cap).length + 1) +
        SignedMidpointSemantics.fuel (EncodedETHTail.encodeInteger a) cap +
        2 * (finalPacket (EncodedETHTail.encodeInteger a) cap).length + 4) := by
  let answer := EncodedETHTail.encodeInteger a
  let S := inputBank answer cap
  let input := packet answer cap
  let F := finalBank
  have hd : BitMachineBankCodec.decode 5 input = some S := by
    exact BitMachineBankCodec.decode_encode S
  have hr : BitMachineBankWrapper.result F input = finalPacket answer cap := by
    simp only [BitMachineBankWrapper.result, hd, finalPacket, F, S]
  rw [← hr]
  change (BitMachineBankWrapper.machine SignedMidpointMachine.program start initial).OutputsWithin
    input (BitMachineBankWrapper.result F input)
    ((2 * 5 + 1) * (input.length + 1) +
      SignedMidpointSemantics.fuel answer cap +
      2 * (BitMachineBankWrapper.result F input).length + 4)
  apply BitMachineBankWrapper.outputs SignedMidpointMachine.program start initial F input
    (SignedMidpointSemantics.fuel answer cap)
    (BitMachineBankWrapper.result F input).length
  · intro T hT
    have he : T = S := by rw [hd] at hT; exact Option.some.inj hT.symm
    subst T
    let c := SignedMidpointMachine.run (SignedMidpointSemantics.fuel answer cap)
      (⟨some start, initial, S⟩ : SignedMidpointMachine.Config)
    refine ⟨SignedMidpointSemantics.fuel answer cap, c, le_rfl, rfl, ?_, rfl⟩
    have hh := SignedMidpointSemantics.halt_encodeInteger a cap
    simpa only [c, SignedMidpointMachine.run, SignedMidpointMachine.cfg,
      inputBank, start, initial, answer, S] using hh
  · intro T hT
    have he : T = S := by rw [hd] at hT; exact Option.some.inj hT.symm
    subst T
    rw [hr]
    exact le_rfl

noncomputable def timeBound (n : ℕ) : ℕ :=
  (20 * (n + 1) ^ 2 + 2) * (1 + 20 * rawMachine.pushBound) + 15 * (n + 1)

theorem outputs_packet_timeBound (a : ℤ) (cap : List Bool) :
    machine.OutputsWithin
      (packet (EncodedETHTail.encodeInteger a) cap)
      (finalPacket (EncodedETHTail.encodeInteger a) cap)
      (timeBound (packet (EncodedETHTail.encodeInteger a) cap).length) := by
  let answer := EncodedETHTail.encodeInteger a
  let n := (packet answer cap).length
  let t := SignedMidpointSemantics.fuel answer cap
  let p := rawMachine.pushBound
  have hOut := outputs_packet a cap
  have hFinal := finalPacket_length answer cap
  have hFuel := fuel_le_packet answer cap
  have hmul := Nat.mul_le_mul_right (1 + 20 * p) hFuel
  apply BitMachine.outputsWithin_mono machine hOut
  change 11 * (n + 1) + t + 2 * (finalPacket answer cap).length + 4 ≤
    (20 * (n + 1) ^ 2 + 2) * (1 + 20 * p) + 15 * (n + 1)
  change (finalPacket answer cap).length ≤ n + 10 * t * p at hFinal
  change t ≤ 20 * (n + 1) ^ 2 + 2 at hFuel
  calc
    11 * (n + 1) + t + 2 * (finalPacket answer cap).length + 4 ≤
        t * (1 + 20 * p) + 15 * (n + 1) := by nlinarith
    _ ≤ (20 * (n + 1) ^ 2 + 2) * (1 + 20 * p) + 15 * (n + 1) := by
      exact Nat.add_le_add_right hmul _

noncomputable def decisionMachine : BitMachine.Machine :=
  BitMachineComposition.composition machine (BankFieldProjection.machine (4 : Fin 5))

theorem decision_outputs_packet (a : ℤ) (cap : List Bool) :
    decisionMachine.OutputsWithin
      (packet (EncodedETHTail.encodeInteger a) cap)
      [decide (2 * a < (cap.length : ℤ))]
      (timeBound (packet (EncodedETHTail.encodeInteger a) cap).length +
        2 * (finalPacket (EncodedETHTail.encodeInteger a) cap).length + 2 +
        14 * ((finalPacket (EncodedETHTail.encodeInteger a) cap).length + 1)) := by
  have hA := outputs_packet_timeBound a cap
  have hB := BankFieldProjection.outputs (4 : Fin 5)
    (finalPacket (EncodedETHTail.encodeInteger a) cap)
  rw [final_decision] at hB
  exact BitMachineComposition.composition_outputsWithin machine
    (BankFieldProjection.machine (4 : Fin 5)) hA hB

noncomputable def decisionTimeBound (n : ℕ) : ℕ :=
  timeBound n + 16 * (n + 1) +
    160 * (20 * (n + 1) ^ 2 + 2) * rawMachine.pushBound

theorem decision_outputs_polynomial (a : ℤ) (cap : List Bool) :
    decisionMachine.OutputsWithin
      (packet (EncodedETHTail.encodeInteger a) cap)
      [decide (2 * a < (cap.length : ℤ))]
      (decisionTimeBound (packet (EncodedETHTail.encodeInteger a) cap).length) := by
  let answer := EncodedETHTail.encodeInteger a
  let n := (packet answer cap).length
  let t := SignedMidpointSemantics.fuel answer cap
  let p := rawMachine.pushBound
  have hOut := decision_outputs_packet a cap
  have hFinal := finalPacket_length answer cap
  have hFuel := fuel_le_packet answer cap
  have hmul := Nat.mul_le_mul_right p hFuel
  apply BitMachine.outputsWithin_mono decisionMachine hOut
  change timeBound n + 2 * (finalPacket answer cap).length + 2 +
      14 * ((finalPacket answer cap).length + 1) ≤
    timeBound n + 16 * (n + 1) + 160 * (20 * (n + 1) ^ 2 + 2) * p
  change (finalPacket answer cap).length ≤ n + 10 * t * p at hFinal
  change t ≤ 20 * (n + 1) ^ 2 + 2 at hFuel
  nlinarith

/-- The exact pointwise item interface expected by the framed source-list
mapper, after the approximation answer and unary cap have been supplied. -/
def branchPacket (answer : List Bool → ℤ) (k : ℕ)
    (b : EncodedETHTail.Branch) : List Bool :=
  packet (EncodedETHTail.encodeInteger (answer b.table))
    (List.replicate (2 * b.threshold + k) true)

theorem branch_outputs_polynomial (answer : List Bool → ℤ) (k : ℕ)
    (b : EncodedETHTail.Branch) :
    decisionMachine.OutputsWithin
      (branchPacket answer k b)
      [SignedMidpointSemantics.branchBit answer k b]
      (decisionTimeBound (branchPacket answer k b).length) := by
  rw [SignedMidpointSemantics.branchBit_correct]
  simpa [branchPacket, EncodedETHTail.branchAccept] using
    decision_outputs_polynomial (answer b.table)
      (List.replicate (2 * b.threshold + k) true)

end EthInapproximability.CurrentPaper.SignedMidpointPacket
