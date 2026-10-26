import EthInapproximability.CurrentPaper.SignedMidpointCapCompare
import EthInapproximability.CurrentPaper.BitMachineComposition

/-!
# Ordinary input for unary-cap construction and signed comparison

The canonical packet contains the signed approximation output, unary `Y`,
and unary `k`. Its fixed framed machine constructs `2Y+k` physically before
comparing. This is a per-branch endpoint once those three physical fields
have been produced; it is not the source or approximation compiler.
-/

namespace EthInapproximability.CurrentPaper.SignedMidpointCapPacket

open Turing BitMachineEncoding

def start : SignedMidpointCapCompare.Label := .inl .double
def initial : SignedMidpointCapCompare.Control :=
  (none, SignedMidpointPacket.initial)

def fuel (S : Fin 5 → List Bool) : ℕ :=
  3*(S 1).length + (S 2).length + 3 +
    SignedMidpointSemantics.fuel (S 0)
      (List.replicate (2*(S 1).length+(S 2).length) true)

def finalBank (S : Fin 5 → List Bool) : Fin 5 → List Bool :=
  (SignedMidpointCapCompare.run (fuel S)
    (⟨some start, initial, S⟩ : SignedMidpointCapCompare.Config)).stk

def finalPacket (answer : List Bool) (threshold separation : ℕ) : List Bool :=
  BitMachineBankCodec.encode
    (finalBank (SignedMidpointCapCompare.inputBank answer threshold separation))

noncomputable def machine : BitMachine.Machine :=
  BitMachineBankWrapper.machine SignedMidpointCapCompare.program start initial

noncomputable def rawMachine : BitMachine.Machine :=
  ofFinite (0 : Fin 5) 4 start initial SignedMidpointCapCompare.program

theorem finalBank_word_length (S : Fin 5 → List Bool) (j : Fin 5) :
    ((finalBank S) j).length ≤ (S j).length + fuel S * rawMachine.pushBound := by
  let c : SignedMidpointCapCompare.Config := ⟨some start, initial, S⟩
  let ek := Fintype.equivFin (Fin 5)
  let el := Fintype.equivFin SignedMidpointCapCompare.Label
  let ev := Fintype.equivFin SignedMidpointCapCompare.Control
  have h := BitMachine.run_length rawMachine (renameCfg ek el ev c) (ek j) (fuel S)
  have hr := ofFinite_run (0 : Fin 5) 4 start initial SignedMidpointCapCompare.program c
    (fuel S)
  change (rawMachine.run _ (renameCfg ek el ev c)) = _ at hr
  rw [hr] at h
  simp only [renameCfg] at h
  have hj : ek.symm (ek j) = j := ek.symm_apply_apply j
  change ((finalBank S) (ek.symm (ek j))).length ≤
    (S (ek.symm (ek j))).length + fuel S * rawMachine.pushBound at h
  rw [hj] at h
  exact h

theorem finalPacket_length (answer : List Bool) (Y k : ℕ) :
    (finalPacket answer Y k).length ≤
      (SignedMidpointCapCompare.inputPacket answer Y k).length +
        10 * fuel (SignedMidpointCapCompare.inputBank answer Y k) *
          rawMachine.pushBound := by
  let S := SignedMidpointCapCompare.inputBank answer Y k
  have hs : (∑ j : Fin 5, ((finalBank S) j).length) ≤
      ∑ j : Fin 5, ((S j).length + fuel S * rawMachine.pushBound) := by
    apply Finset.sum_le_sum
    intro j _
    exact finalBank_word_length S j
  simp only [Fin.sum_univ_five] at hs
  simp only [finalPacket, SignedMidpointCapCompare.inputPacket,
    BitMachineBankCodec.encode_length]
  dsimp [S, SignedMidpointCapCompare.inputBank] at hs ⊢
  simp only [Fin.sum_univ_five] at ⊢
  simp only [Nat.mul_assoc] at ⊢
  simp at hs ⊢
  omega

theorem fuel_le_packet (answer : List Bool) (Y k : ℕ) :
    fuel (SignedMidpointCapCompare.inputBank answer Y k) ≤
      64 * ((SignedMidpointCapCompare.inputPacket answer Y k).length + 1) ^ 2 + 5 := by
  let S := SignedMidpointCapCompare.inputBank answer Y k
  let n := (SignedMidpointCapCompare.inputPacket answer Y k).length
  have ha := BitMachineBankCodec.word_length_le_encode S (0 : Fin 5)
  have hY := BitMachineBankCodec.word_length_le_encode S (1 : Fin 5)
  have hk := BitMachineBankCodec.word_length_le_encode S (2 : Fin 5)
  change answer.length ≤ n at ha
  have hY' : Y ≤ n := by
    simpa [S, n, SignedMidpointCapCompare.inputBank,
      SignedMidpointCapCompare.inputPacket] using hY
  have hk' : k ≤ n := by
    simpa [S, n, SignedMidpointCapCompare.inputBank,
      SignedMidpointCapCompare.inputPacket] using hk
  have hcap : 2*Y+k+1 ≤ 3*(n+1) := by omega
  have hm := Nat.mul_le_mul (Nat.succ_le_succ ha) hcap
  change (answer.length+1)*(2*Y+k+1) ≤ (n+1)*(3*(n+1)) at hm
  simp [fuel, SignedMidpointSemantics.fuel,
    SignedMidpointCapCompare.inputBank] at ⊢
  change 3*Y+k+3+20*(answer.length+1)*(2*Y+k+1)+2 ≤
    64*(n+1)^2+5
  nlinarith

theorem canonical_halt (a : ℤ) (Y k : ℕ) :
    (SignedMidpointCapCompare.run
      (fuel (SignedMidpointCapCompare.inputBank (EncodedETHTail.encodeInteger a) Y k))
      (⟨some start, initial,
        SignedMidpointCapCompare.inputBank (EncodedETHTail.encodeInteger a) Y k⟩ :
          SignedMidpointCapCompare.Config)).l = none := by
  let S := SignedMidpointCapCompare.inputBank (EncodedETHTail.encodeInteger a) Y k
  let c : SignedMidpointCapCompare.Config := ⟨some start, initial, S⟩
  obtain ⟨t,ht,hh,_⟩ := SignedMidpointCapCompare.comparison_run a Y k
  have hc : c = SignedMidpointCapCompare.capFrame
      (SignedMidpointCap.cfg (some .double) none (EncodedETHTail.encodeInteger a)
        (List.replicate Y true) (List.replicate k true) [] []) := rfl
  have hf : fuel S = 3*Y+k+3 +
      SignedMidpointSemantics.fuel (EncodedETHTail.encodeInteger a)
        (List.replicate (2*Y+k) true) := by
    simp [fuel, S, SignedMidpointCapCompare.inputBank]
  obtain ⟨u,hu⟩ := Nat.exists_eq_add_of_le (show t ≤ fuel S by rw [hf]; exact ht)
  have hstay := BitMachineSubroutine.run_halted SignedMidpointCapCompare.program
    (SignedMidpointCapCompare.run t c) (by rw [hc]; exact hh) u
  change SignedMidpointCapCompare.run u (SignedMidpointCapCompare.run t c) = _ at hstay
  change (SignedMidpointCapCompare.run (fuel S) c).l = none
  rw [hu]
  have hadd : SignedMidpointCapCompare.run (t+u) c =
      SignedMidpointCapCompare.run u (SignedMidpointCapCompare.run t c) := by
    simp only [SignedMidpointCapCompare.run, Nat.add_comm t u,
      Function.iterate_add_apply]
  rw [hadd, hstay, hc]
  exact hh

theorem final_decision (a : ℤ) (Y k : ℕ) :
    BankFieldProjection.result (4 : Fin 5)
      (finalPacket (EncodedETHTail.encodeInteger a) Y k) =
      [decide (2*a < (2*Y+k : ℤ))] := by
  let S := SignedMidpointCapCompare.inputBank (EncodedETHTail.encodeInteger a) Y k
  let c : SignedMidpointCapCompare.Config := ⟨some start, initial, S⟩
  obtain ⟨t,ht,hh,ho⟩ := SignedMidpointCapCompare.comparison_run a Y k
  have hc : c = SignedMidpointCapCompare.capFrame
      (SignedMidpointCap.cfg (some .double) none (EncodedETHTail.encodeInteger a)
        (List.replicate Y true) (List.replicate k true) [] []) := rfl
  have hf : fuel S = 3*Y+k+3 +
      SignedMidpointSemantics.fuel (EncodedETHTail.encodeInteger a)
        (List.replicate (2*Y+k) true) := by
    simp [fuel, S, SignedMidpointCapCompare.inputBank]
  have ht' : t ≤ fuel S := by rw [hf]; exact ht
  obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le ht'
  have hstay := BitMachineSubroutine.run_halted SignedMidpointCapCompare.program
    (SignedMidpointCapCompare.run t c) (by rw [hc]; exact hh) u
  change SignedMidpointCapCompare.run u (SignedMidpointCapCompare.run t c) = _ at hstay
  have hfinal : SignedMidpointCapCompare.run (fuel S) c =
      SignedMidpointCapCompare.run t c := by
    rw [hu]
    simpa only [SignedMidpointCapCompare.run, Nat.add_comm t u,
      Function.iterate_add_apply] using hstay
  rw [finalPacket, BankFieldProjection.result_encode]
  change (SignedMidpointCapCompare.run (fuel S) c).stk 4 = _
  rw [hfinal, hc]
  exact ho

theorem outputs_packet (a : ℤ) (Y k : ℕ) :
    machine.OutputsWithin
      (SignedMidpointCapCompare.inputPacket (EncodedETHTail.encodeInteger a) Y k)
      (finalPacket (EncodedETHTail.encodeInteger a) Y k)
      (11 * ((SignedMidpointCapCompare.inputPacket
        (EncodedETHTail.encodeInteger a) Y k).length + 1) +
        fuel (SignedMidpointCapCompare.inputBank (EncodedETHTail.encodeInteger a) Y k) +
        2 * (finalPacket (EncodedETHTail.encodeInteger a) Y k).length + 4) := by
  let S := SignedMidpointCapCompare.inputBank (EncodedETHTail.encodeInteger a) Y k
  let input := SignedMidpointCapCompare.inputPacket (EncodedETHTail.encodeInteger a) Y k
  have hd : BitMachineBankCodec.decode 5 input = some S := by
    exact BitMachineBankCodec.decode_encode S
  have hr : BitMachineBankWrapper.result finalBank input =
      finalPacket (EncodedETHTail.encodeInteger a) Y k := by
    simp only [BitMachineBankWrapper.result, hd, finalPacket, S]
  rw [← hr]
  change (BitMachineBankWrapper.machine
    SignedMidpointCapCompare.program start initial).OutputsWithin
    input (BitMachineBankWrapper.result finalBank input)
    (11*(input.length+1)+fuel S+
      2*(BitMachineBankWrapper.result finalBank input).length+4)
  apply BitMachineBankWrapper.outputs SignedMidpointCapCompare.program start initial
    finalBank input (fuel S) (BitMachineBankWrapper.result finalBank input).length
  · intro T hT
    have he : T = S := by rw [hd] at hT; exact Option.some.inj hT.symm
    subst T
    let c := SignedMidpointCapCompare.run (fuel S)
      (⟨some start, initial, S⟩ : SignedMidpointCapCompare.Config)
    refine ⟨fuel S, c, le_rfl, rfl, ?_, rfl⟩
    simpa only [c, SignedMidpointCapCompare.run, S] using canonical_halt a Y k
  · intro T hT
    have he : T = S := by rw [hd] at hT; exact Option.some.inj hT.symm
    subst T
    rw [hr]
    exact le_rfl

noncomputable def timeBound (n : ℕ) : ℕ :=
  (64*(n+1)^2+5)*(1+20*rawMachine.pushBound)+15*(n+1)

theorem outputs_packet_polynomial (a : ℤ) (Y k : ℕ) :
    machine.OutputsWithin
      (SignedMidpointCapCompare.inputPacket (EncodedETHTail.encodeInteger a) Y k)
      (finalPacket (EncodedETHTail.encodeInteger a) Y k)
      (timeBound (SignedMidpointCapCompare.inputPacket
        (EncodedETHTail.encodeInteger a) Y k).length) := by
  let answer := EncodedETHTail.encodeInteger a
  let n := (SignedMidpointCapCompare.inputPacket answer Y k).length
  let t := fuel (SignedMidpointCapCompare.inputBank answer Y k)
  let p := rawMachine.pushBound
  have hOut := outputs_packet a Y k
  have hFinal := finalPacket_length answer Y k
  have hFuel := fuel_le_packet answer Y k
  have hmul := Nat.mul_le_mul_right (1+20*p) hFuel
  apply BitMachine.outputsWithin_mono machine hOut
  change 11*(n+1)+t+2*(finalPacket answer Y k).length+4 ≤
    (64*(n+1)^2+5)*(1+20*p)+15*(n+1)
  change (finalPacket answer Y k).length ≤ n+10*t*p at hFinal
  change t ≤ 64*(n+1)^2+5 at hFuel
  calc
    11*(n+1)+t+2*(finalPacket answer Y k).length+4 ≤
        t*(1+20*p)+15*(n+1) := by nlinarith
    _ ≤ (64*(n+1)^2+5)*(1+20*p)+15*(n+1) := by
      exact Nat.add_le_add_right hmul _

noncomputable def decisionMachine : BitMachine.Machine :=
  BitMachineComposition.composition machine (BankFieldProjection.machine (4 : Fin 5))

noncomputable def decisionTimeBound (n : ℕ) : ℕ :=
  timeBound n + 16*(n+1) +
    160*(64*(n+1)^2+5)*rawMachine.pushBound

theorem decision_outputs_polynomial (a : ℤ) (Y k : ℕ) :
    decisionMachine.OutputsWithin
      (SignedMidpointCapCompare.inputPacket (EncodedETHTail.encodeInteger a) Y k)
      [decide (2*a < (2*Y+k : ℤ))]
      (decisionTimeBound (SignedMidpointCapCompare.inputPacket
        (EncodedETHTail.encodeInteger a) Y k).length) := by
  let answer := EncodedETHTail.encodeInteger a
  let n := (SignedMidpointCapCompare.inputPacket answer Y k).length
  let t := fuel (SignedMidpointCapCompare.inputBank answer Y k)
  let p := rawMachine.pushBound
  have hA := outputs_packet_polynomial a Y k
  have hB := BankFieldProjection.outputs (4 : Fin 5) (finalPacket answer Y k)
  rw [final_decision] at hB
  have hOut := BitMachineComposition.composition_outputsWithin machine
    (BankFieldProjection.machine (4 : Fin 5)) hA hB
  have hFinal := finalPacket_length answer Y k
  have hFuel := fuel_le_packet answer Y k
  have hmul := Nat.mul_le_mul_right p hFuel
  apply BitMachine.outputsWithin_mono decisionMachine hOut
  change timeBound n + 2*(finalPacket answer Y k).length+2+
      14*((finalPacket answer Y k).length+1) ≤
    timeBound n+16*(n+1)+160*(64*(n+1)^2+5)*p
  change (finalPacket answer Y k).length ≤ n+10*t*p at hFinal
  change t ≤ 64*(n+1)^2+5 at hFuel
  nlinarith

def branchPacket (answer : List Bool → ℤ) (k : ℕ)
    (b : EncodedETHTail.Branch) : List Bool :=
  SignedMidpointCapCompare.inputPacket
    (EncodedETHTail.encodeInteger (answer b.table)) b.threshold k

theorem branch_outputs_polynomial (answer : List Bool → ℤ) (k : ℕ)
    (b : EncodedETHTail.Branch) :
    decisionMachine.OutputsWithin
      (branchPacket answer k b)
      [SignedMidpointSemantics.branchBit answer k b]
      (decisionTimeBound (branchPacket answer k b).length) := by
  rw [SignedMidpointSemantics.branchBit_correct]
  simpa [branchPacket, EncodedETHTail.branchAccept] using
    decision_outputs_polynomial (answer b.table) b.threshold k

end EthInapproximability.CurrentPaper.SignedMidpointCapPacket
