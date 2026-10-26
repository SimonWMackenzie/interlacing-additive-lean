import EthInapproximability.CurrentPaper.SignedMidpointApproxCore
import EthInapproximability.CurrentPaper.BitMachineComposition

/-!
# Ordinary framed approximation-plus-midpoint callback

A canonical input packet contains the table on `M.input`, unary `Y`, unary
`k`, and empty scratch/output banks. The generic fixed machine parses this
one bit string, runs `M` and the cap comparison in a single finite program,
and serializes the final bank. Field projection extracts the decision.
-/

namespace EthInapproximability.CurrentPaper.SignedMidpointApproxPacket

open Turing BitMachineEncoding

variable (M : BitMachine.Machine)

abbrev Width := M.stackCount + 4

def stackEquiv : SignedMidpointApproxCore.Stack M ≃ Fin (Width M) :=
  finSumFinEquiv

def program (l : SignedMidpointApproxCore.Label M) :
    TM2.Stmt (fun _ : Fin (Width M) => Bool)
      (SignedMidpointApproxCore.Label M) (SignedMidpointApproxCore.Control M) :=
  renameStmt (stackEquiv M) (Equiv.refl _) (Equiv.refl _)
    (SignedMidpointApproxCore.program M l)

def startLabel : SignedMidpointApproxCore.Label M := .inl M.start
def initial : SignedMidpointApproxCore.Control M :=
  (M.initial, SignedMidpointApproxCore.initialCompare)

noncomputable def inputBank (table : List Bool) (Y k : ℕ) :
    Fin (Width M) → List Bool :=
  fun j => (SignedMidpointApproxCore.start M table Y k).stk ((stackEquiv M).symm j)

noncomputable def packet (table : List Bool) (Y k : ℕ) : List Bool :=
  BitMachineBankCodec.encode (inputBank M table Y k)

noncomputable def machine : BitMachine.Machine :=
  BitMachineBankWrapper.machine (program M) (startLabel M) (initial M)

def outputKey : Fin (Width M) := (stackEquiv M) (.inr 3)

theorem initial_eq_renamed (table : List Bool) (Y k : ℕ) :
    (⟨some (startLabel M), initial M, inputBank M table Y k⟩ :
      TM2.Cfg (fun _ : Fin (Width M) => Bool)
        (SignedMidpointApproxCore.Label M) (SignedMidpointApproxCore.Control M)) =
      renameCfg (stackEquiv M) (Equiv.refl _) (Equiv.refl _)
        (SignedMidpointApproxCore.start M table Y k) := by
  rfl

theorem renamed_run (table : List Bool) (Y k t : ℕ) :
    ((advance (program M))^[t])
      (⟨some (startLabel M), initial M, inputBank M table Y k⟩ :
        TM2.Cfg (fun _ : Fin (Width M) => Bool)
          (SignedMidpointApproxCore.Label M) (SignedMidpointApproxCore.Control M)) =
      renameCfg (stackEquiv M) (Equiv.refl _) (Equiv.refl _)
        (SignedMidpointApproxCore.run M t
          (SignedMidpointApproxCore.start M table Y k)) := by
  rw [initial_eq_renamed]
  exact rename_run (stackEquiv M) (Equiv.refl _) (Equiv.refl _)
    (SignedMidpointApproxCore.program M)
    (SignedMidpointApproxCore.start M table Y k) t

noncomputable def finalBank (t : ℕ) (table : List Bool) (Y k : ℕ) :
    Fin (Width M) → List Bool :=
  (renameCfg (stackEquiv M) (Equiv.refl _) (Equiv.refl _)
    (SignedMidpointApproxCore.run M t
      (SignedMidpointApproxCore.start M table Y k))).stk

noncomputable def finalPacket (t : ℕ) (table : List Bool) (Y k : ℕ) : List Bool :=
  BitMachineBankCodec.encode (finalBank M t table Y k)

theorem outputs_packet_at (table : List Bool) (Y k t : ℕ)
    (hh : (SignedMidpointApproxCore.run M t
      (SignedMidpointApproxCore.start M table Y k)).l = none) :
    (machine M).OutputsWithin (packet M table Y k)
      (finalPacket M t table Y k)
      ((2*Width M+1)*((packet M table Y k).length+1)+t+
        2*(finalPacket M t table Y k).length+4) := by
  let S := inputBank M table Y k
  let input := packet M table Y k
  let F : Fin (Width M) → List Bool := finalBank M t table Y k
  let G : (Fin (Width M) → List Bool) → (Fin (Width M) → List Bool) := fun _ => F
  have hd : BitMachineBankCodec.decode (Width M) input = some S := by
    exact BitMachineBankCodec.decode_encode S
  have hr : BitMachineBankWrapper.result G input = finalPacket M t table Y k := by
    simp only [BitMachineBankWrapper.result, hd, finalPacket, G, F]
  rw [← hr]
  change (BitMachineBankWrapper.machine (program M) (startLabel M) (initial M)).OutputsWithin
    input (BitMachineBankWrapper.result G input)
    ((2*Width M+1)*(input.length+1)+t+
      2*(BitMachineBankWrapper.result G input).length+4)
  apply BitMachineBankWrapper.outputs (program M) (startLabel M) (initial M)
    G input t (BitMachineBankWrapper.result G input).length
  · intro T hT
    have he : T = S := by rw [hd] at hT; exact Option.some.inj hT.symm
    subst T
    let c := renameCfg (stackEquiv M) (Equiv.refl _) (Equiv.refl _)
      (SignedMidpointApproxCore.run M t
        (SignedMidpointApproxCore.start M table Y k))
    refine ⟨t,c,le_rfl,?_,?_,?_⟩
    · exact renamed_run M table Y k t
    · simp only [c, renameCfg, hh, Option.map_none]
    · rfl
  · intro T hT
    have he : T = S := by rw [hd] at hT; exact Option.some.inj hT.symm
    subst T
    rw [hr]
    exact le_rfl

theorem finalPacket_decision (table : List Bool) (Y k t : ℕ) (bit : Bool)
    (hout : (SignedMidpointApproxCore.run M t
      (SignedMidpointApproxCore.start M table Y k)).stk (.inr 3) = [bit]) :
    BankFieldProjection.result (outputKey M) (finalPacket M t table Y k) = [bit] := by
  rw [finalPacket, BankFieldProjection.result_encode]
  change (SignedMidpointApproxCore.run M t
    (SignedMidpointApproxCore.start M table Y k)).stk
      ((stackEquiv M).symm ((stackEquiv M) (.inr 3))) = _
  rw [(stackEquiv M).symm_apply_apply]
  exact hout

def callbackBound (answer : List Bool) (Y k bound : ℕ) : ℕ :=
  bound + 1 + SignedMidpointCapPacket.fuel
    (SignedMidpointCapCompare.inputBank answer Y k)

theorem callback_packet (table : List Bool) (a : ℤ) (Y k bound : ℕ)
    (hM : M.OutputsWithin table (EncodedETHTail.encodeInteger a) bound) :
    ∃ t ≤ callbackBound (EncodedETHTail.encodeInteger a) Y k bound,
      (machine M).OutputsWithin (packet M table Y k)
        (finalPacket M t table Y k)
        ((2*Width M+1)*((packet M table Y k).length+1)+
          callbackBound (EncodedETHTail.encodeInteger a) Y k bound+
          2*(finalPacket M t table Y k).length+4) ∧
      BankFieldProjection.result (outputKey M)
        (finalPacket M t table Y k) =
          [decide (2*a < (2*Y+k : ℤ))] := by
  obtain ⟨t,ht,hh,ho⟩ := SignedMidpointApproxCore.callback_run M table a Y k bound hM
  refine ⟨t,ht,?_,?_⟩
  · exact BitMachine.outputsWithin_mono (machine M)
      (outputs_packet_at M table Y k t hh) (by
        dsimp only [callbackBound]
        omega)
  · exact finalPacket_decision M table Y k t _ ho

noncomputable def decisionMachine : BitMachine.Machine :=
  BitMachineComposition.composition (machine M)
    (BankFieldProjection.machine (outputKey M))

noncomputable def rawMachine : BitMachine.Machine :=
  ofFinite ((stackEquiv M) (.inl M.input)) (outputKey M)
    (startLabel M) (initial M)
    (program M)

theorem finalBank_word_length (t : ℕ) (table : List Bool) (Y k : ℕ)
    (j : Fin (Width M)) :
    ((finalBank M t table Y k) j).length ≤
      ((inputBank M table Y k) j).length + t*(rawMachine M).pushBound := by
  let c : TM2.Cfg (fun _ : Fin (Width M) => Bool)
    (SignedMidpointApproxCore.Label M) (SignedMidpointApproxCore.Control M) :=
      ⟨some (startLabel M), initial M, inputBank M table Y k⟩
  let ek := Fintype.equivFin (Fin (Width M))
  let el := Fintype.equivFin (SignedMidpointApproxCore.Label M)
  let ev := Fintype.equivFin (SignedMidpointApproxCore.Control M)
  have h := BitMachine.run_length (rawMachine M)
    (renameCfg ek el ev c) (ek j) t
  have hr := ofFinite_run ((stackEquiv M) (.inl M.input)) (outputKey M)
    (startLabel M) (initial M) (program M) c t
  change ((rawMachine M).run _ (renameCfg ek el ev c)) = _ at hr
  rw [hr] at h
  simp only [renameCfg] at h
  rw [renamed_run M table Y k t] at h
  have hj : ek.symm (ek j) = j := ek.symm_apply_apply j
  change ((finalBank M t table Y k) (ek.symm (ek j))).length ≤
    ((inputBank M table Y k) (ek.symm (ek j))).length +
      t*(rawMachine M).pushBound at h
  rw [hj] at h
  exact h

theorem finalPacket_length (t : ℕ) (table : List Bool) (Y k : ℕ) :
    (finalPacket M t table Y k).length ≤
      (packet M table Y k).length +
        2*(Width M)*t*(rawMachine M).pushBound := by
  have hs : (∑ j : Fin (Width M), ((finalBank M t table Y k) j).length) ≤
      ∑ j : Fin (Width M),
        (((inputBank M table Y k) j).length + t*(rawMachine M).pushBound) := by
    apply Finset.sum_le_sum
    intro j _
    exact finalBank_word_length M t table Y k j
  rw [Finset.sum_add_distrib] at hs
  simp only [Finset.sum_const,
    Finset.card_fin, nsmul_eq_mul] at hs
  rw [finalPacket, BitMachineBankCodec.encode_length,
    packet, BitMachineBankCodec.encode_length]
  nlinarith

theorem callback_decision (table : List Bool) (a : ℤ) (Y k bound : ℕ)
    (hM : M.OutputsWithin table (EncodedETHTail.encodeInteger a) bound) :
    ∃ t ≤ callbackBound (EncodedETHTail.encodeInteger a) Y k bound,
      (decisionMachine M).OutputsWithin (packet M table Y k)
        [decide (2*a < (2*Y+k : ℤ))]
        ((2*Width M+1)*((packet M table Y k).length+1)+
          callbackBound (EncodedETHTail.encodeInteger a) Y k bound+
          4*(finalPacket M t table Y k).length+6+
          (2*Width M+4)*((finalPacket M t table Y k).length+1)) := by
  obtain ⟨t,ht,hA,hcorrect⟩ := callback_packet M table a Y k bound hM
  have hB := BankFieldProjection.outputs (outputKey M)
    (finalPacket M t table Y k)
  rw [hcorrect] at hB
  refine ⟨t,ht,?_⟩
  have h := BitMachineComposition.composition_outputsWithin (machine M)
    (BankFieldProjection.machine (outputKey M)) hA hB
  convert h using 1
  omega

noncomputable def decisionBound (inputLength callbackTime : ℕ) : ℕ :=
  (2*Width M+1)*(inputLength+1)+callbackTime+
    (2*Width M+8)*
      (inputLength+2*Width M*callbackTime*(rawMachine M).pushBound)+
    (2*Width M+10)

theorem callback_decision_bounded (table : List Bool) (a : ℤ)
    (Y k bound : ℕ)
    (hM : M.OutputsWithin table (EncodedETHTail.encodeInteger a) bound) :
    (decisionMachine M).OutputsWithin (packet M table Y k)
      [decide (2*a < (2*Y+k : ℤ))]
      (decisionBound M (packet M table Y k).length
        (callbackBound (EncodedETHTail.encodeInteger a) Y k bound)) := by
  obtain ⟨t,ht,hOut⟩ := callback_decision M table a Y k bound hM
  let n := (packet M table Y k).length
  let B := callbackBound (EncodedETHTail.encodeInteger a) Y k bound
  let p := (rawMachine M).pushBound
  let F := (finalPacket M t table Y k).length
  have hF := finalPacket_length M t table Y k
  change F ≤ n+2*Width M*t*p at hF
  have htp : 2*Width M*t*p ≤ 2*Width M*B*p :=
    Nat.mul_le_mul_right p (Nat.mul_le_mul_left (2*Width M) ht)
  have hFL : F ≤ n+2*Width M*B*p := by omega
  have hterm := Nat.mul_le_mul_left (2*Width M+8) hFL
  apply BitMachine.outputsWithin_mono (decisionMachine M) hOut
  change (2*Width M+1)*(n+1)+B+4*F+6+
      (2*Width M+4)*(F+1) ≤
    (2*Width M+1)*(n+1)+B+
      (2*Width M+8)*(n+2*Width M*B*p)+(2*Width M+10)
  nlinarith

end EthInapproximability.CurrentPaper.SignedMidpointApproxPacket
