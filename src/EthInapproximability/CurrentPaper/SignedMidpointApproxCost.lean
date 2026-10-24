import EthInapproximability.CurrentPaper.SignedMidpointApproxPacket

/-!
# Size and runtime of the actual approximation callback

The approximation machine's polynomial witness is a cited input. All
additional work is charged by the concrete framed callback program. The
eventual list runtime is the sum over callback items, not a polynomial of
the number of branches.
-/

namespace EthInapproximability.CurrentPaper.SignedMidpointApproxCost

open Turing BitMachineEncoding

variable (M : BitMachine.Machine)

theorem inputBank_table (table : List Bool) (Y k : ℕ) :
    SignedMidpointApproxPacket.inputBank M table Y k
      ((SignedMidpointApproxPacket.stackEquiv M) (.inl M.input)) = table := by
  simp only [SignedMidpointApproxPacket.inputBank, Equiv.symm_apply_apply,
    SignedMidpointApproxCore.start, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg]
  change BitMachineStackEmbedding.bank (SignedMidpointApproxCore.localStack M)
    (SignedMidpointApproxCore.foreign M Y k) (M.init table).stk
    ((SignedMidpointApproxCore.localStack M) M.input) = table
  rw [BitMachineStackEmbedding.bank_at]
  simp [BitMachine.Machine.init]

theorem inputBank_Y (table : List Bool) (Y k : ℕ) :
    SignedMidpointApproxPacket.inputBank M table Y k
      ((SignedMidpointApproxPacket.stackEquiv M) (.inr 0)) =
        List.replicate Y true := by
  simp only [SignedMidpointApproxPacket.inputBank, Equiv.symm_apply_apply,
    SignedMidpointApproxCore.start, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg]
  change BitMachineStackEmbedding.bank (SignedMidpointApproxCore.localStack M)
    (SignedMidpointApproxCore.foreign M Y k) (M.init table).stk (.inr 0) = _
  rw [BitMachineStackEmbedding.bank_outside]
  · rfl
  · intro h
    obtain ⟨x,hx⟩ := h
    cases hx

theorem inputBank_k (table : List Bool) (Y k : ℕ) :
    SignedMidpointApproxPacket.inputBank M table Y k
      ((SignedMidpointApproxPacket.stackEquiv M) (.inr 1)) =
        List.replicate k true := by
  simp only [SignedMidpointApproxPacket.inputBank, Equiv.symm_apply_apply,
    SignedMidpointApproxCore.start, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg]
  change BitMachineStackEmbedding.bank (SignedMidpointApproxCore.localStack M)
    (SignedMidpointApproxCore.foreign M Y k) (M.init table).stk (.inr 1) = _
  rw [BitMachineStackEmbedding.bank_outside]
  · rfl
  · intro h
    obtain ⟨x,hx⟩ := h
    cases hx

theorem table_length_le_packet (table : List Bool) (Y k : ℕ) :
    table.length ≤ (SignedMidpointApproxPacket.packet M table Y k).length := by
  have h := BitMachineBankCodec.word_length_le_encode
    (SignedMidpointApproxPacket.inputBank M table Y k)
    ((SignedMidpointApproxPacket.stackEquiv M) (.inl M.input))
  rw [inputBank_table M] at h
  exact h

theorem parameters_length_le_packet (table : List Bool) (Y k : ℕ) :
    Y ≤ (SignedMidpointApproxPacket.packet M table Y k).length ∧
      k ≤ (SignedMidpointApproxPacket.packet M table Y k).length := by
  have hY := BitMachineBankCodec.word_length_le_encode
    (SignedMidpointApproxPacket.inputBank M table Y k)
    ((SignedMidpointApproxPacket.stackEquiv M) (.inr 0))
  have hk := BitMachineBankCodec.word_length_le_encode
    (SignedMidpointApproxPacket.inputBank M table Y k)
    ((SignedMidpointApproxPacket.stackEquiv M) (.inr 1))
  rw [inputBank_Y M, List.length_replicate] at hY
  rw [inputBank_k M, List.length_replicate] at hk
  exact ⟨hY,hk⟩

def callbackCostBound (n bound : ℕ) : ℕ :=
  bound+1+4*n+3+20*(n+bound*M.pushBound+1)*(3*n+1)+2

theorem callbackBound_le_packet (table : List Bool) (a : ℤ)
    (Y k bound : ℕ)
    (hM : M.OutputsWithin table (EncodedETHTail.encodeInteger a) bound) :
    SignedMidpointApproxPacket.callbackBound
      (EncodedETHTail.encodeInteger a) Y k bound ≤
        callbackCostBound M
          (SignedMidpointApproxPacket.packet M table Y k).length bound := by
  let n := (SignedMidpointApproxPacket.packet M table Y k).length
  have ht := table_length_le_packet M table Y k
  have ⟨hY,hk⟩ := parameters_length_le_packet M table Y k
  have hAnswer := BitMachine.output_length_bound M hM
  have hword : (EncodedETHTail.encodeInteger a).length + 1 ≤
      n+bound*M.pushBound+1 := by omega
  have hcap : 2*Y+k+1 ≤ 3*n+1 := by omega
  have hmul := Nat.mul_le_mul hword hcap
  change ((EncodedETHTail.encodeInteger a).length+1)*(2*Y+k+1) ≤
    (n+bound*M.pushBound+1)*(3*n+1) at hmul
  have hmul20 := Nat.mul_le_mul_left 20 hmul
  have hmul20' :
      20*((EncodedETHTail.encodeInteger a).length+1)*(2*Y+k+1) ≤
      20*(n+bound*M.pushBound+1)*(3*n+1) := by
    simpa only [Nat.mul_assoc] using hmul20
  unfold SignedMidpointApproxPacket.callbackBound
    SignedMidpointCapPacket.fuel SignedMidpointSemantics.fuel
    callbackCostBound
  simp [SignedMidpointCapCompare.inputBank] at ⊢
  change bound+1+(3*Y+k+3+
      (20*((EncodedETHTail.encodeInteger a).length+1)*(2*Y+k+1)+2)) ≤
    bound+1+4*n+3+20*(n+bound*M.pushBound+1)*(3*n+1)+2
  omega

theorem decisionBound_mono (n B C : ℕ) (h : B ≤ C) :
    SignedMidpointApproxPacket.decisionBound M n B ≤
      SignedMidpointApproxPacket.decisionBound M n C := by
  let p := (SignedMidpointApproxPacket.rawMachine M).pushBound
  have hinner : 2*SignedMidpointApproxPacket.Width M*B*p ≤
      2*SignedMidpointApproxPacket.Width M*C*p :=
    Nat.mul_le_mul_right p
      (Nat.mul_le_mul_left (2*SignedMidpointApproxPacket.Width M) h)
  have houter := Nat.mul_le_mul_left
    (2*SignedMidpointApproxPacket.Width M+8)
    (Nat.add_le_add_left hinner n)
  unfold SignedMidpointApproxPacket.decisionBound
  change (2*SignedMidpointApproxPacket.Width M+1)*(n+1)+B+
      (2*SignedMidpointApproxPacket.Width M+8)*
        (n+2*SignedMidpointApproxPacket.Width M*B*p)+
      (2*SignedMidpointApproxPacket.Width M+10) ≤
    (2*SignedMidpointApproxPacket.Width M+1)*(n+1)+C+
      (2*SignedMidpointApproxPacket.Width M+8)*
        (n+2*SignedMidpointApproxPacket.Width M*C*p)+
      (2*SignedMidpointApproxPacket.Width M+10)
  omega

theorem callback_decision_cost (table : List Bool) (a : ℤ)
    (Y k bound : ℕ)
    (hM : M.OutputsWithin table (EncodedETHTail.encodeInteger a) bound) :
    (SignedMidpointApproxPacket.decisionMachine M).OutputsWithin
      (SignedMidpointApproxPacket.packet M table Y k)
      [decide (2*a < (2*Y+k : ℤ))]
      (SignedMidpointApproxPacket.decisionBound M
        (SignedMidpointApproxPacket.packet M table Y k).length
        (callbackCostBound M
          (SignedMidpointApproxPacket.packet M table Y k).length bound)) := by
  have hrun := SignedMidpointApproxPacket.callback_decision_bounded
    M table a Y k bound hM
  have hB := callbackBound_le_packet M table a Y k bound hM
  exact BitMachine.outputsWithin_mono _ hrun
    (decisionBound_mono M _ _ _ hB)

theorem callback_decision_polynomial_on_packet
    (answer : List Bool → ℤ) (c d : ℕ)
    (hM : M.ComputesWithin
      (fun table => EncodedETHTail.encodeInteger (answer table))
      (fun n => c*(n+1)^d))
    (table : List Bool) (Y k : ℕ) :
    (SignedMidpointApproxPacket.decisionMachine M).OutputsWithin
      (SignedMidpointApproxPacket.packet M table Y k)
      [decide (2*answer table < (2*Y+k : ℤ))]
      (SignedMidpointApproxPacket.decisionBound M
        (SignedMidpointApproxPacket.packet M table Y k).length
        (callbackCostBound M
          (SignedMidpointApproxPacket.packet M table Y k).length
          (c*((SignedMidpointApproxPacket.packet M table Y k).length+1)^d))) := by
  let n := (SignedMidpointApproxPacket.packet M table Y k).length
  have htable := table_length_le_packet M table Y k
  have hpow : (table.length+1)^d ≤ (n+1)^d :=
    Nat.pow_le_pow_left (by omega) d
  have hbound := Nat.mul_le_mul_left c hpow
  have hrun := hM table
  have hrun' := BitMachine.outputsWithin_mono M hrun hbound
  exact callback_decision_cost M table (answer table) Y k
    (c*(n+1)^d) hrun'

end EthInapproximability.CurrentPaper.SignedMidpointApproxCost
