import CurrentAdditive.GenericFeatureIterationPacket

/-! Internal scalar transport from proved per-prefix bounds to the actual
iteration clock. The final raw-input theorem must discharge both premises. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
namespace CurrentAdditive.GenericFeatureIterationSumBound
open EthInapproximability.CurrentPaper
open GenericFeatureGeneratedIteration
attribute [local irreducible] GenericFeatureCoordinateTransition.machine

private noncomputable opaque machineNumbers (D : Nat) :
    {p : Nat × Nat // p.1=(M D).stackCount ∧ p.2=(M D).pushBound} :=
  ⟨((M D).stackCount,(M D).pushBound),rfl,rfl⟩
def stackConstant (D : Nat) : Nat := (machineNumbers D).val.1
def pushConstant (D : Nat) : Nat := (machineNumbers D).val.2
theorem stackConstant_eq (D : Nat) : stackConstant D=(M D).stackCount := (machineNumbers D).property.1
theorem pushConstant_eq (D : Nat) : pushConstant D=(M D).pushBound := (machineNumbers D).property.2
def coefficient (D : Nat) : Nat := (stackConstant D+2)*(pushConstant D+1)+stackConstant D+100
attribute [local irreducible] stackConstant pushConstant coefficient

theorem arithmetic (q B S P inputLength T L : Nat)
    (hi : inputLength ≤ 2*(B+q)+2) (ht : T ≤ q*B) (hl : L ≤ (q+1)*B) :
    5*(inputLength+1)+(q*(T+(S+2)*(L+T*P)+S+4)+1)+1 ≤
      ((S+2)*(P+1)+S+100)*(q+1)^2*(B+1) := by
  let Q := q+1
  let Z := Q^2*(B+1)
  have hQ : 1 ≤ Q := by dsimp [Q]; omega
  have hq : q ≤ Q := by dsimp [Q]; omega
  have hQsq : Q ≤ Q^2 := by nlinarith
  have hsqZ : Q^2 ≤ Z := by dsimp [Z]; nlinarith
  have hone : 1 ≤ Z := by nlinarith
  have hqZ : q ≤ Z := le_trans hq (le_trans hQsq hsqZ)
  have hBZ : B ≤ Z := by dsimp [Z]; nlinarith
  have hqq : q*q ≤ Q^2 := by nlinarith
  have hqQ : q*Q ≤ Q^2 := by nlinarith
  have hTT : q*T ≤ Z := by
    have h1 := Nat.mul_le_mul_left q ht
    have h2 := Nat.mul_le_mul_right B hqq
    dsimp [Z]
    nlinarith
  have hTP : L+T*P ≤ Q*B*(P+1) := by
    have hTQ : T ≤ Q*B := ht.trans (Nat.mul_le_mul_right B hq)
    have hp := Nat.mul_le_mul_right P hTQ
    dsimp [Q] at *
    nlinarith
  have hqTP : q*(L+T*P) ≤ (P+1)*Z := by
    have h1 := Nat.mul_le_mul_left q hTP
    have h2 := Nat.mul_le_mul_right (B*(P+1)) hqQ
    dsimp [Z]
    nlinarith
  have hS := Nat.mul_le_mul_left (S+2) hqTP
  have hqS := Nat.mul_le_mul_left (S+4) hqZ
  have hparse : 5*(inputLength+1) ≤ 35*Z := by nlinarith
  dsimp only [Z,Q] at hTT hS hqS hparse hone
  nlinarith

theorem clock_le (D q : Nat) (ys : List Nat) (carry : List Bool) (B : Nat)
    (hstep : ∀ j<q, GenericFeatureCoordinateTransition.packetClock D j ys (featuresAt D j ys) [] [] carry ≤ B)
    (hstate : ∀ j≤q, (states D ys carry j).length ≤ B) :
    GenericFeatureIterationPacket.clock D q ys carry ≤ coefficient D*(q+1)^2*(B+1) := by
  have ht : timeBound D q ys carry ≤ q*B := by
    unfold timeBound
    calc
      _ ≤ ∑ _ ∈ Finset.range q, B := by
        apply Finset.sum_le_sum
        intro j hj
        exact hstep j (Finset.mem_range.mp hj)
      _ = _ := by simp
  have hl : lengthBound D q ys carry ≤ (q+1)*B := by
    unfold lengthBound
    calc
      _ ≤ ∑ _ ∈ Finset.range (q+1), B := by
        apply Finset.sum_le_sum
        intro j hj
        exact hstate j (by have := Finset.mem_range.mp hj; omega)
      _ = _ := by simp
  have hin : (BitMachineBankCodec.encode (GenericFeatureIterationPacket.words D q ys carry)).length ≤
      2*(B+q)+2 := by
    rw [BitMachineBankCodec.encode_length]
    have hz := hstate 0 (by omega)
    simp only [GenericFeatureIterationPacket.words,Fin.sum_univ_two,
      Matrix.cons_val_zero,Matrix.cons_val_one,List.length_replicate]
    omega
  unfold GenericFeatureIterationPacket.clock GenericFeatureGeneratedIteration.clock
    BitMachineIteration.roundBound
  rw [←stackConstant_eq,←pushConstant_eq]
  unfold coefficient
  exact arithmetic q B (stackConstant D) (pushConstant D) _ _ _ hin ht hl

#print axioms arithmetic
#print axioms clock_le
end CurrentAdditive.GenericFeatureIterationSumBound
