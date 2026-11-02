import Paper2.CodeSamplerInterpreterPolynomial
import Paper2.GeneratorPublicCap
import Paper2.FairBitCap
import Mathlib.Tactic

/-! Actual manuscript-count bounds for the scheduled serialized sample root.
The two dimensions are the source schedule, not arbitrary caller counts. -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

namespace Paper2.CodeSamplerScheduledBounds

open GeneratorCode GeneratorSerialization
open RecursiveSamplingExecution
open SourceProfileParameters SourceRecursiveNoSampling
open ParameterizedCanonicalSource

private theorem root_size_le (mX mY E F : Nat) (row col : Code)
    (hx : mX ≤ E) (hy : mY ≤ E)
    (hp : codeSize row + codeSize col + 1 ≤ F) :
    codeSize (.append (copies mY col) (copies mX row)) ≤
      11+2*E*(F+3) := by
  have hc : codeSize col+3 ≤ F+3 := by omega
  have hr : codeSize row+3 ≤ F+3 := by omega
  have hcy := Nat.mul_le_mul hy hc
  have hrx := Nat.mul_le_mul hx hr
  simp only [GeneratorSize.copies_size, codeSize]
  nlinarith

private theorem root_numeric (T : Nat) (hT : 1 ≤ T) :
    11+2*2^(29*T)*(2^(144*T)+3) ≤ 2^(180*T) := by
  let E := 2^(29*T)
  let F := 2^(144*T)
  let V := 2^(173*T)
  have hF : 1 ≤ F := by
    have hp : 0 < F := by
      dsimp [F]
      exact pow_pos (by decide : 0 < (2:Nat)) _
    omega
  have hF3 : F+3 ≤ 4*F := by omega
  have hmul := Nat.mul_le_mul_left (2*E) hF3
  have hEF : E*F = V := by
    dsimp [E,F,V]
    rw [← pow_add]
    congr 1
    omega
  have hV : 1 ≤ V := by
    have hp : 0 < V := by
      dsimp [V]
      exact pow_pos (by decide : 0 < (2:Nat)) _
    omega
  have hbase : 128 ≤ 2^(7*T) := by
    have hh : 7 ≤ 7*T := by omega
    have hp : 2^7 ≤ 2^(7*T) :=
      pow_le_pow_right₀ (by decide : 1 ≤ (2:Nat)) hh
    norm_num at hp ⊢
    exact hp
  have hlast : 11+8*V ≤ 2^(7*T)*V := by
    have hnum : 11+8*V ≤ 128*V := by omega
    exact hnum.trans (Nat.mul_le_mul_right V hbase)
  calc
    11+2*2^(29*T)*(2^(144*T)+3)
        = 11+2*E*(F+3) := rfl
    _ ≤ 11+8*(E*F) := by nlinarith [hmul]
    _ = 11+8*V := by rw [hEF]
    _ ≤ 2^(7*T)*V := hlast
    _ = 2^(180*T) := by
      dsimp [V]
      rw [← pow_add]
      congr 1
      omega

theorem linear_le_pow (T : Nat) (hT : 1 ≤ T) :
    73*T ≤ 2^(8*T) := by
  have ht := WidthDomination.nat_le_two_pow T
  have hm := Nat.mul_le_mul_left 73 ht
  have hstep : 73*T ≤ 128*2^T := by omega
  have hexp : T+7 ≤ 8*T := by omega
  calc
    73*T ≤ 128*2^T := hstep
    _ = 2^(T+7) := by
      rw [pow_add]
      norm_num
      ring
    _ ≤ 2^(8*T) :=
      pow_le_pow_right₀ (by decide : 1 ≤ (2:Nat)) hexp

theorem scheduled_root_size_le {n m : Nat} [NeZero n]
    (L Δ : Nat) (γ : Rat) (k : Nat)
    (hc : CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) L Δ γ) :
    let mX := sourceRows L (restorationDepth L)
      (coverDepth n m L Δ γ) k
    let mY := sourceCols L (restorationDepth L)
      (coverDepth n m L Δ γ) k
    codeSize (GeneratorFullSample.scheduledSampleCode
      n m L Δ γ k mX mY) ≤ 2^(180*(k+1)*L) := by
  let mX := sourceRows L (restorationDepth L)
    (coverDepth n m L Δ γ) k
  let mY := sourceCols L (restorationDepth L)
    (coverDepth n m L Δ γ) k
  let pair := GeneratorSource.scheduledCodes n m L Δ γ k
  let T := (k+1)*L
  obtain ⟨hx,hy⟩ := FairBitCap.scheduled_each_dimension_le L Δ γ hc k
  have hexp29 : 29*(k+1)*L = 29*T := by dsimp [T]; ring
  rw [hexp29] at hx hy
  have hp := GeneratorPublicCap.scheduled_serialized_length_le_two_pow
    L Δ γ k hc
  dsimp only at hp
  rw [GeneratorSerialization.encodeCode_length,
    GeneratorSerialization.encodeCode_length] at hp
  have hexp : 144*(k+1)*L = 144*T := by dsimp [T]; ring
  rw [hexp] at hp
  change codeSize pair.1+codeSize pair.2+1 ≤ 2^(144*T) at hp
  have hr := root_size_le mX mY (2^(29*T)) (2^(144*T))
    pair.1 pair.2 hx hy hp
  have hL : 16 ≤ L := by
    rcases hc with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hL, _⟩
    exact hL
  have hT : 1 ≤ T := by
    have hp : 0 < (k+1)*L :=
      Nat.mul_pos (by omega) (by omega)
    dsimp [T]
    omega
  have hn := root_numeric T hT
  have hexp180 : 180*(k+1)*L = 180*T := by dsimp [T]; ring
  rw [hexp180]
  dsimp only
  rw [GeneratorFullSample.scheduledSampleCode_columns_first]
  exact hr.trans hn

theorem scheduled_parameters_le {n m : Nat} [NeZero n]
    (L Δ : Nat) (γ : Rat) (k : Nat)
    (hc : CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) L Δ γ) :
    let mX := sourceRows L (restorationDepth L)
      (coverDepth n m L Δ γ) k
    let mY := sourceCols L (restorationDepth L)
      (coverDepth n m L Δ γ) k
    let root := GeneratorFullSample.scheduledSampleCode
      n m L Δ γ k mX mY
    let B := Nat.clog 2 (CodeFullRunConsumer.scheduledM n m L Δ γ)
    let N := CodeFullRunConsumer.scheduledN n m L Δ γ k mX mY
    let R := Paper2.rejectionAttemptCap N
    codeSize root ≤ 2^(180*(k+1)*L) ∧
      B ≤ 2^(180*(k+1)*L) ∧
      R ≤ 2^(180*(k+1)*L) ∧
      N ≤ 2^(180*(k+1)*L) := by
  let mX := sourceRows L (restorationDepth L)
    (coverDepth n m L Δ γ) k
  let mY := sourceCols L (restorationDepth L)
    (coverDepth n m L Δ γ) k
  let T := (k+1)*L
  have hL : 16 ≤ L := by
    rcases hc with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hL, _⟩
    exact hL
  have hT : 1 ≤ T := by
    have hp : 0 < (k+1)*L :=
      Nat.mul_pos (by omega) (by omega)
    dsimp [T]
    omega
  have hLT : L ≤ T := by
    dsimp [T]
    nlinarith
  have hlinear := linear_le_pow T hT
  have hpow : 2^(8*T) ≤ 2^(180*T) :=
    pow_le_pow_right₀ (by decide : 1 ≤ (2:Nat)) (by omega)
  have h73 : 73*T ≤ 2^(180*T) := hlinear.trans hpow
  have hroot := scheduled_root_size_le L Δ γ k hc
  have hB := FairBitCap.scheduled_alphabet_bitWidth_le L Δ γ hc
  have hN := FairBitCap.scheduled_drawCap_le L Δ γ hc k
  change CodeFullRunConsumer.scheduledN n m L Δ γ k mX mY ≤
    2^(60*(k+1)*L) at hN
  have hR := FairBitCap.rejectionAttemptCap_le_of_pow
    (CodeFullRunConsumer.scheduledN n m L Δ γ k mX mY)
    (60*T) (by
      convert hN using 1 <;> dsimp [T] <;> ring)
  have hNpow : 2^(60*T) ≤ 2^(180*T) :=
    pow_le_pow_right₀ (by decide : 1 ≤ (2:Nat)) (by omega)
  have hNfinal :
      CodeFullRunConsumer.scheduledN n m L Δ γ k mX mY ≤
        2^(180*T) := by
    calc
      _ ≤ 2^(60*T) := by convert hN using 1 <;> dsimp [T] <;> ring
      _ ≤ _ := hNpow
  have hBfinal :
      Nat.clog 2 (CodeFullRunConsumer.scheduledM n m L Δ γ) ≤
        2^(180*T) := by
    have hB' :
        Nat.clog 2 (CodeFullRunConsumer.scheduledM n m L Δ γ) ≤
          8*L := by convert hB using 1
    exact hB'.trans (by calc
      8*L ≤ 73*T := by omega
      _ ≤ _ := h73)
  have hRfinal :
      Paper2.rejectionAttemptCap
        (CodeFullRunConsumer.scheduledN n m L Δ γ k mX mY) ≤
          2^(180*T) := by
    exact hR.trans (by calc
      13+60*T ≤ 73*T := by omega
      _ ≤ _ := h73)
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hroot
  · simpa [T, Nat.mul_assoc] using hBfinal
  · simpa [T, mX, mY, Nat.mul_assoc] using hRfinal
  · simpa [T, mX, mY, Nat.mul_assoc] using hNfinal

#print axioms scheduled_root_size_le
#print axioms scheduled_parameters_le

end Paper2.CodeSamplerScheduledBounds
