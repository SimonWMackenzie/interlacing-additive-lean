import Paper2.GeneratorSize
import Mathlib.Tactic

/-! Public scheduled scalar caps for the literal first-order generators. -/

namespace Paper2.GeneratorPublicCap

open Paper2.GeneratorSize Paper2.GeneratorSource
  Paper2.GeneratorCode Paper2.GeneratorSerialization
  Paper2.ParameterizedCanonicalSource

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def publicCap (L : Nat) : Nat := 2 ^ (7 * L)

theorem scheduled_scalars_le_publicCap {n m : Nat} [NeZero n]
    (L Δ : Nat) (γ : ℚ)
    (hc : Paper2.CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) L Δ γ) :
    let M := publicCap L
    512 ≤ M ∧ n ≤ M ∧ LookupSeed.width L ≤ M ∧
      SourceProfileParameters.width L ≤ M ∧
      SourceProfileParameters.width L - 2 ≤ M ∧
      SourceProfileParameters.outerWidth L ≤ M ∧
      ParameterizedCanonicalSource.restorationWidth L ≤ M ∧
      ParameterizedCanonicalSource.coverWidth n m L Δ γ ≤ M := by
  rcases hc with ⟨_, hpopulation, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    hover, hL, hseed⟩
  let M := publicCap L
  have hM : 512 ≤ M := by
    dsimp [M, publicCap]
    have h9 : 9 ≤ 7*L := by omega
    exact (show 512 = 2^9 by norm_num).trans_le
      (pow_le_pow_right₀ (by omega) h9)
  have hExp : SourceProfileParameters.exponent L ≤ 7*L := by
    unfold Paper2.SourceOverheadBounds.overhead at hover
    omega
  have hOuter : SourceProfileParameters.outerExponent L ≤ 7*L := by
    unfold Paper2.SourceOverheadBounds.overhead at hover
    omega
  have hRest : ParameterizedCanonicalSource.restorationDepth L ≤ 7*L := by
    unfold Paper2.SourceOverheadBounds.overhead at hover
    dsimp [ParameterizedCanonicalSource.restorationDepth]
    omega
  have hCover : ParameterizedCanonicalSource.coverDepth n m L Δ γ ≤ 7*L := by
    unfold Paper2.SourceOverheadBounds.overhead at hover
    dsimp [ParameterizedCanonicalSource.coverDepth]
    omega
  have hp : LookupSeed.width L ≤ M := by
    have he : LookupSeed.exponent L ≤ 7*L := by omega
    unfold LookupSeed.width M publicCap
    exact pow_le_pow_right₀ (by omega) he
  have hs : SourceProfileParameters.width L ≤ M := by
    unfold SourceProfileParameters.width M publicCap
    exact pow_le_pow_right₀ (by omega) hExp
  have hq₁ : SourceProfileParameters.width L - 2 ≤ M :=
    (Nat.sub_le _ _).trans hs
  have hq₂ : SourceProfileParameters.outerWidth L ≤ M := by
    unfold SourceProfileParameters.outerWidth M publicCap
    exact pow_le_pow_right₀ (by omega) hOuter
  have hw : ParameterizedCanonicalSource.restorationWidth L ≤ M := by
    unfold ParameterizedCanonicalSource.restorationWidth
      RestorationWidthScheduleScratch.width M publicCap
    exact pow_le_pow_right₀ (by omega) hRest
  have hQ : ParameterizedCanonicalSource.coverWidth n m L Δ γ ≤ M := by
    rw [show ParameterizedCanonicalSource.coverWidth n m L Δ γ =
      2 ^ ParameterizedCanonicalSource.coverDepth n m L Δ γ from
        Paper2.SourceOverheadBounds.actualQ_pow
          (V := Fin n) (E := Fin m) L γ Δ]
    dsimp [M, publicCap]
    exact pow_le_pow_right₀ (by omega) hCover
  have hs4 : 4 ≤ SourceProfileParameters.width L := by
    have h := SourceProfileParameters.width_admissible L
    omega
  have hnq₂ : n ≤ SourceProfileParameters.outerWidth L := by
    simp only [Fintype.card_fin] at hpopulation
    omega
  exact ⟨hM, hnq₂.trans hq₂, hp, hs, hq₁, hq₂, hw, hQ⟩

theorem scheduled_serialized_length_le_two_pow {n m : Nat} [NeZero n]
    (L Δ : Nat) (γ : ℚ) (k : Nat)
    (hc : Paper2.CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) L Δ γ) :
    let pair := scheduledCodes n m L Δ γ k
    (encodeCode pair.1).length + (encodeCode pair.2).length + 1 ≤
      2 ^ (144 * (k+1) * L) := by
  let M := publicCap L
  obtain ⟨hM, hn, hp, hs, hq₁, hq₂, hw, hQ⟩ :=
    scheduled_scalars_le_publicCap L Δ γ hc
  have hsize := scheduled_serialized_length_le_cap M n m L Δ γ k
    hM hn hp hs hq₁ hq₂ hw hQ
  have hM1 : 1 ≤ M := by omega
  have hL : 16 ≤ L := by
    rcases hc with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hL, _⟩
    exact hL
  have hplus : M+1 ≤ 2^(8*L) := by
    calc
      M+1 ≤ 2*M := by omega
      _ = 2^(7*L+1) := by
        dsimp [M, publicCap]
        rw [pow_add]
        ring
      _ ≤ 2^(8*L) := pow_le_pow_right₀ (by omega) (by omega)
  have hpow := Nat.pow_le_pow_left hplus (18*(k+1))
  calc
    (encodeCode (scheduledCodes n m L Δ γ k).1).length +
        (encodeCode (scheduledCodes n m L Δ γ k).2).length + 1
      ≤ (M+1)^(18*(k+1)) := hsize
    _ ≤ (2^(8*L))^(18*(k+1)) := hpow
    _ = 2^(144*(k+1)*L) := by
      rw [← pow_mul]
      congr 1
      ring

theorem scheduled_nodes_le_two_pow {n m : Nat} [NeZero n]
    (L Δ : Nat) (γ : ℚ) (k : Nat)
    (hc : Paper2.CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) L Δ γ) :
    let pair := scheduledCodes n m L Δ γ k
    nodes pair.1 + nodes pair.2 + 1 ≤ 2 ^ (144 * (k+1) * L) := by
  have hsize := scheduled_serialized_length_le_two_pow L Δ γ k hc
  simp only [encodeCode_length] at hsize
  have hr := nodes_le_codeSize (scheduledCodes n m L Δ γ k).1
  have hc' := nodes_le_codeSize (scheduledCodes n m L Δ γ k).2
  omega

theorem scheduled_serialized_length_le_npow {n m : Nat} [NeZero n]
    (Δ : Nat) (γ : ℚ) (k : Nat)
    (hc : Paper2.CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) (Nat.clog 2 n) Δ γ) :
    let pair := scheduledCodes n m (Nat.clog 2 n) Δ γ k
    (encodeCode pair.1).length + (encodeCode pair.2).length + 1 ≤
      (n+2)^(288*(k+1)) := by
  let L := Nat.clog 2 n
  have hn : 0 < n := NeZero.pos n
  have hbase : 2^L ≤ (n+2)^2 := by
    have hd := Paper2.CappedSampler.ticketSize_le_twice n hn
    change 2^L ≤ 2*n at hd
    have hn2 : 2*n ≤ (n+2)^2 := by nlinarith
    exact hd.trans hn2
  have hpow := Nat.pow_le_pow_left hbase (144*(k+1))
  have hsize := scheduled_serialized_length_le_two_pow L Δ γ k hc
  calc
    (encodeCode (scheduledCodes n m L Δ γ k).1).length +
        (encodeCode (scheduledCodes n m L Δ γ k).2).length + 1
      ≤ 2^(144*(k+1)*L) := hsize
    _ = (2^L)^(144*(k+1)) := by
      rw [← pow_mul]
      congr 1
      ring
    _ ≤ ((n+2)^2)^(144*(k+1)) := hpow
    _ = (n+2)^(288*(k+1)) := by
      rw [← pow_mul]
      congr 1
      ring

#print axioms scheduled_scalars_le_publicCap
#print axioms scheduled_serialized_length_le_two_pow
#print axioms scheduled_nodes_le_two_pow
#print axioms scheduled_serialized_length_le_npow

end Paper2.GeneratorPublicCap
