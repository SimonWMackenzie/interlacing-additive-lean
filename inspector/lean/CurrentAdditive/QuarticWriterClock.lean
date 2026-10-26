import CurrentAdditive.QuarticSCFinal
import Paper2.SuccessPremiseComposition

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

namespace Paper2.CurrentAdditive.QuarticWriterClock

open Paper2.SourceRecursiveNoSampling Paper2.ParameterizedCanonicalSource
open CurrentAdditive.RandomizedSchedule

theorem writerBound_entry27 {n m : Nat} [NeZero n]
    (L Δ : Nat) (γ : ℚ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) L Δ γ) (k Tent cE : Nat)
    (hent : Tent ≤ 2 ^ (cE * (k + 1) * L)) :
    EthInapproximability.CurrentPaper.MatrixTableWriter.writerBound
      (sourceRows L (4 * RestorationWidthScheduleScratch.ell L) (q27 (V := Fin n) (E := Fin m) L γ Δ) k)
      (sourceCols L (4 * RestorationWidthScheduleScratch.ell L) (q27 (V := Fin n) (E := Fin m) L γ Δ) k) Tent ≤
      2 ^ ((cE + 63) * (k + 1) * L) := by
  let T := (k + 1) * L
  have hL : 16 ≤ L := by
    rcases hc with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hL, _⟩
    exact hL
  have hT : 1 ≤ T := by
    have hp : 0 < (k + 1) * L := Nat.mul_pos (by omega) (by omega)
    dsimp [T]; omega
  obtain ⟨hx, hy⟩ := QuarticClockCaps.dims_cap27 L Δ γ hc k
  have e29 : 29 * (k + 1) * L = 29 * T := by dsimp [T]; ring
  have eE : cE * (k + 1) * L = cE * T := by dsimp [T]; ring
  rw [e29] at hx hy
  rw [eE] at hent
  have e63 : (cE + 63) * (k + 1) * L = (cE + 63) * T := by dsimp [T]; ring
  rw [e63]
  generalize sourceRows L (4 * RestorationWidthScheduleScratch.ell L) (q27 (V := Fin n) (E := Fin m) L γ Δ) k = r at hx ⊢
  generalize sourceCols L (4 * RestorationWidthScheduleScratch.ell L) (q27 (V := Fin n) (E := Fin m) L γ Δ) k = c at hy ⊢
  let E := 2 ^ (29 * T)
  let X := 2 ^ (cE * T)
  have hE : 1 ≤ E := Nat.one_le_two_pow
  have hX : 1 ≤ X := Nat.one_le_two_pow
  have hr : r ≤ E := hx
  have hc' : c ≤ E := hy
  have ht : Tent ≤ X := hent
  have hinner : c * (Tent + 2) + 4 * c + 8 ≤ 15 * (E * X) := by
    have h1 : c * (Tent + 2) ≤ E * (X + 2) := Nat.mul_le_mul hc' (by omega)
    have h2 : E ≤ E * X := by nlinarith
    have h3 : 1 ≤ E * X := by nlinarith
    nlinarith
  have hwb : EthInapproximability.CurrentPaper.MatrixTableWriter.writerBound r c Tent ≤
      20 * (E * (E * X)) := by
    unfold EthInapproximability.CurrentPaper.MatrixTableWriter.writerBound
    have h1 : r * (c * (Tent + 2) + 4 * c + 8) ≤ E * (15 * (E * X)) :=
      Nat.mul_le_mul hr hinner
    have h3 : 1 ≤ E * (E * X) := by
      have := Nat.mul_le_mul hE (show 1 ≤ E * X by nlinarith)
      simpa using this
    nlinarith
  have hpow : 20 * (E * (E * X)) ≤ 2 ^ ((cE + 63) * T) := by
    have h5 : 20 ≤ 2 ^ (5 * T) := by
      have : 2 ^ 5 ≤ 2 ^ (5 * T) := pow_le_pow_right₀ (by decide) (by omega)
      norm_num at this ⊢; omega
    calc
      20 * (E * (E * X)) ≤ 2 ^ (5 * T) * (E * (E * X)) := Nat.mul_le_mul_right _ h5
      _ = 2 ^ (5 * T + (29 * T + (29 * T + cE * T))) := by
        dsimp [E, X]; rw [← pow_add, ← pow_add, ← pow_add]
      _ ≤ 2 ^ ((cE + 63) * T) :=
        pow_le_pow_right₀ (by decide : 1 ≤ (2:Nat)) (by nlinarith)
  exact hwb.trans hpow

theorem fallback_writer27 {n m : Nat} [NeZero n]
    (L Δ : Nat) (γ : ℚ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) L Δ γ) (k : Nat) :
    EthInapproximability.CurrentPaper.MatrixTableWriter.writerBound
      (sourceRows L (4 * RestorationWidthScheduleScratch.ell L)
        (q27 (V := Fin n) (E := Fin m) L γ Δ) k)
      (sourceCols L (4 * RestorationWidthScheduleScratch.ell L)
        (q27 (V := Fin n) (E := Fin m) L γ Δ) k) 1 ≤
      2 ^ (64 * (k + 1) * L) := by
  have h := writerBound_entry27 L Δ γ hc k 1 0 (by simp)
  have he : (0 + 63) * (k + 1) * L ≤ 64 * (k + 1) * L :=
    Nat.mul_le_mul_right L (Nat.mul_le_mul_right (k + 1) (by omega))
  exact h.trans (pow_le_pow_right₀ (by norm_num) he)

end Paper2.CurrentAdditive.QuarticWriterClock

#print axioms Paper2.CurrentAdditive.QuarticWriterClock.writerBound_entry27
#print axioms Paper2.CurrentAdditive.QuarticWriterClock.fallback_writer27
