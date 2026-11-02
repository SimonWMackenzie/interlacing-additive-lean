import CurrentAdditive.QuarticAtoms
import Paper2.CodeSamplerScheduledBounds

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

namespace Paper2.CurrentAdditive.QuarticRootCap

open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.RecursiveSamplingExecution
open Paper2.SourceProfileParameters Paper2.SourceRecursiveNoSampling
open Paper2.ParameterizedCanonicalSource
open CurrentAdditive.RandomizedSchedule

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

theorem root_size27 {n m : Nat} [NeZero n]
    (L Δ : Nat) (γ : Rat) (k : Nat)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) L Δ γ) :
    let mX := sourceRows L (4 * RestorationWidthScheduleScratch.ell L)
      (q27 (V := Fin n) (E := Fin m) L γ Δ) k
    let mY := sourceCols L (4 * RestorationWidthScheduleScratch.ell L)
      (q27 (V := Fin n) (E := Fin m) L γ Δ) k
    codeSize (CodeFallbackSourceResult.sampleRoot n (LookupSeed.width L)
      (width L) (width L - 2) (outerWidth L) (width27 L)
      (Q27 (V := Fin n) (E := Fin m) L γ Δ) k mX mY) ≤
      2^(180*(k+1)*L) := by
  let mX := sourceRows L (4 * RestorationWidthScheduleScratch.ell L)
    (q27 (V := Fin n) (E := Fin m) L γ Δ) k
  let mY := sourceCols L (4 * RestorationWidthScheduleScratch.ell L)
    (q27 (V := Fin n) (E := Fin m) L γ Δ) k
  let pair := GeneratorSource.seedRecursiveCodes n (LookupSeed.width L) (width L) (width L - 2) (outerWidth L)
    (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ) k
  let T := (k+1)*L
  obtain ⟨hx,hy⟩ := QuarticClockCaps.dims_cap27 L Δ γ hc k
  have hexp29 : 29*(k+1)*L = 29*T := by dsimp [T]; ring
  rw [hexp29] at hx hy
  have hp := QuarticClockCaps.code_size27 L Δ γ hc k
  dsimp only at hp
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
  dsimp [CodeFallbackSourceResult.sampleRoot]
  exact hr.trans hn


end Paper2.CurrentAdditive.QuarticRootCap

#print axioms Paper2.CurrentAdditive.QuarticRootCap.root_size27
