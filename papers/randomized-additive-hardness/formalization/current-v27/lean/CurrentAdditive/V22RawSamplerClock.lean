import CurrentAdditive.V22RawSamplerJoin
import CurrentAdditive.V39PhysicalShapeClock

set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 16384
namespace V22RawSamplerJoin
noncomputable section
open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open V22FullScheduleBatch V22FullSchedulePeak V22FullScheduleExpressions V22UnaryExpression
open V38Schedule V39PublicSchedule V39FullSampleResources
open CurrentAdditive.V38OneStep CurrentAdditive.V39RecursiveGenerator

theorem constructor_length_le (n k edgeCount : ℕ) (cc δv ζ : ℚ)
    (hn : 2 ≤ n) (hk : 1 ≤ k) (ht : FullTests cc (Nat.clog 2 n) edgeCount δv ζ) :
    constructorLength n k ≤ 80*cap n k := by
  have hp := all_peaks n k edgeCount cc δv ζ hn hk ht
  have hv (i : Fin 19) := ((expressions i).eval_le_peak n k).trans (hp i)
  have hq2 : fullQ₂ (Nat.clog 2 n) ≤ cap n k := by
    have h := hv 0; change q2.eval n k ≤ _ at h; simpa only [eval_q2] using h
  have hq1 : fullQ₁ (Nat.clog 2 n) ≤ cap n k := by
    have h := hv 1; change q1.eval n k ≤ _ at h; simpa only [eval_q1] using h
  have hs : fullS (Nat.clog 2 n) ≤ cap n k := by
    have h := hv 2; change s.eval n k ≤ _ at h; simpa only [eval_s] using h
  have hnn : n ≤ cap n k := by exact hv 3
  have hw : fullW (Nat.clog 2 n) ≤ cap n k := by
    have h := hv 4; change w.eval n k ≤ _ at h; simpa only [eval_w] using h
  have hQ : fullQ (Nat.clog 2 n) ≤ cap n k := by
    have h := hv 5; change Q.eval n k ≤ _ at h; simpa only [eval_Q] using h
  have hseed : seedWidth (Nat.clog 2 n) ≤ cap n k := by
    have h := hv 6; change seed.eval n k ≤ _ at h; simpa only [eval_seed] using h
  have hkk : k ≤ cap n k := by exact hv 7
  have hm : sampleSide (Nat.clog 2 n) k ≤ cap n k := by
    have h := hv 8; change sample.eval n k ≤ _ at h; simpa only [eval_sample] using h
  have hall (j : Constructor) : (constructorInput n k j).length ≤ cap n k := by
    rcases j with j|(j|j)
    · fin_cases j <;> simp [constructor_core,Paper2.CodeRecursiveSeedPrep.publicBase] <;> omega
    · fin_cases j <;> simp [constructor_foreign,Paper2.CodeGeneratorSampleTransfer.foreign]
    · fin_cases j <;> simp only [constructor_foreign,Paper2.CodeGeneratorSampleTransfer.foreign,
        List.length_replicate,List.length_nil] <;> omega
  calc
    constructorLength n k ≤ ∑ _j : Constructor,cap n k := Finset.sum_le_sum (fun j _ => hall j)
    _=80*cap n k := by simp

def joinExponent : ℕ := V22FullScheduleClock.exponent+CurrentAdditive.V39PhysicalShapeSample.fullExponent+334

/-- The exact physical clock, including graph parsing and every constructor
and precision copy, has one source-uniform exponential bound. -/
theorem clock_le_exp (graph : List Bool) (n k edgeCount : ℕ) (cc δv ζ : ℚ)
    (hn : 2 ≤ n) (hk : 1 ≤ k) (ht : FullTests cc (Nat.clog 2 n) edgeCount δv ζ) :
    clock graph n k ≤ 102*(graph.length+1)^3+2^(joinExponent*R n k) := by
  have hR : 1 ≤ R n k := by have hL := ht.2.2.1; unfold R; nlinarith
  have hc := constructor_length_le n k edgeCount cc δv ζ hn hk ht
  have hraw := V22FullScheduleClock.raw_exponential graph n k edgeCount cc δv ζ hn hk ht
  have hshape := CurrentAdditive.V39PhysicalShapeSample.full_clock_le_exp n cc (Nat.clog 2 n)
    edgeCount k δv ζ (Nat.le_pow_clog (by decide) n) ht
  change sampleClock n k ≤ 2^(CurrentAdditive.V39PhysicalShapeSample.fullExponent*R n k) at hshape
  have hp := all_peaks n k edgeCount cc δv ζ hn hk ht
  have hb : precision n k ≤ cap n k := by
    have h := ((expressions (10 : Fin 19)).eval_le_peak n k).trans (hp 10)
    change V22FullScheduleExpressions.precision.eval n k ≤ _ at h
    simpa only [eval_precision] using h
  let Z := 2^((V22FullScheduleClock.exponent+CurrentAdditive.V39PhysicalShapeSample.fullExponent+320)*R n k)
  have hm : cap n k ≤ Z := Nat.pow_le_pow_right (by decide) (by nlinarith)
  have hr : 2^((V22FullScheduleClock.exponent+6)*R n k) ≤ Z :=
    Nat.pow_le_pow_right (by decide) (by nlinarith)
  have hs : 2^(CurrentAdditive.V39PhysicalShapeSample.fullExponent*R n k) ≤ Z :=
    Nat.pow_le_pow_right (by decide) (by nlinarith)
  have hone : 1 ≤ Z := Nat.one_le_two_pow
  have h1 : clock graph n k ≤ 102*(graph.length+1)^3+16384*Z := by
    unfold clock countClock
    nlinarith
  apply h1.trans
  apply Nat.add_le_add_left
  calc
    16384*Z=2^((V22FullScheduleClock.exponent+CurrentAdditive.V39PhysicalShapeSample.fullExponent+320)*R n k+14) := by
      dsimp [Z]; rw [pow_add]; norm_num; ring
    _ ≤ 2^(joinExponent*R n k) := Nat.pow_le_pow_right (by decide) (by unfold joinExponent; nlinarith)

#print axioms constructor_length_le
#print axioms clock_le_exp
end
end V22RawSamplerJoin
