import CurrentAdditive.V42ZeroArithmetic

namespace CurrentAdditive.V42ZeroAccess
noncomputable section
open Paper2 EthInapproximability.CurrentPaper
open V22UnaryExpression V42FullScheduleExpressions V42FullScheduleBatch V42FullSchedulePeak
open V42RuntimeSchedule V42RawSamplerJoin
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

theorem constructor_length_from_peaks (n k M : ℕ)
    (hp : ∀ i : Fin 19, (expressions i).peak n k ≤ M) :
    constructorLength n k ≤ 80*M := by
  have hv (i : Fin 19) := ((expressions i).eval_le_peak n k).trans (hp i)
  have hq2 : fullQ₂ (Nat.clog 2 n) ≤ M := by
    have h := hv 0; change q2.eval n k ≤ _ at h; simpa only [eval_q2] using h
  have hq1 : fullQ₁ (Nat.clog 2 n) ≤ M := by
    have h := hv 1; change q1.eval n k ≤ _ at h; simpa only [eval_q1] using h
  have hs : fullS (Nat.clog 2 n) ≤ M := by
    have h := hv 2; change s.eval n k ≤ _ at h; simpa only [eval_s] using h
  have hnn : n ≤ M := by exact hv 3
  have hw : fullW (Nat.clog 2 n) ≤ M := by
    have h := hv 4; change w.eval n k ≤ _ at h; simpa only [eval_w] using h
  have hQ : fullQ (Nat.clog 2 n) ≤ M := by
    have h := hv 5; change Q.eval n k ≤ _ at h; simpa only [eval_Q] using h
  have hseed : seedWidth (Nat.clog 2 n) ≤ M := by
    have h := hv 6; change seed.eval n k ≤ _ at h; simpa only [eval_seed] using h
  have hkk : k ≤ M := by exact hv 7
  have hm : sampleSide (Nat.clog 2 n) k ≤ M := by
    have h := hv 8; change sample.eval n k ≤ _ at h; simpa only [eval_sample] using h
  have hall (j : Constructor) : (constructorInput n k j).length ≤ M := by
    rcases j with j|(j|j)
    · fin_cases j <;> simp [constructor_core,Paper2.CodeRecursiveSeedPrep.publicBase] <;> omega
    · fin_cases j <;> simp [constructor_foreign,Paper2.CodeGeneratorSampleTransfer.foreign]
    · fin_cases j <;> simp only [constructor_foreign,Paper2.CodeGeneratorSampleTransfer.foreign,
        List.length_replicate,List.length_nil] <;> omega
  calc
    constructorLength n k ≤ ∑ _j : Constructor,M := Finset.sum_le_sum (fun j _ => hall j)
    _=80*M := by simp

/-- The actual zero-round raw sampler has its own bound, with the same
fixed program and actual zero-round constructor bank. -/
theorem sampler_clock_zero (graph : List Bool) (n edgeCount : ℕ) (cc δv ζ : ℚ)
    (hn : 2 ≤ n) (ht : FullTests cc (Nat.clog 2 n) edgeCount δv ζ) :
    V42RawSamplerJoin.clock graph n 0 ≤
      102*(graph.length+1)^3+2^(joinExponent*R n 1) := by
  have hR : 1 ≤ R n 1 := by have hL := ht.1.2.2.1; unfold R; nlinarith
  have hp := all_peaks_zero n edgeCount cc δv ζ hn ht
  have hc := constructor_length_from_peaks n 0 (cap n 1) hp
  have hraw := raw_graph_zero_exponential graph n edgeCount cc δv ζ hn ht
  have hshape := CurrentAdditive.V42ShapeClock.full_clock_le_exp n cc (Nat.clog 2 n)
    edgeCount 0 δv ζ (Nat.le_pow_clog (by decide) n) ht
  have hshape' : sampleClock n 0 ≤
      2^(CurrentAdditive.V42ShapeClock.fullExponent*R n 1) := by
    apply hshape.trans
    apply Nat.pow_le_pow_right (by decide)
    unfold R
    nlinarith
  have hb : V42RawSamplerJoin.precision n 0 ≤ cap n 1 := by
    have h := ((expressions (10 : Fin 19)).eval_le_peak n 0).trans (hp 10)
    change V42FullScheduleExpressions.precision.eval n 0 ≤ _ at h
    simpa only [eval_precision] using h
  let Z := 2^((V42FullScheduleClock.exponent+CurrentAdditive.V42ShapeClock.fullExponent+320)*R n 1)
  have hm : cap n 1 ≤ Z := Nat.pow_le_pow_right (by decide) (by nlinarith)
  have hr : 2^((V42FullScheduleClock.exponent+6)*R n 1) ≤ Z :=
    Nat.pow_le_pow_right (by decide) (by nlinarith)
  have hs : 2^(CurrentAdditive.V42ShapeClock.fullExponent*R n 1) ≤ Z :=
    Nat.pow_le_pow_right (by decide) (by nlinarith)
  have hone : 1 ≤ Z := Nat.one_le_two_pow
  have h1 : V42RawSamplerJoin.clock graph n 0 ≤ 102*(graph.length+1)^3+16384*Z := by
    unfold V42RawSamplerJoin.clock countClock
    nlinarith
  apply h1.trans
  apply Nat.add_le_add_left
  calc
    16384*Z=2^((V42FullScheduleClock.exponent+CurrentAdditive.V42ShapeClock.fullExponent+320)*R n 1+14) := by
      dsimp [Z]; rw [pow_add]; norm_num; ring
    _ ≤ 2^(joinExponent*R n 1) := Nat.pow_le_pow_right (by decide) (by unfold joinExponent; nlinarith)

def samplerExponent : ℕ := 2*joinExponent

/-- Quantitative raw-sampler access for every supplied natural round count.
The zero and positive cases use their own actual clocks. -/
theorem sampler_clock_all (graph : List Bool) (n K edgeCount : ℕ) (cc δv ζ : ℚ)
    (hn : 2 ≤ n) (ht : FullTests cc (Nat.clog 2 n) edgeCount δv ζ) :
    V42RawSamplerJoin.clock graph n K ≤
      102*(graph.length+1)^3+2^(samplerExponent*R n K) := by
  by_cases hK : K=0
  · subst K
    simpa only [samplerExponent,R,Nat.add_zero,Nat.zero_add,Nat.one_mul,
      Nat.reduceAdd,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using
      sampler_clock_zero graph n edgeCount cc δv ζ hn ht
  · have hp := V42RawSamplerJoin.clock_le_exp graph n K edgeCount cc δv ζ hn
      (by omega) ht
    apply hp.trans
    apply Nat.add_le_add_left
    apply Nat.pow_le_pow_right (by decide)
    exact Nat.mul_le_mul_right _ (by unfold samplerExponent; omega)

#print axioms constructor_length_from_peaks
#print axioms sampler_clock_zero
#print axioms sampler_clock_all
end
end CurrentAdditive.V42ZeroAccess


