import CurrentAdditive.V42FullSuccessor
import CurrentAdditive.V42PublicCutoff
import CurrentAdditive.V42FixedPromiseCutoff

/-! An effective graph-size cutoff for the replacement full-product
construction. It depends only on the fixed graph promise constants. -/
namespace CurrentAdditive.V42FullCutoff
open V42Schedule V42PublicSchedule V42PublicCutoff

def sourceCutoff (γ : ℚ) (Δ : ℕ) : ℕ :=
  max (V39FullCutoff.sourceCutoff γ Δ)
    (2^(fullLengthCutoff (fixedPromiseCutoff γ Δ)))

theorem bounds (γ : ℚ) (Δ n m : ℕ) (hγ : 0<γ) (hΔ : 0<Δ)
    (hn : 0<n) (hnm : n≤2*m) (hlarge : sourceCutoff γ Δ≤n) :
    V39FullCutoff.sourceCutoff γ Δ≤n ∧
    commonCutoff (V38Schedule.sourceDeltaV γ Δ n m) (V38Schedule.sourceZeta γ) Δ≤
      fullExponent (Nat.clog 2 n) ∧
    4*fullExponent (Nat.clog 2 n)≤Nat.clog 2 n ∧
    16≤Nat.clog 2 n ∧ seedCost (Nat.clog 2 n)≤Nat.clog 2 n ∧
    fullOverhead (Nat.clog 2 n)≤7*Nat.clog 2 n := by
  have hnOld : V39FullCutoff.sourceCutoff γ Δ≤n := (le_max_left _ _).trans hlarge
  have hnPow : 2^(fullLengthCutoff (fixedPromiseCutoff γ Δ))≤n :=
    (le_max_right _ _).trans hlarge
  have hlog:=Nat.clog_mono_right 2 hnPow
  rw [Nat.clog_pow 2 _ (by decide)] at hlog
  obtain ⟨hK,hL,hseed,hover,hb⟩:=full_cutoff_bounds (fixedPromiseCutoff γ Δ) (Nat.clog 2 n) hlog
  exact ⟨hnOld,fixedPromiseCutoff_graph γ Δ n m _ hγ hΔ hn hnm hK,hb,hL,hseed,hover⟩

#print axioms bounds
end CurrentAdditive.V42FullCutoff
