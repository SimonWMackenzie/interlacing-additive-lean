import CurrentAdditive.V42RandomizedETHFits
import CurrentAdditive.V42RawSamplerJoin

namespace CurrentAdditive.V42RandomizedETHEndpoint
noncomputable section
open Paper2 V42PublicSchedule V42RuntimeSchedule
open Paper2.Unit4Shell.Asymptotics
set_option maxHeartbeats 3000000
set_option maxRecDepth 65536

theorem construction_bits_source_power (n edgeCount k : ℕ) (hn : 1 ≤ n)
    (cc δv ζ : ℚ) (ht : V42RuntimeSchedule.FullTests cc (Nat.clog 2 n) edgeCount δv ζ) :
    V42RawSamplerJoin.precision n k * V42RawSamplerJoin.reservation n k ≤
      (n+2)^(544*(k+1)) := by
  have hb := V42RuntimeSchedule.reserved_bits_le n (Nat.clog 2 n) k
    (Nat.le_pow_clog (by decide) _) ht.2
  have hc : 2^(Nat.clog 2 n) ≤ (n+2)^2 := by
    have h := V39PublicSchedule.pow2Ceil_lt_twice n (by omega)
    change 2^(Nat.clog 2 n) < 2*n at h
    nlinarith
  calc
    _ ≤ 2^(272*(k+1)*Nat.clog 2 n) := hb
    _ = (2^(Nat.clog 2 n))^(272*(k+1)) := by rw [←pow_mul]; congr 1; ring
    _ ≤ ((n+2)^2)^(272*(k+1)) := Nat.pow_le_pow_left hc _
    _ = _ := by rw [←pow_mul]; congr 1; ring

theorem construction_bits_fit (p : ℕ) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ n edgeCount,
      1 ≤ n → n ≤ N*(Nat.clog 2 (N+2))^p → ∀ cc δv ζ : ℚ,
      V42RuntimeSchedule.FullTests cc (Nat.clog 2 n) edgeCount δv ζ →
      V42RawSamplerJoin.precision n (kOf N)*
        V42RawSamplerJoin.reservation n (kOf N) ≤ AEth.expLen N := by
  obtain ⟨N₀,h⟩ := AEth.budget_numeric 544 p
  refine ⟨N₀,?_⟩
  intro N hN n edgeCount hn hs cc δv ζ ht
  apply (construction_bits_source_power n edgeCount (kOf N) hn cc δv ζ ht).trans
  exact h N hN n N hs le_rfl
    ((show N ≤ N+2 by omega).trans (Nat.le_self_pow (by decide) (N+2)))

def classifierBlockExponent (C : SelectedTape.Algorithm) : ℕ := C.cR+1

theorem independent_block_fits (C : SelectedTape.Algorithm) (r L s : ℕ)
    (hr : r ≤ L) (hs : s ≤ C.cR*r) :
    L+s ≤ 2^(classifierBlockExponent C)*L := by
  have hs' := hs.trans (Nat.mul_le_mul_left C.cR hr)
  calc
    L+s ≤ L+C.cR*L := Nat.add_le_add_left hs' L
    _ = (C.cR+1)*L := by rw [Nat.add_mul,Nat.one_mul,Nat.add_comm]
    _ ≤ 2^(classifierBlockExponent C)*L :=
      Nat.mul_le_mul_right _ (Nat.lt_two_pow_self.le)

/-- The construction uses its literal new-width bit reservation and the
classifier reads a disjoint bounded suffix. Both resource inequalities are
derived; no run or desired probability law is supplied. -/
theorem current_two_blocks_fit (C : SelectedTape.Algorithm) (p : ℕ) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ n edgeCount L,
      1 ≤ n → n ≤ N*(Nat.clog 2 (N+2))^p → AEth.expLen N ≤ L →
      ∀ cc δv ζ : ℚ, V42RuntimeSchedule.FullTests cc (Nat.clog 2 n) edgeCount δv ζ →
      V42RawSamplerJoin.precision n (kOf N)*V42RawSamplerJoin.reservation n (kOf N) ≤ L ∧
      ∀ f : Fin (V42PublicSchedule.sampleSide (Nat.clog 2 n) (kOf N)) →
        Fin (V42PublicSchedule.sampleSide (Nat.clog 2 n) (kOf N)) → Bool,
      L+C.tapeLength (requestedWord (Nat.clog 2 n) (kOf N) f) ≤
        2^(classifierBlockExponent C)*L := by
  obtain ⟨Nb,hb⟩ := construction_bits_fit p
  obtain ⟨Nc,hc⟩ := classifier_fits C p
  refine ⟨max Nb Nc,?_⟩
  intro N hN n edgeCount L hn hs hL cc δv ζ ht
  refine ⟨(hb N ((le_max_left _ _).trans hN) n edgeCount hn hs cc δv ζ ht).trans hL,?_⟩
  intro f
  exact independent_block_fits C (AEth.expLen N) L _ hL
    (hc N ((le_max_right _ _).trans hN) n hn hs f).1

#print axioms construction_bits_source_power
#print axioms construction_bits_fit
#print axioms independent_block_fits
#print axioms current_two_blocks_fit
end
end CurrentAdditive.V42RandomizedETHEndpoint
