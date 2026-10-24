import CurrentAdditive.V40RandomizedETHFits
import CurrentAdditive.V39PhysicalFullSample

/-! Fit the actual reserved construction bits and the actual independent
classifier prefix inside the existing physical source cut. -/
namespace CurrentAdditive.V40RandomizedETHEndpoint
noncomputable section
open Paper2 V38Schedule V39PublicSchedule
open Paper2.Unit4Shell.Asymptotics
set_option maxHeartbeats 200000
set_option maxRecDepth 8192

theorem construction_bits_source_power (n edgeCount k : ℕ) (hn : 1 ≤ n)
    (cc δv ζ : ℚ) (ht : FullTests cc (Nat.clog 2 n) edgeCount δv ζ) :
    V39PhysicalSample.fullPrecision n (Nat.clog 2 n) k *
      V39PhysicalSample.fullReservation (Nat.clog 2 n) k ≤
        (n+2)^(1484*(k+1)) := by
  have hb := V39PhysicalSample.full_reserved_bits_le n cc (Nat.clog 2 n) edgeCount k
    δv ζ (Nat.le_pow_clog (by decide) _) ht
  have he := binary_clock_and_entries 240 n k hn
  have h2 : 2 ≤ (n+2)^(4*(k+1)) := by
    apply (show 2 ≤ n+2 by omega).trans
    exact Nat.le_self_pow (by omega) _
  calc
    _ ≤ 2^(240*((k+1)*Nat.clog 2 n)) := hb
    _ ≤ 2^(240*((k+1)*Nat.clog 2 n))+
        sampleEntries (Nat.clog 2 n) k := Nat.le_add_right _ _
    _ ≤ 2*(n+2)^(1480*(k+1)) := he
    _ ≤ (n+2)^(4*(k+1))*(n+2)^(1480*(k+1)) := Nat.mul_le_mul_right _ h2
    _ = _ := by rw [←pow_add]; congr 1; ring

theorem construction_bits_fit (p : ℕ) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ n edgeCount,
      1 ≤ n → n ≤ N*(Nat.clog 2 (N+2))^p → ∀ cc δv ζ : ℚ,
      FullTests cc (Nat.clog 2 n) edgeCount δv ζ →
      V39PhysicalSample.fullPrecision n (Nat.clog 2 n) (kOf N) *
        V39PhysicalSample.fullReservation (Nat.clog 2 n) (kOf N) ≤ AEth.expLen N := by
  obtain ⟨N₀,h⟩ := AEth.budget_numeric 1484 p
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

/-- These are exactly the two resource inequalities required by the
single-uniform-tape all-event law and the physical prefix cutter. -/
theorem current_two_blocks_fit (C : SelectedTape.Algorithm) (p : ℕ) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ n edgeCount L,
      1 ≤ n → n ≤ N*(Nat.clog 2 (N+2))^p → AEth.expLen N ≤ L →
      ∀ cc δv ζ : ℚ, FullTests cc (Nat.clog 2 n) edgeCount δv ζ →
      V39PhysicalSample.fullPrecision n (Nat.clog 2 n) (kOf N)*
          V39PhysicalSample.fullReservation (Nat.clog 2 n) (kOf N) ≤ L ∧
      ∀ f : Fin (sampleSide (Nat.clog 2 n) (kOf N)) →
        Fin (sampleSide (Nat.clog 2 n) (kOf N)) → Bool,
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
end CurrentAdditive.V40RandomizedETHEndpoint
