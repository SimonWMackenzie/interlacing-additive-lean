import CurrentAdditive.V40RandomizedETHFits
import CurrentAdditive.V22PhysicalRawTableClock

/-! Eventual fit for the exact physical raw-constructor clock and the
actual number of printed entries, measured in the original variable count. -/
namespace CurrentAdditive.V40RandomizedETHEndpoint
noncomputable section
open Paper2
open Paper2.Unit4Shell.Asymptotics
open EthInapproximability.CurrentPaper
open V38Schedule V39PublicSchedule
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

/-- The bound uses the actual fixed constructor clock, rather than a
promised running time. The same entry count is used by the requester. -/
theorem raw_clock_and_entries_fit (p : ℕ) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ (g : EncodedGraph.Graph),
      g.Valid → 1 ≤ g.vertices →
      g.vertices ≤ N*(Nat.clog 2 (N+2))^p →
      ∀ (cc δv ζ : ℚ),
      FullTests cc (Nat.clog 2 g.vertices) g.edges.length δv ζ →
      V39WRaw.clock g (kOf N) + sampleEntries (Nat.clog 2 g.vertices) (kOf N) ≤
        AEth.expLen N := by
  let E := V22FullTableClock.rawTableExponent+440
  obtain ⟨Nb,hb⟩ := AEth.budget_numeric (2*E+1004) p
  obtain ⟨Nk,hk⟩ := V39ETHArithmetic.iterations_eventually_ge 1
  refine ⟨max Nb Nk,?_⟩
  intro N hN g hg hn hs cc δv ζ ht
  have hr := V22FullTableClock.raw_table_pure g hg (kOf N) cc δv ζ
    (hk N ((le_max_right _ _).trans hN)) ht
  rw [←V22FullTableClock.physical_clock_eq] at hr
  have hbin := binary_clock_and_entries E g.vertices (kOf N) hn
  have htwo : 2 ≤ (g.vertices+2)^(4*(kOf N+1)) := by
    have hbase : 2 ≤ g.vertices+2 := by omega
    have hpos : 1 ≤ 4*(kOf N+1) := by omega
    exact hbase.trans (Nat.le_self_pow (by omega) _)
  have hsource := hb N ((le_max_left _ _).trans hN) g.vertices N hs le_rfl
    ((show N ≤ N+2 by omega).trans (Nat.le_self_pow (by decide) (N+2)))
  calc
    _ ≤ 2^(E*((kOf N+1)*Nat.clog 2 g.vertices)) +
        sampleEntries (Nat.clog 2 g.vertices) (kOf N) := by
      exact Nat.add_le_add_right hr _
    _ ≤ 2*(g.vertices+2)^((2*E+1000)*(kOf N+1)) := hbin
    _ ≤ (g.vertices+2)^(4*(kOf N+1)) *
        (g.vertices+2)^((2*E+1000)*(kOf N+1)) := Nat.mul_le_mul_right _ htwo
    _ = (g.vertices+2)^((2*E+1004)*(kOf N+1)) := by
      rw [←pow_add]
      exact congrArg (fun r : ℕ => (g.vertices+2)^r)
        ((show ∀ (e k : ℕ), 4*(k+1)+(2*e+1000)*(k+1) =
          (2*e+1004)*(k+1) from by intros; ring) E (kOf N))
    _ ≤ _ := hsource


/-- The graph bytes physically parsed by that same raw constructor fit the
same source budget; this is the actual graph encoding, with no prepared bank. -/
theorem graph_bytes_fit (p : ℕ) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ (g : EncodedGraph.Graph),
      g.Valid → 1 ≤ g.vertices →
      g.vertices ≤ N*(Nat.clog 2 (N+2))^p →
      ∀ (cc δv ζ : ℚ),
      FullTests cc (Nat.clog 2 g.vertices) g.edges.length δv ζ →
      (EncodedGraph.encode g).length ≤ AEth.expLen N := by
  obtain ⟨N₀,hb⟩ := AEth.budget_numeric 80 p
  refine ⟨N₀,?_⟩
  intro N hN g hg hn hs cc δv ζ ht
  have hr := V22FullTableClock.graph_size_full g hg cc δv ζ
    (Nat.clog 2 g.vertices) (Nat.le_pow_clog (by decide) _) ht
  have hc : 2^(Nat.clog 2 g.vertices) ≤ (g.vertices+2)^2 := by
    have h := V39PublicSchedule.pow2Ceil_lt_twice g.vertices (by omega)
    change 2^(Nat.clog 2 g.vertices) < 2*g.vertices at h
    nlinarith
  have hsource := hb N hN g.vertices N hs le_rfl
    ((show N ≤ N+2 by omega).trans (Nat.le_self_pow (by decide) (N+2)))
  calc
    _ ≤ V22FullTableClock.graphSize g := by unfold V22FullTableClock.graphSize; omega
    _ ≤ 2^(40*Nat.clog 2 g.vertices) := hr
    _ = (2^(Nat.clog 2 g.vertices))^40 := by rw [←pow_mul]; congr 1; omega
    _ ≤ ((g.vertices+2)^2)^40 := Nat.pow_le_pow_left hc _
    _ = (g.vertices+2)^80 := by rw [←pow_mul]
    _ ≤ (g.vertices+2)^(80*(kOf N+1)) := Nat.pow_le_pow_right (by omega) (by omega)
    _ ≤ _ := hsource

#print axioms graph_bytes_fit

#print axioms raw_clock_and_entries_fit
end
end CurrentAdditive.V40RandomizedETHEndpoint
