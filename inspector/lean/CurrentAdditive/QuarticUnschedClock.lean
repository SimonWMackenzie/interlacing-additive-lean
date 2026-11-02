import CurrentAdditive.QuarticUnschedRun
import Paper2.A3H3ClockB
import Paper2.A3H3Size

/-!
# Unit 3 endpoint (H_A3 closure), segment 2 addendum: the not-hc branch clock `clockU` in H_A3 shape

Lane `owner:a-h-a3-assembly-3` (private, 26 September 2026). Pure arithmetic.

`QuarticUnschedRun.clockU27` is the literal clock of the frozen private lane a-h-a3-assembly-owner-2 theorem
`Unsched.unscheduled_run` (graph decoding, charged copies, the admitted `FallbackFiniteClock` table clock,
charged copies, the admitted header). Under the degree bound and `1 ≤ k` it is at most
`CU·(n+2)^(6(k+1))` with `CU = 103(2Δ+1)^3 + 6Δ + coefficient(sizeThreshold Δ γ) Δ + 12·coef + 77`.
-/

set_option maxHeartbeats 4000000

namespace Paper2.CurrentAdditive.QuarticUnschedClock

open EthInapproximability.CurrentPaper
open Paper2.A3Assembly.Clocks
open Paper2.A3Assembly
open Paper2

/-- The not-hc branch constant. -/
noncomputable def CU27 (Δ : ℕ) (γ : ℚ) : ℕ :=
  103 * (2 * Δ + 1) ^ 3 + 6 * Δ +
    FallbackFiniteClock.coefficient (CurrentAdditive.QuarticSchedule.threshold27 Δ γ) Δ +
    12 * UnaryBinaryEncoding.coefficient + 77

theorem unsched_header_eq (k : ℕ) :
    Unsched.headerClock k = headerClock (FiniteFallbackOutput.rows k) (FiniteFallbackOutput.cols k) 0 :=
  rfl

/-- **(U, whole branch)** The literal clock of `Unsched.unscheduled_run` in H_A3 shape. -/
theorem clockU_HA3_27 (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices) (Δ : ℕ) (γ : ℚ)
    (k : ℕ) (hk : 1 ≤ k)
    (hdeg : ∀ v, SourceItems.degree (CanonicalEdgeTape.graphEdge g hg) v ≤ Δ) :
    QuarticUnschedRun.clockU27 g hg Δ γ k ≤ CU27 Δ γ * (g.vertices + 2) ^ (6 * (k + 1)) := by
  set Z := (g.vertices + 2) ^ (6 * (k + 1)) with hZ
  have hZ1 : 1 ≤ Z := Nat.one_le_pow _ _ (by omega)
  have hsq : (g.vertices + 2) ^ 2 ≤ Z := Nat.pow_le_pow_right (by omega) (by omega)
  have h6 : (g.vertices + 2) ^ 6 ≤ Z := Nat.pow_le_pow_right (by omega) (by omega)
  have hsq' : (g.vertices + 2) * (g.vertices + 2) ≤ Z := by simpa only [pow_two] using hsq
  have hnZ : g.vertices ≤ Z := by nlinarith
  have h2k : 2 ^ k ≤ (g.vertices + 2) ^ k := Nat.pow_le_pow_left (by omega) k
  have hkZ : k ≤ Z := by
    have h1 : k < 2 ^ k := Nat.lt_two_pow_self
    have h2 : (g.vertices + 2) ^ k ≤ Z := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have h3k : 2 ^ (3 * k) ≤ Z :=
    (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) (by omega))
  -- edges from the degree bound
  have hm : 2 * g.edges.length ≤ Δ * g.vertices := Paper2.A3Assembly.Size.twice_edges_le g hg hn Δ hdeg
  -- graph code
  have hG := EncodedGraph.encode_length_upper g hg
  have hmn : g.edges.length * (4 * g.vertices + 4) ≤ 2 * Δ * ((g.vertices + 2) * (g.vertices + 2)) := by
    have e : g.edges.length * (4 * g.vertices + 4) = (2 * g.edges.length) * (2 * g.vertices + 2) := by ring
    rw [e]
    calc (2 * g.edges.length) * (2 * g.vertices + 2) ≤ (Δ * g.vertices) * (2 * g.vertices + 2) := Nat.mul_le_mul_right _ hm
      _ ≤ 2 * Δ * ((g.vertices + 2) * (g.vertices + 2)) := by nlinarith
  have hE : (EncodedGraph.encode g).length + 1 ≤ (2 * Δ + 1) * ((g.vertices + 2) * (g.vertices + 2)) := by
    have : g.vertices + 3 ≤ (g.vertices + 2) * (g.vertices + 2) := by nlinarith
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hE3 : ((EncodedGraph.encode g).length + 1) ^ 3 ≤ (2 * Δ + 1) ^ 3 * Z := by
    calc ((EncodedGraph.encode g).length + 1) ^ 3
        ≤ ((2 * Δ + 1) * ((g.vertices + 2) * (g.vertices + 2))) ^ 3 := Nat.pow_le_pow_left hE 3
      _ = (2 * Δ + 1) ^ 3 * (g.vertices + 2) ^ 6 := by ring
      _ ≤ (2 * Δ + 1) ^ 3 * Z := Nat.mul_le_mul_left _ h6
  -- the public endpoint tape
  have hw := CanonicalEdgeTape.word_length_le (CanonicalEdgeTape.graphEdge g hg)
  have hwZ : (CanonicalEdgeTape.word (CanonicalEdgeTape.graphEdge g hg)).length ≤ Δ * Z := by
    have h1 : 2 * g.edges.length * g.vertices ≤ Δ * ((g.vertices + 2) * (g.vertices + 2)) := by
      calc 2 * g.edges.length * g.vertices ≤ (Δ * g.vertices) * g.vertices := Nat.mul_le_mul_right _ hm
        _ ≤ Δ * ((g.vertices + 2) * (g.vertices + 2)) := by
          rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (by nlinarith)
    have h2 : Δ * ((g.vertices + 2) * (g.vertices + 2)) ≤ Δ * Z := Nat.mul_le_mul_left _ hsq'
    omega
  have hLB : Unsched.LB g hg k ≤ Z + Δ * Z + Z := by
    unfold Unsched.LB
    omega
  -- the fallback table
  obtain ⟨hr, hc⟩ := fallback_dims_le k hk
  have hrc : FiniteFallbackOutput.rows k * FiniteFallbackOutput.cols k ≤ Z := by
    have h1 : FiniteFallbackOutput.rows k * FiniteFallbackOutput.cols k ≤ 2 ^ k * 2 ^ k :=
      Nat.mul_le_mul hr hc
    have h2 : 2 ^ k * 2 ^ k ≤ 2 ^ (3 * k) := by
      rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h2kZ : 2 ^ k ≤ Z := (Nat.pow_le_pow_right (by norm_num) (by omega)).trans h3k
  have hLD : Unsched.LD g hg k ≤ 3 * Z := by
    unfold Unsched.LD Unsched.tableU
    rw [MatrixMaterialization.rowMajor_length]
    omega
  -- the header
  have hH : Unsched.headerClock k ≤ (12 * UnaryBinaryEncoding.coefficient + 23) * Z := by
    rw [unsched_header_eq]
    refine (fallback_header_HA3 g.vertices k hk).trans (Nat.mul_le_mul_left _ ?_)
    exact Nat.pow_le_pow_right (by omega) (by omega)
  -- the fallback table clock
  have hF : FallbackFiniteClock.coefficient (CurrentAdditive.QuarticSchedule.threshold27 Δ γ) Δ *
      2 ^ (3 * k) ≤
      FallbackFiniteClock.coefficient (CurrentAdditive.QuarticSchedule.threshold27 Δ γ) Δ * Z :=
    Nat.mul_le_mul_left _ h3k
  -- assemble
  have e : CU27 Δ γ * Z = 103 * ((2 * Δ + 1) ^ 3 * Z) + 6 * (Δ * Z) +
      FallbackFiniteClock.coefficient (CurrentAdditive.QuarticSchedule.threshold27 Δ γ) Δ * Z +
      (12 * UnaryBinaryEncoding.coefficient + 23) * Z + 54 * Z := by
    unfold CU27; ring
  rw [e]
  unfold QuarticUnschedRun.clockU27
  omega

end Paper2.CurrentAdditive.QuarticUnschedClock

#print axioms Paper2.CurrentAdditive.QuarticUnschedClock.unsched_header_eq
#print axioms Paper2.CurrentAdditive.QuarticUnschedClock.clockU_HA3_27
