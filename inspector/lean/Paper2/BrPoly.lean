import Paper2.BrClock

/-! Lane a-bridge-owner-1, segment 4 (continued): the packet-stage clock on a
checked graph and ANY raw word, as a fixed graph monomial plus a linear raw-word
term. -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

namespace Paper2.ABridge

noncomputable section

open EthInapproximability.CurrentPaper
open Paper2.SourceRecursiveNoSampling Paper2.ParameterizedCanonicalSource

/-- The graph exponent of the packet clock. -/
def ePk (Δ : ℕ) (γ : ℚ) : ℕ := FrontClock13.cF Δ γ * 266 * 45 + 360

/-- `prepBd` at the literal graph-front arguments equals its value at the schedule. -/
theorem prepBd_graph_le (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (g : EncodedGraph.Graph) (hn : 0 < g.vertices) (hm : 0 < g.edges.length) (k : ℕ)
    (hc : CompletePublicScheduleScratch.Checks
      (V := Fin g.vertices) (E := Fin g.edges.length) (Nat.clog 2 g.vertices) Δ γ)
    (word : List Bool) :
    FrontPreparedCut.prepBd g.vertices (FullFront.pV g) (FullFront.sV g)
        (FullFront.q1V g) (FullFront.q2V g) (FullFront.wV g)
        (FullFront.QV γ.num.toNat γ.den Δ g) k
        (FrontPreparedCut.frontMX γ.num.toNat γ.den Δ g k)
        (FrontPreparedCut.frontMY γ.num.toNat γ.den Δ g k) word ≤
      prepConst * (2 ^ (60 * ((k + 1) * Nat.clog 2 g.vertices))) ^ 3 +
        (word.length + 2 * (word.length * cutPS)) := by
  haveI : NeZero g.vertices := ⟨by omega⟩
  let L := Nat.clog 2 g.vertices
  let r := ParameterizedCanonicalSource.restorationDepth L
  let q := ParameterizedCanonicalSource.coverDepth g.vertices g.edges.length L Δ γ
  have hb := FullFront.budget_sched Δ γ hγ hΔ g hn hm k
  have hmX : FrontPreparedCut.frontMX γ.num.toNat γ.den Δ g k =
      SourceRecursiveNoSampling.sourceRows L r q k := by
    change FullFront.mXV
      (TMFront.thrVal k ![FullFront.pV g, FullFront.sV g, FullFront.q2V g,
        FullFront.wV g, FullFront.QV γ.num.toNat γ.den Δ g])
      k (FullFront.Lg g) = _
    rw [hb, MProducer.rows_eq]
    rfl
  have hmY : FrontPreparedCut.frontMY γ.num.toNat γ.den Δ g k =
      SourceRecursiveNoSampling.sourceCols L r q k := by
    change FullFront.mYV
      (TMFront.thrVal k ![FullFront.pV g, FullFront.sV g, FullFront.q2V g,
        FullFront.wV g, FullFront.QV γ.num.toNat γ.den Δ g]) k = _
    rw [hb, MProducer.cols_eq]
    rfl
  rw [FullFront.pV_eq, FullFront.sV_eq, FullFront.q1V_eq,
    FullFront.q2V_eq, FullFront.wV_eq,
    FullFront.QV_eq Δ γ hγ hΔ g hn hm, hmX, hmY]
  exact prepBd_sched_le (n := g.vertices) (m := g.edges.length) L Δ γ hc k word

theorem two_pow_sched_le (n k : ℕ) :
    (2 ^ (60 * ((k + 1) * Nat.clog 2 n))) ^ 3 ≤ (n + 2) ^ (360 * (k + 1)) := by
  have h := A3Assembly.Clock.two_pow_clog_le n
  have e1 : (2 ^ (60 * ((k + 1) * Nat.clog 2 n))) ^ 3 =
      (2 ^ Nat.clog 2 n) ^ (180 * (k + 1)) := by
    rw [← pow_mul, ← pow_mul]; exact congrArg (fun e => 2 ^ e) (by ring)
  have e2 : (n + 2) ^ (360 * (k + 1)) = ((n + 2) ^ 2) ^ (180 * (k + 1)) := by
    rw [← pow_mul]; exact congrArg (fun e => (n + 2) ^ e) (by ring)
  rw [e1, e2]
  exact Nat.pow_le_pow_left h _

/-- **Packet clock majorant.** On a checked graph satisfying the H_A3 hypotheses, for ANY raw
word, the segment-1 packet clock is at most a fixed monomial in `|encode g| + 1` plus a linear
term in the raw word length. -/
theorem packetBd_graph_le (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices) (hm : 0 < g.edges.length)
    (k : ℕ) (hH : A3Assembly.Run.Hyp Δ g hg k)
    (hc : CompletePublicScheduleScratch.Checks
      (V := Fin g.vertices) (E := Fin g.edges.length) (Nat.clog 2 g.vertices) Δ γ)
    (word : List Bool) :
    packetBd γ.num.toNat γ.den Δ g k word ≤
      (2 + prepConst) * ((EncodedGraph.encode g).length + 1) ^ (ePk Δ γ * (k + 1)) +
        (26 * word.length + 2 * (word.length * cutPS) + 7) := by
  obtain ⟨t, -⟩ := exists_tape_of_prefix hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k hc
    (List.replicate (TotalFiniteConstructorScratch.select hn
      (CanonicalEdgeTape.graphEdge g hg) Δ γ k).inputBits false) (by simp)
  have hF := fullBd_raw_le Δ γ g hg hn k hH t word
  have hP := prepBd_graph_le Δ γ hγ hΔ g hn hm k hc word
  have hZ := two_pow_sched_le g.vertices k
  have hY : g.vertices + 2 ≤ (EncodedGraph.encode g).length + 1 := by
    have := EncodedGraph.encode_length_lower g; omega
  have hY1 : 1 ≤ (EncodedGraph.encode g).length + 1 := by omega
  have he1 : FrontClock13.cF Δ γ * 266 * 45 * (k + 1) ≤ ePk Δ γ * (k + 1) :=
    Nat.mul_le_mul_right _ (by unfold ePk; omega)
  have he2 : 360 * (k + 1) ≤ ePk Δ γ * (k + 1) :=
    Nat.mul_le_mul_right _ (by unfold ePk; omega)
  have hmono1 : (g.vertices + 2) ^ (FrontClock13.cF Δ γ * 266 * 45 * (k + 1)) ≤
      ((EncodedGraph.encode g).length + 1) ^ (ePk Δ γ * (k + 1)) :=
    (Nat.pow_le_pow_left hY _).trans (Nat.pow_le_pow_right hY1 he1)
  have hmono2 : (g.vertices + 2) ^ (360 * (k + 1)) ≤
      ((EncodedGraph.encode g).length + 1) ^ (ePk Δ γ * (k + 1)) :=
    (Nat.pow_le_pow_left hY _).trans (Nat.pow_le_pow_right hY1 he2)
  have hPC := Nat.mul_le_mul_left prepConst (hZ.trans hmono2)
  have htake := List.length_take_le' (FrontPreparedCut.frontD γ.num.toNat γ.den Δ g k) word
  unfold packetBd
  have hexp : (2 + prepConst) * ((EncodedGraph.encode g).length + 1) ^ (ePk Δ γ * (k + 1)) =
      2 * ((EncodedGraph.encode g).length + 1) ^ (ePk Δ γ * (k + 1)) +
        prepConst * ((EncodedGraph.encode g).length + 1) ^ (ePk Δ γ * (k + 1)) := by ring
  rw [hexp]
  generalize (2 ^ (60 * ((k + 1) * Nat.clog 2 g.vertices))) ^ 3 = Z3 at hP hPC
  generalize ((EncodedGraph.encode g).length + 1) ^ (ePk Δ γ * (k + 1)) = YE at hmono1 hPC ⊢
  generalize (g.vertices + 2) ^ (FrontClock13.cF Δ γ * 266 * 45 * (k + 1)) = A1 at hF hmono1
  generalize FullFront.fullBd γ.num.toNat γ.den Δ g k word = FB at hF ⊢
  generalize FrontPreparedCut.prepBd g.vertices (FullFront.pV g) (FullFront.sV g)
        (FullFront.q1V g) (FullFront.q2V g) (FullFront.wV g)
        (FullFront.QV γ.num.toNat γ.den Δ g) k
        (FrontPreparedCut.frontMX γ.num.toNat γ.den Δ g k)
        (FrontPreparedCut.frontMY γ.num.toNat γ.den Δ g k) word = PB at hP ⊢
  generalize (word.take (FrontPreparedCut.frontD γ.num.toNat γ.den Δ g k)).length = TL at htake ⊢
  generalize word.length * cutPS = WP at hP ⊢
  generalize word.length = W at *
  omega

#print axioms prepBd_graph_le
#print axioms packetBd_graph_le

end

end Paper2.ABridge
