import Paper2.FrontClockB

/-! Unit 3, lane a-success-table-13, segment (3), part C: the `lqBd`, `gBd`, `thrBd`, `mBd`, `tmBd` blocks.
Pure arithmetic from atom bounds against one abstract base `V`. -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

namespace Paper2.FrontClock13

open EthInapproximability.CurrentPaper

theorem pow1 {x V : ℕ} (h : x ≤ V) : x ≤ V ^ 1 := by simpa using h

theorem lqBd_le (a b Δ n m V : ℕ) (hV : 2 ^ 32 ≤ V) (hc : UnaryBinaryEncoding.coefficient + 6 ≤ V)
    (ha : a ≤ V) (hbΔ : 2 * b * Δ ≤ V) (hb : 6144 * b ≤ V) (hn : n + 3 ≤ V) (hm : m ≤ V)
    (hL : 2 ^ Nat.clog 2 n ≤ V) (he : 2 ^ Nat.clog 2 (Nat.clog 2 n + 1) ≤ V)
    (hee : 2 ^ (Nat.clog 2 (Nat.clog 2 n + 1) * Nat.clog 2 (Nat.clog 2 n + 1)) ≤ V ^ 2) :
    CountFront.lqBd a b Δ n m ≤ V ^ 43 := by
  have hV1 : 1 ≤ V := by omega
  have hl := lBd_le n V hV hc hn hL he hee
  have hLn : Nat.clog 2 n ≤ n := clog_le' n
  have hVV : V ≤ V ^ 2 := by have := pw (i := 1) (j := 2) hV1 (by omega); simpa using this
  have hs : 2 ^ (16 + Nat.clog 2 (Nat.clog 2 n + 1)) ≤ V ^ 2 := by
    rw [pow_add]
    have := Nat.mul_le_mul (show 2 ^ 16 ≤ V by omega) he
    calc _ ≤ V * V := this
      _ = V ^ 2 := by ring
  have hq := qBd_le a b Δ n m (Nat.clog 2 n) (2 ^ (16 + Nat.clog 2 (Nat.clog 2 n + 1)))
    (2 ^ (Nat.clog 2 (Nat.clog 2 n + 1) * Nat.clog 2 (Nat.clog 2 n + 1))) (V ^ 2)
    (hV.trans hVV) (hc.trans hVV) (ha.trans hVV) (hbΔ.trans hVV) (hb.trans hVV) (by omega) (hm.trans hVV)
    (by omega) hs hee
  have e42 : (V ^ 2) ^ 21 = V ^ 42 := by rw [← pow_mul]
  rw [e42] at hq
  have p6 : V ^ 6 ≤ V ^ 42 := pw hV1 (by omega)
  have p2 : V ^ 2 ≤ V ^ 42 := pw hV1 (by omega)
  have p1 : V ≤ V ^ 42 := le_trans hVV p2
  have c43 : 20 * V ^ 42 ≤ V ^ 43 := cV (by omega)
  unfold CountFront.lqBd
  omega

theorem gBd_le (a b Δ : ℕ) (g : EncodedGraph.Graph) (V : ℕ) (hV : 2 ^ 32 ≤ V)
    (hc : UnaryBinaryEncoding.coefficient + 6 ≤ V)
    (ha : a ≤ V) (hbΔ : 2 * b * Δ ≤ V) (hb : 6144 * b ≤ V) (hn : g.vertices + 3 ≤ V) (hm : g.edges.length ≤ V)
    (hL : 2 ^ Nat.clog 2 g.vertices ≤ V) (he : 2 ^ Nat.clog 2 (Nat.clog 2 g.vertices + 1) ≤ V)
    (hee : 2 ^ (Nat.clog 2 (Nat.clog 2 g.vertices + 1) * Nat.clog 2 (Nat.clog 2 g.vertices + 1)) ≤ V ^ 2)
    (henc : (EncodedGraph.encode g).length + 1 ≤ V) :
    FullFront.gBd a b Δ g ≤ V ^ 44 := by
  have hV1 : 1 ≤ V := by omega
  have hlq := lqBd_le a b Δ g.vertices g.edges.length V hV hc ha hbΔ hb hn hm hL he hee
  have h3 : ((EncodedGraph.encode g).length + 1) ^ 3 ≤ V ^ 3 := Nat.pow_le_pow_left henc 3
  have p3 : V ^ 3 ≤ V ^ 42 := pw hV1 (by omega)
  have p1 : V ≤ V ^ 43 := by have := pw (i := 1) (j := 43) hV1 (by omega); simpa using this
  have p343 : V ^ 3 ≤ V ^ 43 := pw hV1 (by omega)
  have c1 : 103 * V ^ 42 ≤ V ^ 43 := cV (by omega)
  have c44 : 200 * V ^ 43 ≤ V ^ 44 := cV (by omega)
  unfold FullFront.gBd
  omega

theorem thrBd_le (k : ℕ) (v : Fin 5 → ℕ) (V : ℕ) (hV : 2 ^ 32 ≤ V)
    (hc : UnaryBinaryEncoding.coefficient + 6 ≤ V) (hv : ∀ i, v i ≤ V) (hk : k ≤ V) :
    ThrProducer.thrBd k v ≤ V ^ 6 ∧ ThrProducer.Xv v ≤ 5 * V := by
  have hV1 : 1 ≤ V := by omega
  have hX : ThrProducer.Xv v ≤ 5 * V := by
    unfold ThrProducer.Xv
    have := fun i => (clog_le' (v i)).trans (hv i)
    have h0 := this 0; have h1 := this 1; have h2 := this 2; have h3 := this 3; have h4 := this 4
    omega
  refine ⟨?_, hX⟩
  have lg : ∀ i, ThrProducer.logBd (v i) ≤ V ^ 5 := fun i => by
    unfold ThrProducer.logBd; exact lg_le (i := 1) (by omega) hc (pow1 (hv i))
  have hk2 : k * (2 * ThrProducer.Xv v + 4 + 2) ≤ V * (11 * V) := Nat.mul_le_mul hk (by omega)
  have e2 : V * (11 * V) = 11 * V ^ 2 := by ring
  have p25 : V ^ 2 ≤ V ^ 5 := pw hV1 (by omega)
  have p15 : V ≤ V ^ 5 := by have := pw (i := 1) (j := 5) hV1 (by omega); simpa using this
  have hc0 := (clog_le' (v 0)).trans (hv 0)
  have c6 : 100 * V ^ 5 ≤ V ^ 6 := cV (by omega)
  have l0 := lg 0; have l1 := lg 1; have l2 := lg 2; have l3 := lg 3; have l4 := lg 4
  unfold ThrProducer.thrBd
  omega

theorem mBd_le (b k L V : ℕ) (hV : 2 ^ 32 ≤ V) (hb : b ≤ V) (hk : k ≤ V) (hL : L ≤ V)
    (hB : 2 ^ (b - 1) ≤ V) (hP : 2 ^ (k + b - 1) ≤ V) :
    MProducer.mBd b k L ≤ V ^ 7 := by
  have hV1 : 1 ≤ V := by omega
  have hV12 : 12 ≤ V := by omega
  have hV15 : 15 ≤ V := by omega
  unfold MProducer.mBd
  generalize 2 ^ (b - 1) = B at *
  generalize 2 ^ (k + b - 1) = P at *
  have hBB : B * (B + 1) ≤ 2 * V ^ 2 := by
    have := Nat.mul_le_mul hB (show B + 1 ≤ 2 * V by omega)
    calc _ ≤ V * (2 * V) := this
      _ = 2 * V ^ 2 := by ring
  have p23 : 4 * V ^ 2 ≤ V ^ 3 := cV (by omega)
  have h2BB : 2 + B * (B + 1) ≤ V ^ 3 := by
    have : 1 ≤ V ^ 2 := one_le_pw hV1
    omega
  have hZP : (2 + B * (B + 1)) * P ≤ V ^ 4 := mulb h2BB (pow1 hP)
  have hB1 : B + 1 ≤ V ^ 2 := by
    have h := Nat.mul_le_mul_right V (show 2 ≤ V by omega)
    have e : V ^ 2 = V * V := by ring
    omega
  have e1 : MatrixAddressMachine.exactTime B (B + 1) 0 ≤ V ^ 4 :=
    et_le (l := 0) hV12 (pow1 hB) hB1 (Nat.zero_le _)
  have e2 : MatrixAddressMachine.exactTime (2 + B * (B + 1)) P 0 ≤ V ^ 5 := et_le (l := 0) hV12 h2BB (pow1 hP) (Nat.zero_le _)
  have p45 : V ^ 4 ≤ V ^ 5 := pw hV1 (by omega)
  have p15 : V ≤ V ^ 5 := by have := pw (i := 1) (j := 5) hV1 (by omega); simpa using this
  have c5 : 16 * V ^ 4 ≤ V ^ 5 := cV (by omega)
  have p14 : V ≤ V ^ 4 := by have := pw (i := 1) (j := 4) hV1 (by omega); simpa using this
  have one4 : 1 ≤ V ^ 4 := one_le_pw hV1
  have t1 : MatrixUnaryDivision.totalTime (L + (12 + (2 + B * (B + 1)) * P) - 1) L ≤ V ^ 6 :=
    tt_le (i := 5) hV15 (by omega) (by omega)
  have p56 : V ^ 5 ≤ V ^ 6 := pw hV1 (by omega)
  have c7 : 200 * V ^ 6 ≤ V ^ 7 := cV (by omega)
  omega

theorem tmBd_le (k : ℕ) (v : Fin 5 → ℕ) (L V : ℕ) (hV : 2 ^ 32 ≤ V)
    (hc : UnaryBinaryEncoding.coefficient + 6 ≤ V) (hv : ∀ i, v i ≤ V) (hk : k ≤ V) (hL : L ≤ V)
    (hb : TMFront.thrVal k v ≤ V) (hB : 2 ^ (TMFront.thrVal k v - 1) ≤ V)
    (hP : 2 ^ (k + TMFront.thrVal k v - 1) ≤ V) :
    TMFront.tmBd k v L ≤ V ^ 8 := by
  have hV1 : 1 ≤ V := by omega
  have ht := (thrBd_le k v V hV hc hv hk).1
  have hm := mBd_le (TMFront.thrVal k v) k L V hV hb hk hL hB hP
  have p67 : V ^ 6 ≤ V ^ 7 := pw hV1 (by omega)
  have p17 : V ≤ V ^ 7 := by have := pw (i := 1) (j := 7) hV1 (by omega); simpa using this
  have c8 : 20 * V ^ 7 ≤ V ^ 8 := cV (by omega)
  unfold TMFront.tmBd
  omega

end Paper2.FrontClock13

#print axioms Paper2.FrontClock13.lqBd_le
#print axioms Paper2.FrontClock13.gBd_le
#print axioms Paper2.FrontClock13.thrBd_le
#print axioms Paper2.FrontClock13.mBd_le
#print axioms Paper2.FrontClock13.tmBd_le
