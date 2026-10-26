import Paper2.FrontClockA
import EthInapproximability.CurrentPaper.EntryClockPolyFrame

/-! Unit 3, lane a-success-table-13, segment (3), part B: leaf clocks and the `qBd` block. Pure arithmetic. -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

namespace Paper2.FrontClock13

open EthInapproximability.CurrentPaper

theorem one_le_pw {V i : ℕ} (hV : 1 ≤ V) : 1 ≤ V ^ i := Nat.one_le_pow _ _ hV

theorem et_le {r w c V i j l : ℕ} (hV : 12 ≤ V) (hr : r ≤ V ^ i) (hw : w ≤ V ^ j) (hc : c ≤ V ^ l) :
    MatrixAddressMachine.exactTime r w c ≤ V ^ (i + j + l + 1) := by
  unfold MatrixAddressMachine.exactTime
  have hV1 : 1 ≤ V := by omega
  have h1 : r * w ≤ V ^ (i + j) := mulb hr hw
  have h2 : V ^ (i + j) ≤ V ^ (i + j + l) := pw hV1 (by omega)
  have h3 : V ^ i ≤ V ^ (i + j + l) := pw hV1 (by omega)
  have h4 : V ^ l ≤ V ^ (i + j + l) := pw hV1 (by omega)
  have h5 : 1 ≤ V ^ (i + j + l) := one_le_pw hV1
  have h6 : 12 * V ^ (i + j + l) ≤ V ^ (i + j + l + 1) := cV hV
  have e : 2 * r * w = 2 * (r * w) := by ring
  rw [e]
  omega

theorem tt_le {x y V i : ℕ} (hV : 15 ≤ V) (hx : x ≤ V ^ i) (hy : y ≤ V ^ i) :
    MatrixUnaryDivision.totalTime x y ≤ V ^ (i + 1) := by
  have h := EthInapproximability.CurrentPaper.EntryClockPoly.totalTime_le x y
  have h5 : 1 ≤ V ^ i := one_le_pw (by omega)
  have h6 : 15 * V ^ i ≤ V ^ (i + 1) := cV hV
  omega

theorem lg_le {M V i : ℕ} (hV : 8 ≤ V) (hc : UnaryBinaryEncoding.coefficient + 6 ≤ V) (hM : M ≤ V ^ i) :
    2 * M + 2 + (UnaryBinaryEncoding.coefficient + 6) * (M + 1) ^ 2 ≤ V ^ (2 * i + 3) := by
  have hV1 : 1 ≤ V := by omega
  have h1 : 1 ≤ V ^ i := one_le_pw hV1
  have h2 : M + 1 ≤ 2 * V ^ i := by omega
  have h3 : (M + 1) ^ 2 ≤ 4 * V ^ (2 * i) := by
    have := Nat.pow_le_pow_left h2 2
    calc (M + 1) ^ 2 ≤ (2 * V ^ i) ^ 2 := this
      _ = 4 * V ^ (2 * i) := by ring
  have h4 : (UnaryBinaryEncoding.coefficient + 6) * (M + 1) ^ 2 ≤ V * (4 * V ^ (2 * i)) :=
    Nat.mul_le_mul hc h3
  have h5 : V * (4 * V ^ (2 * i)) = 4 * V ^ (2 * i + 1) := by ring
  have h6 : V ^ i ≤ V ^ (2 * i + 1) := pw hV1 (by omega)
  have h7 : 8 * V ^ (2 * i + 1) ≤ V ^ (2 * i + 1 + 1) := cV hV
  have h8 : V ^ (2 * i + 1 + 1) ≤ V ^ (2 * i + 3) := pw hV1 (by omega)
  have h9 : 1 ≤ V ^ (2 * i + 1) := one_le_pw hV1
  omega

/-! ### The `qBd` block -/

set_option maxRecDepth 100000 in
theorem qBd_le (a b Δ n m L s w V : ℕ) (hV : 2 ^ 32 ≤ V) (hc : UnaryBinaryEncoding.coefficient + 6 ≤ V)
    (ha : a ≤ V) (hbΔ : 2 * b * Δ ≤ V) (hb : 6144 * b ≤ V) (hn : n ≤ V) (hm : m ≤ V)
    (hL : L ≤ V) (hs : s ≤ V) (hw : w ≤ V) :
    QProducer.qBd a b Δ n m L s w ≤ V ^ 21 := by
  have hV1 : 1 ≤ V := by omega
  have hV12 : 12 ≤ V := by omega
  have hV15 : 15 ≤ V := by omega
  have h0 : (0 : ℕ) ≤ V ^ 0 := Nat.zero_le _
  have hL1 : L ≤ V ^ 1 := by simpa using hL
  have hw1 : w ≤ V ^ 1 := by simpa using hw
  have hs1 : s ≤ V ^ 1 := by simpa using hs
  have ha1 : a ≤ V ^ 1 := by simpa using ha
  have hm1 : m ≤ V ^ 1 := by simpa using hm
  have hn1 : n ≤ V ^ 1 := by simpa using hn
  have hbΔ1 : 2 * b * Δ ≤ V ^ 1 := by simpa using hbΔ
  have hb1 : 6144 * b ≤ V ^ 1 := by simpa using hb
  have hLw : L * w ≤ V ^ 2 := mulb hL1 hw1
  have hLws : L * w * s ≤ V ^ 3 := mulb hLw hs1
  have h24 : 2 ^ 24 ≤ V ^ 1 := by simpa using (show 2 ^ 24 ≤ V by omega)
  have h5 : 5 ≤ V ^ 1 := by simpa using (show 5 ≤ V by omega)
  have hLws24 : L * w * s * 2 ^ 24 ≤ V ^ 4 := mulb hLws h24
  have hC0 : QProducer.C0 L s w ≤ V ^ 5 := by unfold QProducer.C0; exact mulb hLws24 h5
  have hC0b : QProducer.C0 L s w * (2 * b * Δ) ≤ V ^ 6 := mulb hC0 hbΔ1
  have hC0bn : QProducer.C0 L s w * (2 * b * Δ) * n ≤ V ^ 7 := mulb hC0b hn1
  have ham : a * m ≤ V ^ 2 := mulb ha1 hm1
  have hC06 : QProducer.C0 L s w * (6144 * b) ≤ V ^ 6 := mulb hC0 hb1
  have p27 : V ^ 2 ≤ V ^ 7 := pw hV1 (by omega)
  have p67 : V ^ 6 ≤ V ^ 7 := pw hV1 (by omega)
  have p57 : V ^ 5 ≤ V ^ 7 := pw hV1 (by omega)
  have p17 : V ≤ V ^ 7 := by have := pw (i := 1) (j := 7) hV1 (by omega); simpa using this
  have c8 : 8 * V ^ 7 ≤ V ^ 8 := cV (by omega)
  have hA2 : QProducer.A2 a b Δ n m L s w ≤ V ^ 8 := by
    unfold QProducer.A2
    exact (Nat.div_le_self _ _).trans (by omega)
  have hA3 : QProducer.A3 a b L s w ≤ V ^ 8 := by
    unfold QProducer.A3
    exact (Nat.div_le_self _ _).trans (by omega)
  have p58 : V ^ 5 ≤ V ^ 8 := pw hV1 (by omega)
  have hM : max (max (QProducer.C0 L s w) (QProducer.A2 a b Δ n m L s w)) (QProducer.A3 a b L s w) ≤ V ^ 8 := by
    simp only [max_le_iff]; omega
  have hM2 : max (QProducer.C0 L s w) (QProducer.A2 a b Δ n m L s w) ≤ V ^ 8 := by
    simp only [max_le_iff]; omega
  have e1 : MatrixAddressMachine.exactTime L w 0 ≤ V ^ 3 := et_le (l := 0) hV12 hL1 hw1 h0
  have e2 : MatrixAddressMachine.exactTime (L * w) s 0 ≤ V ^ 4 := et_le (l := 0) hV12 hLw hs1 h0
  have e3 : MatrixAddressMachine.exactTime (L * w * s) (2 ^ 24) 0 ≤ V ^ 5 := et_le (l := 0) hV12 hLws h24 h0
  have e4 : MatrixAddressMachine.exactTime (L * w * s * 2 ^ 24) 5 0 ≤ V ^ 6 := et_le (l := 0) hV12 hLws24 h5 h0
  have e5 : MatrixAddressMachine.exactTime (QProducer.C0 L s w) (2 * b * Δ) 0 ≤ V ^ 7 :=
    et_le (l := 0) hV12 hC0 hbΔ1 h0
  have e6 : MatrixAddressMachine.exactTime (QProducer.C0 L s w * (2 * b * Δ)) n 0 ≤ V ^ 8 :=
    et_le (l := 0) hV12 hC0b hn1 h0
  have e7 : MatrixAddressMachine.exactTime a m 0 ≤ V ^ 3 := et_le (l := 0) hV12 ha1 hm1 h0
  have e10 : MatrixAddressMachine.exactTime (QProducer.C0 L s w) (6144 * b) 0 ≤ V ^ 7 :=
    et_le (l := 0) hV12 hC0 hb1 h0
  have t9 : MatrixUnaryDivision.totalTime (a * m + QProducer.C0 L s w * (2 * b * Δ) * n - 1) (a * m) ≤ V ^ 9 :=
    tt_le (i := 8) hV15 (by omega) (by omega)
  have t11 : MatrixUnaryDivision.totalTime (a - 1 + QProducer.C0 L s w * (6144 * b)) a ≤ V ^ 9 :=
    tt_le (i := 8) hV15 (by omega) (by omega)
  have hlg : 2 * max (max (QProducer.C0 L s w) (QProducer.A2 a b Δ n m L s w)) (QProducer.A3 a b L s w) + 2 +
      (UnaryBinaryEncoding.coefficient + 6) *
        (max (max (QProducer.C0 L s w) (QProducer.A2 a b Δ n m L s w)) (QProducer.A3 a b L s w) + 1) ^ 2 ≤ V ^ 19 :=
    lg_le (by omega) hc hM
  have hcl : Nat.clog 2 (max (max (QProducer.C0 L s w) (QProducer.A2 a b Δ n m L s w))
      (QProducer.A3 a b L s w)) ≤ V ^ 8 := (clog_le' _).trans hM
  have hpc : 2 ^ Nat.clog 2 (max (max (QProducer.C0 L s w) (QProducer.A2 a b Δ n m L s w))
      (QProducer.A3 a b L s w)) ≤ V ^ 20 := two_pow_clog_V (by omega) hM
  have q : ∀ j, j ≤ 20 → V ^ j ≤ V ^ 20 := fun j hj => pw hV1 hj
  have q3 := q 3 (by omega); have q4 := q 4 (by omega); have q5 := q 5 (by omega)
  have q6 := q 6 (by omega); have q7 := q 7 (by omega); have q8 := q 8 (by omega)
  have q9 := q 9 (by omega); have q19 := q 19 (by omega)
  have p1 : 1 ≤ V ^ 20 := one_le_pw hV1
  have c21 : 200 * V ^ 20 ≤ V ^ 21 := cV (by omega)
  have h224 : 4 * 2 ^ 24 + 5 * 24 + 7 ≤ V ^ 20 := by
    have h1 : V ≤ V ^ 20 := by have := pw (i := 1) (j := 20) hV1 (by omega); simpa using this
    have h2 : 4 * 2 ^ 24 + 5 * 24 + 7 ≤ 2 ^ 32 := by norm_num
    exact h2.trans (hV.trans h1)
  unfold QProducer.qBd QProducer.logBd
  generalize max (max (QProducer.C0 L s w) (QProducer.A2 a b Δ n m L s w)) (QProducer.A3 a b L s w) = M at *
  generalize max (QProducer.C0 L s w) (QProducer.A2 a b Δ n m L s w) = M2 at *
  omega

end Paper2.FrontClock13

#print axioms Paper2.FrontClock13.et_le
#print axioms Paper2.FrontClock13.tt_le
#print axioms Paper2.FrontClock13.lg_le
#print axioms Paper2.FrontClock13.qBd_le
