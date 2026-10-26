import Paper2.FrontClockD

/-! Unit 3, lane a-success-table-13, segment (3), part E: `fullBd` from atom bounds. Pure arithmetic. -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

namespace Paper2.FrontClock13

open EthInapproximability.CurrentPaper
open Paper2.FullFront (pV sV q2V wV q1V QV Lg eg Zv mXV mYV LB LC fullBd gBd)

theorem vec5_le (P1 S1 Q2 W1 Q1 V : ℕ) (hp : P1 ≤ V) (hs : S1 ≤ V) (hq2 : Q2 ≤ V) (hw : W1 ≤ V)
    (hQ : Q1 ≤ V) : ∀ i, (![P1, S1, Q2, W1, Q1] : Fin 5 → ℕ) i ≤ V := by
  intro i
  fin_cases i
  · exact hp
  · exact hs
  · exact hq2
  · exact hw
  · exact hQ

theorem mYV_eq (b k : ℕ) : mYV b k = Zv b k + Zv b k := rfl

theorem fullBd_le (a b Δ : ℕ) (g : EncodedGraph.Graph) (k : ℕ) (word : List Bool) (V : ℕ) (hV : 2 ^ 32 ≤ V)
    (hc : UnaryBinaryEncoding.coefficient + 6 ≤ V)
    (ha : a ≤ V) (hbΔ : 2 * b * Δ ≤ V) (hb : 6144 * b ≤ V) (hn : g.vertices + 3 ≤ V) (hm : g.edges.length ≤ V)
    (hL : 2 ^ Nat.clog 2 g.vertices ≤ V) (he : 2 ^ Nat.clog 2 (Nat.clog 2 g.vertices + 1) ≤ V)
    (hee : 2 ^ (Nat.clog 2 (Nat.clog 2 g.vertices + 1) * Nat.clog 2 (Nat.clog 2 g.vertices + 1)) ≤ V ^ 2)
    (henc : (EncodedGraph.encode g).length + 1 ≤ V)
    (hp : pV g ≤ V) (hs : sV g ≤ V) (hq2 : q2V g ≤ V) (hw : wV g ≤ V) (hQ : QV a b Δ g ≤ V) (hq1 : q1V g ≤ V)
    (hk : k ≤ V) (hLg : Lg g ≤ V) (hword : word.length ≤ V)
    (hthr : TMFront.thrVal k ![pV g, sV g, q2V g, wV g, QV a b Δ g] ≤ V)
    (hB : 2 ^ (TMFront.thrVal k ![pV g, sV g, q2V g, wV g, QV a b Δ g] - 1) ≤ V)
    (hP : 2 ^ (k + TMFront.thrVal k ![pV g, sV g, q2V g, wV g, QV a b Δ g] - 1) ≤ V) :
    fullBd a b Δ g k word ≤ V ^ 45 := by
  have hg := gBd_le a b Δ g V hV hc ha hbΔ hb hn hm hL he hee henc
  unfold fullBd LB LC
  generalize pV g = P1 at *
  generalize sV g = S1 at *
  generalize q2V g = Q2 at *
  generalize wV g = W1 at *
  generalize QV a b Δ g = Q1 at *
  have hv := vec5_le P1 S1 Q2 W1 Q1 V hp hs hq2 hw hQ
  have ht := tmBd_le k ![P1, S1, Q2, W1, Q1] (Lg g) V hV hc hv hk hLg hthr hB hP
  have hZ := zv_le (TMFront.thrVal k ![P1, S1, Q2, W1, Q1]) k V hV hB hP
  have hX : mXV (TMFront.thrVal k ![P1, S1, Q2, W1, Q1]) k (Lg g) ≤
      Lg g + Zv (TMFront.thrVal k ![P1, S1, Q2, W1, Q1]) k := by
    unfold mXV; exact (Nat.div_le_self _ _).trans (by omega)
  exact arith_full _ _ _ k _ _ _ _ _ _ _ _ _ _ _ _ V hV henc hg ht hk hp hs hq2 hw hQ hLg hq1 (by omega) hZ hX
    (mYV_eq _ _) hword

end Paper2.FrontClock13

#print axioms Paper2.FrontClock13.vec5_le
#print axioms Paper2.FrontClock13.fullBd_le
