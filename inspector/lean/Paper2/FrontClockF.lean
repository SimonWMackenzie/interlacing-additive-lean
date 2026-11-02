import Paper2.FrontClockE

/-! Unit 3, lane a-success-table-13, segment (3), part F: the front clock premise `FrontClock` discharged.
Base `V0 = (n+2)^cF`, `V = V0^(266(k+1))`; every atom of `fullBd` is bounded against `V`; the `2^(k·Xv)` factor of
the sample-dimension clock is bounded through `2^Xv ≤ V0^220` (k-free) so that the exponent stays linear in `k+1`. -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

namespace Paper2.FrontClock13

open EthInapproximability.CurrentPaper
open Paper2.FullFront (pV sV q2V wV q1V QV Lg eg Zv mXV mYV LB LC fullBd gBd)
open Paper2.A3Assembly

theorem const_le {x c N : ℕ} (hN : 2 ≤ N) (hx : x ≤ c) : x ≤ N ^ c :=
  (Nat.lt_two_pow_self (n := x)).le.trans
    ((Nat.pow_le_pow_right (by norm_num) hx).trans (Nat.pow_le_pow_left hN c))

theorem qv_le (a b Δ n m L s w V : ℕ) (hV : 2 ^ 32 ≤ V)
    (ha : a ≤ V) (hbΔ : 2 * b * Δ ≤ V) (hb : 6144 * b ≤ V) (hn : n ≤ V) (hm : m ≤ V)
    (hL : L ≤ V) (hs : s ≤ V) (hw : w ≤ V) :
    2 ^ Nat.clog 2 (max (max (QProducer.C0 L s w) (QProducer.A2 a b Δ n m L s w)) (QProducer.A3 a b L s w))
      ≤ V ^ 20 := by
  have hV1 : 1 ≤ V := by omega
  have hLws : L * w * s ≤ V ^ 3 := mulb (mulb (pow1 hL) (pow1 hw)) (pow1 hs)
  have hLws24 : L * w * s * 2 ^ 24 ≤ V ^ 4 := mulb hLws (pow1 (show 2 ^ 24 ≤ V by omega))
  have hC0 : QProducer.C0 L s w ≤ V ^ 5 := by
    unfold QProducer.C0; exact mulb hLws24 (pow1 (show 5 ≤ V by omega))
  have hC0bn : QProducer.C0 L s w * (2 * b * Δ) * n ≤ V ^ 7 := mulb (mulb hC0 (pow1 hbΔ)) (pow1 hn)
  have ham : a * m ≤ V ^ 2 := mulb (pow1 ha) (pow1 hm)
  have hC06 : QProducer.C0 L s w * (6144 * b) ≤ V ^ 6 := mulb hC0 (pow1 hb)
  have p27 : V ^ 2 ≤ V ^ 7 := pw hV1 (by omega)
  have p67 : V ^ 6 ≤ V ^ 7 := pw hV1 (by omega)
  have p58 : V ^ 5 ≤ V ^ 8 := pw hV1 (by omega)
  have p17 : V ≤ V ^ 7 := by have := pw (i := 1) (j := 7) hV1 (by omega); simpa using this
  have c8 : 8 * V ^ 7 ≤ V ^ 8 := cV (by omega)
  have hA2 : QProducer.A2 a b Δ n m L s w ≤ V ^ 8 := by
    unfold QProducer.A2; exact (Nat.div_le_self _ _).trans (by omega)
  have hA3 : QProducer.A3 a b L s w ≤ V ^ 8 := by
    unfold QProducer.A3; exact (Nat.div_le_self _ _).trans (by omega)
  have hM : max (max (QProducer.C0 L s w) (QProducer.A2 a b Δ n m L s w)) (QProducer.A3 a b L s w) ≤ V ^ 8 := by
    simp only [max_le_iff]; omega
  exact two_pow_clog_V (by omega) hM

/-- `|tapeBits t| ≤ (4Δ+9)(n+2)^(160(k+1))` from the checked `Size.inputSize`. -/
theorem word_le (Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices) (k : ℕ)
    (hH : Run.Hyp Δ g hg k)
    (t : (TotalFiniteConstructorScratch.select hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape) :
    ((TotalFiniteConstructorScratch.select hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).tapeBits t).length ≤
      (4 * Δ + 9) * (g.vertices + 2) ^ (160 * (k + 1)) := by
  obtain ⟨hk, hinc, hdeg⟩ := hH
  have h := Size.inputSize Δ γ g hg hn k hk hinc hdeg t
  rw [BitMachineBankCodec.encode_length] at h
  simp only [Fin.sum_univ_three, Wrap.inputBank] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at h
  omega

theorem thr_bounds (k : ℕ) (vv : Fin 5 → ℕ) (V0 : ℕ) (hV0 : 2 ≤ V0)
    (hcl : ∀ i, 2 ^ Nat.clog 2 (vv i) ≤ V0 ^ 44) : 2 ^ TMFront.thrVal k vv ≤ V0 ^ (220 * k + 45) := by
  have hX : 2 ^ ThrProducer.Xv vv ≤ V0 ^ 220 := by
    unfold ThrProducer.Xv
    rw [pow_add, pow_add, pow_add, pow_add]
    have h := Nat.mul_le_mul (hcl 4) (Nat.mul_le_mul (hcl 3) (Nat.mul_le_mul (hcl 1)
      (Nat.mul_le_mul (hcl 2) (hcl 1))))
    have e : V0 ^ 44 * (V0 ^ 44 * (V0 ^ 44 * (V0 ^ 44 * V0 ^ 44))) = V0 ^ 220 := by
      rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]
    omega
  have hkX : 2 ^ (k * ThrProducer.Xv vv) ≤ V0 ^ (220 * k) := by
    rw [Nat.mul_comm k, pow_mul 2 (ThrProducer.Xv vv) k, pow_mul V0 220 k]
    exact Nat.pow_le_pow_left hX k
  unfold TMFront.thrVal
  rw [pow_add, pow_succ]
  have h := Nat.mul_le_mul hkX (hcl 0)
  calc 2 ^ (k * ThrProducer.Xv vv) * (2 ^ Nat.clog 2 (vv 0) * 2)
      = (2 ^ (k * ThrProducer.Xv vv) * 2 ^ Nat.clog 2 (vv 0)) * 2 := by ring
    _ ≤ (V0 ^ (220 * k) * V0 ^ 44) * 2 := Nat.mul_le_mul_right 2 h
    _ ≤ (V0 ^ (220 * k) * V0 ^ 44) * V0 := Nat.mul_le_mul_left _ hV0
    _ = V0 ^ (220 * k + 45) := by rw [← pow_add, ← pow_succ]

/-- The machine-constant exponent base. -/
noncomputable def cF (Δ : ℕ) (γ : ℚ) : ℕ := 200 + γ.num.toNat + γ.den + Δ + UnaryBinaryEncoding.coefficient

theorem clog_add_le (n : ℕ) : Nat.clog 2 n + 3 ≤ n + 3 := by have := clog_le' n; omega

/-- **Segment (3)**: the front clock premise, discharged. -/
theorem frontClock (Δ : ℕ) (γ : ℚ) :
    FrontLift.FrontClock Δ γ 2 (cF Δ γ * 266 * 45) := by
  intro g hg hn k hH t
  have hH' := hH
  obtain ⟨hk1, hinc, hdeg⟩ := hH'
  haveI : Nonempty (Fin g.vertices) := ⟨⟨0, hn⟩⟩
  have hm2 := SourceDensityScheduleScratch.twice_edges_le_degree_vertices
    (V := Fin g.vertices) (E := Fin g.edges.length) (CanonicalEdgeTape.graphEdge g hg) Δ hdeg
  simp only [Fintype.card_fin] at hm2
  have hword := word_le Δ γ g hg hn k hH t
  generalize ((TotalFiniteConstructorScratch.select hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).tapeBits t) = word
    at hword ⊢
  have hbpos : 0 < γ.den := γ.den_pos
  have hcge : 200 + γ.num.toNat + γ.den + Δ + UnaryBinaryEncoding.coefficient ≤ cF Δ γ := le_rfl
  generalize γ.num.toNat = a at *
  generalize γ.den = b at *
  -- the bases
  set N := g.vertices + 2 with hNdef
  have hN2 : 2 ≤ N := by omega
  have hN3 : 3 ≤ N := by omega
  set c := cF Δ γ with hcdef
  set V0 := N ^ c with hV0def
  have hV01 : 1 ≤ V0 := Nat.one_le_pow _ _ (by omega)
  have hNc : ∀ j, j ≤ c → N ^ j ≤ V0 := fun j hj => Nat.pow_le_pow_right (by omega) hj
  -- constants
  have k32 : 2 ^ 32 ≤ V0 := (Nat.pow_le_pow_right (by norm_num) (by omega)).trans (Nat.pow_le_pow_left hN2 c)
  have kc : UnaryBinaryEncoding.coefficient + 6 ≤ V0 := const_le hN2 (by omega)
  have ka : a ≤ V0 := const_le hN2 (by omega)
  have kbΔ : 2 * b * Δ ≤ V0 := by
    have h1 : b < 2 ^ b := Nat.lt_two_pow_self
    have h2 : Δ < 2 ^ Δ := Nat.lt_two_pow_self
    have h3 : 2 * b * Δ ≤ 2 * 2 ^ b * 2 ^ Δ := Nat.mul_le_mul (Nat.mul_le_mul_left _ h1.le) h2.le
    have h4 : 2 * 2 ^ b * 2 ^ Δ = 2 ^ (1 + b + Δ) := by rw [pow_add, pow_add]; ring
    have h5 : 2 ^ (1 + b + Δ) ≤ N ^ c :=
      (Nat.pow_le_pow_right (by norm_num) (by omega)).trans (Nat.pow_le_pow_left hN2 c)
    omega
  have kb : 6144 * b ≤ V0 := by
    have h1 : b < 2 ^ b := Nat.lt_two_pow_self
    have h3 : 6144 * b ≤ 2 ^ 13 * 2 ^ b := Nat.mul_le_mul (by norm_num) h1.le
    have h4 : 2 ^ 13 * 2 ^ b = 2 ^ (13 + b) := by rw [pow_add]
    have h5 : 2 ^ (13 + b) ≤ N ^ c :=
      (Nat.pow_le_pow_right (by norm_num) (by omega)).trans (Nat.pow_le_pow_left hN2 c)
    omega
  -- graph atoms
  have hNN : N ≤ N ^ 2 := by nlinarith
  have kn : g.vertices + 3 ≤ V0 := by
    have : g.vertices + 3 ≤ N ^ 2 := by nlinarith
    exact this.trans (hNc 2 (by omega))
  have kΔN : Δ * N ≤ N ^ (Δ + 1) := by
    rw [pow_succ]; exact Nat.mul_le_mul_right _ (const_le hN2 le_rfl)
  have km : g.edges.length ≤ N ^ (Δ + 1) := by
    have : Δ * g.vertices ≤ Δ * N := Nat.mul_le_mul_left _ (by omega)
    omega
  have km0 : g.edges.length ≤ V0 := km.trans (hNc _ (by omega))
  have hLn : Nat.clog 2 g.vertices ≤ g.vertices := clog_le' _
  have kL : Nat.clog 2 g.vertices ≤ V0 := by omega
  have k2L : 2 ^ Nat.clog 2 g.vertices ≤ N ^ 2 := Clock.two_pow_clog_le g.vertices
  have k2e : 2 ^ Nat.clog 2 (Nat.clog 2 g.vertices + 1) ≤ N ^ 3 := by
    have h := Clock.two_pow_clog_le (Nat.clog 2 g.vertices + 1)
    have h1 : (Nat.clog 2 g.vertices + 1 + 2) ^ 2 ≤ (N + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h2 : (N + 1) ^ 2 ≤ N ^ 3 := by nlinarith
    omega
  have kee : 2 ^ (Nat.clog 2 (Nat.clog 2 g.vertices + 1) * Nat.clog 2 (Nat.clog 2 g.vertices + 1)) ≤ N ^ 11 := by
    have h := clog_sq_le (Nat.clog 2 g.vertices)
    have h1 : 2 ^ (Nat.clog 2 (Nat.clog 2 g.vertices + 1) * Nat.clog 2 (Nat.clog 2 g.vertices + 1)) ≤
        2 ^ (Nat.clog 2 g.vertices + 9) := Nat.pow_le_pow_right (by norm_num) h
    have h2 : 2 ^ (Nat.clog 2 g.vertices + 9) = 2 ^ Nat.clog 2 g.vertices * 2 ^ 9 := pow_add _ _ _
    have h3 : 2 ^ 9 ≤ N ^ 9 := Nat.pow_le_pow_left hN2 9
    have h4 : N ^ 2 * N ^ 9 = N ^ 11 := by rw [← pow_add]
    have h5 := Nat.mul_le_mul k2L h3
    omega
  have kenc : (EncodedGraph.encode g).length + 1 ≤ V0 := by
    have h := EncodedGraph.encode_length_upper g hg
    have h1 : 4 * g.vertices + 4 ≤ N ^ 3 := by nlinarith
    have h2 : g.edges.length * (4 * g.vertices + 4) ≤ N ^ (Δ + 1) * N ^ 3 := Nat.mul_le_mul km h1
    have h3 : N ^ (Δ + 1) * N ^ 3 = N ^ (Δ + 4) := by rw [← pow_add]
    have h4 : N ^ 2 ≤ N ^ (Δ + 4) := Nat.pow_le_pow_right (by omega) (by omega)
    have h5 : 2 * N ^ (Δ + 4) ≤ N ^ (Δ + 5) := by
      have e : N ^ (Δ + 5) = N ^ (Δ + 4) * N := pow_succ N (Δ + 4)
      rw [e, Nat.mul_comm (N ^ (Δ + 4)) N]; exact Nat.mul_le_mul_right _ hN2
    have h6 := hNc (Δ + 5) (by omega)
    have h7 : g.vertices + 3 ≤ N ^ 2 := by nlinarith
    omega
  -- the named counts (k-free)
  have epV : pV g = 2 ^ 6 * 2 ^ Nat.clog 2 (Nat.clog 2 g.vertices + 1) := by
    show 2 ^ (6 + Nat.clog 2 (Nat.clog 2 g.vertices + 1)) = _; rw [pow_add]
  have esV : sV g = 2 ^ 16 * 2 ^ Nat.clog 2 (Nat.clog 2 g.vertices + 1) := by
    show 2 ^ (16 + Nat.clog 2 (Nat.clog 2 g.vertices + 1)) = _; rw [pow_add]
  have eq2V : q2V g = 2 ^ 32 * (2 ^ Nat.clog 2 (Nat.clog 2 g.vertices + 1) *
      (2 ^ Nat.clog 2 (Nat.clog 2 g.vertices + 1) * 2 ^ Nat.clog 2 g.vertices)) := by
    show 2 ^ (32 + (Nat.clog 2 (Nat.clog 2 g.vertices + 1) + (Nat.clog 2 (Nat.clog 2 g.vertices + 1) +
      Nat.clog 2 g.vertices))) = _
    rw [pow_add, pow_add, pow_add]
  have ewV : wV g = 2 ^ (Nat.clog 2 (Nat.clog 2 g.vertices + 1) * Nat.clog 2 (Nat.clog 2 g.vertices + 1)) := rfl
  have eq1V : q1V g = sV g - 2 := rfl
  have eLg : Lg g = Nat.clog 2 g.vertices := rfl
  have kp : pV g ≤ V0 := by
    rw [epV]
    have h := Nat.mul_le_mul (Nat.pow_le_pow_left hN2 6) k2e
    have h2 : N ^ 6 * N ^ 3 = N ^ 9 := by rw [← pow_add]
    have := hNc 9 (by omega); omega
  have ks : sV g ≤ V0 := by
    rw [esV]
    have h := Nat.mul_le_mul (Nat.pow_le_pow_left hN2 16) k2e
    have h2 : N ^ 16 * N ^ 3 = N ^ 19 := by rw [← pow_add]
    have := hNc 19 (by omega); omega
  have kq2 : q2V g ≤ V0 := by
    rw [eq2V]
    have h := Nat.mul_le_mul (Nat.pow_le_pow_left hN2 32) (Nat.mul_le_mul k2e (Nat.mul_le_mul k2e k2L))
    have h2 : N ^ 32 * (N ^ 3 * (N ^ 3 * N ^ 2)) = N ^ 40 := by rw [← pow_add, ← pow_add, ← pow_add]
    have := hNc 40 (by omega); omega
  have kw : wV g ≤ V0 := by rw [ewV]; exact kee.trans (hNc 11 (by omega))
  have kq1 : q1V g ≤ V0 := by rw [eq1V]; omega
  have kQ : QV a b Δ g ≤ V0 ^ 20 := by
    show 2 ^ Nat.clog 2 (max (max (QProducer.C0 (Lg g) (sV g) (wV g))
      (QProducer.A2 a b Δ g.vertices g.edges.length (Lg g) (sV g) (wV g))) (QProducer.A3 a b (Lg g) (sV g) (wV g))) ≤ _
    exact qv_le a b Δ g.vertices g.edges.length (Lg g) (sV g) (wV g) V0 k32 ka kbΔ kb (by omega) km0
      (by rw [eLg]; exact kL) ks kw
  -- the big base
  set V := V0 ^ (266 * (k + 1)) with hVdef
  have hVV : ∀ j, j ≤ 266 * (k + 1) → V0 ^ j ≤ V := fun j hj => Nat.pow_le_pow_right hV01 hj
  have hV0V : V0 ≤ V := by have := hVV 1 (by omega); simpa using this
  have hV0_20 : V0 ^ 20 ≤ V := hVV 20 (by omega)
  -- the threshold
  have hV02 : 2 ≤ V0 := by omega
  have hv20 : ∀ i, (![pV g, sV g, q2V g, wV g, QV a b Δ g] : Fin 5 → ℕ) i ≤ V0 ^ 20 := by
    have p1 : V0 ≤ V0 ^ 20 := by have := pw (i := 1) (j := 20) hV01 (by omega); simpa using this
    exact vec5_le _ _ _ _ _ _ (kp.trans p1) (ks.trans p1) (kq2.trans p1) (kw.trans p1) kQ
  have hthr2 := thr_bounds k ![pV g, sV g, q2V g, wV g, QV a b Δ g] V0 hV02
    (fun i => two_pow_clog_V hV02 (hv20 i))
  have kthr : TMFront.thrVal k ![pV g, sV g, q2V g, wV g, QV a b Δ g] ≤ V :=
    (Nat.lt_two_pow_self).le.trans (hthr2.trans (hVV _ (by omega)))
  have kB : 2 ^ (TMFront.thrVal k ![pV g, sV g, q2V g, wV g, QV a b Δ g] - 1) ≤ V :=
    (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)).trans (hthr2.trans (hVV _ (by omega)))
  have kP : 2 ^ (k + TMFront.thrVal k ![pV g, sV g, q2V g, wV g, QV a b Δ g] - 1) ≤ V := by
    have h1 : 2 ^ (k + TMFront.thrVal k ![pV g, sV g, q2V g, wV g, QV a b Δ g] - 1) ≤
        2 ^ k * 2 ^ TMFront.thrVal k ![pV g, sV g, q2V g, wV g, QV a b Δ g] := by
      rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
    have h2 : 2 ^ k ≤ V0 ^ k := Nat.pow_le_pow_left hV02 k
    have h3 := Nat.mul_le_mul h2 hthr2
    have h4 : V0 ^ k * V0 ^ (220 * k + 45) = V0 ^ (221 * k + 45) := by rw [← pow_add]; ring_nf
    have h5 := hVV (221 * k + 45) (by omega)
    omega
  have kk : k ≤ V := by
    have h1 : k < 2 ^ k := Nat.lt_two_pow_self
    have h2 : 2 ^ k ≤ V0 ^ k := Nat.pow_le_pow_left hV02 k
    have h3 := hVV k (by omega)
    omega
  have kwd : word.length ≤ V := by
    have h0 : 4 * Δ + 9 < 2 ^ (Δ + 4) := by
      have h := Nat.lt_two_pow_self (n := Δ)
      rw [pow_add]; omega
    have h1 : 2 ^ (Δ + 4) ≤ N ^ (Δ + 4) := Nat.pow_le_pow_left hN2 _
    have h2 : (4 * Δ + 9) * N ^ (160 * (k + 1)) ≤ N ^ (Δ + 4) * N ^ (160 * (k + 1)) :=
      Nat.mul_le_mul_right _ (by omega)
    have h3 : N ^ (Δ + 4) * N ^ (160 * (k + 1)) ≤ N ^ (c * (k + 1)) := by
      rw [← pow_add]; exact Nat.pow_le_pow_right (by omega) (by nlinarith)
    have h4 : N ^ (c * (k + 1)) = V0 ^ (k + 1) := by rw [hV0def, ← pow_mul]
    have h5 := hVV (k + 1) (by omega)
    omega
  have hee2 : 2 ^ (Nat.clog 2 (Nat.clog 2 g.vertices + 1) * Nat.clog 2 (Nat.clog 2 g.vertices + 1)) ≤ V ^ 2 := by
    have h1 : V ≤ V ^ 2 := by
      have := Nat.pow_le_pow_right (show 1 ≤ V by omega) (show 1 ≤ 2 by omega); simpa using this
    exact kee.trans ((hNc 11 (by omega)).trans (hV0V.trans h1))
  have hfull := fullBd_le a b Δ g k word V (k32.trans hV0V) (kc.trans hV0V) (ka.trans hV0V) (kbΔ.trans hV0V)
    (kb.trans hV0V) (kn.trans hV0V) (km0.trans hV0V) (k2L.trans ((hNc 2 (by omega)).trans hV0V))
    (k2e.trans ((hNc 3 (by omega)).trans hV0V)) hee2 (kenc.trans hV0V) (kp.trans hV0V) (ks.trans hV0V)
    (kq2.trans hV0V) (kw.trans hV0V) (kQ.trans hV0_20) (kq1.trans hV0V) kk (by rw [eLg]; exact kL.trans hV0V)
    kwd kthr kB kP
  have hV45 : V ≤ V ^ 45 := by
    have := Nat.pow_le_pow_right (show 1 ≤ V by omega) (show 1 ≤ 45 by omega); simpa using this
  have eV : V ^ 45 = N ^ (c * 266 * 45 * (k + 1)) := by
    rw [hVdef, hV0def, ← pow_mul, ← pow_mul]; ring_nf
  have hsmall : g.vertices + g.edges.length + 2 + 1 ≤ V := by
    have := kn.trans hV0V
    have := km0.trans hV0V
    have h2 : 2 * V0 ≤ V0 * V0 := Nat.mul_le_mul_right _ hV02
    have h3 : V0 * V0 = V0 ^ 2 := by ring
    have h4 := hVV 2 (by omega)
    omega
  rw [← eV]
  omega

end Paper2.FrontClock13

#print axioms Paper2.FrontClock13.qv_le
#print axioms Paper2.FrontClock13.word_le
#print axioms Paper2.FrontClock13.thr_bounds
#print axioms Paper2.FrontClock13.frontClock
