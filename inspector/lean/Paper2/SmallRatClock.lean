import Paper2.SmallRatSched

/-! Lane owner:a-small-1, R16 part 4: the k-free polynomial clock of the full schedule machine
`SmallRatSched.schedR Δ γ`: `2^E·(|encode g|+1)^E` with `E = 47·cF Δ γ` (no `k` anywhere). -/

set_option maxHeartbeats 64000000
set_option maxRecDepth 16384

namespace SmallRatClock

noncomputable section

open EthInapproximability.CurrentPaper
open Paper2
open Paper2.FrontClock13
open SmallRatProg SmallRatSched

theorem pw {V i j : ℕ} (hV : 1 ≤ V) (h : i ≤ j) : V ^ i ≤ V ^ j := Nat.pow_le_pow_right hV h

theorem mulb {V x y i j : ℕ} (hx : x ≤ V ^ i) (hy : y ≤ V ^ j) : x * y ≤ V ^ (i + j) := by
  rw [pow_add]; exact Nat.mul_le_mul hx hy

theorem et {V r w i j : ℕ} (hV : 1 ≤ V) (hr : r ≤ V ^ i) (hw : w ≤ V ^ j) :
    MatrixAddressMachine.exactTime r w 0 ≤ 10 * V ^ (i + j) := by
  unfold MatrixAddressMachine.exactTime
  have h1 := mulb hr hw
  have h2 : V ^ i ≤ V ^ (i + j) := pw hV (by omega)
  have h3 : 1 ≤ V ^ (i + j) := Nat.one_le_pow _ _ (by omega)
  have e : 2 * r * w = 2 * (r * w) := by ring
  rw [e]
  omega

theorem mx {V x y k : ℕ} (hx : x ≤ V ^ k) (hy : y ≤ V ^ k) : max x y ≤ V ^ k := max_le hx hy

/-- The generic clock of the arithmetic part. -/
theorem ratBd_le (n a am bd b6 s w L Q V : ℕ) (hV : 2 ^ 32 ≤ V) (hn : n ≤ V) (ha : a ≤ V)
    (ham : am ≤ V ^ 2) (hbd : bd ≤ V) (hb6 : b6 ≤ V) (hs : s ≤ V ^ 2) (hw : w ≤ V ^ 2)
    (hL : L ≤ V) (hQ : Q ≤ V ^ 44) (h2L : 2 ^ L ≤ V) (h10 : 2 ^ (10 * L) ≤ V ^ 10) :
    ratBd n a am bd b6 s w L Q ≤ V ^ 46 := by
  have hV1 : 1 ≤ V := le_trans (Nat.one_le_two_pow) hV
  have v1 : ∀ x, x ≤ V → x ≤ V ^ 1 := fun x h => by simpa using h
  have c65 : 65536 ≤ V ^ 1 := v1 _ (le_trans (by norm_num) hV)
  have c16 : 16 ≤ V ^ 1 := v1 _ (le_trans (by norm_num) hV)
  have c10 : 10 ≤ V ^ 1 := v1 _ (le_trans (by norm_num) hV)
  have c320 : 320 ≤ V ^ 1 := v1 _ (le_trans (by norm_num) hV)
  have x0 : a * am ≤ V ^ (1 + 2) := mulb (v1 _ ha) ham
  have x1 : bd * n ≤ V ^ (1 + 1) := mulb (v1 _ hbd) (v1 _ hn)
  have x2 : a * (bd * n) ≤ V ^ (1 + (1 + 1)) := mulb (v1 _ ha) x1
  have x3 : b6 * am ≤ V ^ (1 + 2) := mulb (v1 _ hb6) ham
  have x4 : max (a * am) (a * (bd * n)) ≤ V ^ 3 := mx x0 x2
  have x5 : max (max (a * am) (a * (bd * n))) (b6 * am) ≤ V ^ 3 := mx x4 x3
  have x7 : 65536 * s ≤ V ^ (1 + 2) := mulb c65 hs
  have x8 : 65536 * s * max (max (a * am) (a * (bd * n))) (b6 * am) ≤ V ^ ((1 + 2) + 3) :=
    mulb x7 x5
  have x10 : 16 * w ≤ V ^ (1 + 2) := mulb c16 hw
  have x15 : 10 * L ≤ V ^ (1 + 1) := mulb c10 (v1 _ hL)
  have s1 := et hV1 (v1 _ ha) ham
  have s2 := et hV1 (v1 _ hbd) (v1 _ hn)
  have s3 := et hV1 (v1 _ ha) x1
  have s4 := et hV1 (v1 _ hb6) ham
  have s8 := et hV1 c65 hs
  have s9 := et hV1 x7 x5
  have s11 := et hV1 c16 hw
  have s12 := et hV1 x8 x10
  have s16 := et hV1 c10 (v1 _ hL)
  have s19 := et hV1 c320 hQ
  have p1 : V ^ 1 ≤ V ^ 45 := pw hV1 (by omega)
  have p2 : V ^ (1 + 1) ≤ V ^ 45 := pw hV1 (by omega)
  have p3 : V ^ (1 + 2) ≤ V ^ 45 := pw hV1 (by omega)
  have p3' : V ^ (1 + (1 + 1)) ≤ V ^ 45 := pw hV1 (by omega)
  have p3'' : V ^ 3 ≤ V ^ 45 := pw hV1 (by omega)
  have p4 : V ^ (1 + 1 + 1) ≤ V ^ 45 := pw hV1 (by omega)
  have p5 : V ^ (1 + 2 + 3) ≤ V ^ 45 := pw hV1 (by omega)
  have p6 : V ^ (1 + (1 + 2)) ≤ V ^ 45 := pw hV1 (by omega)
  have p7 : V ^ (1 + 2 + 3 + (1 + 2)) ≤ V ^ 45 := pw hV1 (by omega)
  have p8 : V ^ (1 + (1 + 2)) ≤ V ^ 45 := pw hV1 (by omega)
  have p9 : V ^ 10 ≤ V ^ 45 := pw hV1 (by omega)
  have p10 : V ^ (1 + 44) ≤ V ^ 45 := pw hV1 (by omega)
  have p11 : V ^ (1 + 2 + 3) ≤ V ^ 45 := pw hV1 (by omega)
  have hV1' : V ≤ V ^ 45 := by simpa using p1
  have hbig : 4294967296 * V ^ 45 ≤ V ^ 46 := by
    rw [pow_succ]
    have := Nat.mul_le_mul_left (V ^ 45) hV
    rw [Nat.mul_comm]
    simpa using this
  have hVpos : 1 ≤ V ^ 45 := Nat.one_le_pow _ _ (by omega)
  unfold ratBd
  omega

theorem pow_two_mul (x E : ℕ) : (x + 2) ^ E ≤ 2 ^ E * (x + 1) ^ E := by
  rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) E

theorem le_four_mul (q : ℕ) : q ≤ 4 * q := by omega

private theorem le_add_sandwich (a b c : ℕ) : b ≤ a + b + c := by omega

theorem qBd_four (a b Δ n m L s w : ℕ) :
    4 * QProducer.qVal a b Δ n m L s w ≤ QProducer.qBd a b Δ n m L s w := by
  unfold QProducer.qBd QProducer.qVal
  set z := max (max (QProducer.C0 L s w) (QProducer.A2 a b Δ n m L s w))
    (QProducer.A3 a b L s w)
  apply le_trans (b := 4 * 2 ^ Nat.clog 2 z + 5 * Nat.clog 2 z + 7)
  · omega
  · exact le_add_sandwich _ _ _

theorem lqBd_contains_qBd (a b Δ n m : ℕ) :
    QProducer.qBd a b Δ n m (Nat.clog 2 n)
      (2 ^ (16 + Nat.clog 2 (Nat.clog 2 n + 1)))
      (2 ^ (Nat.clog 2 (Nat.clog 2 n + 1) * Nat.clog 2 (Nat.clog 2 n + 1))) ≤
    CountFront.lqBd a b Δ n m := by
  unfold CountFront.lqBd
  exact le_add_sandwich _ _ _

theorem gBd_contains_lqBd (a b Δ : ℕ) (g : EncodedGraph.Graph) :
    CountFront.lqBd a b Δ g.vertices g.edges.length ≤ FullFront.gBd a b Δ g := by
  unfold FullFront.gBd
  exact le_add_sandwich _ _ _

theorem coverWidth_le_front (Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph)
    (heq : ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length
      (Nat.clog 2 g.vertices) Δ γ =
      QProducer.qVal γ.num.toNat γ.den Δ g.vertices g.edges.length
        (Nat.clog 2 g.vertices)
        (2 ^ (16 + Nat.clog 2 (Nat.clog 2 g.vertices + 1)))
        (2 ^ (Nat.clog 2 (Nat.clog 2 g.vertices + 1) *
          Nat.clog 2 (Nat.clog 2 g.vertices + 1)))) :
    4 * ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length
      (Nat.clog 2 g.vertices) Δ γ ≤ FullFront.gBd γ.num.toNat γ.den Δ g := by
  rw [heq]
  exact (qBd_four γ.num.toNat γ.den Δ g.vertices g.edges.length
    (Nat.clog 2 g.vertices)
    (2 ^ (16 + Nat.clog 2 (Nat.clog 2 g.vertices + 1)))
    (2 ^ (Nat.clog 2 (Nat.clog 2 g.vertices + 1) *
      Nat.clog 2 (Nat.clog 2 g.vertices + 1)))).trans
    ((lqBd_contains_qBd γ.num.toNat γ.den Δ g.vertices g.edges.length).trans
      (gBd_contains_lqBd γ.num.toNat γ.den Δ g))

/-- **The k-free clock of the arithmetic part**, at the actual values. -/
theorem ratTime_le (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices)
    (hinc : ∀ v, ∃ e b, CanonicalEdgeTape.graphEdge g hg e b = v)
    (hdeg : ∀ v, SourceItems.degree (CanonicalEdgeTape.graphEdge g hg) v ≤ Δ) :
    ratTime Δ γ g ≤ ((EncodedGraph.encode g).length + 2) ^ (cF Δ γ * 46) := by
  obtain ⟨-, -, -, -, FL, FQ, -, -, hQF, -, -, -, -, -, -, hQ, -⟩ :=
    SSSchedClock.schedule_machine Δ γ hγ hΔ g hg hn hinc hdeg
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, q24, -⟩ := hQF
  have hQeq := congrArg List.length (hQ.symm.trans q24)
  simp only [QProducer.u, List.length_replicate] at hQeq
  -- the frozen front's clock dominates Q
  have hQg : 4 * ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length
      (Nat.clog 2 g.vertices) Δ γ ≤ FullFront.gBd γ.num.toNat γ.den Δ g := by
    apply coverWidth_le_front Δ γ g
    simpa only [QProducer.qVal] using hQeq
  have hlow := EncodedGraph.encode_length_lower g
  have hcge : 200 + γ.num.toNat + γ.den + Δ + UnaryBinaryEncoding.coefficient ≤ cF Δ γ := le_rfl
  unfold ratTime
  rw [LProducer.s_eq, LProducer.w_eq]
  generalize hQv : ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length
    (Nat.clog 2 g.vertices) Δ γ = Qv at hQg
  obtain ⟨N, hNdef⟩ : ∃ N, N = (EncodedGraph.encode g).length + 2 := ⟨_, rfl⟩
  rw [← hNdef]
  generalize cF Δ γ = c at *
  have hN2 : 2 ≤ N := by omega
  obtain ⟨V0, hV0def⟩ : ∃ V0, V0 = N ^ c := ⟨_, rfl⟩
  have hV01 : 1 ≤ V0 := by rw [hV0def]; exact Nat.one_le_pow _ _ (by omega)
  have hNc : ∀ j, j ≤ c → N ^ j ≤ V0 := fun j hj => by
    rw [hV0def]; exact Nat.pow_le_pow_right (by omega) hj
  have hN2V : N ^ 2 ≤ V0 := hNc 2 (by omega)
  have k32 : 2 ^ 32 ≤ V0 := by
    rw [hV0def]
    exact (Nat.pow_le_pow_right (by norm_num) (by omega)).trans (Nat.pow_le_pow_left hN2 c)
  have kc : UnaryBinaryEncoding.coefficient + 6 ≤ V0 := by rw [hV0def]; exact const_le hN2 (by omega)
  have ka : γ.num.toNat ≤ V0 := by rw [hV0def]; exact const_le hN2 (by omega)
  have kbΔ : 2 * γ.den * Δ ≤ V0 := by
    have h1 : γ.den < 2 ^ γ.den := Nat.lt_two_pow_self
    have h2 : Δ < 2 ^ Δ := Nat.lt_two_pow_self
    have h3 : 2 * γ.den * Δ ≤ 2 * 2 ^ γ.den * 2 ^ Δ :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ h1.le) h2.le
    have h4 : 2 * 2 ^ γ.den * 2 ^ Δ = 2 ^ (1 + γ.den + Δ) := by rw [pow_add, pow_add]; ring
    have h5 : 2 ^ (1 + γ.den + Δ) ≤ N ^ c :=
      (Nat.pow_le_pow_right (by norm_num) (by omega)).trans (Nat.pow_le_pow_left hN2 c)
    rw [hV0def]; omega
  have kb : 6144 * γ.den ≤ V0 := by
    have h1 : γ.den < 2 ^ γ.den := Nat.lt_two_pow_self
    have h3 : 6144 * γ.den ≤ 2 ^ 13 * 2 ^ γ.den := Nat.mul_le_mul (by norm_num) h1.le
    have h4 : 2 ^ 13 * 2 ^ γ.den = 2 ^ (13 + γ.den) := by rw [pow_add]
    have h5 : 2 ^ (13 + γ.den) ≤ N ^ c :=
      (Nat.pow_le_pow_right (by norm_num) (by omega)).trans (Nat.pow_le_pow_left hN2 c)
    rw [hV0def]; omega
  have hNV : N ≤ V0 := by have := hNc 1 (by omega); simpa using this
  have kn : g.vertices + 3 ≤ V0 := by omega
  have km : g.edges.length ≤ V0 := by omega
  have kenc : (EncodedGraph.encode g).length + 1 ≤ V0 := by omega
  have k2L : 2 ^ Nat.clog 2 g.vertices ≤ V0 := by
    have h := A3Assembly.Clock.two_pow_clog_le g.vertices
    have h1 : (g.vertices + 2) ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have k2e : 2 ^ Nat.clog 2 (Nat.clog 2 g.vertices + 1) ≤ V0 := by
    have h := A3Assembly.Clock.two_pow_clog_le (Nat.clog 2 g.vertices + 1)
    have hl := clog_le' g.vertices
    have h1 : (Nat.clog 2 g.vertices + 1 + 2) ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have kee : 2 ^ (Nat.clog 2 (Nat.clog 2 g.vertices + 1) * Nat.clog 2 (Nat.clog 2 g.vertices + 1)) ≤
      V0 ^ 2 := by
    have h := clog_sq_le (Nat.clog 2 g.vertices)
    have h1 : 2 ^ (Nat.clog 2 (Nat.clog 2 g.vertices + 1) * Nat.clog 2 (Nat.clog 2 g.vertices + 1)) ≤
        2 ^ (Nat.clog 2 g.vertices + 9) := Nat.pow_le_pow_right (by norm_num) h
    have h2 : 2 ^ (Nat.clog 2 g.vertices + 9) = 2 ^ Nat.clog 2 g.vertices * 2 ^ 9 := pow_add _ _ _
    have hL2 : 2 ^ Nat.clog 2 g.vertices ≤ N ^ 2 := by
      have h := A3Assembly.Clock.two_pow_clog_le g.vertices
      have h1 : (g.vertices + 2) ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left (by omega) 2
      omega
    have h3 : 2 ^ 9 ≤ N ^ 9 := Nat.pow_le_pow_left hN2 9
    have h4 : N ^ 2 * N ^ 9 = N ^ 11 := by rw [← pow_add]
    have h5 := Nat.mul_le_mul hL2 h3
    have h6 := hNc 11 (by omega)
    have h7 : V0 ≤ V0 ^ 2 := by
      have := Nat.pow_le_pow_right hV01 (show 1 ≤ 2 by omega); simpa using this
    calc
      2 ^ (Nat.clog 2 (Nat.clog 2 g.vertices + 1) * Nat.clog 2 (Nat.clog 2 g.vertices + 1))
          ≤ 2 ^ (Nat.clog 2 g.vertices + 9) := h1
      _ = 2 ^ Nat.clog 2 g.vertices * 2 ^ 9 := h2
      _ ≤ N ^ 2 * N ^ 9 := h5
      _ = N ^ 11 := h4
      _ ≤ V0 := h6
      _ ≤ V0 ^ 2 := h7
  have hgb := gBd_le γ.num.toNat γ.den Δ g V0 k32 kc ka kbΔ kb kn km k2L k2e kee kenc
  -- the nine input bounds
  have bam : γ.num.toNat * g.edges.length ≤ V0 ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul ka km
  have bs : 2 ^ (16 + Nat.clog 2 (Nat.clog 2 g.vertices + 1)) ≤ V0 ^ 2 := by
    rw [pow_add, sq]
    exact Nat.mul_le_mul (le_trans (by norm_num) k32) k2e
  have bL : Nat.clog 2 g.vertices ≤ V0 := le_trans (Nat.lt_two_pow_self).le k2L
  have bQ : Qv ≤ V0 ^ 44 := (le_four_mul Qv).trans (hQg.trans hgb)
  have b10 : 2 ^ (10 * Nat.clog 2 g.vertices) ≤ V0 ^ 10 := by
    rw [pow_mul']; exact Nat.pow_le_pow_left k2L 10
  have hr := ratBd_le g.vertices γ.num.toNat (γ.num.toNat * g.edges.length) (2 * γ.den * Δ)
    (6144 * γ.den) _ _ (Nat.clog 2 g.vertices) Qv V0 k32 (by omega) ka bam kbΔ kb bs kee bL bQ k2L b10
  have e46 : V0 ^ 46 = N ^ (c * 46) := by rw [hV0def, ← pow_mul]
  rw [← e46]
  exact hr

/-- **The k-free polynomial clock of the whole program.** -/
theorem total_le (Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph)
    (hr : ratTime Δ γ g ≤ ((EncodedGraph.encode g).length + 2) ^ (cF Δ γ * 46)) :
    2 ^ (cF Δ γ * 45) * ((EncodedGraph.encode g).length + 1) ^ (cF Δ γ * 45) + ratTime Δ γ g + 1 ≤
      2 ^ (cF Δ γ * 47) * ((EncodedGraph.encode g).length + 1) ^ (cF Δ γ * 47) := by
  have hcge : 200 ≤ cF Δ γ := by unfold cF; omega
  generalize cF Δ γ = c at *
  generalize (EncodedGraph.encode g).length = x at *
  have h46 := pow_two_mul x (c * 46)
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = 2 ^ c * (x + 1) ^ c := ⟨_, rfl⟩
  have eZ : ∀ k, 2 ^ (c * k) * (x + 1) ^ (c * k) = Z ^ k := fun k => by
    rw [hZ, mul_pow, ← pow_mul, ← pow_mul]
  rw [eZ 45, eZ 47]
  rw [eZ 46] at h46
  have hZ2 : 2 ≤ Z := by
    rw [hZ]
    have h1 : 2 ≤ 2 ^ c := by
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 1 ≤ c by omega); simpa using this
    have h2 : 1 ≤ (x + 1) ^ c := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have hZ1 : 1 ≤ Z ^ 45 := Nat.one_le_pow _ _ (by omega)
  have a1 : Z ^ 46 = Z ^ 45 * Z := pow_succ Z 45
  have a2 : Z ^ 47 = Z ^ 46 * Z := pow_succ Z 46
  have a3 : Z ^ 45 * 2 ≤ Z ^ 45 * Z := Nat.mul_le_mul_left _ hZ2
  have a4 : Z ^ 46 * 2 ≤ Z ^ 46 * Z := Nat.mul_le_mul_left _ hZ2
  omega

end

end SmallRatClock

#print axioms SmallRatClock.ratBd_le
#print axioms SmallRatClock.ratTime_le
#print axioms SmallRatClock.total_le
#print axioms SmallRatClock.ratTime_le
