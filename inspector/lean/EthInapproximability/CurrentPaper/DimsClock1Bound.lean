import EthInapproximability.CurrentPaper.DimsClock1Reads
import EthInapproximability.CurrentPaper.ClockD
import EthInapproximability.CurrentPaper.EntryClockPolyFrame

/-! Lane owner:b-dims-clock-1, segments 1 and 2 (arithmetic over the ADMITTED `NextDimsMachineTN`).

Segment 1 (`vals_le`): if the two output words are nonempty (`1 ≤ rowsOut x`, `1 ≤ colsOut x`) and
`1 ≤ x.c`, EVERY value read by a stage clock of the admitted `dimsBound` (and every cell cleared by
the final charged clear) is at most `W = 16 (rowsOut x + colsOut x + 1)`. Each pow2 stage's `2^e` is
its own written cell (`v5, v14, v32, v39, v55`), bounded as such. Route: `rowsOut = v43 = v40^v39`,
`colsOut = v63 = v39 * v62`, `v62 = v59^v32`; positivity of the outputs forces every factor of the
products `v40 = v32 v29 = v32 (184 v21 v24) v17 v24`, `v59 = 2^22 v53 t v46 v50` to be `≥ 1`, so each
factor is at most the product; the exponents `v39`, `v38`, `v13`, `v31` are below their powers
(`v40 ≥ 184`), the log arguments below `2^clog`; `x.b ≤ v34 ≤ v35` uses `1 ≤ x.c`.

Segment 2 (`dimsBound_le`): `dimsBound x ≤ (2 Kc + 5000) (W + 1)^2` (`Kc` the admitted
`ClockD.Kc`), hence `dimsBound_le_sq`: `≤ Kd (rowsOut x + colsOut x + 1)^2`, `Kd = 289 (2 Kc + 5000)`.
Stage clocks: products `exactTime u v 0 = 2 u v + 4 u + 4` with `u v` the written cell; copies
`2 v + 2`; pow2 `4·2^e + 5e + 7`; the two log stages by admitted `ClockD.logStageBound_le`; the five
power stages by admitted `EntryClockPoly.powerBound_le` (module `EntryClockPolyFrame`); the clear by admitted
`CostUpdateStages.sum_le_mul'`. -/

namespace EthInapproximability.CurrentPaper.DimsClock1

open NextDimsMachineTN

set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

theorem one_le_mul_left {m a b : ℕ} (e : m = a * b) (h : 1 ≤ m) : 1 ≤ a := by
  subst e
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha; simp at h
  · exact ha

theorem one_le_mul_right {m a b : ℕ} (e : m = a * b) (h : 1 ≤ m) : 1 ≤ b := by
  subst e
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb; simp at h
  · exact hb

theorem le_mul_left {m a b : ℕ} (e : m = a * b) (hb : 1 ≤ b) : a ≤ m := by
  subst e; exact Nat.le_mul_of_pos_right a hb

theorem le_mul_right {m a b : ℕ} (e : m = a * b) (ha : 1 ≤ a) : b ≤ m := by
  subst e; exact Nat.le_mul_of_pos_left b ha

theorem one_le_pow_base {m a k : ℕ} (e : m = a ^ k) (hk : 1 ≤ k) (h : 1 ≤ m) : 1 ≤ a := by
  subst e
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha; rw [zero_pow (by omega)] at h; omega
  · exact ha

theorem le_pow_base {m a k : ℕ} (e : m = a ^ k) (hk : 1 ≤ k) : a ≤ m := by
  subst e; exact Nat.le_self_pow (by omega) a

theorem exp_le_two_pow (k : ℕ) : k ≤ 2 ^ k := (Nat.lt_two_pow_self).le

theorem le_pow_exp {m a k : ℕ} (e : m = a ^ k) (ha : 2 ≤ a) : k ≤ m := by
  subst e; exact (exp_le_two_pow k).trans (Nat.pow_le_pow_left ha k)

/-- A product stage. -/
theorem mul_le (u v W : ℕ) (hu : u ≤ W) (hp : u * v ≤ W) :
    MatrixAddressMachine.exactTime u v 0 ≤ 6 * W + 4 := by
  unfold MatrixAddressMachine.exactTime
  have h : 2 * u * v = 2 * (u * v) := by ring
  omega

/-- A pow2 stage (`2^e` is the written cell). -/
theorem pow2_le (e W : ℕ) (h : 2 ^ e ≤ W) : 4 * 2 ^ e + 5 * e + 7 ≤ 9 * W + 7 := by
  have := exp_le_two_pow e
  omega

/-- A log stage (admitted `ClockD.logStageBound_le`). -/
theorem log_le (m W : ℕ) (h : m ≤ W) :
    CostUpdateStages.logStageBound m ≤ ClockD.Kc * (W + 1) ^ 2 :=
  (ClockD.logStageBound_le m).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))

/-- A power stage (admitted `EntryClockPoly.powerBound_le` of module `EntryClockPolyFrame`; `base^m` is the written cell). -/
theorem power_le (base m W : ℕ) (hm : m ≤ W) (hp : base ^ m ≤ W) :
    MatrixWeightedPower.powerBound base m ≤ 25 * (W + 1) ^ 2 := by
  have h := EntryClockPoly.powerBound_le base m
  have h1 : m * (9 * (base ^ m + 1) + 7) ≤ W * (9 * (W + 1) + 7) :=
    Nat.mul_le_mul hm (by omega)
  have h2 : W * (9 * (W + 1) + 7) + 1 ≤ 25 * (W + 1) ^ 2 := by nlinarith
  omega

/-- The final clear (admitted `CostUpdateStages.sum_le_mul'`). -/
theorem clearSum_le (x : DimIn) (W : ℕ)
    (h : ∀ i : Fin (64 - 11), S63 x ⟨11 + i.val, by omega⟩ ≤ W) : clearSum x ≤ (64 - 11) * W :=
  CostUpdateStages.sum_le_mul' _ W h

/-- **Segment 1.** Every read value, and every cleared cell, is at most `16 (rowsOut + colsOut + 1)`. -/
theorem vals_le (x : DimIn) (hR : 1 ≤ rowsOut x) (hC : 1 ≤ colsOut x) (hc : 1 ≤ x.c) :
    let W := 16 * (rowsOut x + colsOut x + 1)
    x.lam ≤ W ∧ x.s ≤ W ∧ x.E ≤ W ∧ x.cols ≤ W ∧ x.b ≤ W ∧ x.nv ≤ W ∧ x.rows ≤ W ∧ x.t ≤ W ∧
    v1 x ≤ W ∧ v2 x ≤ W ∧ v3 x ≤ W ∧ v4 x ≤ W ∧ v5 x ≤ W ∧ v6 x ≤ W ∧ v9 x ≤ W ∧ v10 x ≤ W ∧
    v11 x ≤ W ∧ v12 x ≤ W ∧ v13 x ≤ W ∧ v14 x ≤ W ∧ v16 x ≤ W ∧ v17 x ≤ W ∧ v19 x ≤ W ∧
    v21 x ≤ W ∧ v22 x ≤ W ∧ v24 x ≤ W ∧ v25 x ≤ W ∧ v26 x ≤ W ∧ v27 x ≤ W ∧ v28 x ≤ W ∧
    v29 x ≤ W ∧ v30 x ≤ W ∧ v31 x ≤ W ∧ v32 x ≤ W ∧ v33 x ≤ W ∧ v34 x ≤ W ∧ v35 x ≤ W ∧
    v36 x ≤ W ∧ v37 x ≤ W ∧ v38 x ≤ W ∧ v39 x ≤ W ∧ v40 x ≤ W ∧ v41 x ≤ W ∧ v43 x ≤ W ∧
    v44 x ≤ W ∧ v45 x ≤ W ∧ v46 x ≤ W ∧ v48 x ≤ W ∧ v49 x ≤ W ∧ v50 x ≤ W ∧ v53 x ≤ W ∧
    v54 x ≤ W ∧ v55 x ≤ W ∧ v56 x ≤ W ∧ v57 x ≤ W ∧ v58 x ≤ W ∧ v59 x ≤ W ∧ v60 x ≤ W ∧
    v62 x ≤ W ∧ v63 x ≤ W := by
  intro W
  -- the admitted definitions, one step each (`rfl`)
  have e43 : rowsOut x = v40 x ^ v39 x := rfl
  have e63 : colsOut x = v39 x * v62 x := rfl
  have e40 : v40 x = v32 x * v29 x := rfl
  have e29 : v29 x = v28 x * v24 x := rfl
  have e28 : v28 x = v27 x * v17 x := rfl
  have e27 : v27 x = v25 x * v26 x := rfl
  have e25 : v25 x = 184 := rfl
  have e26 : v26 x = v21 x * v24 x := rfl
  have e24 : v24 x = v17 x ^ v22 x := rfl
  have e22 : v22 x = x.s := rfl
  have e21 : v21 x = x.cols ^ v19 x := rfl
  have e19 : v19 x = 1 + x.s := rfl
  have e17 : v17 x = v14 x * v16 x := rfl
  have e16 : v16 x = x.cols ^ v9 x := rfl
  have e14 : v14 x = 2 ^ v13 x := rfl
  have e13 : v13 x = Nat.clog 2 (v12 x) := rfl
  have e12 : v12 x = v11 x * x.E := rfl
  have e11 : v11 x = v10 x * x.s := rfl
  have e10 : v10 x = 12 := rfl
  have e9 : v9 x = 1 + (x.s + v6 x) := rfl
  have e6 : v6 x = v5 x - 2 := rfl
  have e5 : v5 x = 2 ^ v4 x := rfl
  have e4 : v4 x = v2 x * v3 x := rfl
  have e2 : v2 x = 256 := rfl
  have e3 : v3 x = x.lam * v1 x := rfl
  have e1 : v1 x = x.lam := rfl
  have e31 : v31 x = v30 x * v3 x := rfl
  have e30 : v30 x = 1000 := rfl
  have e32 : v32 x = 2 ^ v31 x := rfl
  have e39 : v39 x = 2 ^ v38 x := rfl
  have e38 : v38 x = Nat.clog 2 (v37 x) := rfl
  have e37 : v37 x = v36 x * v32 x := rfl
  have e36 : v36 x = v35 x * x.s := rfl
  have e35 : v35 x = v34 x * x.c := rfl
  have e34 : v34 x = v33 x * x.b := rfl
  have e33 : v33 x = 1280 := rfl
  have e41 : v41 x = v39 x := rfl
  have e43' : v43 x = rowsOut x := rfl
  have e62 : v62 x = v59 x ^ v60 x := rfl
  have e60 : v60 x = v32 x := rfl
  have e59 : v59 x = v58 x * v50 x := rfl
  have e58 : v58 x = v57 x * v46 x := rfl
  have e57 : v57 x = v56 x * x.t := rfl
  have e56 : v56 x = v55 x * v53 x := rfl
  have e55 : v55 x = 2 ^ v54 x := rfl
  have e54 : v54 x = 22 := rfl
  have e53 : v53 x = v50 x + (v46 x + x.t) := rfl
  have e50 : v50 x = v49 x * x.rows := rfl
  have e49 : v49 x = v45 x * v48 x := rfl
  have e45 : v45 x = v44 x * x.s := rfl
  have e44 : v44 x = 4 := rfl
  have e48 : v48 x = x.s - 3 := rfl
  have e46 : v46 x = x.nv * x.rows := rfl
  have e63' : v63 x = colsOut x := rfl
  -- rows side: every factor of v40 is positive and below rowsOut
  have p39 : 1 ≤ v39 x := by rw [e39]; exact Nat.one_le_two_pow
  have p32 : 1 ≤ v32 x := by rw [e32]; exact Nat.one_le_two_pow
  have p40 : 1 ≤ v40 x := one_le_pow_base e43 p39 hR
  have b40 : v40 x ≤ rowsOut x := le_pow_base e43 p39
  have p29 : 1 ≤ v29 x := one_le_mul_right e40 p40
  have b29 : v29 x ≤ v40 x := le_mul_right e40 p32
  have b32 : v32 x ≤ v40 x := le_mul_left e40 p29
  have p28 : 1 ≤ v28 x := one_le_mul_left e29 p29
  have p24 : 1 ≤ v24 x := one_le_mul_right e29 p29
  have b28 : v28 x ≤ v29 x := le_mul_left e29 p24
  have b24 : v24 x ≤ v29 x := le_mul_right e29 p28
  have p27 : 1 ≤ v27 x := one_le_mul_left e28 p28
  have p17 : 1 ≤ v17 x := one_le_mul_right e28 p28
  have b27 : v27 x ≤ v28 x := le_mul_left e28 p17
  have b17 : v17 x ≤ v28 x := le_mul_right e28 p27
  have p26 : 1 ≤ v26 x := one_le_mul_right e27 p27
  have b25 : v25 x ≤ v27 x := le_mul_left e27 p26
  have b26 : v26 x ≤ v27 x := le_mul_right e27 (by rw [e25]; norm_num)
  have p21 : 1 ≤ v21 x := one_le_mul_left e26 p26
  have b21 : v21 x ≤ v26 x := le_mul_left e26 p24
  have p14 : 1 ≤ v14 x := one_le_mul_left e17 p17
  have p16 : 1 ≤ v16 x := one_le_mul_right e17 p17
  have b14 : v14 x ≤ v17 x := le_mul_left e17 p16
  have b16 : v16 x ≤ v17 x := le_mul_right e17 p14
  have h19 : 1 ≤ v19 x := by rw [e19]; omega
  have pcols : 1 ≤ x.cols := one_le_pow_base e21 h19 p21
  have bcols : x.cols ≤ v21 x := le_pow_base e21 h19
  have h184 : 2 ≤ v40 x := by rw [e25] at b25; omega
  have b39 : v39 x ≤ rowsOut x := le_pow_exp e43 h184
  have b37 : v37 x ≤ v39 x := by rw [e39, e38]; exact Nat.le_pow_clog (by norm_num) _
  have b38 : v38 x ≤ v39 x := by rw [e39]; exact exp_le_two_pow _
  have b36 : v36 x ≤ v37 x := le_mul_left e37 p32
  have b12 : v12 x ≤ v14 x := by rw [e14, e13]; exact Nat.le_pow_clog (by norm_num) _
  have b13 : v13 x ≤ v14 x := by rw [e14]; exact exp_le_two_pow _
  have b31 : v31 x ≤ v32 x := by rw [e32]; exact exp_le_two_pow _
  have b43 : v4 x ≤ v31 x := by rw [e4, e31, e2, e30]; omega
  have b5 : v5 x ≤ v32 x := by rw [e5, e32]; exact Nat.pow_le_pow_right (by norm_num) b43
  have b3 : v3 x ≤ v31 x := by rw [e31, e30]; omega
  have blam : x.lam ≤ v3 x := by rw [e3, e1]; exact Nat.le_mul_self _
  have b6 : v6 x ≤ v5 x := by rw [e6]; omega
  -- cols side: every factor of v59 is positive and below colsOut
  have p62 : 1 ≤ v62 x := one_le_mul_right e63 hC
  have b62 : v62 x ≤ colsOut x := le_mul_right e63 p39
  have p60 : 1 ≤ v60 x := by rw [e60]; exact p32
  have p59 : 1 ≤ v59 x := one_le_pow_base e62 p60 p62
  have b59 : v59 x ≤ v62 x := le_pow_base e62 p60
  have p58 : 1 ≤ v58 x := one_le_mul_left e59 p59
  have p50 : 1 ≤ v50 x := one_le_mul_right e59 p59
  have b58 : v58 x ≤ v59 x := le_mul_left e59 p50
  have b50 : v50 x ≤ v59 x := le_mul_right e59 p58
  have p57 : 1 ≤ v57 x := one_le_mul_left e58 p58
  have p46 : 1 ≤ v46 x := one_le_mul_right e58 p58
  have b57 : v57 x ≤ v58 x := le_mul_left e58 p46
  have b46 : v46 x ≤ v58 x := le_mul_right e58 p57
  have p56 : 1 ≤ v56 x := one_le_mul_left e57 p57
  have pt : 1 ≤ x.t := one_le_mul_right e57 p57
  have b56 : v56 x ≤ v57 x := le_mul_left e57 pt
  have bt : x.t ≤ v57 x := le_mul_right e57 p56
  have p53 : 1 ≤ v53 x := one_le_mul_right e56 p56
  have p55 : 1 ≤ v55 x := by rw [e55]; exact Nat.one_le_two_pow
  have b55 : v55 x ≤ v56 x := le_mul_left e56 p53
  have b53 : v53 x ≤ v56 x := le_mul_right e56 p55
  have c55 : v55 x = 4194304 := by rw [e55, e54]; norm_num
  have p49 : 1 ≤ v49 x := one_le_mul_left e50 p50
  have prows : 1 ≤ x.rows := one_le_mul_right e50 p50
  have b49 : v49 x ≤ v50 x := le_mul_left e50 prows
  have brows : x.rows ≤ v50 x := le_mul_right e50 p49
  have p45 : 1 ≤ v45 x := one_le_mul_left e49 p49
  have p48 : 1 ≤ v48 x := one_le_mul_right e49 p49
  have b45 : v45 x ≤ v49 x := le_mul_left e49 p48
  have b48 : v48 x ≤ v49 x := le_mul_right e49 p45
  have ps : 1 ≤ x.s := by rw [e45, e44] at p45; omega
  have bs : x.s ≤ v45 x := by rw [e45, e44]; omega
  have bnv : x.nv ≤ v46 x := le_mul_left e46 prows
  have bE : x.E ≤ v12 x := le_mul_right e12 (by rw [e11, e10]; omega)
  have bb : x.b ≤ v34 x := by rw [e34, e33]; omega
  have b34 : v34 x ≤ v35 x := le_mul_left e35 hc
  have b35 : v35 x ≤ v36 x := le_mul_left e36 ps
  have b11 : v11 x ≤ 12 * x.s := by rw [e11, e10]
  have hW : W = 16 * (rowsOut x + colsOut x + 1) := rfl
  clear_value W
  clear e43 e63 e40 e29 e28 e27 e26 e24 e21 e17 e16 e14 e13 e12 e11 e5 e4 e3 e31 e32 e39 e38 e37 e36
    e35 e34 e62 e59 e58 e57 e56 e55 e50 e49 e45 e46
  and_intros <;> omega

#print axioms vals_le

/-- **Segment 2.** The admitted dims clock is quadratic in the two output dimensions. -/
theorem dimsBound_le (x : DimIn) (hR : 1 ≤ rowsOut x) (hC : 1 ≤ colsOut x) (hc : 1 ≤ x.c) :
    dimsBound x ≤ (2 * ClockD.Kc + 5000) * (16 * (rowsOut x + colsOut x + 1) + 1) ^ 2 := by
  obtain ⟨hlam, hs, hE, hcols, hb, hnv, hrows, ht, h1, h2, h3, h4, h5, h6, h9, h10, h11, h12, h13, h14,
    h16, h17, h19, h21, h22, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38,
    h39, h40, h41, h43, h44, h45, h46, h48, h49, h50, h53, h54, h55, h56, h57, h58, h59, h60, h62,
    h63⟩ := vals_le x hR hC hc
  generalize hW : 16 * (rowsOut x + colsOut x + 1) = W at *
  -- the stages (written cell = product / power, `rfl`)
  have s3 := mul_le x.lam (v1 x) W hlam (show v3 x ≤ W from h3)
  have s4 := mul_le (v2 x) (v3 x) W h2 (show v4 x ≤ W from h4)
  have s11 := mul_le (v10 x) x.s W h10 (show v11 x ≤ W from h11)
  have s12 := mul_le (v11 x) x.E W h11 (show v12 x ≤ W from h12)
  have s17 := mul_le (v14 x) (v16 x) W h14 (show v17 x ≤ W from h17)
  have s26 := mul_le (v21 x) (v24 x) W h21 (show v26 x ≤ W from h26)
  have s27 := mul_le (v25 x) (v26 x) W h25 (show v27 x ≤ W from h27)
  have s28 := mul_le (v27 x) (v17 x) W h27 (show v28 x ≤ W from h28)
  have s29 := mul_le (v28 x) (v24 x) W h28 (show v29 x ≤ W from h29)
  have s31 := mul_le (v30 x) (v3 x) W h30 (show v31 x ≤ W from h31)
  have s34 := mul_le (v33 x) x.b W h33 (show v34 x ≤ W from h34)
  have s35 := mul_le (v34 x) x.c W h34 (show v35 x ≤ W from h35)
  have s36 := mul_le (v35 x) x.s W h35 (show v36 x ≤ W from h36)
  have s37 := mul_le (v36 x) (v32 x) W h36 (show v37 x ≤ W from h37)
  have s40 := mul_le (v32 x) (v29 x) W h32 (show v40 x ≤ W from h40)
  have s45 := mul_le (v44 x) x.s W h44 (show v45 x ≤ W from h45)
  have s46 := mul_le x.nv x.rows W hnv (show v46 x ≤ W from h46)
  have s49 := mul_le (v45 x) (v48 x) W h45 (show v49 x ≤ W from h49)
  have s50 := mul_le (v49 x) x.rows W h49 (show v50 x ≤ W from h50)
  have s56 := mul_le (v55 x) (v53 x) W h55 (show v56 x ≤ W from h56)
  have s57 := mul_le (v56 x) x.t W h56 (show v57 x ≤ W from h57)
  have s58 := mul_le (v57 x) (v46 x) W h57 (show v58 x ≤ W from h58)
  have s59 := mul_le (v58 x) (v50 x) W h58 (show v59 x ≤ W from h59)
  have s63 := mul_le (v39 x) (v62 x) W h39 (show v63 x ≤ W from h63)
  have q5 := pow2_le (v4 x) W (show v5 x ≤ W from h5)
  have q14 := pow2_le (v13 x) W (show v14 x ≤ W from h14)
  have q32 := pow2_le (v31 x) W (show v32 x ≤ W from h32)
  have q39 := pow2_le (v38 x) W (show v39 x ≤ W from h39)
  have q55 := pow2_le (v54 x) W (show v55 x ≤ W from h55)
  have l13 := log_le (v12 x) W h12
  have l38 := log_le (v37 x) W h37
  have w16 := power_le x.cols (v9 x) W h9 (show v16 x ≤ W from h16)
  have w21 := power_le x.cols (v19 x) W h19 (show v21 x ≤ W from h21)
  have w24 := power_le (v17 x) (v22 x) W h22 (show v24 x ≤ W from h24)
  have w43 := power_le (v40 x) (v41 x) W h41 (show v43 x ≤ W from h43)
  have w62 := power_le (v59 x) (v60 x) W h60 (show v62 x ≤ W from h62)
  have cl := clearSum_le x W (by
    intro i
    fin_cases i
    · show v1 x ≤ W; exact h1
    · show v2 x ≤ W; exact h2
    · show v3 x ≤ W; exact h3
    · show v4 x ≤ W; exact h4
    · show v6 x ≤ W; exact h6
    · exact Nat.zero_le _
    · show v10 x ≤ W; exact h10
    · show v11 x ≤ W; exact h11
    · show v12 x ≤ W; exact h12
    · show v13 x ≤ W; exact h13
    · show v14 x ≤ W; exact h14
    · show v16 x ≤ W; exact h16
    · show v17 x ≤ W; exact h17
    · exact Nat.zero_le _
    · show v21 x ≤ W; exact h21
    · exact Nat.zero_le _
    · show v24 x ≤ W; exact h24
    · show v25 x ≤ W; exact h25
    · show v26 x ≤ W; exact h26
    · show v27 x ≤ W; exact h27
    · show v28 x ≤ W; exact h28
    · show v29 x ≤ W; exact h29
    · show v30 x ≤ W; exact h30
    · show v31 x ≤ W; exact h31
    · show v32 x ≤ W; exact h32
    · show v33 x ≤ W; exact h33
    · show v34 x ≤ W; exact h34
    · show v35 x ≤ W; exact h35
    · show v36 x ≤ W; exact h36
    · show v37 x ≤ W; exact h37
    · show v38 x ≤ W; exact h38
    · show v39 x ≤ W; exact h39
    · show v40 x ≤ W; exact h40
    · exact Nat.zero_le _
    · show v44 x ≤ W; exact h44
    · show v45 x ≤ W; exact h45
    · show v46 x ≤ W; exact h46
    · show v48 x ≤ W; exact h48
    · show v49 x ≤ W; exact h49
    · show v50 x ≤ W; exact h50
    · show v53 x ≤ W; exact h53
    · show v54 x ≤ W; exact h54
    · show v55 x ≤ W; exact h55
    · show v56 x ≤ W; exact h56
    · show v57 x ≤ W; exact h57
    · show v58 x ≤ W; exact h58
    · show v59 x ≤ W; exact h59
    · exact Nat.zero_le _
    · show v62 x ≤ W; exact h62
    · exact Nat.zero_le _
    · exact Nat.zero_le _
    · exact Nat.zero_le _
    · exact Nat.zero_le _)
  clear hE hcols hb hnv hrows h1 h2 h3 h4 h5 h9 h10 h11 h12 h13 h14 h16 h17 h19 h21 h22 h24 h25
    h26 h27 h28 h29 h30 h31 h33 h34 h35 h36 h37 h38 h40 h41 h43 h44 h45 h48 h49 h53 h54 h55
    h56 h57 h58 h59 h60 h62 h63
  rw [dimsBound_eq]
  have hQ : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hsplit : (2 * ClockD.Kc + 5000) * (W + 1) ^ 2 =
      2 * (ClockD.Kc * (W + 1) ^ 2) + 5000 * (W + 1) ^ 2 := by ring
  rw [hsplit]
  generalize (W + 1) ^ 2 = Q at *
  generalize ClockD.Kc * Q = KQ at *
  omega

#print axioms dimsBound_le

/-- The fixed constant of the quadratic dims clock. -/
noncomputable def Kd : ℕ := 289 * (2 * ClockD.Kc + 5000)

/-- **Segment 2 (final form).** `dimsBound x ≤ Kd (rowsOut x + colsOut x + 1)^2`. -/
theorem dimsBound_le_sq (x : DimIn) (hR : 1 ≤ rowsOut x) (hC : 1 ≤ colsOut x) (hc : 1 ≤ x.c) :
    dimsBound x ≤ Kd * (rowsOut x + colsOut x + 1) ^ 2 := by
  have h := dimsBound_le x hR hC hc
  have h1 : (16 * (rowsOut x + colsOut x + 1) + 1) ^ 2 ≤ 289 * (rowsOut x + colsOut x + 1) ^ 2 := by
    have : 16 * (rowsOut x + colsOut x + 1) + 1 ≤ 17 * (rowsOut x + colsOut x + 1) := by omega
    calc (16 * (rowsOut x + colsOut x + 1) + 1) ^ 2 ≤ (17 * (rowsOut x + colsOut x + 1)) ^ 2 :=
          Nat.pow_le_pow_left this 2
      _ = 289 * (rowsOut x + colsOut x + 1) ^ 2 := by ring
  unfold Kd
  calc dimsBound x ≤ (2 * ClockD.Kc + 5000) * (16 * (rowsOut x + colsOut x + 1) + 1) ^ 2 := h
    _ ≤ (2 * ClockD.Kc + 5000) * (289 * (rowsOut x + colsOut x + 1) ^ 2) := Nat.mul_le_mul_left _ h1
    _ = 289 * (2 * ClockD.Kc + 5000) * (rowsOut x + colsOut x + 1) ^ 2 := by ring

#print axioms dimsBound_le_sq

end EthInapproximability.CurrentPaper.DimsClock1
