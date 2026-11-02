import Paper2.E6RedClock3
-- a-eth-owner-6 copy of frozen a-eth-owner-3/E3RedBudget.lean (SHA-256 9d3230f05395f4062c284c2e1492796c2c30801c2d36b35c22168a8e11ee7f2c); import lines renamed only; the reference `Paper2.AEth2.ceil_pow_le` -> `Paper2.AEth6.ceil_pow_le`.

/-!
# Paper A (lock v12), lane `owner:a-eth-3`, segment 1 (obstacle B2): the reduction stage is inside
# the D-A6 budget

Author decision D-A6 (clock `2^(εN)·(|input|+1)^O(1)` for every `ε > 0` eventually), lock v12
`sections/06-reduction.tex` (proof of `thm:quantitative`: "$n^{O(k+1)}=2^{O(N/\log N)}=2^{o(N)}$").

`redTime2_budget`: for every density `cs` and every `ε > 0` there are `C d N₀` such that for EVERY
sparse valid `Φ` (`clauses ≤ cs·N`) with `N ≥ N₀`, the additive reduction clock of `E3RedClock`
(front cut, admitted T24 front computing `kOf N`, admitted graph stage at `k = kOf N`) satisfies
`redTime2 Φ ≤ C·⌈2^(εN)⌉·(|encode Φ|+1)^d`.

Proof: one fixed polynomial `Tot` in `Y = (|encode Φ|+1)·(expLen N+1)·(n+2)^(K0·(kOf N+1))`
dominates `redTime2` (monotonicity, admitted `encode_length_upper`, `t45_relations`), then the
admitted `T24Runtime.subexponential` (for the `(n+2)^(…(kOf N+1))` factor) and the a-eth-owner-1
`expLen_le_rpow` (for the cut-length factor), each at `ε/2`.

No ledger row is closed.
-/

noncomputable section

namespace Paper2.AEth3

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-- The fixed exponent constant. -/
def K0 : ℕ :=
  4 * Paper2.ABridge.ePk B.degreeBound (sourceGap D B) +
    Paper2.ABridge.stageEA B.degreeBound (sourceGap D B) B.degreeBound_pos (source_gap_pos D B) + 4

def nbY (Y : ℕ) : ℕ := 2 * (Y + Y + 3 * Y) + 3
def PBY (Y : ℕ) : ℕ :=
  (2 + Paper2.ABridge.prepConst) * Y + (26 * (3 * Y) + 2 * ((3 * Y) * Paper2.ABridge.cutPS) + 7)

/-- ONE fixed polynomial dominating the reduction clock. -/
def Tot (Y : ℕ) : ℕ :=
  G Y + 2 * (2 * Y + 1 + 3 * Y) + 2 +
    (CF D B * (2 * Y + 1 + 3 * Y + 1) ^ EF D B + 2 * nbY Y + 2 +
      (cutClockN (sourceGap D B).num.toNat (sourceGap D B).den B.degreeBound (nbY Y) (PBY Y) +
        2 * nbY Y + 2 +
        Paper2.ABridge.stageCA B.degreeBound (sourceGap D B) B.degreeBound_pos
          (source_gap_pos D B) * Y))

/-- The part of `Tot` after the front-cut term. -/
def TotR (Y : ℕ) : ℕ :=
  CF D B * (2 * Y + 1 + 3 * Y + 1) ^ EF D B + 2 * nbY Y + 2 +
    (cutClockN (sourceGap D B).num.toNat (sourceGap D B).den B.degreeBound (nbY Y) (PBY Y) +
      2 * nbY Y + 2 +
      Paper2.ABridge.stageCA B.degreeBound (sourceGap D B) B.degreeBound_pos
        (source_gap_pos D B) * Y)

theorem nbY_poly : Paper2.Unit4Shell.Poly.PolyIn id nbY := by
  unfold nbY
  repeat (first
    | exact Paper2.Unit4Shell.Poly.self
    | exact Paper2.Unit4Shell.Poly.const _
    | apply Paper2.Unit4Shell.Poly.add
    | apply Paper2.Unit4Shell.Poly.mul
    | apply Paper2.Unit4Shell.Poly.pow)

theorem PBY_poly : Paper2.Unit4Shell.Poly.PolyIn id PBY := by
  unfold PBY
  generalize Paper2.ABridge.prepConst = q
  generalize Paper2.ABridge.cutPS = ps
  repeat (first
    | exact Paper2.Unit4Shell.Poly.self
    | exact Paper2.Unit4Shell.Poly.const _
    | apply Paper2.Unit4Shell.Poly.add
    | apply Paper2.Unit4Shell.Poly.mul
    | apply Paper2.Unit4Shell.Poly.pow)

set_option maxRecDepth 20000 in
theorem cutClockN_poly_gen (a b Δ : ℕ) (f g : ℕ → ℕ) (hf : Paper2.Unit4Shell.Poly.PolyIn id f)
    (hg : Paper2.Unit4Shell.Poly.PolyIn id g) :
    Paper2.Unit4Shell.Poly.PolyIn id (fun Y => cutClockN a b Δ (f Y) (g Y)) := by
  unfold cutClockN Paper2.ABridge.cutBdN Paper2.ABridge.clearBd
  generalize Paper2.ABridge.nJ = j
  generalize Paper2.ABridge.packetPerStep a b Δ = S
  repeat (first
    | exact hf
    | exact hg
    | exact Paper2.Unit4Shell.Poly.self
    | exact Paper2.Unit4Shell.Poly.const _
    | apply Paper2.Unit4Shell.Poly.add
    | apply Paper2.Unit4Shell.Poly.mul
    | apply Paper2.Unit4Shell.Poly.pow)

theorem cutClockN_poly (a b Δ : ℕ) :
    Paper2.Unit4Shell.Poly.PolyIn id (fun Y => cutClockN a b Δ (nbY Y) (PBY Y)) :=
  cutClockN_poly_gen a b Δ nbY PBY nbY_poly PBY_poly

theorem TotR_poly : Paper2.Unit4Shell.Poly.PolyIn id (TotR D B) := by
  have hA : Paper2.Unit4Shell.Poly.PolyIn id
      (fun Y : ℕ => CF D B * (2 * Y + 1 + 3 * Y + 1) ^ EF D B) := by
    repeat (first
      | exact Paper2.Unit4Shell.Poly.self
      | exact Paper2.Unit4Shell.Poly.const _
      | apply Paper2.Unit4Shell.Poly.add
      | apply Paper2.Unit4Shell.Poly.mul
      | apply Paper2.Unit4Shell.Poly.pow)
  have h2nb : Paper2.Unit4Shell.Poly.PolyIn id (fun Y : ℕ => 2 * nbY Y) :=
    Paper2.Unit4Shell.Poly.mul (Paper2.Unit4Shell.Poly.const 2) nbY_poly
  have hS : Paper2.Unit4Shell.Poly.PolyIn id (fun Y : ℕ =>
      Paper2.ABridge.stageCA B.degreeBound (sourceGap D B) B.degreeBound_pos
        (source_gap_pos D B) * Y) :=
    Paper2.Unit4Shell.Poly.mul (Paper2.Unit4Shell.Poly.const _) Paper2.Unit4Shell.Poly.self
  have hCC := cutClockN_poly (sourceGap D B).num.toNat (sourceGap D B).den B.degreeBound
  have h := Paper2.Unit4Shell.Poly.add (Paper2.Unit4Shell.Poly.add
      (Paper2.Unit4Shell.Poly.add hA h2nb) (Paper2.Unit4Shell.Poly.const 2))
    (Paper2.Unit4Shell.Poly.add (Paper2.Unit4Shell.Poly.add
      (Paper2.Unit4Shell.Poly.add hCC h2nb) (Paper2.Unit4Shell.Poly.const 2)) hS)
  exact h

theorem Tot_eq (Y : ℕ) : Tot D B Y = G Y + 2 * (2 * Y + 1 + 3 * Y) + 2 + TotR D B Y := rfl

theorem Tot_poly : Paper2.Unit4Shell.Poly.PolyIn id (Tot D B) := by
  have h1 : Paper2.Unit4Shell.Poly.PolyIn id (fun Y : ℕ => 2 * (2 * Y + 1 + 3 * Y)) := by
    repeat (first
      | exact Paper2.Unit4Shell.Poly.self
      | exact Paper2.Unit4Shell.Poly.const _
      | apply Paper2.Unit4Shell.Poly.add
      | apply Paper2.Unit4Shell.Poly.mul
      | apply Paper2.Unit4Shell.Poly.pow)
  have h := Paper2.Unit4Shell.Poly.add (Paper2.Unit4Shell.Poly.add
    (Paper2.Unit4Shell.Poly.add G_poly h1) (Paper2.Unit4Shell.Poly.const 2)) (TotR_poly D B)
  obtain ⟨C, E, hCE⟩ := h
  exact ⟨C, E, fun Y => by rw [Tot_eq]; exact hCE Y⟩

theorem G_mono {S S' : ℕ} (h : S ≤ S') : G S ≤ G S' := frontOf_mono h h h

/-- The graph-encoding length is at most `(n+2)^4 - 1` once `Δ ≤ n`. -/
theorem gl_le (Φ : ValidFormula) (hΔ : B.degreeBound ≤ (t10Graph D B Φ).vertices) :
    gl D B Φ + 1 ≤ ((t10Graph D B Φ).vertices + 2) ^ 4 := by
  have hu := EncodedGraph.encode_length_upper (t10Graph D B Φ) (t10Graph_valid D B Φ)
  have h2m := (Paper2.Unit4Shell.T10Size.t45_relations D B Φ).2.1
  unfold gl
  generalize (EncodedGraph.encode (t10Graph D B Φ)).length = e at hu ⊢
  generalize (t10Graph D B Φ).edges.length = m at hu h2m ⊢
  generalize (t10Graph D B Φ).vertices = n at hu h2m hΔ ⊢
  have h2 : 2 * m ≤ n * n := h2m.trans (Nat.mul_le_mul_right _ hΔ)
  have h3 : m * (4 * n + 4) ≤ n * n * (2 * n + 2) := by
    calc m * (4 * n + 4) = (2 * m) * (2 * n + 2) := by ring
      _ ≤ (n * n) * (2 * n + 2) := Nat.mul_le_mul_right _ h2
  have hid : (n + 2) ^ 4 = n + 3 + n * n * (2 * n + 2) +
      (n ^ 4 + 6 * n ^ 3 + 22 * n ^ 2 + 31 * n + 13) := by ring
  rw [hid]
  omega

/-- **The reduction stage is inside the D-A6 budget.** -/
theorem redTime2_budget (cs : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C d N₀ : ℕ, ∀ Φ : ValidFormula, Φ.val.clauses.length ≤ cs * Φ.val.variables →
      N₀ ≤ Φ.val.variables →
      redTime2 D B Φ ≤ C * ⌈(2 : ℝ) ^ (ε * Φ.val.variables)⌉₊ *
        ((EncodedCNF.encode Φ.val).length + 1) ^ d := by
  obtain ⟨C, E, hT⟩ := Tot_poly D B
  have hε2 : 0 < ε / 2 := by positivity
  set a : ℝ := ε / 2 / (E + 1) with ha
  have ha0 : 0 < a := by positivity
  have haE : a * E ≤ ε / 2 := by
    rw [ha, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨m₀, hm₀⟩ := Paper2.AEth.expLen_le_rpow a ha0
  obtain ⟨N₁, hN₁⟩ := Paper2.Unit4Shell.T24Runtime.subexponential (K0 D B * E)
    (D.sizeExponent + 2) (ε / 2) hε2
  refine ⟨C * 2 ^ E * 2 ^ E * 2 ^ E * 2, E,
    max (max m₀ N₁) (max (B.degreeBound * B.degreeBound + 1)
      (2 ^ (2 ^ (D.sizeExponent + 1) * Paper2.Unit4Shell.T10Size.t45C D B cs))), ?_⟩
  intro Φ hsp hN
  have hm0 : m₀ ≤ Φ.val.variables := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN1 : N₁ ≤ Φ.val.variables := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hΔN : B.degreeBound * B.degreeBound + 1 ≤ Φ.val.variables :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hbig : 2 ^ (2 ^ (D.sizeExponent + 1) * Paper2.Unit4Shell.T10Size.t45C D B cs) ≤
      Φ.val.variables := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  -- every lemma application first (then abbreviate)
  have hNX := SourceOriginalVariableCapture.original_n_le_input Φ.val
  have hkN : kOf Φ.val.variables ≤ Φ.val.variables := Nat.div_le_self _ _
  have hn1 : 1 ≤ (t10Graph D B Φ).vertices := t10_vertices_pos D B Φ
  have hsize := Paper2.Unit4Shell.T10Size.t45_shell_form D B cs Φ hsp hbig
  have hrel := Paper2.Unit4Shell.T10Size.t45_relations D B Φ
  have hNm := hrel.1
  have h2m := hrel.2.1
  have hΔpos := B.degreeBound_pos
  have hΔn : B.degreeBound ≤ (t10Graph D B Φ).vertices := by
    by_contra hc
    have hlt : (t10Graph D B Φ).vertices < B.degreeBound := Nat.lt_of_not_ge hc
    have h1 : B.degreeBound * (t10Graph D B Φ).vertices < B.degreeBound * B.degreeBound :=
      Nat.mul_lt_mul_of_pos_left hlt hΔpos
    omega
  have hgl := gl_le D B Φ hΔn
  have hsub := hN₁ Φ.val.variables hN1 (t10Graph D B Φ).vertices hn1 hsize
  have hUr : (Paper2.AEth.expLen Φ.val.variables : ℝ) ≤ (2 : ℝ) ^ (a * Φ.val.variables) :=
    hm₀ Φ.val.variables hm0
  have hU1 : 1 ≤ Paper2.AEth.expLen Φ.val.variables := one_le_expLen _
  have hGf := frontTime_le_G Φ.val
  have hLeq := cutLen_eq Φ.val
  set X := (EncodedCNF.encode Φ.val).length with hX
  set N := Φ.val.variables with hNdef
  set k := kOf N with hk
  set n := (t10Graph D B Φ).vertices with hn
  set U := Paper2.AEth.expLen N with hU
  set W := (n + 2) ^ (K0 D B * (k + 1)) with hW
  set Y := (X + 1) * (U + 1) * W with hY
  have hK4 : 4 ≤ K0 D B * (k + 1) := by
    have : 4 ≤ K0 D B := by unfold K0; omega
    calc 4 ≤ K0 D B := this
      _ = K0 D B * 1 := (mul_one _).symm
      _ ≤ K0 D B * (k + 1) := Nat.mul_le_mul_left _ (by omega)
  have hn2 : 1 ≤ n + 2 := by omega
  have hW4 : (n + 2) ^ 4 ≤ W := Nat.pow_le_pow_right hn2 hK4
  have hW1 : 1 ≤ W := Nat.one_le_pow _ _ (by omega)
  have hXU : (X + 1) * (U + 1) ≤ Y := Nat.le_mul_of_pos_right _ hW1
  have hXU0 : X + U + 1 ≤ (X + 1) * (U + 1) := by nlinarith
  have hXU1 : X + U + 1 ≤ Y := hXU0.trans hXU
  have hWY : W ≤ Y := Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) (by omega))
  have hglY : gl D B Φ ≤ Y := by
    have := hgl.trans hW4
    omega
  have hXY : X ≤ Y := by omega
  have hkY : k ≤ Y := by omega
  have hL : cutLen Φ.val ≤ 3 * Y := by rw [hLeq]; omega
  have hpk : (gl D B Φ + 1) ^ (Paper2.ABridge.ePk B.degreeBound (sourceGap D B) * (k + 1)) ≤ Y := by
    calc (gl D B Φ + 1) ^ (Paper2.ABridge.ePk B.degreeBound (sourceGap D B) * (k + 1))
        ≤ ((n + 2) ^ 4) ^ (Paper2.ABridge.ePk B.degreeBound (sourceGap D B) * (k + 1)) :=
          Nat.pow_le_pow_left hgl _
      _ = (n + 2) ^ (4 * Paper2.ABridge.ePk B.degreeBound (sourceGap D B) * (k + 1)) := by
          rw [← pow_mul]; ring_nf
      _ ≤ W := Nat.pow_le_pow_right hn2 (Nat.mul_le_mul_right _ (by unfold K0; omega))
      _ ≤ Y := hWY
  have hsE : (n + 2) ^ (Paper2.ABridge.stageEA B.degreeBound (sourceGap D B) B.degreeBound_pos
      (source_gap_pos D B) * (k + 1)) ≤ Y :=
    (Nat.pow_le_pow_right hn2 (Nat.mul_le_mul_right _ (by unfold K0; omega))).trans hWY
  -- domination by `Tot Y`
  have hA : 2 * X + 1 + cutLen Φ.val ≤ 2 * Y + 1 + 3 * Y := by omega
  have hnb : nbOf D B Φ ≤ nbY Y := by
    have hk' : kOf Φ.val.variables ≤ Y := hkY
    have hg' := hglY
    have hL' := hL
    unfold nbOf nbY
    omega
  have hPB : PBof D B Φ ≤ PBY Y := by
    unfold PBof PBY
    exact Nat.add_le_add (Nat.mul_le_mul_left _ hpk)
      (Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left 26 hL)
        (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ hL))) 7)
  have hG : frontTime Φ.val ≤ G Y := hGf.trans (G_mono (Nat.le_of_succ_le hXU1))
  have hCF : CF D B * (2 * X + 1 + cutLen Φ.val + 1) ^ EF D B ≤
      CF D B * (2 * Y + 1 + 3 * Y + 1) ^ EF D B :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hA 1) _)
  have hTot : redTime2 D B Φ ≤ Tot D B Y := by
    unfold redTime2 stageOf Tot
    exact add_le_add (add_le_add (add_le_add hG (Nat.mul_le_mul_left 2 hA)) le_rfl)
      (add_le_add (add_le_add (add_le_add hCF (Nat.mul_le_mul_left 2 hnb)) le_rfl)
        (add_le_add (add_le_add (add_le_add (cutClockN_mono hnb hPB)
          (Nat.mul_le_mul_left 2 hnb)) le_rfl) (Nat.mul_le_mul_left _ hsE)))
  -- polynomial in `Y`
  have hY1 : 1 ≤ Y := le_trans (by omega) hXU1
  have hYE : (Y + 1) ^ E ≤ 2 ^ E * Y ^ E := by
    calc (Y + 1) ^ E ≤ (2 * Y) ^ E := Nat.pow_le_pow_left (by omega) E
      _ = 2 ^ E * Y ^ E := mul_pow _ _ _
  have hUc : U ≤ ⌈(2 : ℝ) ^ (a * N)⌉₊ := by
    exact_mod_cast hUr.trans (Nat.le_ceil _)
  have hUE : U ^ E ≤ 2 ^ E * ⌈(2 : ℝ) ^ (ε / 2 * N)⌉₊ :=
    (Nat.pow_le_pow_left hUc E).trans
      (Paper2.AEth6.ceil_pow_le E ha0.le (Nat.cast_nonneg N) haE)
  have hU2 : (U + 1) ^ E ≤ 2 ^ E * U ^ E := by
    calc (U + 1) ^ E ≤ (2 * U) ^ E := Nat.pow_le_pow_left (by omega) E
      _ = 2 ^ E * U ^ E := mul_pow _ _ _
  have hWE : W ^ E = (n + 2) ^ (K0 D B * E * (k + 1)) := by
    rw [hW, ← pow_mul]; ring_nf
  set c1 := ⌈(2 : ℝ) ^ (ε / 2 * N)⌉₊ with hc1
  have hnat : redTime2 D B Φ ≤ C * 2 ^ E * 2 ^ E * 2 ^ E * (X + 1) ^ E * c1 * W ^ E := by
    calc redTime2 D B Φ ≤ Tot D B Y := hTot
      _ ≤ C * (Y + 1) ^ E := hT Y
      _ ≤ C * (2 ^ E * Y ^ E) := Nat.mul_le_mul_left _ hYE
      _ = C * 2 ^ E * ((X + 1) ^ E * (U + 1) ^ E * W ^ E) := by rw [hY, mul_pow, mul_pow]; ring
      _ ≤ C * 2 ^ E * ((X + 1) ^ E * (2 ^ E * (2 ^ E * c1)) * W ^ E) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
            (hU2.trans (Nat.mul_le_mul_left _ hUE))))
      _ = C * 2 ^ E * 2 ^ E * 2 ^ E * (X + 1) ^ E * c1 * W ^ E := by ring
  set wE := W ^ E with hwE
  set A := C * 2 ^ E * 2 ^ E * 2 ^ E * (X + 1) ^ E with hAdef
  set c2 := ⌈(2 : ℝ) ^ (ε * N)⌉₊ with hc2
  -- real step
  set r : ℝ := (2 : ℝ) ^ (ε / 2 * N) with hr
  have hr1 : 1 ≤ r := Real.one_le_rpow (by norm_num) (by positivity)
  have hc1r : (c1 : ℝ) ≤ 2 * r := by
    have := Nat.ceil_lt_add_one (show 0 ≤ r by positivity)
    rw [hc1]; linarith
  have hWr : (wE : ℝ) ≤ r := by
    rw [hWE]; exact_mod_cast hsub
  have hrr : r * r = (2 : ℝ) ^ (ε * N) := by
    rw [hr, ← Real.rpow_add (by norm_num)]; congr 1; ring
  have hceil : (2 : ℝ) ^ (ε * N) ≤ (c2 : ℝ) := Nat.le_ceil _
  have hprod : (c1 : ℝ) * (wE : ℝ) ≤ 2 * (c2 : ℝ) := by
    have h0 : (0 : ℝ) ≤ (wE : ℝ) := Nat.cast_nonneg _
    have h1 : (c1 : ℝ) * (wE : ℝ) ≤ (2 * r) * r := mul_le_mul hc1r hWr h0 (by positivity)
    calc (c1 : ℝ) * (wE : ℝ) ≤ (2 * r) * r := h1
      _ = 2 * (r * r) := by ring
      _ = 2 * (2 : ℝ) ^ (ε * N) := by rw [hrr]
      _ ≤ 2 * (c2 : ℝ) := by linarith
  have hreal : (redTime2 D B Φ : ℝ) ≤ (A : ℝ) * (2 * (c2 : ℝ)) := by
    have h1 : (redTime2 D B Φ : ℝ) ≤ ((A * c1 * wE : ℕ) : ℝ) := by exact_mod_cast hnat
    have h2 : ((A * c1 * wE : ℕ) : ℝ) = (A : ℝ) * ((c1 : ℝ) * (wE : ℝ)) := by
      push_cast; ring
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg _))
  have hgoal : redTime2 D B Φ ≤ A * (2 * c2) := by exact_mod_cast hreal
  calc redTime2 D B Φ ≤ A * (2 * c2) := hgoal
    _ = C * 2 ^ E * 2 ^ E * 2 ^ E * 2 * c2 * (X + 1) ^ E := by rw [hAdef]; ring

end Paper2.AEth3

#print axioms Paper2.AEth3.Tot_poly
#print axioms Paper2.AEth3.gl_le
#print axioms Paper2.AEth3.redTime2_budget
