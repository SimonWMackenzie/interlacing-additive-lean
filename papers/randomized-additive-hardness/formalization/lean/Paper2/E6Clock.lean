import Paper2.E6RedBudget3
import Paper2.E6Size
-- a-eth-owner-6 copy of frozen a-eth-owner-5/E5Clock.lean (SHA-256 0bc167795f379de3184089e0f2e64a51a13b345471e84f6c7d87a702efdbf7c1); import lines renamed only; the reference `Paper2.AEth2.ceil_pow_le` -> `Paper2.AEth6.ceil_pow_le`.

/-! a-eth-owner-5 copy of frozen `a-eth-owner-4/E4Clock.lean` (SHA-256 735337b6497710cb30554c9529c2d9856ab074a0195657a175fb479982ddee8b). Changes: import lines renamed E4Budget/E4Red/E4Hd/E4Size -> E5Budget/E5Red/E5Hd/E5Size; nothing else. -/

/-!
# Paper A (lock v12), lane `owner:a-eth-4`, segment 4 (partial, 4f for the deterministic part): the header machine
# runs within the D-A6 budget on sparse inputs

`hdTime4_budget`: for every density `K`, threshold `N₁` and `ε > 0` there are `C d N₀` such that for every sparse
valid `Φ` with `N ≥ N₀`, the clock of the ONE fixed machine `hdMachine4 D B K N₁` on `pair (encode Φ) t` (EVERY tape
`t`; the clock never mentions `t`) is at most `C · ⌈2^(εN)⌉ · (|encode Φ| + 1)^d`.

Method: a generic tail `budget_of_dom` (the argument of a-eth-owner-3 `redTime2_budget`, abstracted over the clock and
the dominating polynomial) and a domination `hdTime4 ≤ P4 Y`, `Y = (X+1)(expLen N+1)(n+2)^(Kx(kOf N+1))`,
`Kx = K0 + 164`, with `P4` one fixed polynomial (`PolyIn id`). No ledger row is closed. Nothing here is admitted.
-/

noncomputable section

namespace Paper2.AEth4

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics
open Paper2.AEth3 (MF CF EF GS cut0 nbOf PBof stageOf cutClockN_mono gl cutLen cutLen_eq cutLen_ge fOut
  fOut_length innerOf innerTime_eq innerOf_mono K0 nbY PBY TotR TotR_poly gl_le one_le_expLen)

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-- **Generic D-A6 tail.** A clock dominated by a fixed polynomial of
`Y = (X+1)(expLen N+1)(n+2)^(Kx(kOf N+1))` on sparse inputs is inside the D-A6 budget. -/
theorem budget_of_dom (cs Kx : ℕ) (T : ValidFormula → ℕ) (P : ℕ → ℕ)
    (hP : Paper2.Unit4Shell.Poly.PolyIn id P) (N₂ : ℕ)
    (hT : ∀ Φ : ValidFormula, Φ.val.clauses.length ≤ cs * Φ.val.variables →
      N₂ ≤ Φ.val.variables →
      T Φ ≤ P (((EncodedCNF.encode Φ.val).length + 1) * (Paper2.AEth.expLen Φ.val.variables + 1) *
        ((t10Graph D B Φ).vertices + 2) ^ (Kx * (kOf Φ.val.variables + 1))))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C d N₀ : ℕ, ∀ Φ : ValidFormula, Φ.val.clauses.length ≤ cs * Φ.val.variables →
      N₀ ≤ Φ.val.variables →
      T Φ ≤ C * ⌈(2 : ℝ) ^ (ε * Φ.val.variables)⌉₊ * ((EncodedCNF.encode Φ.val).length + 1) ^ d := by
  obtain ⟨C, E, hPC⟩ := hP
  have hε2 : 0 < ε / 2 := by positivity
  set a : ℝ := ε / 2 / (E + 1) with ha
  have ha0 : 0 < a := by positivity
  have haE : a * E ≤ ε / 2 := by
    rw [ha, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨m₀, hm₀⟩ := Paper2.AEth.expLen_le_rpow a ha0
  obtain ⟨N₁, hN₁⟩ := Paper2.Unit4Shell.T24Runtime.subexponential (Kx * E)
    (D.sizeExponent + 2) (ε / 2) hε2
  refine ⟨C * 2 ^ E * 2 ^ E * 2 ^ E * 2, E,
    max (max m₀ N₁) (max N₂
      (2 ^ (2 ^ (D.sizeExponent + 1) * Paper2.Unit4Shell.T10Size.t45C D B cs))), ?_⟩
  intro Φ hsp hN
  have hm0 : m₀ ≤ Φ.val.variables := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN1 : N₁ ≤ Φ.val.variables := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN2 : N₂ ≤ Φ.val.variables := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hbig : 2 ^ (2 ^ (D.sizeExponent + 1) * Paper2.Unit4Shell.T10Size.t45C D B cs) ≤
      Φ.val.variables := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hn1 : 1 ≤ (t10Graph D B Φ).vertices := t10_vertices_pos D B Φ
  have hsize := Paper2.Unit4Shell.T10Size.t45_shell_form D B cs Φ hsp hbig
  have hsub := hN₁ Φ.val.variables hN1 (t10Graph D B Φ).vertices hn1 hsize
  have hUr : (Paper2.AEth.expLen Φ.val.variables : ℝ) ≤ (2 : ℝ) ^ (a * Φ.val.variables) :=
    hm₀ Φ.val.variables hm0
  have hU1 : 1 ≤ Paper2.AEth.expLen Φ.val.variables := one_le_expLen _
  have hTY := hT Φ hsp hN2
  set X := (EncodedCNF.encode Φ.val).length with hX
  set N := Φ.val.variables with hNdef
  set k := kOf N with hk
  set n := (t10Graph D B Φ).vertices with hn
  set U := Paper2.AEth.expLen N with hU
  set W := (n + 2) ^ (Kx * (k + 1)) with hW
  set Y := (X + 1) * (U + 1) * W with hY
  have hn2 : 1 ≤ n + 2 := by omega
  have hW1 : 1 ≤ W := Nat.one_le_pow _ _ (by omega)
  have hY1 : 1 ≤ Y := Nat.one_le_iff_ne_zero.mpr (by positivity)
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
  have hWE : W ^ E = (n + 2) ^ (Kx * E * (k + 1)) := by
    rw [hW, ← pow_mul]; ring_nf
  set c1 := ⌈(2 : ℝ) ^ (ε / 2 * N)⌉₊ with hc1
  have hnat : T Φ ≤ C * 2 ^ E * 2 ^ E * 2 ^ E * (X + 1) ^ E * c1 * W ^ E := by
    calc T Φ ≤ P Y := hTY
      _ ≤ C * (Y + 1) ^ E := hPC Y
      _ ≤ C * (2 ^ E * Y ^ E) := Nat.mul_le_mul_left _ hYE
      _ = C * 2 ^ E * ((X + 1) ^ E * (U + 1) ^ E * W ^ E) := by rw [hY, mul_pow, mul_pow]; ring
      _ ≤ C * 2 ^ E * ((X + 1) ^ E * (2 ^ E * (2 ^ E * c1)) * W ^ E) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
            (hU2.trans (Nat.mul_le_mul_left _ hUE))))
      _ = C * 2 ^ E * 2 ^ E * 2 ^ E * (X + 1) ^ E * c1 * W ^ E := by ring
  set wE := W ^ E with hwE
  set A := C * 2 ^ E * 2 ^ E * 2 ^ E * (X + 1) ^ E with hAdef
  set c2 := ⌈(2 : ℝ) ^ (ε * N)⌉₊ with hc2
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
  have hreal : (T Φ : ℝ) ≤ (A : ℝ) * (2 * (c2 : ℝ)) := by
    have h1 : (T Φ : ℝ) ≤ ((A * c1 * wE : ℕ) : ℝ) := by exact_mod_cast hnat
    have h2 : ((A * c1 * wE : ℕ) : ℝ) = (A : ℝ) * ((c1 : ℝ) * (wE : ℝ)) := by
      push_cast; ring
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg _))
  have hgoal : T Φ ≤ A * (2 * c2) := by exact_mod_cast hreal
  calc T Φ ≤ A * (2 * c2) := hgoal
    _ = C * 2 ^ E * 2 ^ E * 2 ^ E * 2 * c2 * (X + 1) ^ E := by rw [hAdef]; ring

/-! ## Domination of the header clock -/

theorem cutTimeG_mono (c d pb : ℕ) {m T m' T' : ℕ} (hm : m ≤ m') (hT : T ≤ T') :
    Paper2.AEth2.Cut.cutTimeG c d pb m T ≤ Paper2.AEth2.Cut.cutTimeG c d pb m' T' := by
  unfold Paper2.AEth2.Cut.cutTimeG
  have h1 : m + T * pb ≤ m' + T' * pb := Nat.add_le_add hm (Nat.mul_le_mul_right _ hT)
  gcongr

/-- The front-cut part as ONE polynomial expression in `Y` (constants `pb`, `C3` generic). -/
def H4g (pb C3 Y : ℕ) : ℕ :=
  Paper2.AEth2.Cut.cutTimeG 1 1 pb Y (C3 * (Y + 1) ^ 3 + 2 * Y + 2 + innerOf 0 Y Y Y) +
    2 * (2 * (2 * Y) + 1 + 3 * Y) + 2 + (2 * (2 * Y) + (2 * Y + 3) + 2 * Y + 6)

set_option maxRecDepth 20000 in
theorem H4g_poly (pb C3 : ℕ) : Paper2.Unit4Shell.Poly.PolyIn id (H4g pb C3) := by
  unfold H4g Paper2.AEth2.Cut.cutTimeG innerOf
  repeat (first
    | exact Paper2.Unit4Shell.Poly.self
    | exact Paper2.Unit4Shell.Poly.const _
    | apply Paper2.Unit4Shell.Poly.add
    | apply Paper2.Unit4Shell.Poly.mul
    | apply Paper2.Unit4Shell.Poly.pow)

/-- ONE fixed polynomial dominating the header clock (the constants are fixed by `D B K N₁`). -/
def P4 (K N₁ Y : ℕ) : ℕ :=
  H4g (inner4 K N₁).pushBound (3000 + 30 * phiLen N₁) Y + 100 * (7 * Y + 2) + TotR D B Y +
    ((Paper2.Unit4Shell.KofFront.BK + 40) * (Y + 1) ^ 2 + 20 * Y + 20)

theorem P4_poly (K N₁ : ℕ) : Paper2.Unit4Shell.Poly.PolyIn id (P4 D B K N₁) := by
  have h1 := H4g_poly (inner4 K N₁).pushBound (3000 + 30 * phiLen N₁)
  have h2 : Paper2.Unit4Shell.Poly.PolyIn id (fun Y : ℕ => 100 * (7 * Y + 2)) := by
    repeat (first
      | exact Paper2.Unit4Shell.Poly.self
      | exact Paper2.Unit4Shell.Poly.const _
      | apply Paper2.Unit4Shell.Poly.add
      | apply Paper2.Unit4Shell.Poly.mul
      | apply Paper2.Unit4Shell.Poly.pow)
  have h3 := TotR_poly D B
  have h4 : Paper2.Unit4Shell.Poly.PolyIn id (fun Y : ℕ =>
      (Paper2.Unit4Shell.KofFront.BK + 40) * (Y + 1) ^ 2 + 20 * Y + 20) := by
    generalize Paper2.Unit4Shell.KofFront.BK + 40 = b
    repeat (first
      | exact Paper2.Unit4Shell.Poly.self
      | exact Paper2.Unit4Shell.Poly.const _
      | apply Paper2.Unit4Shell.Poly.add
      | apply Paper2.Unit4Shell.Poly.mul
      | apply Paper2.Unit4Shell.Poly.pow)
  exact Paper2.Unit4Shell.Poly.add (Paper2.Unit4Shell.Poly.add (Paper2.Unit4Shell.Poly.add h1 h2) h3) h4

/-- The header clock on EVERY word, split into its front, core and header parts. -/
theorem hdTime4_split (K N₁ : ℕ) (hN₁ : 1 ≤ N₁) (w : List Bool) :
    hdTime4 D B K N₁ hN₁ w ≤ frontTime4 K N₁ w +
      100 * ((2 * (EncodedCNF.encode (routedV K N₁ hN₁ w).val).length + 1 +
        cutLen (routedV K N₁ hN₁ w).val) + obLen D B (routedV K N₁ hN₁ w) +
        (EncodedCNF.encode (routedV K N₁ hN₁ w).val).length + 1) +
      mgTime D B (routedV K N₁ hN₁ w) + khTime D B (routedV K N₁ hN₁ w) := by
  dsimp only [hdTime4]
  omega

/-- The front-cut clock of a formula word routed to itself, bounded by `H4g` at any `Y ≥ X + U + 1`. -/
theorem frontTime4_le (K N₁ : ℕ) (Φ : EncodedCNF.Formula)
    (hr4 : routed4 K N₁ (EncodedCNF.encode Φ) = Φ) (Y : ℕ)
    (hXU : (EncodedCNF.encode Φ).length + Paper2.AEth.expLen Φ.variables + 1 ≤ Y)
    (hNX : Φ.variables ≤ (EncodedCNF.encode Φ).length) :
    frontTime4 K N₁ (EncodedCNF.encode Φ) ≤
      H4g (inner4 K N₁).pushBound (3000 + 30 * phiLen N₁) Y := by
  have hin := Paper2.AEth3.innerTime_eq Φ
  have hfo := fOut_length Φ
  have hLeq := cutLen_eq Φ
  have h0 : innerOf Paper2.AEth3.innerMachine.pushBound Y Y Y = innerOf 0 Y Y Y := by
    unfold innerOf
    simp only [Nat.zero_mul]
  have hI0 : innerOf Paper2.AEth3.innerMachine.pushBound (EncodedCNF.encode Φ).length Φ.variables
      (Paper2.AEth.expLen Φ.variables) ≤ innerOf 0 Y Y Y :=
    (innerOf_mono (by omega) (by omega) (by omega)).trans (le_of_eq h0)
  have hR3 : (3000 + 30 * phiLen N₁) * ((EncodedCNF.encode Φ).length + 1) ^ 3 ≤
      (3000 + 30 * phiLen N₁) * (Y + 1) ^ 3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
  have hT : route3Time K N₁ (EncodedCNF.encode Φ) +
      2 * (route3Out K N₁ (EncodedCNF.encode Φ)).length + 2 + Paper2.AEth3.innerTime Φ ≤
      (3000 + 30 * phiLen N₁) * (Y + 1) ^ 3 + 2 * Y + 2 + innerOf 0 Y Y Y := by
    rw [route3Out_eq, hr4, hin]
    unfold route3Time
    omega
  have hc := cutTimeG_mono 1 1 (inner4 K N₁).pushBound
    (show (EncodedCNF.encode Φ).length ≤ Y by omega) hT
  unfold frontTime4 H4g inner4Time
  rw [hr4]
  omega

theorem khTime_le (Φ : ValidFormula) (Y : ℕ) (hkY : kOf Φ.val.variables ≤ Y)
    (hNY : Φ.val.variables ≤ Y)
    (hbits : (Sel D B Φ).rows.bits.length + (Sel D B Φ).cols.bits.length +
      (Sel D B Φ).budget.bits.length ≤ Y) (hXY : (EncodedCNF.encode Φ.val).length ≤ Y)
    (hob : obLen D B Φ ≤ Y) :
    khTime D B Φ ≤ (Paper2.Unit4Shell.KofFront.BK + 40) * (Y + 1) ^ 2 + 20 * Y + 20 := by
  have hBK : Paper2.Unit4Shell.KofFront.BK * (Φ.val.variables + 1) ^ 2 ≤
      Paper2.Unit4Shell.KofFront.BK * (Y + 1) ^ 2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  have hprod : kOf Φ.val.variables * (2 * (((Sel D B Φ).budget.bits.length + 1) +
      kOf Φ.val.variables) + 4) ≤ 6 * (Y + 1) ^ 2 := by
    have h1 : kOf Φ.val.variables * (2 * (((Sel D B Φ).budget.bits.length + 1) +
        kOf Φ.val.variables) + 4) ≤ Y * (2 * ((Y + 1) + Y) + 4) := Nat.mul_le_mul hkY (by omega)
    have h2 : Y * (2 * ((Y + 1) + Y) + 4) ≤ 6 * (Y + 1) ^ 2 := by
      nlinarith only [Nat.zero_le (Y * Y), Nat.zero_le Y]
    exact h1.trans h2
  have hY2 : Y + 1 ≤ (Y + 1) ^ 2 := Nat.le_self_pow two_ne_zero _
  unfold khTime GrowHeader.clock
  rw [Nat.add_mul (Paper2.Unit4Shell.KofFront.BK) 40]
  omega

set_option maxHeartbeats 800000 in
/-- **Domination on sparse promise inputs.** -/
theorem hdTime4_dom (K N₁ : ℕ) (hN₁ : 1 ≤ N₁) :
    ∃ N₂ : ℕ, ∀ Φ : ValidFormula, Φ.val.clauses.length ≤ K * Φ.val.variables →
      N₂ ≤ Φ.val.variables →
      hdTime4 D B K N₁ hN₁ (EncodedCNF.encode Φ.val) ≤
        P4 D B K N₁ (((EncodedCNF.encode Φ.val).length + 1) *
          (Paper2.AEth.expLen Φ.val.variables + 1) *
          ((t10Graph D B Φ).vertices + 2) ^ ((K0 D B + 164) * (kOf Φ.val.variables + 1))) := by
  obtain ⟨Nf, hNf⟩ := Paper2.AEth3.inputBits_fit D B K
  refine ⟨max N₁ (max Nf (max (B.degreeBound * B.degreeBound + 1) (cut0 D B))), ?_⟩
  intro Φ hsp hN
  have hN1 : N₁ ≤ Φ.val.variables := le_trans (le_max_left _ _) hN
  have hNf' : Nf ≤ Φ.val.variables := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hΔN : B.degreeBound * B.degreeBound + 1 ≤ Φ.val.variables :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hN
  have hc0 : cut0 D B ≤ Φ.val.variables :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hN
  have hr4 : routed4 K N₁ (EncodedCNF.encode Φ.val) = Φ.val :=
    routed4_encode K N₁ Φ.val Φ.property hsp hN1
  have hV : routedV K N₁ hN₁ (EncodedCNF.encode Φ.val) = Φ := Subtype.ext hr4
  have hsplit := hdTime4_split D B K N₁ hN₁ (EncodedCNF.encode Φ.val)
  rw [hV] at hsplit
  obtain ⟨hk, hI⟩ := hNf Φ hsp hNf'
  have hge := cutLen_ge Φ.val
  have hI' : (Sel D B Φ).inputBits ≤ Paper2.AEth.expLen Φ.val.variables := hI
  obtain ⟨t', -, -⟩ := mg_outputs D B Φ hk hc0 (List.replicate (cutLen Φ.val) false)
    (by simp) (by simp only [List.length_replicate]; omega)
  have hobl := outputBits_length D B Φ t'
  have hobp := EncodedOutputSize.outputBits_length_le_poly (t10_vertices_pos D B Φ)
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
    B.degreeBound (sourceGap D B) (kOf Φ.val.variables) hk t'
  rw [hobl] at hobp
  have hNX := SourceOriginalVariableCapture.original_n_le_input Φ.val
  have hkN : kOf Φ.val.variables ≤ Φ.val.variables := Nat.div_le_self _ _
  have hrel := Paper2.Unit4Shell.T10Size.t45_relations D B Φ
  have hNm := hrel.1
  have hΔpos := B.degreeBound_pos
  have hΔn : B.degreeBound ≤ (t10Graph D B Φ).vertices := by
    by_contra hc
    have hlt : (t10Graph D B Φ).vertices < B.degreeBound := Nat.lt_of_not_ge hc
    have h1 : B.degreeBound * (t10Graph D B Φ).vertices < B.degreeBound * B.degreeBound :=
      Nat.mul_lt_mul_of_pos_left hlt hΔpos
    omega
  have hgl := gl_le D B Φ hΔn
  have hU1 : 1 ≤ Paper2.AEth.expLen Φ.val.variables := one_le_expLen _
  have hLeq := cutLen_eq Φ.val
  have hfo := fOut_length Φ.val
  have hin := Paper2.AEth3.innerTime_eq Φ.val
  clear hNf hI hN hobl hV
  have hbits2 : 2 * ((Sel D B Φ).rows.bits.length + (Sel D B Φ).cols.bits.length +
      (Sel D B Φ).budget.bits.length) ≤ obLen D B Φ := by unfold obLen; omega
  set X := (EncodedCNF.encode Φ.val).length with hX
  set N := Φ.val.variables with hNdef
  set k := kOf N with hk'
  set n := (t10Graph D B Φ).vertices with hn
  set U := Paper2.AEth.expLen N with hU
  set Kx := K0 D B + 164 with hKx
  set W := (n + 2) ^ (Kx * (k + 1)) with hW
  set Y := (X + 1) * (U + 1) * W with hY
  have hn2 : 1 ≤ n + 2 := by omega
  have hW1 : 1 ≤ W := Nat.one_le_pow _ _ (by omega)
  have hXU : (X + 1) * (U + 1) ≤ Y := Nat.le_mul_of_pos_right _ hW1
  have hXU0 : X + U + 1 ≤ (X + 1) * (U + 1) := by nlinarith
  have hXU1 : X + U + 1 ≤ Y := hXU0.trans hXU
  have hWY : W ≤ Y := Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) (by omega))
  have hK4 : 4 ≤ Kx * (k + 1) := by
    calc 4 ≤ Kx := by omega
      _ = Kx * 1 := (mul_one _).symm
      _ ≤ Kx * (k + 1) := Nat.mul_le_mul_left _ (by omega)
  have hW4 : (n + 2) ^ 4 ≤ W := Nat.pow_le_pow_right hn2 hK4
  have hglY : gl D B Φ ≤ Y := by
    have := hgl.trans hW4
    omega
  have hXY : X ≤ Y := by omega
  have hkY : k ≤ Y := by omega
  have hNY : N ≤ Y := by omega
  have hUY : U ≤ Y := by omega
  have hL : cutLen Φ.val ≤ 3 * Y := by rw [hLeq]; omega
  have hkYr : kOf Φ.val.variables ≤ Y := hkY
  have hNYr : Φ.val.variables ≤ Y := hNY
  have hpk : (gl D B Φ + 1) ^ (Paper2.ABridge.ePk B.degreeBound (sourceGap D B) * (k + 1)) ≤ Y := by
    calc (gl D B Φ + 1) ^ (Paper2.ABridge.ePk B.degreeBound (sourceGap D B) * (k + 1))
        ≤ ((n + 2) ^ 4) ^ (Paper2.ABridge.ePk B.degreeBound (sourceGap D B) * (k + 1)) :=
          Nat.pow_le_pow_left hgl _
      _ = (n + 2) ^ (4 * Paper2.ABridge.ePk B.degreeBound (sourceGap D B) * (k + 1)) := by
          rw [← pow_mul]; ring_nf
      _ ≤ W := Nat.pow_le_pow_right hn2 (Nat.mul_le_mul_right _ (by rw [hKx]; unfold K0; omega))
      _ ≤ Y := hWY
  have hsE : (n + 2) ^ (Paper2.ABridge.stageEA B.degreeBound (sourceGap D B) B.degreeBound_pos
      (source_gap_pos D B) * (k + 1)) ≤ Y :=
    (Nat.pow_le_pow_right hn2 (Nat.mul_le_mul_right _ (by rw [hKx]; unfold K0; omega))).trans hWY
  have hobY : obLen D B Φ ≤ Y := by
    have : (n + 2) ^ (164 * (k + 1)) ≤ W :=
      Nat.pow_le_pow_right hn2 (Nat.mul_le_mul_right _ (by omega))
    omega
  have hA : 2 * X + 1 + cutLen Φ.val ≤ 2 * Y + 1 + 3 * Y := by omega
  have hnb : nbOf D B Φ ≤ nbY Y := by
    unfold nbOf nbY
    omega
  have hPB : PBof D B Φ ≤ PBY Y := by
    unfold PBof PBY
    exact Nat.add_le_add (Nat.mul_le_mul_left _ hpk)
      (Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left 26 hL)
        (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ hL))) 7)
  have hCF : CF D B * (2 * X + 1 + cutLen Φ.val + 1) ^ EF D B ≤
      CF D B * (2 * Y + 1 + 3 * Y + 1) ^ EF D B :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hA 1) _)
  have hmg : mgTime D B Φ ≤ TotR D B Y := by
    unfold mgTime stageOf TotR
    exact add_le_add (add_le_add (add_le_add hCF (Nat.mul_le_mul_left 2 hnb)) le_rfl)
      (add_le_add (add_le_add (add_le_add (cutClockN_mono hnb hPB)
        (Nat.mul_le_mul_left 2 hnb)) le_rfl) (Nat.mul_le_mul_left _ hsE))
  have hbits : (Sel D B Φ).rows.bits.length + (Sel D B Φ).cols.bits.length +
      (Sel D B Φ).budget.bits.length ≤ Y := by omega
  have hXYr : (EncodedCNF.encode Φ.val).length ≤ Y := hXY
  have hkh := khTime_le D B Φ Y hkYr hNYr hbits hXYr hobY
  have hF : frontTime4 K N₁ (EncodedCNF.encode Φ.val) ≤
      H4g (inner4 K N₁).pushBound (3000 + 30 * phiLen N₁) Y :=
    frontTime4_le K N₁ Φ.val hr4 Y hXU1 hNX
  have hXL : 2 * X + 1 + cutLen Φ.val ≤ 5 * Y + 1 := by omega
  unfold P4
  clear * - hsplit hF hmg hkh hXL hobY hXY
  omega

/-- **The header machine is inside the D-A6 budget.** For every density `K`, threshold `N₁ ≥ 1` and
`ε > 0` there are `C d N₀` such that for every sparse valid `Φ` with `N ≥ N₀` the clock of the fixed machine
`hdMachine4 D B K N₁` on `pair (encode Φ) t` (every tape) is at most `C · ⌈2^(εN)⌉ · (|encode Φ| + 1)^d`. -/
theorem hdTime4_budget (K N₁ : ℕ) (hN₁ : 1 ≤ N₁) (ε : ℝ) (hε : 0 < ε) :
    ∃ C d N₀ : ℕ, ∀ Φ : ValidFormula, Φ.val.clauses.length ≤ K * Φ.val.variables →
      N₀ ≤ Φ.val.variables →
      hdTime4 D B K N₁ hN₁ (EncodedCNF.encode Φ.val) ≤
        C * ⌈(2 : ℝ) ^ (ε * Φ.val.variables)⌉₊ * ((EncodedCNF.encode Φ.val).length + 1) ^ d := by
  obtain ⟨N₂, hN₂⟩ := hdTime4_dom D B K N₁ hN₁
  exact budget_of_dom D B K (K0 D B + 164) (fun Φ => hdTime4 D B K N₁ hN₁ (EncodedCNF.encode Φ.val))
    (P4 D B K N₁) (P4_poly D B K N₁) N₂ hN₂ ε hε

end Paper2.AEth4

end

#print axioms Paper2.AEth4.budget_of_dom
#print axioms Paper2.AEth4.cutTimeG_mono
#print axioms Paper2.AEth4.H4g_poly
#print axioms Paper2.AEth4.P4_poly
#print axioms Paper2.AEth4.hdTime4_split
#print axioms Paper2.AEth4.hdTime4_dom
#print axioms Paper2.AEth4.hdTime4_budget
#print axioms Paper2.AEth4.frontTime4_le
#print axioms Paper2.AEth4.khTime_le
