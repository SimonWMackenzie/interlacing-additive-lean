import Paper2.ParameterizedCanonicalSource

/-! Unit 3, segment (1): the value identity for the public cover width
`Q = ParameterizedCanonicalSource.coverWidth n m L Δ γ`, read literally:

`coverWidth n m L Δ γ = SourceOverheadBounds.actualQ (V := Fin n) (E := Fin m) L γ Δ
  = SourceRationalScheduleScratch.publicQ L γ Δ = RestorationPublicQScratch.publicQ L deltaU
  = powTwoCeil ⌈(80 L : ℕ) / deltaU⌉₊`,
`deltaU = eta / (16 w')`, `w' = 2 ^ (ell L)^2`,
`eta = min (min 1 (γ m / (2 Δ n))) ((1/256) (γ/24)) / (65536 s)`.

For `γ = a / b` in lowest terms with `0 < γ`, `0 < Δ`, `0 < n`, `0 < m`:
`⌈(80 L) / deltaU⌉₊ = max (max C0 A2) A3` with the natural numbers
`C0 = L w s 2^24 5` (`80·16·65536 = 5·2^24`), `A2 = ⌈C0 (2bΔ) n / (a m)⌉`, `A3 = ⌈C0 (6144 b) / a⌉`,
written in the exact form the physical producer computes. -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

namespace Paper2.QProducer

open SourceProfileParameters

/-- `C0 = L w s 2^24 5`, in the multiplication order of the producer. -/
def C0 (L s w : ℕ) : ℕ := L * w * s * 2 ^ 24 * 5
/-- `A2 = (a m + C0 (2 b Δ) n - 1) / (a m)` (unary ceiling division as computed). -/
def A2 (a b Δ n m L s w : ℕ) : ℕ := (a * m + C0 L s w * (2 * b * Δ) * n - 1) / (a * m)
/-- `A3 = (a - 1 + C0 (6144 b)) / a` (unary ceiling division as computed). -/
def A3 (a b L s w : ℕ) : ℕ := (a - 1 + C0 L s w * (6144 * b)) / a
/-- The value the producer writes: `2 ^ clog₂ (max (max C0 A2) A3)`. -/
def qVal (a b Δ n m L s w : ℕ) : ℕ :=
  2 ^ Nat.clog 2 (max (max (C0 L s w) (A2 a b Δ n m L s w)) (A3 a b L s w))

theorem ceil_div_nat (N D : ℕ) (hD : 0 < D) :
    ⌈(N : ℚ) / (D : ℚ)⌉₊ = (D + N - 1) / D := by
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  apply eq_of_forall_ge_iff
  intro c
  rw [Nat.ceil_le, div_le_iff₀ hDq]
  have h1 : (D + N - 1) / D = N ⌈/⌉ D := by
    rw [Nat.ceilDiv_eq_add_pred_div, Nat.add_comm D N]
  rw [h1, ceilDiv_le_iff_le_mul hD]
  constructor
  · intro h
    have : ((N : ℕ) : ℚ) ≤ ((D * c : ℕ) : ℚ) := by push_cast; linarith
    exact_mod_cast this
  · intro h
    have : ((N : ℕ) : ℚ) ≤ ((D * c : ℕ) : ℚ) := by exact_mod_cast h
    push_cast at this; linarith

theorem ceil_max (x y : ℚ) : ⌈max x y⌉₊ = max ⌈x⌉₊ ⌈y⌉₊ := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, max_eq_right (Nat.ceil_mono h)]
  · rw [max_eq_left h, max_eq_left (Nat.ceil_mono h)]

theorem div_min (x a b : ℚ) (hx : 0 ≤ x) (ha : 0 < a) (hb : 0 < b) :
    x / min a b = max (x / a) (x / b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_left (div_le_div_of_nonneg_left hx ha h)]
  · rw [min_eq_right h, max_eq_right (div_le_div_of_nonneg_left hx hb h)]

theorem restorationWidth_eq (L : ℕ) :
    SourceRationalScheduleScratch.restorationWidth L =
      ParameterizedCanonicalSource.restorationWidth L := by
  unfold SourceRationalScheduleScratch.restorationWidth
    ParameterizedCanonicalSource.restorationWidth RestorationWidthScheduleScratch.width
    RestorationWidthScheduleScratch.depth
  rfl

/-- The ceiling of the literal threshold, for `γ = a / b`. -/
theorem ceil_threshold (n m L Δ a b s w : ℕ) (γ : ℚ) (hγab : γ = (a : ℚ) / (b : ℚ))
    (ha : 0 < a) (hb : 0 < b) (hΔ : 0 < Δ) (hn : 0 < n) (hm : 0 < m)
    (hs : width L = s) (hw : ParameterizedCanonicalSource.restorationWidth L = w) :
    ⌈RestorationPublicQScratch.threshold L
        (SourceRationalScheduleScratch.deltaU (V := Fin n) (E := Fin m) L γ Δ)⌉₊ =
      max (max (C0 L s w) (A2 a b Δ n m L s w)) (A3 a b L s w) := by
  have haQ : (0 : ℚ) < a := by exact_mod_cast ha
  have hbQ : (0 : ℚ) < b := by exact_mod_cast hb
  have hΔQ : (0 : ℚ) < Δ := by exact_mod_cast hΔ
  have hnQ : (0 : ℚ) < n := by exact_mod_cast hn
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
  have hγ : 0 < γ := by rw [hγab]; positivity
  obtain ⟨vt, hvt⟩ : ∃ vt : ℚ, vt = γ * (m : ℚ) / (2 * (Δ : ℚ) * (n : ℚ)) := ⟨_, rfl⟩
  obtain ⟨cw, hcw⟩ : ∃ cw : ℚ, cw = 1 / 256 * (γ / 24) := ⟨_, rfl⟩
  have hvt_pos : 0 < vt := by rw [hvt]; positivity
  have hcw_pos : 0 < cw := by rw [hcw]; positivity
  have hthr : RestorationPublicQScratch.threshold L
      (SourceRationalScheduleScratch.deltaU (V := Fin n) (E := Fin m) L γ Δ) =
      ((C0 L s w : ℕ) : ℚ) / min (min 1 vt) cw := by
    unfold RestorationPublicQScratch.threshold SourceRationalScheduleScratch.deltaU
      SourceRationalScheduleScratch.eta SourceRationalScheduleScratch.vertexTolerance
      SourceRationalScheduleScratch.witnessDensity
    rw [restorationWidth_eq, Fintype.card_fin, Fintype.card_fin, hs, hw, ← hvt, ← hcw,
      div_div_eq_mul_div, div_div_eq_mul_div]
    exact congrArg (· / min (min 1 vt) cw) (by unfold C0; push_cast; ring)
  rw [hthr, div_min _ _ _ (Nat.cast_nonneg _) (lt_min one_pos hvt_pos) hcw_pos,
    div_min _ _ _ (Nat.cast_nonneg _) one_pos hvt_pos, ceil_max, ceil_max, div_one,
    Nat.ceil_natCast]
  have h2 : ((C0 L s w : ℕ) : ℚ) / vt =
      ((C0 L s w * (2 * b * Δ) * n : ℕ) : ℚ) / ((a * m : ℕ) : ℚ) := by
    rw [hvt, hγab]
    push_cast
    field_simp
  have h3 : ((C0 L s w : ℕ) : ℚ) / cw = ((C0 L s w * (6144 * b) : ℕ) : ℚ) / ((a : ℕ) : ℚ) := by
    rw [hcw, hγab]
    push_cast
    field_simp
    ring
  rw [h2, h3, ceil_div_nat _ _ (Nat.mul_pos ha hm), ceil_div_nat _ _ ha]
  unfold A2 A3
  have e3 : a + C0 L s w * (6144 * b) - 1 = a - 1 + C0 L s w * (6144 * b) := by omega
  rw [e3]

/-- The literal value identity (`γ = a / b` in lowest terms: `a = γ.num.toNat`, `b = γ.den`). -/
theorem coverWidth_eq (n m L Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ) (hn : 0 < n)
    (hm : 0 < m) :
    ParameterizedCanonicalSource.coverWidth n m L Δ γ =
      qVal γ.num.toNat γ.den Δ n m L (width L) (ParameterizedCanonicalSource.restorationWidth L) := by
  have hnum : 0 < γ.num := Rat.num_pos.mpr hγ
  have haq : ((γ.num.toNat : ℕ) : ℚ) = (γ.num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hnum.le
  have ha : 0 < γ.num.toNat := by omega
  have hγab : γ = ((γ.num.toNat : ℕ) : ℚ) / ((γ.den : ℕ) : ℚ) := by
    rw [haq, Rat.num_div_den]
  unfold ParameterizedCanonicalSource.coverWidth SourceOverheadBounds.actualQ
    SourceRationalScheduleScratch.publicQ RestorationPublicQScratch.publicQ
    SourcePadding.powTwoCeil qVal
  rw [ceil_threshold n m L Δ γ.num.toNat γ.den (width L)
    (ParameterizedCanonicalSource.restorationWidth L) γ hγab ha γ.den_pos hΔ hn hm rfl rfl]

end Paper2.QProducer

#print axioms Paper2.QProducer.ceil_div_nat
#print axioms Paper2.QProducer.coverWidth_eq
