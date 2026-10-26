import Paper2.GeneratorPublicCap
import Paper2.RecursiveLabelCodec
import Paper2.FairBitCap
import Paper2.SourceRepetition
import Mathlib.Tactic

/-! Unit 3, clock bounds of the success branch, segment (1): every word length on
the loop bank at the public schedule is at most `2^(c*(K+1)*L)`, from the ADMITTED
schedule caps only (`GeneratorPublicCap.scheduled_scalars_le_publicCap`,
`GeneratorPublicCap.scheduled_serialized_length_le_two_pow`,
`RecursiveLabelCodecScratch.carrierCodecs_maxLen_le`, `labelStepCap_le_cube`,
`FairBitCap.scheduled_each_dimension_le`, the `GeneratorSize` size identities).
Pure arithmetic; no machine is defined here. -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

namespace Paper2.SuccessClock

open Paper2.GeneratorCode Paper2.GeneratorSource Paper2.GeneratorSerialization
  Paper2.GeneratorSize Paper2.RecursiveLabelCodecScratch Paper2.ParameterizedCanonicalSource

/-! ### Exponent calculus on `2^(a*T)` -/

theorem pw_mono {a b T : ℕ} (h : a ≤ b) : 2 ^ (a * T) ≤ 2 ^ (b * T) :=
  pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right _ h)

theorem pw_const {c T : ℕ} (hT : 1 ≤ T) : c ≤ 2 ^ (c * T) := by
  have h1 : c < 2 ^ c := Nat.lt_two_pow_self
  have h2 : 2 ^ c ≤ 2 ^ (c * T) := pow_le_pow_right₀ (by norm_num) (by nlinarith)
  omega

theorem pw_add {x y a b T : ℕ} (hT : 1 ≤ T) (hx : x ≤ 2 ^ (a * T)) (hy : y ≤ 2 ^ (b * T)) :
    x + y ≤ 2 ^ ((a + b + 1) * T) := by
  have ha : 2 ^ (a * T) ≤ 2 ^ ((a + b) * T) := pw_mono (by omega)
  have hb : 2 ^ (b * T) ≤ 2 ^ ((a + b) * T) := pw_mono (by omega)
  have h2 : 2 * 2 ^ ((a + b) * T) ≤ 2 ^ ((a + b + 1) * T) := by
    rw [show (a + b + 1) * T = (a + b) * T + T by ring, pow_add]
    have : 2 ≤ 2 ^ T := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ T := pow_le_pow_right₀ (by norm_num) hT
    nlinarith [Nat.one_le_two_pow (n := (a + b) * T)]
  omega

theorem pw_mul {x y a b T : ℕ} (hx : x ≤ 2 ^ (a * T)) (hy : y ≤ 2 ^ (b * T)) :
    x * y ≤ 2 ^ ((a + b) * T) := by
  calc x * y ≤ 2 ^ (a * T) * 2 ^ (b * T) := Nat.mul_le_mul hx hy
    _ = 2 ^ ((a + b) * T) := by rw [← pow_add]; ring_nf

/-! ### Scalar caps -/

/-- Every public scalar of the schedule, the edge count and the repetition factor are at
most `2^(7L)`. -/
theorem scalar_caps {n m : ℕ} [NeZero n] (L Δ : ℕ) (γ : ℚ)
    (hc : Paper2.CompletePublicScheduleScratch.Checks (V := Fin n) (E := Fin m) L Δ γ) :
    n ≤ 2 ^ (7 * L) ∧ LookupSeed.width L ≤ 2 ^ (7 * L) ∧
      SourceProfileParameters.width L ≤ 2 ^ (7 * L) ∧
      SourceProfileParameters.width L - 2 ≤ 2 ^ (7 * L) ∧
      SourceProfileParameters.outerWidth L ≤ 2 ^ (7 * L) ∧
      restorationWidth L ≤ 2 ^ (7 * L) ∧ coverWidth n m L Δ γ ≤ 2 ^ (7 * L) ∧
      m ≤ 2 ^ (7 * L) ∧ 16 ≤ L := by
  obtain ⟨_, hn, hp, hs, hq₁, hq₂, hw, hQ⟩ := GeneratorPublicCap.scheduled_scalars_le_publicCap L Δ γ hc
  have hL : 16 ≤ L := by
    rcases hc with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hL, _⟩
    exact hL
  have hadm : SourceRepetitionScratch.coordinateAdmissible L (Fin m) := hc.1
  unfold SourceRepetitionScratch.coordinateAdmissible at hadm
  have h1 := SourcePadding.le_powTwoCeil (12 * SourceProfileParameters.width L * Fintype.card (Fin m))
  simp only [Fintype.card_fin] at h1 hadm
  have hs1 : 1 ≤ SourceProfileParameters.width L := by
    have := SourceProfileParameters.width_admissible L
    omega
  have hm : m ≤ SourceProfileParameters.outerWidth L := by
    have : m ≤ 12 * SourceProfileParameters.width L * m := by nlinarith
    omega
  exact ⟨hn, hp, hs, hq₁, hq₂, hw, hQ, hm.trans hq₂, hL⟩

/-- The repetition factor `r` with `q₂ = sourceQ0 * r` is at most `q₂`. -/
theorem rep_le_outer {s m q₂ r : ℕ} (hq₂ : 0 < q₂)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin m) * r) : r ≤ q₂ := by
  rcases Nat.eq_zero_or_pos (SourceItems.sourceQ0 (Fin (4 * s)) (Fin m)) with h0 | h0
  · rw [h0] at hq; omega
  · rw [hq]; exact Nat.le_mul_of_pos_left r h0

/-! ### Code caps -/

/-- The serialized level-`k` codes, for every level `k ≤ K + 1`. -/
theorem code_cap {n m : ℕ} [NeZero n] (L Δ : ℕ) (γ : ℚ)
    (hc : Paper2.CompletePublicScheduleScratch.Checks (V := Fin n) (E := Fin m) L Δ γ)
    (K k : ℕ) (hk : k ≤ K + 1) :
    codeSize (seedRecursiveCodes n (LookupSeed.width L) (SourceProfileParameters.width L)
        (SourceProfileParameters.width L - 2) (SourceProfileParameters.outerWidth L)
        (restorationWidth L) (coverWidth n m L Δ γ) k).1 +
      codeSize (seedRecursiveCodes n (LookupSeed.width L) (SourceProfileParameters.width L)
        (SourceProfileParameters.width L - 2) (SourceProfileParameters.outerWidth L)
        (restorationWidth L) (coverWidth n m L Δ γ) k).2 + 1 ≤
      2 ^ (288 * ((K + 1) * L)) := by
  have h := GeneratorPublicCap.scheduled_serialized_length_le_two_pow L Δ γ k hc
  dsimp only at h
  simp only [encodeCode_length] at h
  have hm : 2 ^ (144 * (k + 1) * L) ≤ 2 ^ (288 * ((K + 1) * L)) :=
    pow_le_pow_right₀ (by norm_num) (by nlinarith)
  exact h.trans hm

/-- Codes derived from the level-`k` codes are bounded by the level-`k+1` codes. -/
theorem derived_le {n s q₁ q₂ w Q : ℕ} (hw : 1 ≤ w) (hQ : 1 ≤ Q) (row₀ col₀ : Code) (k : ℕ) :
    let c := recursiveCodes n s q₁ q₂ w Q row₀ col₀ k
    let c' := recursiveCodes n s q₁ q₂ w Q row₀ col₀ (k + 1)
    codeSize (.append (.ticket w) (taggedCode q₁ q₂ s c.2)) ≤ codeSize c'.1 ∧
    codeSize (taggedCode q₁ q₂ s c.2) ≤ codeSize c'.1 ∧
    codeSize (outerCode q₁ q₂ s c.2) ≤ codeSize c'.1 ∧
    codeSize (copies (s + 1) c.2) ≤ codeSize c'.1 ∧
    codeSize c.2 ≤ codeSize c'.1 ∧
    codeSize (graphRowsCode (V := Fin n) q₁ q₂ s c.1) ≤ codeSize c'.2 ∧
    codeSize c.1 ≤ codeSize c'.2 := by
  intro c c'
  have hr := recursive_row_size n s q₁ q₂ w Q row₀ col₀ k
  have hcl := recursive_col_size n s q₁ q₂ w Q row₀ col₀ k
  have ht := tagged_size q₁ q₂ s c.2
  have ho := outer_size q₁ q₂ s c.2
  have hcp := copies_size (s + 1) c.2
  have hg := graphRows_size n q₁ q₂ s c.1
  have hap : codeSize (.append (.ticket w) (taggedCode q₁ q₂ s c.2)) =
      3 + (3 + (w + 1)) + codeSize (taggedCode q₁ q₂ s c.2) := rfl
  change codeSize c'.1 = _ at hr
  change codeSize c'.2 = _ at hcl
  have e1 : codeSize (.append (.ticket w) (taggedCode q₁ q₂ s c.2)) ≤ codeSize c'.1 := by
    rw [hap, hr]; nlinarith
  have e3 : codeSize (outerCode q₁ q₂ s c.2) ≤ codeSize (taggedCode q₁ q₂ s c.2) := by
    rw [ht]; omega
  have e4 : codeSize (copies (s + 1) c.2) ≤ codeSize (outerCode q₁ q₂ s c.2) := by
    rw [hcp, ho]; nlinarith
  have e5 : codeSize c.2 ≤ codeSize (copies (s + 1) c.2) := by
    rw [hcp]; nlinarith
  have e6 : codeSize (graphRowsCode (V := Fin n) q₁ q₂ s c.1) ≤ codeSize c'.2 := by
    rw [hcl]; nlinarith
  have e7 : codeSize c.1 ≤ codeSize (graphRowsCode (V := Fin n) q₁ q₂ s c.1) := by
    rw [hg]; omega
  refine ⟨e1, by omega, by omega, by omega, by omega, e6, by omega⟩

/-- The level-`k` derived codes read by one level step (`k + 1 ≤ K`), at the schedule. -/
theorem derived_cap {n m : ℕ} [NeZero n] (L Δ : ℕ) (γ : ℚ)
    (hc : Paper2.CompletePublicScheduleScratch.Checks (V := Fin n) (E := Fin m) L Δ γ)
    (K k : ℕ) (hk : k ≤ K) :
    let s := SourceProfileParameters.width L
    let q₁ := SourceProfileParameters.width L - 2
    let q₂ := SourceProfileParameters.outerWidth L
    let w := restorationWidth L
    let Q := coverWidth n m L Δ γ
    let c := seedRecursiveCodes n (LookupSeed.width L) s q₁ q₂ w Q k
    let B := 2 ^ (288 * ((K + 1) * L))
    codeSize (.append (.ticket w) (taggedCode q₁ q₂ s c.2)) ≤ B ∧
    codeSize (taggedCode q₁ q₂ s c.2) ≤ B ∧
    codeSize (outerCode q₁ q₂ s c.2) ≤ B ∧
    codeSize (copies (s + 1) c.2) ≤ B ∧
    codeSize (graphRowsCode (V := Fin n) q₁ q₂ s c.1) ≤ B ∧
    codeSize (.append (.ticket q₁) c.1) ≤ B := by
  intro s q₁ q₂ w Q c B
  have hw : 1 ≤ w := by
    unfold w restorationWidth RestorationWidthScheduleScratch.width; exact Nat.one_le_two_pow
  have hQ : 1 ≤ Q := by
    unfold Q
    rw [show coverWidth n m L Δ γ = 2 ^ coverDepth n m L Δ γ from
      Paper2.SourceOverheadBounds.actualQ_pow (V := Fin n) (E := Fin m) L γ Δ]
    exact Nat.one_le_two_pow
  obtain ⟨e1, e2, e3, e4, -, e6, -⟩ := derived_le (n := n) (s := s) (q₁ := q₁) (q₂ := q₂)
    hw hQ (copies (LookupSeed.width L) .bit) (.ticket (LookupSeed.width L)) k
  have hk1 := code_cap L Δ γ hc K (k + 1) (by omega)
  have hk0 := code_cap L Δ γ hc K k (by omega)
  obtain ⟨-, -, -, hq₁, -, -, -, -, hL⟩ := scalar_caps L Δ γ hc
  have hq1B : q₁ ≤ 2 ^ (7 * L) := hq₁
  have h7 : 2 ^ (7 * L) ≤ 2 ^ (287 * ((K + 1) * L)) :=
    pow_le_pow_right₀ (by norm_num) (by nlinarith)
  have hB2 : 2 * 2 ^ (287 * ((K + 1) * L)) ≤ B := by
    unfold B
    rw [show 288 * ((K + 1) * L) = 287 * ((K + 1) * L) + (K + 1) * L by ring, pow_add]
    have : 2 ≤ 2 ^ ((K + 1) * L) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ ((K + 1) * L) := pow_le_pow_right₀ (by norm_num) (by nlinarith)
    nlinarith [Nat.one_le_two_pow (n := 287 * ((K + 1) * L))]
  change codeSize c.1 + codeSize c.2 + 1 ≤ B at hk0
  let c' := seedRecursiveCodes n (LookupSeed.width L) s q₁ q₂ w Q (k + 1)
  change codeSize c'.1 + codeSize c'.2 + 1 ≤ B at hk1
  change codeSize (Code.append (.ticket w) (taggedCode q₁ q₂ s c.2)) ≤ codeSize c'.1 at e1
  change codeSize (taggedCode q₁ q₂ s c.2) ≤ codeSize c'.1 at e2
  change codeSize (outerCode q₁ q₂ s c.2) ≤ codeSize c'.1 at e3
  change codeSize (copies (s + 1) c.2) ≤ codeSize c'.1 at e4
  change codeSize (graphRowsCode (V := Fin n) q₁ q₂ s c.1) ≤ codeSize c'.2 at e6
  have hap : codeSize (.append (.ticket q₁) c.1) = 3 + (3 + (q₁ + 1)) + codeSize c.1 := rfl
  refine ⟨by omega, by omega, by omega, by omega, by omega, ?_⟩
  rw [hap]
  have hc1 : codeSize c.1 ≤ 2 ^ (287 * ((K + 1) * L)) := by
    have h := GeneratorPublicCap.scheduled_serialized_length_le_two_pow L Δ γ k hc
    dsimp only at h
    simp only [encodeCode_length] at h
    have : 2 ^ (144 * (k + 1) * L) ≤ 2 ^ (287 * ((K + 1) * L)) :=
      pow_le_pow_right₀ (by norm_num) (by nlinarith)
    change codeSize c.1 + codeSize c.2 + 1 ≤ 2 ^ (144 * (k + 1) * L) at h
    omega
  have ha : 2 ^ (7 * L) + 7 ≤ 2 ^ (287 * ((K + 1) * L)) := by
    have h8 : 2 ^ (7 * L) + 7 ≤ 2 ^ (8 * L) := by
      rw [show 8 * L = 7 * L + L by ring, pow_add]
      have : 16 ≤ 2 ^ L := by
        calc 16 = 2 ^ 4 := by norm_num
          _ ≤ 2 ^ L := pow_le_pow_right₀ (by norm_num) (by omega)
      nlinarith [Nat.one_le_two_pow (n := 7 * L)]
    exact h8.trans (pow_le_pow_right₀ (by norm_num) (by nlinarith))
  omega

/-! ### Label caps (no `n ≤ 2^L` premise) -/

/-- The level-`k` label codecs at the schedule: `maxLen ≤ 2^(26*(k+1)*L)`, from the scalar cap
`2^(7L)` (the production `scheduled_codec_maxLen_le` additionally assumes `n ≤ 2^L`). -/
theorem label_maxLen_cap {n m : ℕ} [NeZero n] (L Δ : ℕ) (γ : ℚ)
    (hc : Paper2.CompletePublicScheduleScratch.Checks (V := Fin n) (E := Fin m) L Δ γ) (k : ℕ) :
    (defaultCarrierCodecs n (LookupSeed.width L) (SourceProfileParameters.width L)
        (SourceProfileParameters.width L - 2) (SourceProfileParameters.outerWidth L)
        (restorationWidth L) (coverWidth n m L Δ γ) k).1.maxLen ≤ 2 ^ (26 * (k + 1) * L) ∧
    (defaultCarrierCodecs n (LookupSeed.width L) (SourceProfileParameters.width L)
        (SourceProfileParameters.width L - 2) (SourceProfileParameters.outerWidth L)
        (restorationWidth L) (coverWidth n m L Δ γ) k).2.maxLen ≤ 2 ^ (26 * (k + 1) * L) := by
  obtain ⟨hn, hp, hs, hq₁, hq₂, hw, hQ, -, hL⟩ := scalar_caps L Δ γ hc
  let B := 2 ^ (7 * L)
  let p := LookupSeed.width L
  let s := SourceProfileParameters.width L
  let ci := defaultItemCodec n s
  let M := max 1 (max p (max p ci.maxLen))
  let T := labelStepCap s (s - 2) (SourceProfileParameters.outerWidth L) (restorationWidth L)
    (coverWidth n m L Δ γ)
  have hB : 1 ≤ B := Nat.one_le_two_pow
  have hci : ci.maxLen ≤ 6 * B := by
    rw [show ci.maxLen = 4 * s + (1 + max n (s - 3)) from default_item_maxLen n s]
    have : max n (s - 3) ≤ B := max_le hn (le_trans (Nat.sub_le _ _) hs)
    change s ≤ B at hs
    omega
  have hM : M ≤ 8 * B := by
    have hp' : p ≤ B := hp
    dsimp only [M]; omega
  have hT : T ≤ 32 * B ^ 3 := labelStepCap_le_cube _ _ _ _ _ B hB hs hq₁ hq₂ hw hQ
  have hMpow : M ≤ 2 ^ (8 * L) := by
    calc
      M ≤ 8 * B := hM
      _ = 2 ^ (3 + 7 * L) := by norm_num [B, pow_add]
      _ ≤ 2 ^ (8 * L) := pow_le_pow_right₀ (by omega) (by omega)
  have hTpow : T ≤ 2 ^ (26 * L) := by
    calc
      T ≤ 32 * B ^ 3 := hT
      _ = 2 ^ (5 + 21 * L) := by
        have he : 21 * L = (7 * L) * 3 := by omega
        rw [he, pow_add, pow_mul]
        norm_num [B]
      _ ≤ 2 ^ (26 * L) := pow_le_pow_right₀ (by omega) (by omega)
  have hb := carrierCodecs_maxLen_le s (s - 2) (SourceProfileParameters.outerWidth L)
    (restorationWidth L) (coverWidth n m L Δ γ) (piCodec boolCodec p) (finCodec p) ci k
  simp only [piCodec_maxLen, boolCodec, mul_one] at hb
  have htarget : M * T ^ k ≤ 2 ^ (26 * (k + 1) * L) := by
    have hpow := Nat.pow_le_pow_left hTpow k
    calc
      M * T ^ k ≤ 2 ^ (8 * L) * (2 ^ (26 * L)) ^ k := Nat.mul_le_mul hMpow hpow
      _ = 2 ^ ((8 + 26 * k) * L) := by rw [← pow_mul, ← pow_add]; congr 1; ring
      _ ≤ 2 ^ (26 * (k + 1) * L) := by
        have he : 8 + 26 * k ≤ 26 * (k + 1) := by omega
        exact pow_le_pow_right₀ (by omega) (Nat.mul_le_mul_right L he)
  exact ⟨hb.1.trans htarget, hb.2.trans htarget⟩

/-- Label caps at every level `k ≤ K`, in the common exponent `26*T`, `T = (K+1)*L`. -/
theorem label_cap {n m : ℕ} [NeZero n] (L Δ : ℕ) (γ : ℚ)
    (hc : Paper2.CompletePublicScheduleScratch.Checks (V := Fin n) (E := Fin m) L Δ γ)
    (K k : ℕ) (hk : k ≤ K) :
    (defaultCarrierCodecs n (LookupSeed.width L) (SourceProfileParameters.width L)
        (SourceProfileParameters.width L - 2) (SourceProfileParameters.outerWidth L)
        (restorationWidth L) (coverWidth n m L Δ γ) k).1.maxLen ≤ 2 ^ (26 * ((K + 1) * L)) ∧
    (defaultCarrierCodecs n (LookupSeed.width L) (SourceProfileParameters.width L)
        (SourceProfileParameters.width L - 2) (SourceProfileParameters.outerWidth L)
        (restorationWidth L) (coverWidth n m L Δ γ) k).2.maxLen ≤ 2 ^ (26 * ((K + 1) * L)) := by
  have h := label_maxLen_cap L Δ γ hc k
  have hm : 2 ^ (26 * (k + 1) * L) ≤ 2 ^ (26 * ((K + 1) * L)) :=
    pow_le_pow_right₀ (by norm_num) (by nlinarith)
  exact ⟨h.1.trans hm, h.2.trans hm⟩

/-! ### Lists of encoded words -/

/-- A list of `N` words of one codec: total length at most `N * maxLen`. -/
theorem ofFn_flatten_le {α : Type} (ca : PrefixCodec α) (N : ℕ) (f : Fin N → α) :
    (List.ofFn (fun j => ca.encode (f j))).flatten.length ≤ N * ca.maxLen := by
  rw [List.length_flatten]
  have h : ∀ l ∈ (List.ofFn (fun j => ca.encode (f j))).map List.length, l ≤ ca.maxLen := by
    intro l hl
    simp only [List.map_ofFn, List.mem_ofFn] at hl
    obtain ⟨j, rfl⟩ := hl
    exact ca.length_le (f j)
  have := List.sum_le_card_nsmul _ _ h
  simpa [List.length_ofFn] using this

/-- The sampled rectangle's two sides, at the common exponent `29*T`. -/
theorem dims_cap {n m : ℕ} [NeZero n] (L Δ : ℕ) (γ : ℚ)
    (hc : Paper2.CompletePublicScheduleScratch.Checks (V := Fin n) (E := Fin m) L Δ γ) (k : ℕ) :
    SourceRecursiveNoSampling.sourceRows L (restorationDepth L) (coverDepth n m L Δ γ) k ≤
        2 ^ (29 * ((k + 1) * L)) ∧
    SourceRecursiveNoSampling.sourceCols L (restorationDepth L) (coverDepth n m L Δ γ) k ≤
        2 ^ (29 * ((k + 1) * L)) := by
  have h := FairBitCap.scheduled_each_dimension_le L Δ γ hc k
  rw [show 29 * ((k + 1) * L) = 29 * (k + 1) * L by ring]
  exact h

end Paper2.SuccessClock

#print axioms Paper2.SuccessClock.scalar_caps
#print axioms Paper2.SuccessClock.code_cap
#print axioms Paper2.SuccessClock.derived_cap
#print axioms Paper2.SuccessClock.label_maxLen_cap
#print axioms Paper2.SuccessClock.label_cap
#print axioms Paper2.SuccessClock.ofFn_flatten_le
#print axioms Paper2.SuccessClock.dims_cap
