import CurrentAdditive.RankCountV37

/-! Private current-source v38 adaptation. The v37 module is preserved. -/

namespace CurrentAdditive.V38RankCount

open CurrentAdditive.V37RankCount Paper2 Paper2.RankLeaves Matrix Workspace.Types.Protocol

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The two leaf-output row families, placed in one Boolean matrix. -/
def stacked (F : X → Y → Bool) : Bool × X → Y → Bool :=
  fun p y => if p.1 then !(F p.2 y) else F p.2 y

/-- The combined row space lies in the original row space plus constants. -/
theorem stacked_rank_le (F : X → Y → Bool) :
    (realMatrix (stacked F)).rank ≤ (realMatrix F).rank + 1 := by
  classical
  let V : Submodule ℝ (Y → ℝ) :=
    Submodule.span ℝ (Set.range (realMatrix F).row)
  let L : (V × ℝ) →ₗ[ℝ] (Y → ℝ) :=
    { toFun := fun z y => z.1.val y + z.2
      map_add' := by
        intro a b
        funext y
        simp [add_assoc, add_left_comm, add_comm]
      map_smul' := by
        intro a b
        funext y
        simp [mul_add] }
  have hrows : Submodule.span ℝ (Set.range (realMatrix (stacked F)).row) ≤
      LinearMap.range L := by
    rw [Submodule.span_le]
    rintro v ⟨⟨b, x⟩, rfl⟩
    let row : V := ⟨(realMatrix F).row x, Submodule.subset_span ⟨x, rfl⟩⟩
    cases b with
    | false =>
        refine ⟨(row, 0), ?_⟩
        funext y
        simp [L, row, Matrix.row, realMatrix, stacked]
    | true =>
        refine ⟨(-row, 1), ?_⟩
        funext y
        cases hf : F x y <;> simp [L, row, Matrix.row, realMatrix, stacked, hf]
  calc
    (realMatrix (stacked F)).rank =
        Module.finrank ℝ (Submodule.span ℝ (Set.range (realMatrix (stacked F)).row)) :=
      Matrix.rank_eq_finrank_span_row _
    _ ≤ Module.finrank ℝ (LinearMap.range L) := Submodule.finrank_mono hrows
    _ ≤ Module.finrank ℝ (V × ℝ) := LinearMap.finrank_range_le L
    _ = (realMatrix F).rank + 1 := by
      rw [Module.finrank_prod, ← Matrix.rank_eq_finrank_span_row]
      simp

noncomputable def signedRows (U : Finset X) (b : Bool) : Finset (Bool × X) := by
  classical
  exact U.image fun x => (b, x)

theorem signed_leaf_eq (F : X → Y → Bool) (U : Finset X) (b : Bool) :
    leafDomain (stacked F) (signedRows U b) false = leafDomain F U b := by
  classical
  ext y
  simp only [mem_leafDomain]
  constructor
  · intro h x hx
    have hm : (b, x) ∈ signedRows U b := by
      change (b, x) ∈ U.image (fun z => (b, z))
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    have h' := h (b, x) hm
    cases b <;> cases hf : F x y <;> simp [stacked, hf] at h' ⊢
  · intro h p hp
    change p ∈ U.image (fun x => (b, x)) at hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
    have h' := h x hx
    cases b <;> cases hf : F x y <;> simp [stacked, hf] at h' ⊢

/-- One common-zero catalogue for both output bits. -/
theorem stacked_leaf_catalogue_covers (F : X → Y → Bool)
    (U : Set X) (b : Bool) :
    ∃ a : ↥(zeroDomains (stacked F)),
      (↑a.val : Set Y) = {y | ∀ x ∈ U, b = F x y} := by
  classical
  let V := signedRows U.toFinset b
  refine ⟨⟨leafDomain (stacked F) V false, ?_⟩, ?_⟩
  · exact Finset.mem_image.mpr ⟨V, Finset.mem_univ _, rfl⟩
  · ext y
    change y ∈ (leafDomain (stacked F) V false : Set Y) ↔
      (∀ x ∈ U, b = F x y)
    rw [signed_leaf_eq]
    simp [mem_leafDomain, eq_comm]

def leafBitsV38 (r : ℕ) : ℕ := (r + 1) * Nat.clog 2 (r + 2)

def rankCountExponentV38 (r t : ℕ) : ℕ := leafBitsV38 r * 2 ^ (t + 1)

theorem leafBitsV38_pos (r : ℕ) : 1 ≤ leafBitsV38 r := by
  have hb : 1 ≤ Nat.clog 2 (r + 2) := by
    have h := Nat.le_pow_clog (by decide : 1 < 2) (r + 2)
    by_contra hn
    have hz : Nat.clog 2 (r + 2) = 0 := by omega
    simp [hz] at h
  unfold leafBitsV38
  nlinarith

theorem stacked_leaf_card_le_pow (F : X → Y → Bool) (r : ℕ)
    (hrank : (realMatrix F).rank ≤ r) :
    (zeroDomains (stacked F)).card ≤ 2 ^ leafBitsV38 r := by
  have hrank' : (realMatrix (stacked F)).rank ≤ r + 1 := by
    exact (stacked_rank_le F).trans (Nat.add_le_add_right hrank 1)
  have hc := zeroDomains_card_le (stacked F) (r + 1) hrank'
  have hb : r + 2 ≤ 2 ^ Nat.clog 2 (r + 2) :=
    Nat.le_pow_clog (by decide : 1 < 2) (r + 2)
  calc
    (zeroDomains (stacked F)).card ≤ (r + 2) ^ (r + 1) := by simpa using hc
    _ ≤ (2 ^ Nat.clog 2 (r + 2)) ^ (r + 1) := Nat.pow_le_pow_left hb _
    _ = 2 ^ leafBitsV38 r := by
      rw [← pow_mul]
      rw [Nat.mul_comm (Nat.clog 2 (r + 2)) (r + 1)]
      rfl

/-- The v38 compatible-set count, using one stacked leaf alphabet and all
partial trees with arbitrary Alice/Bob speaking choices. -/
theorem compatibleDomains_card_le_v38 (F : X → Y → Bool) (r t : ℕ)
    (hrank : (realMatrix F).rank ≤ r) :
    (Paper2.compatibleDomains F t).ncard ≤ 2 ^ rankCountExponentV38 r t := by
  classical
  let leaf : ↥(zeroDomains (stacked F)) → Set Y := fun a => (↑a.val : Set Y)
  have hsub := Paper2.compatibleDomains_subset_formula_domains F leaf
    (stacked_leaf_catalogue_covers F) t
  have hcard : Fintype.card ↥(zeroDomains (stacked F)) ≤ 2 ^ leafBitsV38 r := by
    simpa only [Fintype.card_coe] using stacked_leaf_card_le_pow F r hrank
  have hf := Paper2.formula_domains_card_le leaf (leafBitsV38 r) t hcard
  have ha : leafBitsV38 r + 1 ≤ 2 * leafBitsV38 r := by
    have hp := leafBitsV38_pos r
    omega
  have hm := Nat.mul_le_mul_right (2 ^ t) ha
  have he : (leafBitsV38 r + 1) * 2 ^ t - 1 ≤ rankCountExponentV38 r t := by
    calc
      (leafBitsV38 r + 1) * 2 ^ t - 1 ≤
          (leafBitsV38 r + 1) * 2 ^ t := Nat.sub_le _ _
      _ ≤ (2 * leafBitsV38 r) * 2 ^ t := hm
      _ = rankCountExponentV38 r t := by
        unfold rankCountExponentV38
        rw [pow_succ]
        ring
  calc
    (Paper2.compatibleDomains F t).ncard ≤
        (Set.range (Paper2.CompleteFormula.eval leaf (t := t))).ncard :=
      Set.ncard_le_ncard hsub (Set.finite_range _)
    _ ≤ 2 ^ ((leafBitsV38 r + 1) * 2 ^ t - 1) := hf
    _ ≤ 2 ^ rankCountExponentV38 r t := Nat.pow_le_pow_right (by omega) he

theorem exists_compatible_cover_v38 (F : X → Y → Bool) (r t : ℕ)
    (hrank : (realMatrix F).rank ≤ r) :
    ∃ C : Finset (Set Y),
      C.card ≤ 2 ^ rankCountExponentV38 r t ∧
      ∀ (U : Set X) (P : Paper2.PartialProtocol X),
        P.cost ≤ t → P.compatible F U ∈ C := by
  classical
  let C := (Paper2.compatibleDomains_finite F t).toFinset
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    rw [← Set.ncard_eq_toFinset_card]
    exact compatibleDomains_card_le_v38 F r t hrank
  · intro U P hP
    change P.compatible F U ∈ (Paper2.compatibleDomains_finite F t).toFinset
    rw [Set.Finite.mem_toFinset]
    exact ⟨U, P, hP, rfl⟩

def entropyV38 (r H : ℕ) : ℕ := rankCountExponentV38 r (H - 1)

def squareDrawsV38 (r H : ℕ) : ℕ :=
  2 ^ Nat.clog 2 (16 * leafBitsV38 r * 2 ^ H)

theorem entropyV38_eq (r H : ℕ) (hH : 1 ≤ H) :
    entropyV38 r H = leafBitsV38 r * 2 ^ H := by
  unfold entropyV38 rankCountExponentV38
  have he : H - 1 + 1 = H := by omega
  rw [he]

theorem squareDrawsV38_cover (r H : ℕ) (hH : 1 ≤ H) :
    16 * entropyV38 r H ≤ squareDrawsV38 r H := by
  rw [entropyV38_eq r H hH]
  unfold squareDrawsV38
  convert Nat.le_pow_clog (by decide : 1 < 2)
    (16 * leafBitsV38 r * 2 ^ H) using 1
  ring

theorem squareDrawsV38_le_pow (r H k : ℕ)
    (h : 16 * leafBitsV38 r * 2 ^ H ≤ 2 ^ k) :
    squareDrawsV38 r H ≤ 2 ^ k := by
  unfold squareDrawsV38
  exact Nat.pow_le_pow_right (by omega)
    ((Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr h)

theorem entropyV38_ge_two (r H : ℕ) (hH : 1 ≤ H) :
    2 ≤ entropyV38 r H := by
  rw [entropyV38_eq r H hH]
  have ha := leafBitsV38_pos r
  have hp : 2 ≤ 2 ^ H := by
    simpa using (Nat.pow_le_pow_right (by omega : 0 < 2) hH)
  nlinarith

theorem square_sampling_numeric_v38 (E m : ℕ)
    (hE : 2 ≤ E) (hm : 16 * E ≤ m) :
    2 * ((2 : ℝ) ^ E * (3 / 5 : ℝ) ^ m) < 1 / 100 := by
  have hpow : (3 / 5 : ℝ) ^ m ≤ (3 / 5 : ℝ) ^ (16 * E) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
  have hb : (2 : ℝ) * (3 / 5 : ℝ) ^ 16 ≤ 1 / 16 := by norm_num
  have hbase : ((2 : ℝ) * (3 / 5 : ℝ) ^ 16) ^ E ≤ (1 / 16 : ℝ) ^ E :=
    pow_le_pow_left₀ (by positivity) hb _
  have htail : (1 / 16 : ℝ) ^ E ≤ (1 / 16 : ℝ) ^ 2 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hE
  calc
    2 * ((2 : ℝ) ^ E * (3 / 5 : ℝ) ^ m) ≤
        2 * ((2 : ℝ) ^ E * (3 / 5 : ℝ) ^ (16 * E)) := by gcongr
    _ = 2 * ((2 : ℝ) * (3 / 5 : ℝ) ^ 16) ^ E := by
      rw [pow_mul, mul_pow]
    _ ≤ 2 * (1 / 16 : ℝ) ^ E := by gcongr
    _ ≤ 2 * (1 / 16 : ℝ) ^ 2 := by gcongr
    _ < 1 / 100 := by norm_num

/-- The selected v38 two-sided compression failure theorem. The compatible
catalogue is produced above from rank; it is not a theorem premise. -/
theorem square_compression_failure_v38 (F : X → Y → Bool)
    (μX : Paper2.FiniteLaw X) (μY : Paper2.FiniteLaw Y) (r H : ℕ)
    (hH : 1 ≤ H)
    (hrank : (realMatrix F).rank ≤ r)
    (hrobust : ∀ U V, (3 / 5 : ℝ) ≤ μX.prob (· ∈ U) →
      (3 / 5 : ℝ) ≤ μY.prob (· ∈ V) →
      H ≤ Paper2.Compression.restrictionD F U V) :
    let m := squareDrawsV38 r H
    ((μY.iid m).prod (μX.iid m)).prob
      (fun z => Workspace.Types.CommComplexity.D (Paper2.sampleMatrix F z.2 z.1) < H) <
      1 / 100 := by
  classical
  dsimp
  let E := entropyV38 r H
  let m := squareDrawsV38 r H
  let e : ℝ := (2 ^ E : ℕ) * (3 / 5 : ℝ) ^ m
  have hE : 2 ≤ E := entropyV38_ge_two r H hH
  have hm : 16 * E ≤ m := squareDrawsV38_cover r H hH
  have hfirst : (μY.iid m).prob
      (fun ys => ¬ Paper2.Compression.ColumnGood F μX (3 / 5) H ys) ≤ e := by
    obtain ⟨s, hcard, hcover⟩ := exists_compatible_cover_v38 F r (H - 1) hrank
    exact Paper2.Compression.first_failure_le (n := m) F μX μY (3 / 5) (3 / 5)
      H (2 ^ E) hH (by norm_num) hrobust s hcard hcover
  have hsecond : ∀ ys : Fin m → Y,
      Paper2.Compression.ColumnGood F μX (3 / 5) H ys →
      (μX.iid m).prob
        (fun xs => Workspace.Types.CommComplexity.D
          (Paper2.sampleMatrix F xs ys) < H) ≤ e := by
    intro ys hgood
    have hrank' : (realMatrix (fun j x => F x (ys j))).rank ≤ r := by
      have ht := Paper2.transpose_rank (fun x j => F x (ys j))
      rw [ht]
      exact (Paper2.pullback_rank_le F id ys).trans hrank
    obtain ⟨s, hcard, hcover⟩ :=
      exists_compatible_cover_v38 (fun j x => F x (ys j)) r (H - 1) hrank'
    exact Paper2.Compression.second_failure_le (m := m) F μX (3 / 5) H
      (2 ^ E) hH (by norm_num) ys hgood s hcard hcover
  have ht := Paper2.FiniteLaw.two_stage_failure_le (μY.iid m) (μX.iid m)
    (Paper2.Compression.ColumnGood F μX (3 / 5) H)
    (fun ys xs => Workspace.Types.CommComplexity.D
      (Paper2.sampleMatrix F xs ys) < H)
    e e hfirst hsecond (by positivity)
  have hn : e + e < (1 / 100 : ℝ) := by
    dsimp [e]
    have hs := square_sampling_numeric_v38 E m hE hm
    simpa only [Nat.cast_pow, Nat.cast_ofNat, ← two_mul] using hs
  exact ht.trans_lt hn

omit [Fintype X] [Fintype Y] in
/-- The every-outcome upper protocol in v38, reusing the proved indexed
restriction theorem from the preserved v37 packet. -/
theorem square_sample_upper_v38 {m : ℕ} (F : X → Y → Bool)
    (P : Protocol X Y Bool) (hP : P.Computes F)
    (xs : Fin m → X) (ys : Fin m → Y) :
    ∃ Q : Protocol (Fin m) (Fin m) Bool,
      Q.cost = P.cost ∧ Q.Computes (Paper2.sampleMatrix F xs ys) :=
  square_sample_upper F P hP xs ys

end CurrentAdditive.V38RankCount

#print axioms CurrentAdditive.V38RankCount.stacked_rank_le
#print axioms CurrentAdditive.V38RankCount.stacked_leaf_card_le_pow
#print axioms CurrentAdditive.V38RankCount.compatibleDomains_card_le_v38
#print axioms CurrentAdditive.V38RankCount.exists_compatible_cover_v38
#print axioms CurrentAdditive.V38RankCount.square_compression_failure_v38
#print axioms CurrentAdditive.V38RankCount.square_sample_upper_v38
