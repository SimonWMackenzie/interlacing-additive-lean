import Paper2.RestrictionProfiles
import Paper2.InterlaceProtocol
import Paper2.ProtocolLeafRank

/-!
# The Boolean-cube coordinate-evaluation seed

Frozen source: v12 Appendix A, `cl:seed` (line 677), and the seed rank
used by Section 3. Rows are actual Boolean words and columns are coordinates.
This file does not import the concurrent Paper 1 `CurrentPaper` development.
-/

namespace Paper2.LookupSeed

open scoped BigOperators
open Workspace.Types.Protocol Workspace.Types.CommComplexity
open RankLeaves

/-- The actual coordinate-evaluation matrix. -/
def matrix (p : ℕ) : (Fin p → Bool) → Fin p → Bool := fun x j => x j

@[simp] theorem card_rows (p : ℕ) : Fintype.card (Fin p → Bool) = 2 ^ p := by simp

/-- The unit word is an actual input, not a linear combination of rows. -/
def unitRow {p : ℕ} (i : Fin p) : Fin p → Bool := fun j => decide (i = j)

/-- The coordinate-evaluation matrix has full column rank. -/
theorem rank_matrix (p : ℕ) : (realMatrix (matrix p)).rank = p := by
  apply le_antisymm
  · simpa using (realMatrix (matrix p)).rank_le_card_width
  · have h := card_le_rank_of_zero_witness (realMatrix (matrix p))
      unitRow id (by intro i; simp [realMatrix, matrix, unitRow])
      (by intro i j hij; simp [realMatrix, matrix, unitRow, hij])
    simpa using h

/-- Complementary unit words are also actual inputs, so the Boolean
complement of the full cube matrix has the same full column rank. -/
theorem rank_complement_matrix (p : ℕ) :
    (realMatrix (fun x j => !(matrix p x j))).rank = p := by
  apply le_antisymm
  · simpa using (realMatrix (fun x j => !(matrix p x j))).rank_le_card_width
  · have h := card_le_rank_of_zero_witness
      (realMatrix (fun x j => !(matrix p x j)))
      (fun i j => !(unitRow i j)) id
      (by intro i; simp [realMatrix, matrix, unitRow])
      (by intro i j hij; simp [realMatrix, matrix, unitRow, hij])
    simpa using h

/-- The one-bit base protocol used after the coordinate is announced. -/
def bitProtocol : Protocol Unit Bool Bool := .bNode id (.leaf false) (.leaf true)

theorem bitProtocol_computes : bitProtocol.Computes (fun _ b => b) := by
  intro x b
  cases b <;> rfl

theorem bit_D_le : D (fun (_ : Unit) (b : Bool) => b) ≤ 1 := by
  apply Nat.sInf_le
  exact ⟨bitProtocol, rfl, bitProtocol_computes⟩

/-- Bob announces a coordinate and Alice sends that coordinate's value.
This is obtained from the already checked concrete selector protocol. -/
theorem D_matrix_le (p : ℕ) (hp : 0 < p) :
    D (matrix p) ≤ Nat.clog 2 p + 1 := by
  have h := fullInterlace_transpose_D_le (fun (_ : Unit) (b : Bool) => b) p hp
  have hs := Workspace.ProofLemmas.SublemmaPrecompNoIncrease
    (fun z a => fullInterlace (fun (_ : Unit) (b : Bool) => b) p a z)
    id (fun j : Fin p => (j, ()))
  exact hs.trans (h.trans (Nat.add_le_add_left bit_D_le _))

theorem D_matrix_two_pow_le (a : ℕ) : D (matrix (2 ^ a)) ≤ a + 1 := by
  simpa only [Nat.clog_pow, one_lt_two] using D_matrix_le (2 ^ a) (Nat.two_pow_pos a)

/-- Rational uniform laws are constructed explicitly on every nonempty
finite carrier; they agree with the real uniform law used for profiles. -/
noncomputable def uniformRational (α : Type*) [Fintype α] [Nonempty α] :
    PositiveRationalLaw α where
  weight _ := (Fintype.card α : ℚ)⁻¹
  positive _ := inv_pos.mpr (by exact_mod_cast Fintype.card_pos)
  total := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)

theorem uniformRational_prob (α : Type*) [Fintype α] [Nonempty α] (S : Set α) :
    (uniformRational α).toFiniteLaw.prob (· ∈ S) =
      (S.ncard : ℝ) / Fintype.card α := by
  classical
  simp only [FiniteLaw.prob, PositiveRationalLaw.toFiniteLaw, uniformRational,
    Rat.cast_inv, Rat.cast_natCast]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [div_eq_mul_inv]
  congr 1
  have he : Finset.univ.filter (· ∈ S) = S.toFinset := by ext; simp
  rw [he]
  exact_mod_cast (Set.ncard_eq_toFinset_card' S).symm

/-- Uniform Boolean-cube row law. -/
noncomputable def rowLaw (p : ℕ) : PositiveRationalLaw (Fin p → Bool) :=
  uniformRational (Fin p → Bool)

/-- Uniform coordinate law. -/
noncomputable def columnLaw (p : ℕ) (hp : 0 < p) : PositiveRationalLaw (Fin p) := by
  letI : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
  exact uniformRational (Fin p)

theorem rowLaw_prob (p : ℕ) (U : Set (Fin p → Bool)) :
    (rowLaw p).toFiniteLaw.prob (· ∈ U) = (U.ncard : ℝ) / 2 ^ p := by
  simpa [rowLaw] using uniformRational_prob (Fin p → Bool) U

theorem columnLaw_prob (p : ℕ) (hp : 0 < p) (V : Set (Fin p)) :
    (columnLaw p hp).toFiniteLaw.prob (· ∈ V) = (V.ncard : ℝ) / p := by
  letI : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
  simpa [columnLaw] using uniformRational_prob (Fin p) V

/-- A row is determined by its retained-coordinate pattern together with
its unretained bits. Counting the retained patterns by real rank therefore
bounds the size of every retained cube set. -/
theorem retained_rows_card_le (p : ℕ) (U : Set (Fin p → Bool)) (V : Set (Fin p))
    [Fintype U] [Fintype V] :
    U.ncard ≤ 2 ^ ((realMatrix
      (fun (x : U) (j : V) => matrix p x.val j.val)).rank + (p - V.ncard)) := by
  classical
  let F : U → V → Bool := fun x j => x.val j.val
  let encode : U → ↥(rowValues F) × (↑(Vᶜ) → Bool) := fun x =>
    (⟨F x, Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩⟩,
      fun j => x.val j.val)
  have hinj : Function.Injective encode := by
    intro x y h
    apply Subtype.ext
    funext j
    by_cases hj : j ∈ V
    · have hc := congrArg (fun z => z.1.val ⟨j, hj⟩) h
      exact hc
    · have hc := congrArg (fun z => z.2 ⟨j, hj⟩) h
      exact hc
  have hc := Fintype.card_le_of_injective encode hinj
  have hV : Fintype.card ↑(Vᶜ) = p - V.ncard := by
    rw [Set.fintypeCard_eq_ncard, Set.ncard_compl]
    simp
  have hrows := distinct_row_values_card_le F
  calc
    U.ncard = Fintype.card U := (Set.fintypeCard_eq_ncard U).symm
    _ ≤ Fintype.card (↥(rowValues F) × (↑(Vᶜ) → Bool)) := hc
    _ = (rowValues F).card * 2 ^ (p - V.ncard) := by simp [hV]
    _ ≤ 2 ^ (realMatrix F).rank * 2 ^ (p - V.ncard) := Nat.mul_le_mul_right _ hrows
    _ = _ := by rw [← pow_add]; rfl

/-- Cardinal density on the full cube forces large rank after deleting
arbitrary columns. This uses actual retained words and arbitrary retained
coordinates; it is not an assumption about their span. -/
theorem retained_rank_lower_bound (p L : ℕ) (hL : L ≤ p)
    (U : Set (Fin p → Bool)) (V : Set (Fin p))
    [Fintype U] [Fintype V]
    (hU : 2 ^ (p - L) ≤ U.ncard) :
    V.ncard ≤ (realMatrix
      (fun (x : U) (j : V) => matrix p x.val j.val)).rank + L := by
  have he := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    (hU.trans (retained_rows_card_le p U V))
  have hV : V.ncard ≤ p := by
    simpa using Set.ncard_le_ncard (Set.subset_univ V)
  omega

/-- Exact seed cost at any positive power-of-two width. Full column rank
of both output matrices forces `2p` leaves in one shared protocol tree. -/
theorem D_matrix_two_pow (a : ℕ) : D (matrix (2 ^ a)) = a + 1 := by
  apply le_antisymm (D_matrix_two_pow_le a)
  have h := rank_pair_le_two_pow_D (matrix (2 ^ a))
  rw [rank_matrix, rank_complement_matrix] at h
  have he : 2 ^ a + 2 ^ a = 2 ^ (a + 1) := by omega
  rw [he] at h
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp h

/-- The probability row threshold in the manuscript implies its exact
cardinality threshold on the uniformly weighted full Boolean cube. -/
theorem row_density_card (p L : ℕ) (hL : L ≤ p) (U : Set (Fin p → Bool))
    (hU : (1 / 2 : ℝ) ^ L ≤ (rowLaw p).toFiniteLaw.prob (· ∈ U)) :
    2 ^ (p - L) ≤ U.ncard := by
  rw [rowLaw_prob] at hU
  have hmul := (le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) p)).mp hU
  have he : (1 / 2 : ℝ) ^ L * 2 ^ p = 2 ^ (p - L) := by
    have hp : (2 : ℝ) ^ p = 2 ^ (p - L) * 2 ^ L := by
      rw [← pow_add, Nat.sub_add_cancel hL]
    rw [hp, div_pow, one_pow]
    field_simp
  rw [he] at hmul
  exact_mod_cast hmul

/-- A real-rank lower bound expressed directly in the prescribed uniform
input probabilities, before applying the paired leaf-rank inequality. -/
theorem retained_rank_mass (p L : ℕ) (hp : 0 < p) (hL : L ≤ p)
    (U : Set (Fin p → Bool)) (V : Set (Fin p)) [Fintype U] [Fintype V]
    (b : ℝ)
    (hU : (1 / 2 : ℝ) ^ L ≤ (rowLaw p).toFiniteLaw.prob (· ∈ U))
    (hV : b ≤ (columnLaw p hp).toFiniteLaw.prob (· ∈ V)) :
    b * p ≤ ((realMatrix
      (fun (x : U) (j : V) => matrix p x.val j.val)).rank : ℝ) + L := by
  have hr := retained_rank_lower_bound p L hL U V (row_density_card p L hL U hU)
  rw [columnLaw_prob] at hV
  have hmul := (le_div_iff₀ (by exact_mod_cast hp : (0 : ℝ) < p)).mp hV
  exact hmul.trans (by exact_mod_cast hr)

/-- The manuscript's seed-size condition provides strict room at each
of the three column-density thresholds. -/
theorem profile_rank_threshold (a L r : ℕ) (hp : 64 * (L + 1) ≤ 2 ^ a)
    (j : Fin 3)
    (hr : ((3 / 5 : ℝ) * (1 / 2 : ℝ) ^ j.val) * (2 : ℝ) ^ a ≤ r + L) :
    2 ^ (a - j.val) + 1 < 2 * r := by
  have ha : 2 ≤ a := by
    by_contra hn
    have he : 2 ^ a ≤ 2 ^ 1 := Nat.pow_le_pow_right (by omega) (by omega)
    norm_num at he
    omega
  have hpR : (64 : ℝ) * (L + 1) ≤ (2 : ℝ) ^ a := by exact_mod_cast hp
  fin_cases j
  · norm_num at hr ⊢
    exact_mod_cast (show (2 : ℝ) ^ a + 1 < 2 * r by nlinarith)
  · have he : (2 : ℝ) ^ (a - 1) * 2 = 2 ^ a := by
      rw [← pow_succ]
      congr 1
      omega
    norm_num at hr ⊢
    exact_mod_cast (show (2 : ℝ) ^ (a - 1) + 1 < 2 * r by nlinarith)
  · have he : (2 : ℝ) ^ (a - 2) * 4 = 2 ^ a := by
      calc
        _ = (2 : ℝ) ^ (a - 2) * 2 ^ 2 := by norm_num
        _ = 2 ^ a := by rw [← pow_add]; congr 1; omega
    norm_num at hr ⊢
    exact_mod_cast (show (2 : ℝ) ^ (a - 2) + 1 < 2 * r by nlinarith)

/-- All three restriction inequalities of the full-cube seed, for any
power-of-two width satisfying the stated size threshold. Minimality is
needed only for later construction-size bounds. -/
theorem profile (a L : ℕ) (hp : 64 * (L + 1) ≤ 2 ^ a) :
    RestrictionProfile (matrix (2 ^ a)) (rowLaw (2 ^ a)).toFiniteLaw
      (columnLaw (2 ^ a) (Nat.two_pow_pos a)).toFiniteLaw
      ((1 / 2 : ℝ) ^ L) ((a : ℤ) + 1) := by
  classical
  intro j U V hU hV
  have hLp : L ≤ 2 ^ a := by omega
  have hr := retained_rank_mass (2 ^ a) L (Nat.two_pow_pos a) hLp U V
    ((3 / 5 : ℝ) * (1 / 2 : ℝ) ^ j.val) hU hV
  have hr' : ((3 / 5 : ℝ) * (1 / 2 : ℝ) ^ j.val) * (2 : ℝ) ^ a ≤
      ((realMatrix (fun (x : U) (y : V) => matrix (2 ^ a) x.val y.val)).rank : ℝ) + L := by
    simpa using hr
  have ht := profile_rank_threshold a L _ hp j hr'
  have hD := cost_gt_of_two_mul_rank_gt
    (fun (x : U) (y : V) => matrix (2 ^ a) x.val y.val) (a - j.val) ht
  have ha : j.val ≤ a := by
    by_contra hn
    have he : 2 ^ a ≤ 2 ^ 1 := Nat.pow_le_pow_right (by omega) (by omega)
    norm_num at he
    omega
  change (a : ℤ) + 1 - (j.val : ℤ) ≤
    (D (fun (x : U) (y : V) => matrix (2 ^ a) x.val y.val) : ℤ)
  omega

/-- Finite mathematical conclusion of `cl:seed`, together with the rank
used in the iteration. This does not yet claim a machine-level polynomial
construction or the explicit comparison with the source size `n`. -/
theorem seed_finite (a L : ℕ) (hp : 64 * (L + 1) ≤ 2 ^ a) :
    D (matrix (2 ^ a)) = a + 1 ∧
    RestrictionProfile (matrix (2 ^ a)) (rowLaw (2 ^ a)).toFiniteLaw
      (columnLaw (2 ^ a) (Nat.two_pow_pos a)).toFiniteLaw
      ((1 / 2 : ℝ) ^ L) ((a : ℤ) + 1) ∧
    (realMatrix (matrix (2 ^ a))).rank = 2 ^ a :=
  ⟨D_matrix_two_pow a, profile a L hp, rank_matrix (2 ^ a)⟩

/-- The effective natural-number exponent selecting the least admissible
power of two. It depends only on the public parameter `L`. -/
def exponent (L : ℕ) : ℕ := Nat.clog 2 (64 * (L + 1))

def width (L : ℕ) : ℕ := 2 ^ exponent L

theorem width_admissible (L : ℕ) : 64 * (L + 1) ≤ width L :=
  Nat.le_pow_clog (by decide) _

theorem exponent_minimal (L b : ℕ) (hb : 64 * (L + 1) ≤ 2 ^ b) :
    exponent L ≤ b := Nat.clog_le_of_le_pow hb

theorem width_lt (L : ℕ) : width L < 128 * (L + 1) := by
  have he := Nat.clog_pos (by decide : 1 < 2) (show 1 < 64 * (L + 1) by omega)
  have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2)
    (show 1 < 64 * (L + 1) by omega)
  have heq : Nat.pred (exponent L) + 1 = exponent L := by
    change 0 < exponent L at he
    exact Nat.succ_pred_eq_of_pos he
  have hpow : width L = 2 ^ Nat.pred (exponent L) * 2 := by
    rw [← pow_succ, heq]
    rfl
  rw [hpow]
  change 2 ^ Nat.pred (exponent L) < 64 * (L + 1) at hp
  omega

/-- The exact public seed choice has the specified cost, profile and rank. -/
theorem selected_seed_finite (L : ℕ) :
    D (matrix (width L)) = exponent L + 1 ∧
    RestrictionProfile (matrix (width L)) (rowLaw (width L)).toFiniteLaw
      (columnLaw (width L) (Nat.two_pow_pos (exponent L))).toFiniteLaw
      ((1 / 2 : ℝ) ^ L) ((exponent L : ℤ) + 1) ∧
    (realMatrix (matrix (width L))).rank = width L :=
  seed_finite (exponent L) L (width_admissible L)

/-- The exact width estimate stated in `cl:seed`, with the ceiling-log
parameter computed as an integer. -/
theorem width_source_bound (n : ℕ) (hn : 4 ≤ n) :
    (width (Nat.clog 2 n) : ℝ) < 256 * Real.logb 2 (n : ℝ) := by
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : (2 : ℝ) ≤ Real.logb 2 (n : ℝ) := by
    have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 4) hnR
    have he : Real.logb 2 (4 : ℝ) = 2 := by
      calc
        _ = Real.logb 2 ((2 : ℝ) ^ 2) := by norm_num
        _ = 2 := by rw [Real.logb_pow]; norm_num [Real.logb_self_eq_one]
    rwa [he] at h
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ Real.logb 2 (n : ℝ) by linarith)
  have hc : ⌈Real.logb 2 (n : ℝ)⌉₊ = Nat.clog 2 n := by
    simpa using Real.natCeil_logb_natCast 2 n
  rw [hc] at hceil
  have hw : (width (Nat.clog 2 n) : ℝ) < 128 * ((Nat.clog 2 n : ℝ) + 1) := by
    exact_mod_cast width_lt (Nat.clog 2 n)
  linarith

/-- The Boolean-cube row count is below the stated polynomial `n^256`.
This is a numerical output-size theorem, not a machine-runtime assertion. -/
theorem rows_source_bound (n : ℕ) (hn : 4 ≤ n) :
    2 ^ width (Nat.clog 2 n) < n ^ 256 := by
  have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
    (width_source_bound n hn)
  rw [Real.rpow_natCast] at h
  have he : (2 : ℝ) ^ (256 * Real.logb 2 (n : ℝ)) = (n : ℝ) ^ (256 : ℕ) := by
    calc
      _ = (2 : ℝ) ^ (Real.logb 2 (n : ℝ) * (256 : ℕ)) := by rw [mul_comm]; norm_num
      _ = ((2 : ℝ) ^ Real.logb 2 (n : ℝ)) ^ (256 : ℕ) :=
        Real.rpow_mul_natCast (by norm_num) _ 256
      _ = _ := by rw [Real.rpow_logb (by norm_num) (by norm_num)
        (by exact_mod_cast (by omega : 0 < n))]
  rw [he] at h
  exact_mod_cast h

end Paper2.LookupSeed

#print axioms Paper2.LookupSeed.rank_matrix
#print axioms Paper2.LookupSeed.rank_complement_matrix
#print axioms Paper2.LookupSeed.D_matrix_le
#print axioms Paper2.LookupSeed.retained_rows_card_le
#print axioms Paper2.LookupSeed.D_matrix_two_pow
#print axioms Paper2.LookupSeed.profile
#print axioms Paper2.LookupSeed.seed_finite
#print axioms Paper2.LookupSeed.selected_seed_finite
#print axioms Paper2.LookupSeed.width_source_bound
#print axioms Paper2.LookupSeed.rows_source_bound
