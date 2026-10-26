import Paper2.FiniteSampling
import Paper2.SamplingBounds
import Paper2.ProtocolDomains
import Paper2.IndexedMatrices
import Paper2.RankCounting

/-!
# Two-sided indexed sampling

Source: Paper 2, frozen `2026-09-22-protocol-labels-v12`, Section 2,
Theorem `thm:compression`. The probability space consists of independent
indexed lists. Compatibility always requires one Bob strategy for every
retained row, and the first good event is uniform over all original row sets.
-/

namespace Paper2

open Workspace.Types.CommComplexity

namespace Compression

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Actual deterministic cost on a retained rectangle. -/
noncomputable def restrictionD (F : X → Y → Bool) (U : Set X) (V : Set Y) : ℕ := by
  classical
  exact D (fun (x : U) (y : V) => F x.1 y.1)

/-- Actual deterministic cost after sampling columns, with original retained rows. -/
noncomputable def columnSampleD {n : ℕ} (F : X → Y → Bool)
    (U : Set X) (ys : Fin n → Y) : ℕ := by
  classical
  exact D (fun (x : U) j => F x.1 (ys j))

theorem columnSampleD_eq_range {n : ℕ} (F : X → Y → Bool)
    (U : Set X) (ys : Fin n → Y) :
    columnSampleD F U ys = restrictionD F U (Set.range ys) := by
  classical
  apply pullback_D_eq_of_surjective (fun (x : U) (y : Set.range ys) => F x.1 y.1)
    id (fun j => ⟨ys j, ⟨j, rfl⟩⟩) Function.surjective_id
  rintro ⟨y, j, rfl⟩
  exact ⟨j, rfl⟩

/-- Shortness on an indexed sample is exactly coverage by a compatible
domain in the original input space, even with duplicate sampled labels. -/
theorem columnSampleD_le_iff {n : ℕ} (F : X → Y → Bool)
    (U : Set X) (ys : Fin n → Y) (t : ℕ) :
    columnSampleD F U ys ≤ t ↔ ∃ P : PartialProtocol X,
      P.cost ≤ t ∧ ∀ j, ys j ∈ P.compatible F U := by
  classical
  rw [columnSampleD_eq_range]
  change D (fun (x : U) (y : Set.range ys) => F x.1 y.1) ≤ t ↔ _
  rw [PartialProtocol.D_restriction_le_iff]
  simp only [Set.range_subset_iff]

/-- A robust restriction lower bound forces every cheap compatible domain
on a sufficiently large row set to have small column mass. -/
theorem compatible_mass_lt (F : X → Y → Bool)
    (μX : FiniteLaw X) (μY : FiniteLaw Y) (a b : ℝ) (H : ℕ)
    (hH : 1 ≤ H)
    (hrobust : ∀ U V, a ≤ μX.prob (· ∈ U) → b ≤ μY.prob (· ∈ V) →
      H ≤ restrictionD F U V)
    (U : Set X) (hU : a ≤ μX.prob (· ∈ U))
    (P : PartialProtocol X) (hP : P.cost ≤ H - 1) :
    μY.prob (· ∈ P.compatible F U) < b := by
  classical
  by_contra hn
  have hlow := hrobust U (P.compatible F U) hU (le_of_not_gt hn)
  have hupp := P.D_restriction_le F U (P.compatible F U) (fun _ h => h)
  change restrictionD F U (P.compatible F U) ≤ P.cost at hupp
  omega

/-- The first-stage event keeps all sufficiently large original row sets
hard simultaneously. No new robustness claim is imposed on the final sample. -/
def ColumnGood {n : ℕ} (F : X → Y → Bool)
    (μX : FiniteLaw X) (a : ℝ) (H : ℕ) (ys : Fin n → Y) : Prop :=
  ∀ U : Set X, a ≤ μX.prob (· ∈ U) → H ≤ columnSampleD F U ys

theorem columnSampleD_univ {n : ℕ} (F : X → Y → Bool) (ys : Fin n → Y) :
    columnSampleD F Set.univ ys = D (fun x j => F x (ys j)) := by
  classical
  have h := pullback_D_eq_of_surjective (fun x j => F x (ys j))
    Subtype.val id (fun x => ⟨⟨x, Set.mem_univ x⟩, rfl⟩) Function.surjective_id
  exact h

/-- The first probability estimate, assuming only an explicit catalogue
covering all short domains. The catalogue bound is supplied by rank counting. -/
theorem first_failure_le {n : ℕ} (F : X → Y → Bool)
    (μX : FiniteLaw X) (μY : FiniteLaw Y) (a b : ℝ) (H K : ℕ)
    (hH : 1 ≤ H) (hb : 0 ≤ b)
    (hrobust : ∀ U V, a ≤ μX.prob (· ∈ U) → b ≤ μY.prob (· ∈ V) →
      H ≤ restrictionD F U V)
    (s : Finset (Set Y)) (hcard : s.card ≤ K)
    (hcover : ∀ U (P : PartialProtocol X), P.cost ≤ H - 1 → P.compatible F U ∈ s) :
    (μY.iid n).prob (fun ys => ¬ ColumnGood F μX a H ys) ≤ (K : ℝ) * b ^ n := by
  classical
  let small := s.filter (fun V => ∃ U : Set X, a ≤ μX.prob (· ∈ U) ∧
    ∃ P : PartialProtocol X, P.cost ≤ H - 1 ∧ P.compatible F U = V)
  have hsmall : small.card ≤ K := (Finset.card_filter_le ..).trans hcard
  have hmass : ∀ V ∈ small, μY.prob (· ∈ V) ≤ b := by
    intro V hV
    obtain ⟨_, U, hU, P, hP, rfl⟩ := Finset.mem_filter.mp hV
    exact (compatible_mass_lt F μX μY a b H hH hrobust U hU P hP).le
  have hbad : ∀ ys : Fin n → Y, ¬ ColumnGood F μX a H ys →
      ∃ V ∈ small, ∀ j, ys j ∈ V := by
    intro ys hy
    simp only [ColumnGood, not_forall] at hy
    obtain ⟨U, hU, hd⟩ := hy
    have hd' : columnSampleD F U ys ≤ H - 1 := by omega
    obtain ⟨P, hP, hp⟩ := (columnSampleD_le_iff F U ys (H - 1)).mp hd'
    exact ⟨P.compatible F U, Finset.mem_filter.mpr
      ⟨hcover U P hP, U, hU, P, hP, rfl⟩, hp⟩
  exact ((μY.iid n).prob_mono hbad).trans
    (μY.iid_prob_some_domain_le_of_card n small (fun V y => y ∈ V) b K hb hsmall hmass)

/-- Restricting a transpose-compatible domain gives a short protocol on
the same column-sampled matrix with those original rows. -/
theorem columnSampleD_le_of_transpose_compatible {n : ℕ}
    (F : X → Y → Bool) (ys : Fin n → Y)
    (P : PartialProtocol (Fin n)) (V : Set X)
    (hV : V ⊆ P.compatible (fun j x => F x (ys j)) Set.univ) :
    columnSampleD F V ys ≤ P.cost := by
  classical
  have h := P.D_restriction_le (fun j x => F x (ys j)) Set.univ V hV
  have hr := PartialProtocol.D_reindex_le
    (fun (j : (Set.univ : Set (Fin n))) (x : V) => F x.1 (ys j.1))
    (fun j => (⟨j, Set.mem_univ j⟩ : (Set.univ : Set (Fin n)))) id
  have ht := transpose_D (fun (x : V) j => F x.1 (ys j))
  change D (fun j (x : V) => F x.1 (ys j)) = columnSampleD F V ys at ht
  exact ht ▸ hr.trans h

/-- Conditional second probability estimate. The catalogue may depend on
the entire column outcome; the independent row law is unchanged. -/
theorem second_failure_le {m n : ℕ} (F : X → Y → Bool)
    (μX : FiniteLaw X) (a : ℝ) (H K : ℕ) (hH : 1 ≤ H) (ha : 0 ≤ a)
    (ys : Fin n → Y) (hgood : ColumnGood F μX a H ys)
    (s : Finset (Set X)) (hcard : s.card ≤ K)
    (hcover : ∀ U (P : PartialProtocol (Fin n)), P.cost ≤ H - 1 →
      P.compatible (fun j x => F x (ys j)) U ∈ s) :
    (μX.iid m).prob (fun xs => D (sampleMatrix F xs ys) < H) ≤
      (K : ℝ) * a ^ m := by
  classical
  let small := s.filter (fun V => ∃ P : PartialProtocol (Fin n),
    P.cost ≤ H - 1 ∧ P.compatible (fun j x => F x (ys j)) Set.univ = V)
  have hsmall : small.card ≤ K := (Finset.card_filter_le ..).trans hcard
  have hmass : ∀ V ∈ small, μX.prob (· ∈ V) ≤ a := by
    intro V hV
    obtain ⟨_, P, hP, rfl⟩ := Finset.mem_filter.mp hV
    apply le_of_lt
    by_contra hn
    have hlo := hgood _ (le_of_not_gt hn)
    have hup := columnSampleD_le_of_transpose_compatible F ys P _ (fun _ h => h)
    omega
  have hbad : ∀ xs : Fin m → X, D (sampleMatrix F xs ys) < H →
      ∃ V ∈ small, ∀ i, xs i ∈ V := by
    intro xs hd
    have hd' : columnSampleD (fun j x => F x (ys j)) Set.univ xs ≤ H - 1 := by
      rw [columnSampleD_univ]
      have ht := transpose_D (sampleMatrix F xs ys)
      change D (fun j i => F (xs i) (ys j)) = D (sampleMatrix F xs ys) at ht
      rw [ht]
      omega
    obtain ⟨P, hP, hp⟩ :=
      (columnSampleD_le_iff (fun j x => F x (ys j)) Set.univ xs (H - 1)).mp hd'
    exact ⟨P.compatible (fun j x => F x (ys j)) Set.univ,
      Finset.mem_filter.mpr ⟨hcover Set.univ P hP, P, hP, rfl⟩, hp⟩
  exact ((μX.iid m).prob_mono hbad).trans
    (μX.iid_prob_some_domain_le_of_card m small (fun V x => x ∈ V) a K ha hsmall hmass)

/-- The failure-probability assertion of `thm:compression`, with the exact
sample sizes and constant. Both samples use their original laws independently.
The only mathematical assumptions are real rank and the stated rectangular
restriction lower bound. In particular no counting conclusion is assumed. -/
theorem two_sided_compression_failure (F : X → Y → Bool)
    (μX : FiniteLaw X) (μY : FiniteLaw Y) (r H L : ℕ)
    (hH : 1 ≤ H) (hL : 1 ≤ L)
    (hrank : (RankLeaves.realMatrix F).rank ≤ r)
    (hrobust : ∀ U V, (1 / 2 : ℝ) ^ L ≤ μX.prob (· ∈ U) →
      (3 / 5 : ℝ) ≤ μY.prob (· ∈ V) → H ≤ restrictionD F U V) :
    ((μY.iid (compressionColumnDraws (compressionEntropy r H))).prod
      (μX.iid (compressionRowDraws (compressionEntropy r H) L))).prob
      (fun z => D (sampleMatrix F z.2 z.1) < H) ≤ (1 / 2 : ℝ) ^ 12 := by
  classical
  let Z := compressionEntropy r H
  let n := compressionColumnDraws Z
  let m := compressionRowDraws Z L
  have hZ : 1 ≤ Z := compressionEntropy_pos r H
  have hfirst : (μY.iid n).prob
      (fun ys => ¬ ColumnGood F μX ((1 / 2 : ℝ) ^ L) H ys) ≤ (1 / 2 : ℝ) ^ 13 := by
    obtain ⟨s, hcard, hcover⟩ := exists_compatible_cover F r (H - 1) hrank
    have h := first_failure_le (n := n) F μX μY ((1 / 2 : ℝ) ^ L) (3 / 5) H
      (2 ^ (Z - 1)) hH (by norm_num) hrobust s hcard hcover
    have he := compression_column_error_real Z hZ
    exact h.trans (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using he)
  have hsecond : ∀ ys : Fin n → Y,
      ColumnGood F μX ((1 / 2 : ℝ) ^ L) H ys →
      (μX.iid m).prob (fun xs => D (sampleMatrix F xs ys) < H) ≤
        (1 / 2 : ℝ) ^ 13 := by
    intro ys hgood
    have hrank' : (RankLeaves.realMatrix (fun j x => F x (ys j))).rank ≤ r := by
      have ht := transpose_rank (fun x j => F x (ys j))
      rw [ht]
      exact (pullback_rank_le F id ys).trans hrank
    obtain ⟨s, hcard, hcover⟩ :=
      exists_compatible_cover (fun j x => F x (ys j)) r (H - 1) hrank'
    have h := second_failure_le (m := m) F μX ((1 / 2 : ℝ) ^ L) H
      (2 ^ (Z - 1)) hH (by positivity) ys hgood s hcard hcover
    have he := compression_row_error_mass_real Z L hZ hL
    exact h.trans (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using he)
  have h := FiniteLaw.two_stage_failure_le (μY.iid n) (μX.iid m)
    (ColumnGood F μX ((1 / 2 : ℝ) ^ L) H)
    (fun ys xs => D (sampleMatrix F xs ys) < H)
    ((1 / 2 : ℝ) ^ 13) ((1 / 2 : ℝ) ^ 13) hfirst hsecond (by positivity)
  exact h.trans (by norm_num)

/-- Full two-sided compression, including the every-outcome upper-bound
preservation. This is a finite sampling theorem, not a runtime or hardness
reduction theorem. The rank-zero case is not excluded by the statement. -/
theorem two_sided_compression (F : X → Y → Bool)
    (μX : FiniteLaw X) (μY : FiniteLaw Y) (r H L : ℕ)
    (hH : 1 ≤ H) (hL : 1 ≤ L)
    (hrank : (RankLeaves.realMatrix F).rank ≤ r)
    (hrobust : ∀ U V, (1 / 2 : ℝ) ^ L ≤ μX.prob (· ∈ U) →
      (3 / 5 : ℝ) ≤ μY.prob (· ∈ V) → H ≤ restrictionD F U V) :
    ((μY.iid (compressionColumnDraws (compressionEntropy r H))).prod
      (μX.iid (compressionRowDraws (compressionEntropy r H) L))).prob
      (fun z => D (sampleMatrix F z.2 z.1) < H) ≤ (1 / 2 : ℝ) ^ 12 ∧
    ∀ (xs : Fin (compressionRowDraws (compressionEntropy r H) L) → X)
      (ys : Fin (compressionColumnDraws (compressionEntropy r H)) → Y),
      D (sampleMatrix F xs ys) ≤ D F := by
  exact ⟨two_sided_compression_failure F μX μY r H L hH hL hrank hrobust,
    fun xs ys => sample_D_le F xs ys⟩

end Compression
end Paper2

#print axioms Paper2.Compression.two_sided_compression_failure
#print axioms Paper2.Compression.two_sided_compression
