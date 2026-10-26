import Paper2.Compression
import Paper2.ProtocolLeafRank
import Mathlib

/-!
Private v37 rank-count proof. Source: versions/v37/source/sections/sampling.tex,
`thm:rank-count` and `thm:compression`. No production source is edited here.
-/

namespace CurrentAdditive.V37RankCount

open Paper2 Paper2.RankLeaves Matrix Workspace.Types.Protocol

variable {X Y : Type*} [Fintype X] [Fintype Y]

noncomputable def countOn (F : X → Y → Bool) (V : Finset X) (y : Y) : ℕ :=
  (V.filter fun x => F x y).card

omit [Fintype X] [Fintype Y] in
theorem countOn_le (F : X → Y → Bool) (V : Finset X) (y : Y) :
    countOn F V y ≤ V.card := by
  classical
  exact Finset.card_filter_le _ _

omit [Fintype X] [Fintype Y] in
theorem countOn_eq_sum (F : X → Y → Bool) (V : Finset X) (y : Y) :
    (countOn F V y : ℝ) = ∑ x ∈ V, realMatrix F x y := by
  classical
  induction V using Finset.induction_on with
  | empty => simp [countOn]
  | @insert x V hx ih =>
      simp [countOn, realMatrix]

omit [Fintype X] [Fintype Y] in
/-- Counts on a column basis determine the entire nonnegative row sum. -/
theorem countOn_ext_of_basis (F : X → Y → Bool) (V W : Finset X)
    {q : ℕ} (c : Fin q → Y)
    (hspan : Submodule.span ℝ (Set.range fun i => (realMatrix F).col (c i)) =
      Submodule.span ℝ (Set.range (realMatrix F).col))
    (hc : ∀ i, countOn F V (c i) = countOn F W (c i)) :
    ∀ y, countOn F V y = countOn F W y := by
  classical
  let φ : (X → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun a => (∑ x ∈ V, a x) - (∑ x ∈ W, a x)
      map_add' := by
        intro a b
        simp only [Pi.add_apply, Finset.sum_add_distrib]
        ring
      map_smul' := by
        intro a b
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
          ← Finset.mul_sum, mul_sub] }
  have hφ : Set.EqOn (⇑φ) (⇑(0 : (X → ℝ) →ₗ[ℝ] ℝ))
      (Set.range fun i => (realMatrix F).col (c i)) := by
    rintro a ⟨i, rfl⟩
    change (∑ x ∈ V, realMatrix F x (c i)) -
      (∑ x ∈ W, realMatrix F x (c i)) = 0
    rw [← countOn_eq_sum, ← countOn_eq_sum, hc i]
    simp
  intro y
  have hm : (realMatrix F).col y ∈
      Submodule.span ℝ (Set.range fun i => (realMatrix F).col (c i)) := by
    rw [hspan]
    exact Submodule.subset_span ⟨y, rfl⟩
  have he := LinearMap.eqOn_span hφ hm
  change (∑ x ∈ V, realMatrix F x y) -
    (∑ x ∈ W, realMatrix F x y) = 0 at he
  rw [← countOn_eq_sum, ← countOn_eq_sum] at he
  exact_mod_cast sub_eq_zero.mp he

theorem mem_zero_iff_count_zero (F : X → Y → Bool) (V : Finset X) (y : Y) :
    y ∈ leafDomain F V false ↔ countOn F V y = 0 := by
  classical
  simp [mem_leafDomain, countOn, Finset.card_eq_zero]

theorem zeroDomain_eq_of_count_eq (F : X → Y → Bool) (V W : Finset X)
    (h : ∀ y, countOn F V y = countOn F W y) :
    leafDomain F V false = leafDomain F W false := by
  ext y
  simp only [mem_zero_iff_count_zero]
  rw [h y]

/-- A finite quotient has no more outputs than codes when equal codes imply
equal outputs. This is used only with codes of small row sets. -/
theorem image_card_le_of_factor {A B C : Type*} [Fintype A]
    [DecidableEq B] [DecidableEq C]
    (f : A → B) (g : A → C)
    (h : ∀ a b, g a = g b → f a = f b) :
    (Finset.univ.image f).card ≤ (Finset.univ.image g).card := by
  classical
  let rep : ↥(Finset.univ.image f) → A := fun z =>
    Classical.choose (Finset.mem_image.mp z.property)
  have hrep (z : ↥(Finset.univ.image f)) : f (rep z) = z.val :=
    (Classical.choose_spec (Finset.mem_image.mp z.property)).2
  let map : ↥(Finset.univ.image f) → ↥(Finset.univ.image g) := fun z =>
    ⟨g (rep z), Finset.mem_image.mpr ⟨rep z, Finset.mem_univ _, rfl⟩⟩
  have hinj : Function.Injective map := by
    intro z w he
    have hg : g (rep z) = g (rep w) := congrArg Subtype.val he
    apply Subtype.ext
    calc
      z.val = f (rep z) := (hrep z).symm
      _ = f (rep w) := h _ _ hg
      _ = w.val := hrep w
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective map hinj

noncomputable def zeroDomains (F : X → Y → Bool) : Finset (Finset Y) := by
  classical
  exact Finset.univ.image fun V : Finset X => leafDomain F V false

theorem zeroDomains_card_le_pos (F : X → Y → Bool) (R : ℕ)
    (hR : 1 ≤ R) (hrank : (realMatrix F).rank ≤ R) :
    (zeroDomains F).card ≤ (R + 1) ^ R := by
  classical
  let A := realMatrix F
  let q := Module.finrank ℝ ↥(Submodule.span ℝ (Set.range A.col))
  obtain ⟨g, hgmem, hgspan, _⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℝ (Set.range A.col)
  obtain ⟨c, hc⟩ : ∃ c : Fin q → Y, ∀ i, g i = A.col (c i) := by
    have h : ∀ i, ∃ y, g i = A.col y := by
      intro i
      obtain ⟨y, hy⟩ := hgmem i
      exact ⟨y, hy.symm⟩
    exact Classical.axiomOfChoice h
  have hspan : Submodule.span ℝ (Set.range fun i => A.col (c i)) =
      Submodule.span ℝ (Set.range A.col) := by
    have hgc : g = fun i => A.col (c i) := funext hc
    simpa only [hgc] using hgspan
  have hq : q ≤ R := by
    simpa only [q, A, ← Matrix.rank_eq_finrank_span_cols] using hrank
  let small : Finset (Finset X) := Finset.univ.filter fun V => V.card ≤ R
  have hsmall (V : Finset X) : V ∈ small ↔ V.card ≤ R := by
    simp [small]
  let code : ↥small → (Fin q → Fin (R + 1)) := fun V i =>
    ⟨countOn F V.val (c i), Nat.lt_succ_of_le
      ((countOn_le F V.val (c i)).trans ((hsmall V.val).mp V.property))⟩
  have hfactor (V W : ↥small) (he : code V = code W) :
      leafDomain F V.val false = leafDomain F W.val false := by
    apply zeroDomain_eq_of_count_eq
    apply countOn_ext_of_basis F V.val W.val c hspan
    intro i
    exact congrArg Fin.val (congrFun he i)
  have hpart : (small.image fun V => leafDomain F V false).card ≤
      (R + 1) ^ q := by
    have hf := image_card_le_of_factor
      (fun V : ↥small => leafDomain F V.val false) code hfactor
    have himages : (Finset.univ.image fun V : ↥small =>
        leafDomain F V.val false) = small.image fun V => leafDomain F V false := by
      ext S
      simp
    rw [himages] at hf
    calc
      (small.image fun V => leafDomain F V false).card ≤
          (Finset.univ.image code).card := hf
      _ ≤ Fintype.card (Fin q → Fin (R + 1)) :=
        by simpa using (Finset.card_le_card (Finset.subset_univ (Finset.univ.image code)))
      _ = (R + 1) ^ q := by simp
  have hsub : zeroDomains F ⊆ small.image fun V => leafDomain F V false := by
    intro S hS
    obtain ⟨U, _, rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨V, _, hcard, heq⟩ := exists_small_leaf_constraints F R hR hrank U false
    exact Finset.mem_image.mpr ⟨V, (hsmall V).mpr hcard, heq⟩
  calc
    (zeroDomains F).card ≤ (small.image fun V => leafDomain F V false).card :=
      Finset.card_le_card hsub
    _ ≤ (R + 1) ^ q := hpart
    _ ≤ (R + 1) ^ R := Nat.pow_le_pow_right (by omega) hq

/-- Exact common-zero-row-set count, including rank zero and empty sets. -/
theorem zeroDomains_card_le (F : X → Y → Bool) (R : ℕ)
    (hrank : (realMatrix F).rank ≤ R) :
    (zeroDomains F).card ≤ (R + 1) ^ R := by
  classical
  by_cases hR : R = 0
  · subst R
    have hz : (realMatrix F).rank = 0 := Nat.eq_zero_of_le_zero hrank
    have hsub : zeroDomains F ⊆ ({Finset.univ} : Finset (Finset Y)) := by
      intro S hS
      obtain ⟨U, _, rfl⟩ := Finset.mem_image.mp hS
      have heq : leafDomain F U false = Finset.univ := by
        ext y
        simp [mem_leafDomain, RankLeaves.eq_false_of_rank_zero F hz]
      simp [heq]
    calc
      (zeroDomains F).card ≤ ({Finset.univ} : Finset (Finset Y)).card :=
        Finset.card_le_card hsub
      _ = (0 + 1) ^ 0 := by simp
  · exact zeroDomains_card_le_pos F R (Nat.one_le_iff_ne_zero.mpr hR) hrank

/-- Both leaf output bits are counted as common-zero conditions, with the
one-output condition formed from the Boolean complement. -/
theorem leafDomains_card_le_new (F : X → Y → Bool) (r : ℕ)
    (hrank : (realMatrix F).rank ≤ r) :
    (leafDomains F).card ≤ 2 * (r + 2) ^ (r + 1) := by
  classical
  let Fc : X → Y → Bool := fun x y => !(F x y)
  have hcrank : (realMatrix Fc).rank ≤ r + 1 := by
    have h := Paper2.rank_le_complement_rank_add_one Fc
    have hn : (realMatrix fun x y => !(Fc x y)).rank = (realMatrix F).rank := by
      congr 1
      ext x y
      simp [Fc]
    rw [hn] at h
    omega
  have hsub : leafDomains F ⊆ zeroDomains F ∪ zeroDomains Fc := by
    intro S hS
    obtain ⟨⟨U, b⟩, _, rfl⟩ := Finset.mem_image.mp hS
    cases b with
    | false =>
        exact Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨U, Finset.mem_univ _, rfl⟩)
    | true =>
        apply Finset.mem_union_right
        have heq : leafDomain F U true = leafDomain Fc U false := by
          ext y
          simp [mem_leafDomain, Fc]
        rw [heq]
        exact Finset.mem_image.mpr ⟨U, Finset.mem_univ _, rfl⟩
  have h0 := zeroDomains_card_le F r hrank
  have h1 := zeroDomains_card_le Fc (r + 1) hcrank
  have hp : (r + 1) ^ r ≤ (r + 2) ^ (r + 1) := by
    calc
      (r + 1) ^ r ≤ (r + 2) ^ r := Nat.pow_le_pow_left (by omega) r
      _ ≤ (r + 2) ^ (r + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  calc
    (leafDomains F).card ≤ (zeroDomains F ∪ zeroDomains Fc).card :=
      Finset.card_le_card hsub
    _ ≤ (zeroDomains F).card + (zeroDomains Fc).card := Finset.card_union_le _ _
    _ ≤ (r + 1) ^ r + (r + 2) ^ (r + 1) := Nat.add_le_add h0 h1
    _ ≤ 2 * (r + 2) ^ (r + 1) := by omega

/-- The manuscript's ceiling is the base-two ceiling logarithm. -/
def leafBits (r : ℕ) : ℕ := 1 + (r + 1) * Nat.clog 2 (r + 2)

def rankCountExponent (r t : ℕ) : ℕ :=
  (2 + (r + 1) * Nat.clog 2 (r + 2)) * 2 ^ t

theorem leafDomains_card_le_pow (F : X → Y → Bool) (r : ℕ)
    (hrank : (realMatrix F).rank ≤ r) :
    (leafDomains F).card ≤ 2 ^ leafBits r := by
  have hb : r + 2 ≤ 2 ^ Nat.clog 2 (r + 2) :=
    Nat.le_pow_clog (by decide : 1 < 2) (r + 2)
  have hp := Nat.pow_le_pow_left hb (r + 1)
  have hn : 2 * (r + 2) ^ (r + 1) ≤ 2 ^ leafBits r := by
    calc
      2 * (r + 2) ^ (r + 1) ≤
          2 * (2 ^ Nat.clog 2 (r + 2)) ^ (r + 1) :=
        Nat.mul_le_mul_left _ hp
      _ = 2 ^ leafBits r := by
        rw [← pow_mul, Nat.mul_comm (Nat.clog 2 (r + 2)) (r + 1)]
        rw [← pow_succ']
        simp only [leafBits]
        congr 1
        omega
  exact (leafDomains_card_le_new F r hrank).trans hn

/-- The full v37 count ranges over all retained row sets and every
depth-at-most-t partial protocol, including transcript-dependent speakers. -/
theorem compatibleDomains_card_le_new (F : X → Y → Bool) (r t : ℕ)
    (hrank : (realMatrix F).rank ≤ r) :
    (Paper2.compatibleDomains F t).ncard ≤ 2 ^ rankCountExponent r t := by
  classical
  let leaf : ↥(leafDomains F) → Set Y := fun a => (↑a.val : Set Y)
  have hsub := Paper2.compatibleDomains_subset_formula_domains F leaf
    (Paper2.leaf_catalogue_covers F) t
  have hcard : Fintype.card ↥(leafDomains F) ≤ 2 ^ leafBits r := by
    simpa only [Fintype.card_coe] using leafDomains_card_le_pow F r hrank
  have hf := Paper2.formula_domains_card_le leaf (leafBits r) t hcard
  have he : (leafBits r + 1) * 2 ^ t - 1 ≤ rankCountExponent r t := by
    have heq : leafBits r + 1 = 2 + (r + 1) * Nat.clog 2 (r + 2) := by
      unfold leafBits
      omega
    rw [heq]
    unfold rankCountExponent
    exact Nat.sub_le _ _
  calc
    (Paper2.compatibleDomains F t).ncard ≤
        (Set.range (Paper2.CompleteFormula.eval leaf (t := t))).ncard :=
      Set.ncard_le_ncard hsub (Set.finite_range _)
    _ ≤ 2 ^ ((leafBits r + 1) * 2 ^ t - 1) := hf
    _ ≤ 2 ^ rankCountExponent r t := Nat.pow_le_pow_right (by omega) he

/-- The exact count and coverage interface for the v37 sampling consumer. -/
theorem exists_compatible_cover_new (F : X → Y → Bool) (r t : ℕ)
    (hrank : (realMatrix F).rank ≤ r) :
    ∃ C : Finset (Set Y),
      C.card ≤ 2 ^ rankCountExponent r t ∧
      ∀ (U : Set X) (P : Paper2.PartialProtocol X),
        P.cost ≤ t → P.compatible F U ∈ C := by
  classical
  let C := (Paper2.compatibleDomains_finite F t).toFinset
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    rw [← Set.ncard_eq_toFinset_card]
    exact compatibleDomains_card_le_new F r t hrank
  · intro U P hP
    change P.compatible F U ∈ (Paper2.compatibleDomains_finite F t).toFinset
    rw [Set.Finite.mem_toFinset]
    exact ⟨U, P, hP, rfl⟩

def compressionEntropyV37 (r H : ℕ) : ℕ := rankCountExponent r (H - 1)

/-- The least dyadic integer above `8Z`; the zero argument is not used by
the sampling theorem. -/
def squareDraws (Z : ℕ) : ℕ := 2 ^ Nat.clog 2 (8 * Z)

theorem squareDraws_cover (Z : ℕ) : 8 * Z ≤ squareDraws Z := by
  exact Nat.le_pow_clog (by decide : 1 < 2) (8 * Z)

theorem squareDraws_le_pow (Z k : ℕ) (h : 8 * Z ≤ 2 ^ k) :
    squareDraws Z ≤ 2 ^ k := by
  unfold squareDraws
  exact Nat.pow_le_pow_right (by omega)
    ((Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr h)

theorem compressionEntropyV37_ge_three (r H : ℕ) :
    3 ≤ compressionEntropyV37 r H := by
  have hb : 1 ≤ Nat.clog 2 (r + 2) := by
    have h := Nat.le_pow_clog (by decide : 1 < 2) (r + 2)
    by_contra hn
    have hz : Nat.clog 2 (r + 2) = 0 := by omega
    simp [hz] at h
  have hp : 1 ≤ 2 ^ (H - 1) := Nat.one_le_pow _ _ (by omega)
  have hf : 3 ≤ 2 + (r + 1) * Nat.clog 2 (r + 2) := by nlinarith
  have hm := Nat.mul_le_mul_left (2 + (r + 1) * Nat.clog 2 (r + 2)) hp
  unfold compressionEntropyV37 rankCountExponent
  omega

theorem square_sampling_numeric (Z m : ℕ) (hZ : 3 ≤ Z) (hm : 8 * Z ≤ m) :
    2 * ((2 : ℝ) ^ Z * (3 / 5 : ℝ) ^ m) < 1 / 100 := by
  have hpow : (3 / 5 : ℝ) ^ m ≤ (3 / 5 : ℝ) ^ (8 * Z) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
  have hb : (2 : ℝ) * (3 / 5 : ℝ) ^ 8 ≤ 1 / 8 := by norm_num
  have hbase : ((2 : ℝ) * (3 / 5 : ℝ) ^ 8) ^ Z ≤ (1 / 8 : ℝ) ^ Z :=
    pow_le_pow_left₀ (by positivity) hb _
  have htail : (1 / 8 : ℝ) ^ Z ≤ (1 / 8 : ℝ) ^ 3 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hZ
  calc
    2 * ((2 : ℝ) ^ Z * (3 / 5 : ℝ) ^ m) ≤
        2 * ((2 : ℝ) ^ Z * (3 / 5 : ℝ) ^ (8 * Z)) := by
      gcongr
    _ = 2 * ((2 : ℝ) * (3 / 5 : ℝ) ^ 8) ^ Z := by
      rw [pow_mul, mul_pow]
    _ ≤ 2 * (1 / 8 : ℝ) ^ Z := by gcongr
    _ ≤ 2 * (1 / 8 : ℝ) ^ 3 := by gcongr
    _ < 1 / 100 := by norm_num

/-- The v37 square-sample compression failure bound. The only hypotheses
are the rank bound and the manuscript's robust restriction lower bound. -/
theorem square_compression_failure (F : X → Y → Bool)
    (μX : Paper2.FiniteLaw X) (μY : Paper2.FiniteLaw Y) (r H : ℕ)
    (hH : 1 ≤ H)
    (hrank : (realMatrix F).rank ≤ r)
    (hrobust : ∀ U V, (3 / 5 : ℝ) ≤ μX.prob (· ∈ U) →
      (3 / 5 : ℝ) ≤ μY.prob (· ∈ V) →
      H ≤ Paper2.Compression.restrictionD F U V) :
    let Z := compressionEntropyV37 r H
    let m := squareDraws Z
    ((μY.iid m).prod (μX.iid m)).prob
      (fun z => Workspace.Types.CommComplexity.D (Paper2.sampleMatrix F z.2 z.1) < H) <
      1 / 100 := by
  classical
  dsimp
  let Z := compressionEntropyV37 r H
  let m := squareDraws Z
  let e : ℝ := (2 ^ Z : ℕ) * (3 / 5 : ℝ) ^ m
  have hZ : 3 ≤ Z := compressionEntropyV37_ge_three r H
  have hm : 8 * Z ≤ m := squareDraws_cover Z
  have hfirst : (μY.iid m).prob
      (fun ys => ¬ Paper2.Compression.ColumnGood F μX (3 / 5) H ys) ≤ e := by
    obtain ⟨s, hcard, hcover⟩ := exists_compatible_cover_new F r (H - 1) hrank
    exact Paper2.Compression.first_failure_le (n := m) F μX μY (3 / 5) (3 / 5)
      H (2 ^ Z) hH (by norm_num) hrobust s hcard hcover
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
      exists_compatible_cover_new (fun j x => F x (ys j)) r (H - 1) hrank'
    exact Paper2.Compression.second_failure_le (m := m) F μX (3 / 5) H
      (2 ^ Z) hH (by norm_num) ys hgood s hcard hcover
  have ht := Paper2.FiniteLaw.two_stage_failure_le (μY.iid m) (μX.iid m)
    (Paper2.Compression.ColumnGood F μX (3 / 5) H)
    (fun ys xs => Workspace.Types.CommComplexity.D
      (Paper2.sampleMatrix F xs ys) < H)
    e e hfirst hsecond (by positivity)
  have hn : e + e < (1 / 100 : ℝ) := by
    dsimp [e]
    have hs := square_sampling_numeric Z m hZ hm
    simpa only [Nat.cast_pow, Nat.cast_ofNat, ← two_mul] using hs
  exact ht.trans_lt hn

omit [Fintype X] [Fintype Y] in
/-- Every deterministic protocol on the original table restricts to every
indexed square sample at exactly the same cost, including repeated labels. -/
theorem square_sample_upper {m : ℕ} (F : X → Y → Bool)
    (P : Protocol X Y Bool) (hP : P.Computes F)
    (xs : Fin m → X) (ys : Fin m → Y) :
    ∃ Q : Protocol (Fin m) (Fin m) Bool,
      Q.cost = P.cost ∧ Q.Computes (Paper2.sampleMatrix F xs ys) := by
  exact Paper2.PartialProtocol.restriction_upper F P hP xs ys

end CurrentAdditive.V37RankCount

#print axioms CurrentAdditive.V37RankCount.zeroDomains_card_le
#print axioms CurrentAdditive.V37RankCount.leafDomains_card_le_new
#print axioms CurrentAdditive.V37RankCount.compatibleDomains_card_le_new
#print axioms CurrentAdditive.V37RankCount.exists_compatible_cover_new
#print axioms CurrentAdditive.V37RankCount.square_compression_failure
#print axioms CurrentAdditive.V37RankCount.square_sample_upper
