import Paper2.ProjectionDefect
import Paper2.DefectInductionRational
import Workspace.Projections
import NPCC.Twin

/-!
# Averaged projection with an explicit coordinate set (WP-AVG, lane a-avg-1)

Frozen v12 source: Appendix A, `cl:projection`, display
`cl:average-projection` (IA:71-75):

  "For every integer 1 <= l <= p, some l-element set J satisfies
   Delta_l(pi_J K) <= (l/p) Delta_p(K)."

and IA:76-77 ("Each projected matrix, with arbitrary retained rows in its
selected blocks, is isomorphic to a restriction of the original matrix"),
now with the coordinate set `J` named in the conclusion.

The projected word `pi_J K` is rendered with its `l` coordinates listed in
increasing order, `c ↦ (i ↦ c (J.orderEmbOfFin hJ i))`; the subtype form
`c ↦ (j : J ↦ c j)` of `ProjectionDefect.specified_columns` is also given
(same cardinality).

The counting input is the admitted Shearer-type
`Workspace.Projections.corollary_3_19` (the same engine the admitted
`EthBridge.member_max_projection` consumes), applied to the graph encoding
of the retained words; no new lower-bound or density premise is introduced.

Positive rational laws (`cl:rational-laws`, IA:252-256, blanket clause
"density thresholds are interpreted as probabilities") are handled by the
admitted all-copies lift `RationalSeparation.liftSet (ν.forgetTuple p)` and
the admitted exact transport `DefectInduction.lifted_columnDensity`.
-/

namespace Paper2.AveragedProjection

open scoped BigOperators
open Workspace.Types.CommComplexity Workspace.Types.Interlace
open ProjectionDefect

section Counting

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- Shearer-type counting with the selected coordinate set named: some
`l`-element set `J` has at least `|K|^(l/p)` distinct projected words. -/
theorem card_image_orderEmb_ge {p l : ℕ} (hl : 1 ≤ l) (hlp : l ≤ p)
    (K : Finset (Fin p → Y)) :
    ∃ (J : Finset (Fin p)) (hJ : J.card = l),
      (K.card : ℝ) ^ ((l : ℝ) / (p : ℝ)) ≤
        ((K.image (fun c : Fin p → Y => fun i : Fin l =>
          c (J.orderEmbOfFin hJ i))).card : ℝ) := by
  classical
  let eY : Fin (Fintype.card Y) ≃ Y := (Fintype.equivFin Y).symm
  let graph : (Fin p → Y) → Finset (Fin (Fintype.card Y) × Fin p) :=
    fun c => Finset.univ.filter fun z => eY z.1 = c z.2
  let F : Finset (Finset (Fin (Fintype.card Y) × Fin p)) := K.image graph
  have hgraph_inj : Function.Injective graph := by
    intro c d hcd
    funext q
    have hc : (eY.symm (c q), q) ∈ graph c := by
      simp [graph]
    rw [hcd] at hc
    simpa [graph] using hc
  have hFcard : F.card = K.card := by
    simp only [F]
    exact Finset.card_image_of_injective _ hgraph_inj
  obtain ⟨Q, hQcard, hQbound⟩ :=
    Workspace.Projections.corollary_3_19 F l hl hlp
  refine ⟨Q, hQcard, ?_⟩
  let ι : Fin l → Fin p := fun i => Q.orderEmbOfFin hQcard i
  have hιmem : ∀ i, ι i ∈ Q := fun i => Q.orderEmbOfFin_mem hQcard i
  have hιsurj : ∀ q ∈ Q, ∃ i, ι i = q := by
    intro q hq
    have hr : q ∈ Set.range (Q.orderEmbOfFin hQcard) := by
      rw [Finset.range_orderEmbOfFin]
      exact hq
    obtain ⟨i, hi⟩ := hr
    exact ⟨i, hi⟩
  have hι_inj : Function.Injective ι := (Q.orderEmbOfFin hQcard).injective
  let π : (Fin p → Y) → (Fin l → Y) := fun c i => c (ι i)
  let C' : Finset (Fin l → Y) := K.image π
  let pgraph : (Fin l → Y) → Finset (Fin (Fintype.card Y) × Fin p) :=
    fun d => Finset.univ.image fun i : Fin l => (eY.symm (d i), ι i)
  have hpgraph_inj : Function.Injective pgraph := by
    intro d d' hdd'
    funext i
    have hm : (eY.symm (d i), ι i) ∈ pgraph d := by
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    rw [hdd'] at hm
    simp only [pgraph, Finset.mem_image, Finset.mem_univ, true_and] at hm
    obtain ⟨j, hj⟩ := hm
    have hij : j = i := hι_inj (congrArg Prod.snd hj)
    subst j
    exact eY.symm.injective (congrArg Prod.fst hj).symm
  have hfiltered : ∀ c : Fin p → Y,
      (graph c).filter (fun z => z.2 ∈ Q) = pgraph (π c) := by
    intro c
    ext z
    constructor
    · intro hz
      obtain ⟨hzgraph, hzQ⟩ := Finset.mem_filter.mp hz
      have hzval : eY z.1 = c z.2 := by simpa [graph] using hzgraph
      obtain ⟨i, hi⟩ := hιsurj z.2 hzQ
      apply Finset.mem_image.mpr
      refine ⟨i, Finset.mem_univ _, ?_⟩
      apply Prod.ext
      · apply eY.injective
        simp only [Equiv.apply_symm_apply, π]
        rw [hi, hzval]
      · exact hi
    · intro hz
      simp only [pgraph, Finset.mem_image] at hz
      obtain ⟨i, _, hi⟩ := hz
      have hi1 := congrArg Prod.fst hi
      have hi2 := congrArg Prod.snd hi
      have hi2' : ι i = z.2 := by simpa using hi2
      have hzQ : z.2 ∈ Q := by
        rw [← hi2']
        exact hιmem i
      apply Finset.mem_filter.mpr
      refine ⟨?_, hzQ⟩
      simp only [graph, Finset.mem_filter, Finset.mem_univ, true_and]
      have hval : π c i = eY z.1 := by
        simpa using congrArg eY hi1
      change c (ι i) = eY z.1 at hval
      rw [← hval, hi2']
  have hproj_eq :
      F.image (fun S => S.filter (fun z => z.2 ∈ Q)) = C'.image pgraph := by
    rw [show F = K.image graph from rfl, Finset.image_image]
    rw [show C' = K.image π from rfl, Finset.image_image]
    apply Finset.image_congr
    intro c _
    exact hfiltered c
  have hprojcard :
      (F.image (fun S => S.filter (fun z => z.2 ∈ Q))).card = C'.card := by
    rw [hproj_eq, Finset.card_image_of_injective _ hpgraph_inj]
  have hmain : (K.card : ℝ) ^ ((l : ℝ) / (p : ℝ)) ≤ (C'.card : ℝ) := by
    rw [← hprojcard, ← hFcard]
    exact hQbound
  exact hmain

omit [Fintype Y] in
/-- The listed-coordinate and subtype renderings of `pi_J K` have the same
number of words. -/
theorem card_image_orderEmb_eq_subtype {p l : ℕ} (K : Finset (Fin p → Y))
    (J : Finset (Fin p)) (hJ : J.card = l) :
    (K.image (fun c : Fin p → Y => fun i : Fin l => c (J.orderEmbOfFin hJ i))).card =
      (K.image (fun x : Fin p → Y => fun j : J => x j.val)).card := by
  classical
  let σ := J.orderIsoOfFin hJ
  let e : (Fin l → Y) → (J → Y) := fun d j => d (σ.symm j)
  have he : Function.Injective e := by
    intro d d' h
    funext i
    have := congrFun h (σ i)
    simpa [e] using this
  have hcomp : ∀ c : Fin p → Y,
      e (fun i => c (J.orderEmbOfFin hJ i)) = fun j : J => c j.val := by
    intro c
    funext j
    simp only [e]
    congr 1
    rw [← Finset.coe_orderIsoOfFin_apply]
    simp [σ]
  rw [← Finset.card_image_of_injective _ he, Finset.image_image]
  apply congrArg Finset.card
  apply Finset.image_congr
  intro c _
  exact hcomp c

end Counting

section Uniform

variable {Y : Type*} [Fintype Y] [DecidableEq Y] [Nonempty Y]

omit [DecidableEq Y] [Nonempty Y] in
private theorem card_pow_rpow (p l : ℕ) (hp : 0 < p) :
    ((Fintype.card Y : ℝ) ^ p) ^ ((l : ℝ) / (p : ℝ)) =
      (Fintype.card Y : ℝ) ^ l := by
  have hn0 : (0 : ℝ) ≤ Fintype.card Y := Nat.cast_nonneg _
  rw [show (Fintype.card Y : ℝ) ^ p = (Fintype.card Y : ℝ) ^ (p : ℝ) from
    (Real.rpow_natCast _ _).symm]
  rw [← Real.rpow_mul hn0]
  rw [show (p : ℝ) * ((l : ℝ) / (p : ℝ)) = (l : ℝ) by
    field_simp]
  exact Real.rpow_natCast _ _

/-- Mass form of `cl:average-projection` with `J` named:
`(|K|/n^p)^(l/p) <= |pi_J K| / n^l`. -/
theorem averaged_projection_J_mass (p l : ℕ) (hl : 1 ≤ l) (hlp : l ≤ p)
    (K : Finset (Fin p → Y)) :
    ∃ (J : Finset (Fin p)) (hJ : J.card = l),
      (columnDensity p K) ^ ((l : ℝ) / (p : ℝ)) ≤
        columnDensity l (K.image (fun c : Fin p → Y => fun i : Fin l =>
          c (J.orderEmbOfFin hJ i))) := by
  obtain ⟨J, hJ, hcard⟩ := card_image_orderEmb_ge hl hlp K
  refine ⟨J, hJ, ?_⟩
  have hp : 0 < p := lt_of_lt_of_le hl hlp
  have hn : 0 < (Fintype.card Y : ℝ) := by exact_mod_cast Fintype.card_pos
  unfold columnDensity
  rw [Real.div_rpow (Nat.cast_nonneg _) (pow_nonneg hn.le _), card_pow_rpow p l hp]
  exact div_le_div_of_nonneg_right hcard (pow_nonneg hn.le _)

/-- **T08 averaged clause (IA:71-75), with the coordinate set explicit.**
For every integer `1 <= l <= p` and nonempty `K ⊆ Y^p`, some `l`-element
`J ⊆ [p]` satisfies `Delta_l(pi_J K) <= (l/p) Delta_p(K)`. -/
theorem averaged_projection_J (p l : ℕ) (hl : 1 ≤ l) (hlp : l ≤ p)
    (K : Finset (Fin p → Y)) (hK : K.Nonempty) :
    ∃ (J : Finset (Fin p)) (hJ : J.card = l),
      defect (columnDensity l (K.image (fun c : Fin p → Y => fun i : Fin l =>
          c (J.orderEmbOfFin hJ i)))) ≤
        ((l : ℝ) / (p : ℝ)) * defect (columnDensity p K) := by
  obtain ⟨J, hJ, hmass⟩ := averaged_projection_J_mass p l hl hlp K
  refine ⟨J, hJ, ?_⟩
  have hy := columnDensity_pos p hK
  calc
    _ ≤ defect ((columnDensity p K) ^ ((l : ℝ) / (p : ℝ))) :=
      defect_antitone (Real.rpow_pos_of_pos hy _) hmass
    _ = _ := defect_rpow hy _

/-- The same clause in the literal logarithmic form of the appendix,
`log (n^|J| / |pi_J K|) <= (l/p) log (n^p/|K|)`, with `pi_J K ⊆ Y^J` the
subtype projection used by `ProjectionDefect.specified_columns`. -/
theorem averaged_projection_J_columns (p l : ℕ) (hl : 1 ≤ l) (hlp : l ≤ p)
    (K : Finset (Fin p → Y)) (hK : K.Nonempty) :
    ∃ J : Finset (Fin p), J.card = l ∧
      Real.logb 2 ((Fintype.card Y : ℝ) ^ J.card /
        ((K.image (fun x : Fin p → Y => fun i : J => x i.val)).card : ℝ)) ≤
      ((l : ℝ) / (p : ℝ)) *
        Real.logb 2 ((Fintype.card Y : ℝ) ^ p / (K.card : ℝ)) := by
  obtain ⟨J, hJ, h⟩ := averaged_projection_J p l hl hlp K hK
  refine ⟨J, hJ, ?_⟩
  rw [defect_columnDensity, defect_columnDensity,
    card_image_orderEmb_eq_subtype K J hJ] at h
  rw [hJ]
  exact h

end Uniform

section ActualMatrices

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  [Nonempty Y]

/-- **T08 averaged clause together with IA:76-77, `J` explicit.**
The selected `l`-element set `J`, listed increasingly by `ι`, gives:
the projected columns `C' = pi_J C` with the averaged defect bound; the
retained rows `R'` of the selected blocks (block `i` of `R'` is exactly
block `ι i` of `R`, so any row floor is kept); injective node maps
`ρ`, `τ` (one actual representative column per projected word) exhibiting
the projected matrix as the restriction of the original one to their
images; hence its cost is at most the parent's. -/
theorem averaged_member_J (F : X → Y → Bool) (p l T : ℕ)
    (hl : 1 ≤ l) (hlp : l ≤ p)
    (R : Finset (Fin p × X)) (C : Finset (Fin p → Y))
    (hR : NPCC.IsEquipartitionedGE R Finset.univ T) (hC : C.Nonempty) :
    ∃ (J : Finset (Fin p)) (hJ : J.card = l),
      defect (columnDensity l (C.image (fun c : Fin p → Y => fun i : Fin l =>
          c (J.orderEmbOfFin hJ i)))) ≤
        ((l : ℝ) / (p : ℝ)) * defect (columnDensity p C) ∧
      (∀ i : Fin l, ∀ x : X,
        (i, x) ∈ Finset.univ.filter
            (fun r : Fin l × X => (J.orderEmbOfFin hJ r.1, r.2) ∈ R) ↔
          (J.orderEmbOfFin hJ i, x) ∈ R) ∧
      NPCC.IsEquipartitionedGE (Finset.univ.filter
          (fun r : Fin l × X => (J.orderEmbOfFin hJ r.1, r.2) ∈ R))
        Finset.univ T ∧
      (∃ (ρ : {s // s ∈ Finset.univ.filter
              (fun r : Fin l × X => (J.orderEmbOfFin hJ r.1, r.2) ∈ R)} →
            {r // r ∈ R})
          (τ : {d // d ∈ C.image (fun c : Fin p → Y => fun i : Fin l =>
              c (J.orderEmbOfFin hJ i))} → {c // c ∈ C}),
        Function.Injective ρ ∧ Function.Injective τ ∧
        NPCC.subgame (interlaceFun F l)
            (Finset.univ.filter
              (fun r : Fin l × X => (J.orderEmbOfFin hJ r.1, r.2) ∈ R))
            (C.image (fun c : Fin p → Y => fun i : Fin l =>
              c (J.orderEmbOfFin hJ i))) =
          fun s d => NPCC.subgame (interlaceFun F p) R C (ρ s) (τ d)) ∧
      D (NPCC.subgame (interlaceFun F l)
          (Finset.univ.filter
            (fun r : Fin l × X => (J.orderEmbOfFin hJ r.1, r.2) ∈ R))
          (C.image (fun c : Fin p → Y => fun i : Fin l =>
            c (J.orderEmbOfFin hJ i)))) ≤
        D (NPCC.subgame (interlaceFun F p) R C) := by
  classical
  obtain ⟨J, hJ, hdef⟩ := averaged_projection_J p l hl hlp C hC
  refine ⟨J, hJ, hdef, ?_⟩
  set ι : Fin l → Fin p := fun i => J.orderEmbOfFin hJ i with hιdef
  have hι_inj : Function.Injective ι := (J.orderEmbOfFin hJ).injective
  set π : (Fin p → Y) → (Fin l → Y) := fun c i => c (ι i) with hπdef
  set R' : Finset (Fin l × X) :=
    Finset.univ.filter (fun r : Fin l × X => (ι r.1, r.2) ∈ R) with hR'def
  set C' : Finset (Fin l → Y) := C.image π with hC'def
  have hblock : ∀ i : Fin l, ∀ x : X, (i, x) ∈ R' ↔ (ι i, x) ∈ R := by
    intro i x
    simp [R']
  have hrowR' : NPCC.IsEquipartitionedGE R' Finset.univ T := by
    intro q' _
    refine le_trans (hR (ι q') (Finset.mem_univ _)) ?_
    apply Finset.card_le_card_of_injOn (fun r => (q', r.2))
    · rintro ⟨r1, r2⟩ hr
      simp only [Finset.mem_coe, Finset.mem_filter] at hr
      obtain ⟨hrR, hr1⟩ := hr
      have hr1' : r1 = ι q' := hr1
      subst r1
      change (q', r2) ∈ ↑(R'.filter fun s : Fin l × X => s.1 = q')
      rw [Finset.mem_filter]
      exact ⟨(hblock q' r2).mpr hrR, rfl⟩
    · rintro ⟨r1, r2⟩ hr ⟨r1', r2'⟩ hr' hrr
      simp only [Finset.mem_coe, Finset.mem_filter] at hr hr'
      have h2 : r2 = r2' := congrArg Prod.snd hrr
      have h1 : r1 = r1' := hr.2.trans hr'.2.symm
      exact Prod.ext h1 h2
  have hpre : ∀ d ∈ C', ∃ c ∈ C, π c = d := fun d hd => Finset.mem_image.mp hd
  choose g hgC hgπ using hpre
  let ρ : {s // s ∈ R'} → {r // r ∈ R} := fun s =>
    ⟨(ι s.1.1, s.1.2), (Finset.mem_filter.mp s.2).2⟩
  let τ : {d // d ∈ C'} → {c // c ∈ C} := fun d => ⟨g d.1 d.2, hgC d.1 d.2⟩
  have hρ : Function.Injective ρ := by
    rintro ⟨⟨a1, a2⟩, ha⟩ ⟨⟨b1, b2⟩, hb⟩ h
    have h' := congrArg Subtype.val h
    simp only [ρ, Prod.mk.injEq] at h'
    obtain ⟨h1, h2⟩ := h'
    have h1' : a1 = b1 := hι_inj h1
    subst h1' h2
    rfl
  have hτ : Function.Injective τ := by
    rintro ⟨d, hd⟩ ⟨d', hd'⟩ h
    have h' : g d hd = g d' hd' := congrArg Subtype.val h
    have : d = d' := by
      rw [← hgπ d hd, ← hgπ d' hd', h']
    subst this
    rfl
  have heq : NPCC.subgame (interlaceFun F l) R' C' = fun s d =>
      NPCC.subgame (interlaceFun F p) R C (ρ s) (τ d) := by
    funext s d
    change F s.1.2 (d.1 s.1.1) = F s.1.2 (g d.1 d.2 (ι s.1.1))
    exact congrArg (F s.1.2) (congrFun (hgπ d.1 d.2) s.1.1).symm
  refine ⟨hblock, hrowR', ⟨ρ, τ, hρ, hτ, heq⟩, ?_⟩
  rw [heq]
  exact NPCC.D_mapNodes_le _ ρ τ

end ActualMatrices

section Rational

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

omit [DecidableEq Y] in
private theorem columnDensity_mono [Nonempty Y] (p : ℕ) {A B : Finset (Fin p → Y)}
    (h : A ⊆ B) : columnDensity p A ≤ columnDensity p B := by
  unfold columnDensity
  apply div_le_div_of_nonneg_right _ (pow_nonneg (Nat.cast_nonneg _) _)
  exact_mod_cast Finset.card_le_card h

/-- **Rational averaged projection (T38 blanket applied to
`cl:average-projection`; U06, U09).** For a positive rational column law
`ν` and a nonempty, arbitrarily correlated `K ⊆ Y^p`, some `l`-element
coordinate set `J` has
`ν^l(pi_J K) >= ν^p(K)^(l/p)`, i.e. the defect with the density threshold
read as a probability is at most `(l/p)` times the parent's. -/
theorem rational_averaged_projection_mass (ν : PositiveRationalLaw Y)
    (p l : ℕ) (hl : 1 ≤ l) (hlp : l ≤ p) (K : Finset (Fin p → Y)) :
    ∃ (J : Finset (Fin p)) (hJ : J.card = l),
      ((ν.toFiniteLaw.iid p).prob (· ∈ K)) ^ ((l : ℝ) / (p : ℝ)) ≤
        (ν.toFiniteLaw.iid l).prob
          (· ∈ K.image (fun c : Fin p → Y => fun i : Fin l =>
            c (J.orderEmbOfFin hJ i))) := by
  classical
  let Khat : Finset (Fin p → ν.Copies) :=
    RationalSeparation.liftSet (ν.forgetTuple p) K
  obtain ⟨J, hJ, hmass⟩ := averaged_projection_J_mass p l hl hlp Khat
  refine ⟨J, hJ, ?_⟩
  set ι : Fin l → Fin p := fun i => J.orderEmbOfFin hJ i with hιdef
  have hsub : Khat.image (fun c : Fin p → ν.Copies => fun i : Fin l => c (ι i)) ⊆
      RationalSeparation.liftSet (ν.forgetTuple l)
        (K.image (fun c : Fin p → Y => fun i : Fin l => c (ι i))) := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    rw [RationalSeparation.mem_liftSet] at hz ⊢
    exact Finset.mem_image.mpr ⟨ν.forgetTuple p z, hz, rfl⟩
  have hup := columnDensity_mono l hsub
  rw [DefectInduction.lifted_columnDensity] at hup
  have hbase : columnDensity p Khat = (ν.toFiniteLaw.iid p).prob (· ∈ K) :=
    DefectInduction.lifted_columnDensity ν p K
  rw [← hbase]
  exact le_trans hmass hup

/-- Defect form of the rational averaged projection. -/
theorem rational_averaged_projection (ν : PositiveRationalLaw Y)
    (p l : ℕ) (hl : 1 ≤ l) (hlp : l ≤ p) (K : Finset (Fin p → Y))
    (hK : K.Nonempty) :
    ∃ (J : Finset (Fin p)) (hJ : J.card = l),
      defect ((ν.toFiniteLaw.iid l).prob
          (· ∈ K.image (fun c : Fin p → Y => fun i : Fin l =>
            c (J.orderEmbOfFin hJ i)))) ≤
        ((l : ℝ) / (p : ℝ)) * defect ((ν.toFiniteLaw.iid p).prob (· ∈ K)) := by
  classical
  obtain ⟨J, hJ, hmass⟩ := rational_averaged_projection_mass ν p l hl hlp K
  refine ⟨J, hJ, ?_⟩
  have hy : 0 < (ν.toFiniteLaw.iid p).prob (· ∈ K) := by
    rw [← DefectInduction.lifted_columnDensity ν p K]
    exact columnDensity_pos p (DefectInduction.lifted_columns_nonempty ν p K hK)
  calc
    _ ≤ defect (((ν.toFiniteLaw.iid p).prob (· ∈ K)) ^ ((l : ℝ) / (p : ℝ))) :=
      defect_antitone (Real.rpow_pos_of_pos hy _) hmass
    _ = _ := defect_rpow hy _

end Rational

end Paper2.AveragedProjection

#print axioms Paper2.AveragedProjection.card_image_orderEmb_ge
#print axioms Paper2.AveragedProjection.card_image_orderEmb_eq_subtype
#print axioms Paper2.AveragedProjection.averaged_projection_J_mass
#print axioms Paper2.AveragedProjection.averaged_projection_J
#print axioms Paper2.AveragedProjection.averaged_projection_J_columns
#print axioms Paper2.AveragedProjection.averaged_member_J
#print axioms Paper2.AveragedProjection.rational_averaged_projection_mass
#print axioms Paper2.AveragedProjection.rational_averaged_projection
