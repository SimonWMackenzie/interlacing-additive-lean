import Paper2.AAvgProjectionJ

/-!
# Rational (probability-threshold) forms of the `cl:projection` restriction
estimates (WP-AVG S3, lane a-avg-1)

Frozen v12 source: Appendix A, `cl:rational-laws` (IA:252-256): "The
estimates for interlacing restrictions in this appendix apply to finite input
sets with positive rational probabilities, provided their profile hypotheses
and density thresholds are interpreted as probabilities."

Applied here to the two `cl:projection` restriction estimates that had no
probability form in the admitted set:

* the averaged projection at the matrix level (IA:71-77): the selected
  `l`-element coordinate set `J`, the retained rows of the selected blocks
  with their own row-probability thresholds, the projected columns with the
  averaged probability-defect bound, and the restriction/cost comparison;
* restriction monotonicity `cl:monotonicity` (IA:78-82) in member form:
  every restriction with `p` blocks, row probability at least `x` in each
  block and column probability at least `z` yields one with `p' <= p`
  blocks, thresholds `x' <= x`, `z' <= z`, and no larger cost.

Everything is stated on the ORIGINAL rationally weighted inputs and actual
retained sets (arbitrarily correlated column tuples). Column probabilities
use the interlace column law `ν^p` (`iid`).
-/

namespace Paper2.AveragedProjection

open scoped BigOperators
open Workspace.Types.CommComplexity Workspace.Types.Interlace
open ProjectionDefect

section Selected

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

omit [Fintype Y] in
/-- Any injective choice of `r` blocks: the retained rows of the selected
blocks (block `i` is exactly parent block `ι i`), the projected columns, and
injective node maps exhibiting the projected matrix as a restriction of the
parent; hence no larger cost. Law-free. -/
theorem selected_member (F : X → Y → Bool) {p r : ℕ} (ι : Fin r → Fin p)
    (hι : Function.Injective ι)
    (R : Finset (Fin p × X)) (C : Finset (Fin p → Y)) :
    (∀ i : Fin r, ∀ x : X,
      (i, x) ∈ Finset.univ.filter (fun s : Fin r × X => (ι s.1, s.2) ∈ R) ↔
        (ι i, x) ∈ R) ∧
    (∃ (ρ : {s // s ∈ Finset.univ.filter
            (fun s : Fin r × X => (ι s.1, s.2) ∈ R)} → {s // s ∈ R})
        (τ : {d // d ∈ C.image (fun c : Fin p → Y => fun i : Fin r => c (ι i))} →
          {c // c ∈ C}),
      Function.Injective ρ ∧ Function.Injective τ ∧
      NPCC.subgame (interlaceFun F r)
          (Finset.univ.filter (fun s : Fin r × X => (ι s.1, s.2) ∈ R))
          (C.image (fun c : Fin p → Y => fun i : Fin r => c (ι i))) =
        fun s d => NPCC.subgame (interlaceFun F p) R C (ρ s) (τ d)) ∧
    D (NPCC.subgame (interlaceFun F r)
        (Finset.univ.filter (fun s : Fin r × X => (ι s.1, s.2) ∈ R))
        (C.image (fun c : Fin p → Y => fun i : Fin r => c (ι i)))) ≤
      D (NPCC.subgame (interlaceFun F p) R C) := by
  classical
  set π : (Fin p → Y) → (Fin r → Y) := fun c i => c (ι i) with hπdef
  set R' : Finset (Fin r × X) :=
    Finset.univ.filter (fun s : Fin r × X => (ι s.1, s.2) ∈ R) with hR'def
  set C' : Finset (Fin r → Y) := C.image π with hC'def
  have hblock : ∀ i : Fin r, ∀ x : X, (i, x) ∈ R' ↔ (ι i, x) ∈ R := by
    intro i x
    simp [R']
  have hpre : ∀ d ∈ C', ∃ c ∈ C, π c = d := fun d hd => Finset.mem_image.mp hd
  choose g hgC hgπ using hpre
  let ρ : {s // s ∈ R'} → {s // s ∈ R} := fun s =>
    ⟨(ι s.1.1, s.1.2), (Finset.mem_filter.mp s.2).2⟩
  let τ : {d // d ∈ C'} → {c // c ∈ C} := fun d => ⟨g d.1 d.2, hgC d.1 d.2⟩
  have hρ : Function.Injective ρ := by
    rintro ⟨⟨a1, a2⟩, ha⟩ ⟨⟨b1, b2⟩, hb⟩ h
    have h' := congrArg Subtype.val h
    simp only [ρ, Prod.mk.injEq] at h'
    obtain ⟨h1, h2⟩ := h'
    have h1' : a1 = b1 := hι h1
    subst h1' h2
    rfl
  have hτ : Function.Injective τ := by
    rintro ⟨d, hd⟩ ⟨d', hd'⟩ h
    have h' : g d hd = g d' hd' := congrArg Subtype.val h
    have : d = d' := by
      rw [← hgπ d hd, ← hgπ d' hd', h']
    subst this
    rfl
  have heq : NPCC.subgame (interlaceFun F r) R' C' = fun s d =>
      NPCC.subgame (interlaceFun F p) R C (ρ s) (τ d) := by
    funext s d
    change F s.1.2 (d.1 s.1.1) = F s.1.2 (g d.1 d.2 (ι s.1.1))
    exact congrArg (F s.1.2) (congrFun (hgπ d.1 d.2) s.1.1).symm
  refine ⟨hblock, ⟨ρ, τ, hρ, hτ, heq⟩, ?_⟩
  rw [heq]
  exact NPCC.D_mapNodes_le _ ρ τ

/-- Row-probability thresholds of the selected blocks are kept exactly, for
any row law. -/
theorem selected_rows_prob (μ : FiniteLaw X) {p r : ℕ} (ι : Fin r → Fin p)
    (R : Finset (Fin p × X)) (i : Fin r) :
    μ.prob (fun x => (i, x) ∈
        Finset.univ.filter (fun s : Fin r × X => (ι s.1, s.2) ∈ R)) =
      μ.prob (fun x => (ι i, x) ∈ R) := by
  classical
  congr 1
  funext x
  apply propext
  simp

end Selected

section ColumnLaw

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

omit [DecidableEq Y] in
theorem iid_eq_pi (ν : FiniteLaw Y) (m : ℕ) :
    ν.iid m = FiniteLaw.pi (fun _ : Fin m => ν) := rfl

/-- Specified projection in the `iid` column-law form: an injective choice of
coordinates cannot lose column probability. -/
theorem iid_prob_le_selected (ν : FiniteLaw Y) {p r : ℕ} (ι : Fin r → Fin p)
    (hι : Function.Injective ι) (C : Finset (Fin p → Y)) :
    (ν.iid p).prob (· ∈ C) ≤
      (ν.iid r).prob (· ∈ C.image (fun c : Fin p → Y => fun i : Fin r => c (ι i))) := by
  classical
  calc
    (ν.iid p).prob (· ∈ C) ≤ (ν.iid p).prob (fun x =>
        (fun j => x (ι j)) ∈ C.image (fun c : Fin p → Y => fun i : Fin r => c (ι i))) := by
      apply FiniteLaw.prob_mono
      intro x hx
      exact Finset.mem_image_of_mem _ hx
    _ = (FiniteLaw.pi (fun _ : Fin r => ν)).prob
        (· ∈ C.image (fun c : Fin p → Y => fun i : Fin r => c (ι i))) := by
      rw [iid_eq_pi]
      exact FiniteLaw.pi_prob_restrict (fun _ : Fin p => ν) ι hι _
    _ = _ := by rw [iid_eq_pi]

end ColumnLaw

section RationalMembers

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

/-- **Rational averaged projection at the matrix level (T38 blanket applied
to IA:71-77; U06, U09).** Original rationally weighted inputs; `R` has row
probability at least `x` in every block and `C` is a nonempty, arbitrarily
correlated retained tuple set. Some `l`-element coordinate set `J` (listed
increasingly) gives a restriction on `l` blocks with row probability at least
`x` in every block, column probability-defect at most `(l/p)` times the
parent's, realized as a restriction of the parent through injective node
maps, and of no larger cost. -/
theorem rational_averaged_member_J (μ : PositiveRationalLaw X)
    (ν : PositiveRationalLaw Y) (F : X → Y → Bool) (p l : ℕ) (x : ℝ)
    (hl : 1 ≤ l) (hlp : l ≤ p)
    (R : Finset (Fin p × X)) (C : Finset (Fin p → Y))
    (hR : ∀ i, x ≤ μ.toFiniteLaw.prob (fun a => (i, a) ∈ R)) (hC : C.Nonempty) :
    ∃ (J : Finset (Fin p)) (hJ : J.card = l),
      (∀ i : Fin l, x ≤ μ.toFiniteLaw.prob (fun a => (i, a) ∈
        Finset.univ.filter (fun s : Fin l × X => (J.orderEmbOfFin hJ s.1, s.2) ∈ R))) ∧
      defect ((ν.toFiniteLaw.iid l).prob
          (· ∈ C.image (fun c : Fin p → Y => fun i : Fin l =>
            c (J.orderEmbOfFin hJ i)))) ≤
        ((l : ℝ) / (p : ℝ)) * defect ((ν.toFiniteLaw.iid p).prob (· ∈ C)) ∧
      (∃ (ρ : {s // s ∈ Finset.univ.filter
              (fun s : Fin l × X => (J.orderEmbOfFin hJ s.1, s.2) ∈ R)} → {s // s ∈ R})
          (τ : {d // d ∈ C.image (fun c : Fin p → Y => fun i : Fin l =>
              c (J.orderEmbOfFin hJ i))} → {c // c ∈ C}),
        Function.Injective ρ ∧ Function.Injective τ ∧
        NPCC.subgame (interlaceFun F l)
            (Finset.univ.filter (fun s : Fin l × X => (J.orderEmbOfFin hJ s.1, s.2) ∈ R))
            (C.image (fun c : Fin p → Y => fun i : Fin l => c (J.orderEmbOfFin hJ i))) =
          fun s d => NPCC.subgame (interlaceFun F p) R C (ρ s) (τ d)) ∧
      D (NPCC.subgame (interlaceFun F l)
          (Finset.univ.filter (fun s : Fin l × X => (J.orderEmbOfFin hJ s.1, s.2) ∈ R))
          (C.image (fun c : Fin p → Y => fun i : Fin l => c (J.orderEmbOfFin hJ i)))) ≤
        D (NPCC.subgame (interlaceFun F p) R C) := by
  obtain ⟨J, hJ, hdef⟩ := rational_averaged_projection ν p l hl hlp C hC
  obtain ⟨_, hiso, hD⟩ := selected_member F (fun i => J.orderEmbOfFin hJ i)
    (J.orderEmbOfFin hJ).injective R C
  refine ⟨J, hJ, ?_, hdef, hiso, hD⟩
  intro i
  rw [selected_rows_prob]
  exact hR _

/-- **Rational restriction monotonicity (T38 blanket applied to
`cl:monotonicity`, IA:78-82), member form.** If `p' <= p`, `x' <= x`,
`z' <= z`, every restriction with `p` blocks, row probability at least `x`
in each block and column probability at least `z` yields an actual
restriction with `p'` blocks meeting the thresholds `x'`, `z'` and of no
larger cost. (Hence the probability-threshold family minima satisfy
`D_M(p';x',z') <= D_M(p;x,z)`.) -/
theorem rational_monotonicity_member (μ : PositiveRationalLaw X)
    (ν : PositiveRationalLaw Y) (F : X → Y → Bool) (p p' : ℕ) (x x' z z' : ℝ)
    (hp : p' ≤ p) (hx : x' ≤ x) (hz : z' ≤ z)
    (R : Finset (Fin p × X)) (C : Finset (Fin p → Y))
    (hR : ∀ i, x ≤ μ.toFiniteLaw.prob (fun a => (i, a) ∈ R))
    (hC : z ≤ (ν.toFiniteLaw.iid p).prob (· ∈ C)) :
    ∃ (R' : Finset (Fin p' × X)) (C' : Finset (Fin p' → Y)),
      (∀ i, x' ≤ μ.toFiniteLaw.prob (fun a => (i, a) ∈ R')) ∧
      z' ≤ (ν.toFiniteLaw.iid p').prob (· ∈ C') ∧
      D (NPCC.subgame (interlaceFun F p') R' C') ≤
        D (NPCC.subgame (interlaceFun F p) R C) := by
  classical
  let ι : Fin p' → Fin p := Fin.castLE hp
  have hι : Function.Injective ι := Fin.castLE_injective hp
  obtain ⟨_, _, hD⟩ := selected_member F ι hι R C
  refine ⟨_, _, ?_, ?_, hD⟩
  · intro i
    rw [selected_rows_prob]
    exact hx.trans (hR _)
  · exact hz.trans (hC.trans (iid_prob_le_selected ν.toFiniteLaw ι hι C))

end RationalMembers

end Paper2.AveragedProjection

#print axioms Paper2.AveragedProjection.selected_member
#print axioms Paper2.AveragedProjection.selected_rows_prob
#print axioms Paper2.AveragedProjection.iid_prob_le_selected
#print axioms Paper2.AveragedProjection.rational_averaged_member_J
#print axioms Paper2.AveragedProjection.rational_monotonicity_member
