import Mathlib
import NPCC.Defs
import NPCC.DefsAux
import NPCC.Complexity
import NPCC.ComplexityAux
import NPCC.Engine
import NPCC.CoordProjection
import NPCC.Stage1
import EthBridge.Arith
import EthBridge.Defs
import EthBridge.Hypotheses
import EthBridge.Bases
import EthBridge.Induction
import EthBridge.Main

/-! # EthBridge Theorem 2 — entry from an arbitrary robust test (Tranche E4)

Statement-only (`sorry`) signatures for the two E4 obligations from
`eth-obligations.json`, drafted for faithfulness sign-off BEFORE any proving
(source: `eth-docs/REENTRY_ROBUSTIFICATION_BY_DIRECT_DEFECT_ACCOUNTING.md`,
§5 "Entry From An Arbitrary Robust Test" (19)–(22) and §6 "A Simple Uniform
Parameter Package" (23)):

* `eth:thm-entry`           — Theorem 2 / (22), split (SEE SPLIT FLAG) into
  - `theorem_two_V`           the V-SIDE core: every restriction of
                              `Interlace(W,Q)` (`Q = 2^R`) with
                              `≥ ⌈Qm·y/2^t⌉` rows and `≥ ⌈n^Q·x_out⌉` columns
                              has complexity `≥ C+R-t`, and
  - `theorem_two`             the thin one-copy TRANSPOSE wrapper landing the
                              note-literal `comp(bracket(R_next,1,x_out,y/2^t))
                              ≥ C+R-t`;
* `eth:lem-uniform-package` — `uniform_package`, (23) ⟹ (21) + `p_t ≤ Q`
                              for `δ < 1/2`, all three `t = 0,1,2`
                              simultaneously.

Entry parameters (note (19)–(20)) as defs, each with arithmetic sanity/unit
lemmas below (BtL discipline):

* `entryDefect`   — `L = ln(1/x_out)`;
* `entryExcess`   — `d = ⌈L/λ⌉`                                   (note (19));
* `entryLevel`    — `a_t = R - t`;
* `entryCopies`   — `p_t = 2^(a_t-1) + d`                         (note (20));
* `entryRowBound` — the (21) LHS `(p-1)·m + (Q-p+1)·(A_a-1)`;
* `goodBlocks`    — the good outer `W` blocks (`≥ A_a` retained rows);
* `Rnext`         — `R_next = transpose(Interlace(W,Q))`          (note §5).

Helper obligations (scout report HB-1…HB-6), each a `sorry` signature:

* `dfamily_one_transpose`    — HB-1: one-copy transpose transport (re-proof of
                               the PRIVATE `NPCC.Dfamily_one_transpose`,
                               Stage2.lean:53; the note's "only one-copy
                               transpose symmetry is used", §8);
* `le_Dfamily`               — HB-2: `Dfamily` lower bound from a ∀-member
                               bound + nonemptiness (`le_csInf` wrapper);
* `filter_fst_fin_one`,
  `card_image_snd_fin_one`,
  `card_image_apply_zero_fin_one`
                             — HB-3: one-copy bracket thresholds transported
                               to the collapsed `(RV,CV)` (the `D`-side of the
                               collapse is the PUBLIC
                               `NPCC.M1_interlace_one_project_le`,
                               Stage1.lean:1710);
* `card_le_entryRowBound_of_few_good`,
  `good_blocks_count`,
  `exists_good_block_choice` — HB-4 (THE genuinely new counting): fewer than
                               `p_t` good blocks caps the row count at the
                               (21) LHS; contrapositive + extraction of an
                               exactly-`p_t` good subset;
* `projected_subgame_le`     — HB-5: `D`-comparison from coordinate-projection
                               provenance (re-proof of the PRIVATE
                               `NPCC.D_projected_subgame_le`, Control.lean:83;
                               body = `D_mapNodes_le`);
* `bracket_subset_stateDensity`
                             — HB-6: `bracketGE X Y p (2^a·x) x_out ⊆
                               stateDensity X Y p a x λ` under
                               `L ≤ c_a(p)·λ`;
* `entry_projected_state`    — the PROJECTED-DEFECT lemma: coordinate
                               projection (`NPCC.coord_projection`,
                               CoordProjection.lean:26) to the `p_t` chosen
                               good blocks keeps total density `≥ x_out`
                               (note §5: "Coordinate projection preserves
                               total density at least `x_out`"), so the
                               projected member lands in the Theorem-1 state
                               family via HB-6.

GLOBAL JUDGE FLAGS (individual flags at each declaration).

* **SPLIT FLAG (flagged per the drafting instruction).** Theorem 2 is drafted
  as `theorem_two_V` (V-side core, no transpose) PLUS the thin wrapper
  `theorem_two` (note-literal (22) form). The wrapper's only content is:
  one-copy transpose transport (HB-1), per-member descent (HB-2 +
  `bracketGE.nonempty`), and the one-copy interlace collapse
  (`M1_interlace_one_project_le` + HB-3 cardinalities). The judge signs BOTH;
  (22) is `theorem_two`.
* **ℕ-subtraction discipline.** `a_t = R - t` is ℕ-subtraction, exact under
  `t ≤ 2 ≤ 4 ≤ R`; the conclusion is phrased `C + (R - t)`, matching the
  note's `C+R-t` (no `C+R` minus `t` truncation hazard: `R - t` is computed
  first, and `hR`/`ht` make it exact). Similarly `p_t - 1`, `Q - p_t + 1`,
  `A - 1` inside `entryRowBound` are exact under `1 ≤ p_t ≤ Q`, `1 ≤ A`
  (hypotheses at the consuming sites).
* **`hax` IS consumed in E4** (unlike E3 per-member): once via
  `rowThreshold … ≤ m + 1` in the good-block counting (each bad block caps at
  `A_(a_t) - 1 ≤ m`), and once forwarded to `theorem_one`. It enters at level
  `a_t = R - t` (the only level Theorem 2 touches for a fixed `t`).
* **Where `x_out < 1` is consumed:** `d = ⌈L/λ⌉ ≥ 1` (`entryExcess_pos`),
  which is exactly what makes `p_t > 2^(a_t-1)` (the doubled-form
  `2^(a_t) < 2·p_t`, `entryCopies_hp`) — Theorem 1's copy-count hypothesis.
* **`d` is the ℕ-ceiling `⌈L/λ⌉₊`.** For `0 < x_out < 1`, `λ > 0` (the only
  regime used) it agrees with the note's real ceiling; at `x_out ≥ 1` it
  degenerates to `0` (total-function artifact, unused).
* **(21) is stated STRICT (`<`)** with LHS the ℕ-valued `entryRowBound` cast
  to ℝ and RHS the note's real `Qm·y/2^t`, literal to the note.
* **`t` ranges over `t ≤ 2`** (note: `t = 0,1,2`), and `hR : 4 ≤ R` (note §5
  `R ≥ 4`); the proofs consume only `t < R` (via `R - t ≥ 1` for the genuine
  `2^(a_t-1)` power and `a_t + t = R`), so `ht`/`hR` are carried for
  statement fidelity. The judge may weaken.
* The wrapper's `Dfamily` conclusion is the note's `comp(bracket(·))`
  orientation `C + (R-t) ≤ Dfamily …`, matching `NearFull`
  (Hypotheses.lean:53).

DISCIPLINE: statements only; every body is `sorry` until the faithfulness
judge signs off against the note's literal §5–§6 text. New defs are numeric
(ℝ/ℕ-valued) or a Boolean matrix (`Rnext`); their inhabitation/sanity unit
lemmas are stated inline below (the judge may relocate them to
`EthBridge/UnitTests.lean` per E0 convention) and are themselves `sorry`
pending sign-off.
-/

namespace EthBridge

open NPCC
open Workspace.Types.Interlace
open Workspace.Types.CommComplexity

/-! ## Note (19)–(20): the entry parameters

Fix `0 < x_out < 1` and put `L = ln(1/x_out)`, `d = ⌈L/λ⌉` (19). For
`t = 0,1,2` set `a_t = R - t`, `p_t = 2^(a_t-1) + d` (20). -/

/-- **Note (19), the target column defect** `L = ln(1/x_out)`. This is the
absolute defect budget the projected column set must respect (`Def ≤ L`). -/
noncomputable def entryDefect (x_out : ℝ) : ℝ :=
  Real.log (1 / x_out)

/-- **Note (19)**: `d = ⌈L/λ⌉`, the excess-copy count purchased to pay for
the entry column defect. ℕ-ceiling; agrees with the note's real ceiling on
the used regime `0 < x_out < 1 < e^λ` (JUDGE FLAG in file header). -/
noncomputable def entryExcess (x_out lam : ℝ) : ℕ :=
  ⌈entryDefect x_out / lam⌉₊

/-- **Note (20)**: the entry level `a_t = R - t` (ℕ-subtraction, exact under
`t ≤ 2 ≤ 4 ≤ R`; JUDGE FLAG in file header). -/
def entryLevel (R t : ℕ) : ℕ :=
  R - t

/-- **Note (20)**: the entry copy count `p_t = 2^(a_t - 1) + d`. The exponent
`a_t - 1` is ℕ-subtraction, a genuine power for `a_t ≥ 1` (i.e. `t < R`, true
under `t ≤ 2 < 4 ≤ R`). -/
noncomputable def entryCopies (R t : ℕ) (x_out lam : ℝ) : ℕ :=
  2 ^ (entryLevel R t - 1) + entryExcess x_out lam

/-- **The (21) left side** `(p-1)·m + (Q-p+1)·(A-1)`: the maximal number of
rows a restriction of `Interlace(W,Q)` can retain when fewer than `p` outer
blocks are good at threshold `A` (each of `≤ p-1` good blocks caps at the
full block size `m`, each of the `≥ Q-p+1` bad blocks at `A-1`).
ℕ-subtractions exact under `1 ≤ p ≤ Q`, `1 ≤ A` (use-site hypotheses). -/
def entryRowBound (Q m p A : ℕ) : ℕ :=
  (p - 1) * m + (Q - p + 1) * (A - 1)

/-- **Note §5**: the good outer `W` blocks of a row set `R` at threshold `A`
("Call an outer `W` block good if it contains at least `A_(a_t)` retained
rows"): the indices `q` whose fiber of `R` holds at least `A` rows. -/
def goodBlocks {X : Type*} {Q : ℕ} (R : Finset (Fin Q × X)) (A : ℕ) :
    Finset (Fin Q) :=
  (Finset.univ : Finset (Fin Q)).filter fun q =>
    A ≤ (R.filter fun r => r.1 = q).card

/-- **Note §5**: the next-round robust test `R_next = transpose(V)`,
`V = Interlace(W,Q)`: rows are the columns `Fin Q → Y` of the `Q`-fold
interlace, columns its rows `Fin Q × X`. -/
def Rnext {X Y : Type*} (W : X → Y → Bool) (Q : ℕ) :
    (Fin Q → Y) → (Fin Q × X) → Bool :=
  fun c r => interlaceFun W Q r c

/-! ## Sanity / unit lemmas for the entry parameters (BtL discipline)

Arithmetic facts each consuming proof needs, stated once. JUDGE FLAG: these
are inline rather than in `UnitTests.lean` because they are load-bearing
helper obligations, not mere inhabitation checks; the judge may relocate. -/

/-- `Rnext` is definitionally the transpose of the `Q`-fold interlace
(inhabitation/fidelity unit test; closes by `rfl`). -/
theorem Rnext_apply {X Y : Type*} (W : X → Y → Bool) (Q : ℕ)
    (c : Fin Q → Y) (r : Fin Q × X) :
    Rnext W Q c r = interlaceFun W Q r c := by
  rfl

/-- `L > 0` exactly on the used regime `0 < x_out < 1` (where `x_out < 1` is
consumed; feeds `entryExcess_pos`). -/
theorem entryDefect_pos (x_out : ℝ) (hx_out0 : 0 < x_out)
    (hx_out1 : x_out < 1) :
    0 < entryDefect x_out := by
  unfold entryDefect
  exact Real.log_pos ((one_lt_div hx_out0).mpr hx_out1)

/-- **`d ≥ 1`** on the used regime — the load-bearing consequence of
`x_out < 1` (file-header flag): it is what makes `p_t` strictly exceed
`2^(a_t-1)`, Theorem 1's copy-count hypothesis. -/
theorem entryExcess_pos (x_out lam : ℝ) (hx_out0 : 0 < x_out)
    (hx_out1 : x_out < 1) (hlam : 0 < lam) :
    1 ≤ entryExcess x_out lam := by
  unfold entryExcess
  exact Nat.ceil_pos.mpr (div_pos (entryDefect_pos x_out hx_out0 hx_out1) hlam)

/-- **Note (19) consumed:** `L ≤ d·λ` (from `d = ⌈L/λ⌉`, `λ > 0`). The defect
budget the projection step hands to `bracket_subset_stateDensity`. -/
theorem entryDefect_le_excess (x_out lam : ℝ) (hlam : 0 < lam) :
    entryDefect x_out ≤ (entryExcess x_out lam : ℝ) * lam := by
  unfold entryExcess
  exact (div_le_iff₀ hlam).mp (Nat.le_ceil _)

/-- **Note §5, `c_(a_t)(p_t) = d` exactly:** `cExcess a (2^(a-1) + d) = d` for
`a ≥ 1` (the `zpow` in `cExcess` is the genuine integer power there). With
`entryDefect_le_excess` this gives the note's
`L ≤ d·λ = (p_t - 2^(a_t-1))·λ = c_(a_t)(p_t)·λ`. -/
theorem cExcess_entryCopies (a d : ℕ) (ha : 1 ≤ a) :
    cExcess a (2 ^ (a - 1) + d) = (d : ℝ) := by
  unfold cExcess
  have hz : ((a : ℤ) - 1) = ((a - 1 : ℕ) : ℤ) := by omega
  rw [hz, zpow_natCast]
  push_cast
  ring

/-- **Theorem 1's copy-count hypothesis at the entry parameters** (doubled
ℕ-safe form, cf. Main.lean header): `2^(a_t) < 2·p_t`, from `d ≥ 1` and
`a_t = R - t ≥ 1`. -/
theorem entryCopies_hp (R t : ℕ) (x_out lam : ℝ) (htR : t < R)
    (hd : 1 ≤ entryExcess x_out lam) :
    2 ^ entryLevel R t < 2 * entryCopies R t x_out lam := by
  unfold entryCopies entryLevel
  have h2 : 2 * 2 ^ (R - t - 1) = 2 ^ (R - t) := by
    conv_rhs => rw [show R - t = (R - t - 1) + 1 by omega]
    rw [pow_succ]; ring
  omega

/-- Row threshold positivity `1 ≤ A_a` (`m ≥ 1`, `x > 0`): makes the
`A - 1` in `entryRowBound` and the good/bad dichotomy honest. -/
theorem rowThreshold_pos (m : ℕ) (x : ℝ) (a : ℕ) (hm : 1 ≤ m) (hx0 : 0 < x) :
    1 ≤ rowThreshold m x a := by
  unfold rowThreshold
  refine Nat.ceil_pos.mpr ?_
  have hmr : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have h2 : (0 : ℝ) < (2 : ℝ) ^ a := by positivity
  exact mul_pos (mul_pos hmr h2) hx0

/-- Row threshold cap `A_a ≤ m + 1` under the note §2 side condition
`2^a·x ≤ 1` — the first of the two places `hax` is genuinely consumed in E4
(a bad block caps at `A_a - 1 ≤ m` rows, so raising a block from bad to good
never lowers the `entryRowBound` cap). -/
theorem rowThreshold_le_succ (m : ℕ) (x : ℝ) (a : ℕ)
    (hax : (2 : ℝ) ^ a * x ≤ 1) :
    rowThreshold m x a ≤ m + 1 := by
  unfold rowThreshold
  have h : (m : ℝ) * 2 ^ a * x ≤ (m : ℝ) := by
    have hstep : (m : ℝ) * ((2 : ℝ) ^ a * x) ≤ (m : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hax (by positivity)
    calc (m : ℝ) * 2 ^ a * x = (m : ℝ) * ((2 : ℝ) ^ a * x) := by ring
      _ ≤ (m : ℝ) * 1 := hstep
      _ = (m : ℝ) := mul_one _
  have hle : ⌈(m : ℝ) * 2 ^ a * x⌉₊ ≤ m := by
    rw [Nat.ceil_le]; exact_mod_cast h
  omega

/-! ## HB-1: one-copy transpose transport (note §8: "only one-copy transpose
symmetry is used")

Re-proof, in the EthBridge namespace, of the PRIVATE
`NPCC.Dfamily_one_transpose` (Stage2.lean:53). Proof route (verbatim from
there): `Dfamily_eq_DSet` (Twin.lean:927) on both sides +
`Workspace.BracketLemmas.transpose_bracket` (stated for ONE copy only —
exactly why the note confines itself to one-copy transpose symmetry). -/

/-- **HB-1.** Typed one-copy transpose transport for bracket-family
complexity: `comp(bracket(fᵀ,1,y,x)) = comp(bracket(f,1,x,y))`. -/
theorem dfamily_one_transpose {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) {x y : ℝ}
    (hx0 : 0 < x) (hx1 : x ≤ 1) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y) :
    Dfamily (interlaceFun (fun yy xx => f xx yy) 1) (bracketGE Y X 1 y x)
      = Dfamily (interlaceFun f 1) (bracketGE X Y 1 x y) := by
  classical
  let eX : Fin (Fintype.card X) ≃ X := (Fintype.equivFin X).symm
  let eY : Fin (Fintype.card Y) ≃ Y := (Fintype.equivFin Y).symm
  let M : Workspace.Types.BoolMat.BoolMat :=
    ⟨Fintype.card X, Fintype.card Y, fun i j => f (eX i) (eY j)⟩
  have he : ∀ i j, M.e i j = f (eX i) (eY j) := fun _ _ => rfl
  have heT : ∀ i j, M.transpose.e i j =
      (fun yy xx => f xx yy) (eY i) (eX j) := fun _ _ => rfl
  have hleft := Dfamily_eq_DSet (p := 1) (fun yy xx => f xx yy) M.transpose eY eX heT
    hy0 hy1 hx0 hx1 hY
  have hright := Dfamily_eq_DSet (p := 1) f M eX eY he hx0 hx1 hy0 hy1 hX
  rw [hleft, hright]
  exact (Workspace.BracketLemmas.transpose_bracket M x y).symm

/-! ## HB-2: `Dfamily` lower bound from a ∀-member bound -/

/-- **HB-2.** `k ≤ Dfamily f Φ` from `k ≤ D(member)` for every member, given
`Φ` nonempty (`Dfamily` is `sInf` over ℕ, which is `0` on the empty family —
hence the nonemptiness guard; discharge via `NPCC.bracketGE.nonempty`,
DefsAux.lean:139, at the use site). -/
theorem le_Dfamily {A B : Type*} (f : A → B → Bool)
    (Φ : Set (Finset A × Finset B)) (k : ℕ) (hne : Φ.Nonempty)
    (h : ∀ RC ∈ Φ, k ≤ D (subgame f RC.1 RC.2)) :
    k ≤ Dfamily f Φ := by
  unfold Dfamily
  apply le_csInf
  · obtain ⟨RC, hRC⟩ := hne
    exact ⟨_, RC, hRC, rfl⟩
  · rintro b ⟨RC, hRC, rfl⟩
    exact h RC hRC

/-! ## HB-3: the one-copy interlace collapse, cardinality side

The `D`-side is the PUBLIC `NPCC.M1_interlace_one_project_le`
(Stage1.lean:1710, polymorphic despite the name): a `p = 1` interlace subgame
on `(R0, C0)` projects to the base game on
`(R0.image (·.2), C0.image (· 0))` without increasing complexity. These three
lemmas transport the one-copy bracket THRESHOLDS to the collapsed pair: on
`Fin 1` the fiber filter is trivial and both image maps are injective. -/

/-- **HB-3(a).** Over `Fin 1` every first-component fiber is the whole set
(there is only one index), so the one-copy equipartition threshold reads
directly on `R0.card`. -/
theorem filter_fst_fin_one {Z : Type*} (R0 : Finset (Fin 1 × Z)) (q : Fin 1) :
    R0.filter (fun r => r.1 = q) = R0 := by
  apply Finset.filter_true_of_mem
  intro r _
  exact Subsingleton.elim r.1 q

/-- **HB-3(b).** Dropping the (unique) copy index preserves row counts:
`(·.2)` is injective on `Fin 1 × Z`. -/
theorem card_image_snd_fin_one {Z : Type*} [DecidableEq Z]
    (R0 : Finset (Fin 1 × Z)) :
    (R0.image fun r => r.2).card = R0.card := by
  apply Finset.card_image_of_injOn
  intro a _ b _ hab
  exact Prod.ext (Subsingleton.elim a.1 b.1) hab

/-- **HB-3(c).** Evaluating at the (unique) coordinate preserves column
counts: `(· 0)` is injective on `Fin 1 → Z`. -/
theorem card_image_apply_zero_fin_one {Z : Type*} [DecidableEq Z]
    (C0 : Finset (Fin 1 → Z)) :
    (C0.image fun c => c 0).card = C0.card := by
  apply Finset.card_image_of_injOn
  intro a _ b _ hab
  funext i
  have hi : i = 0 := Subsingleton.elim i 0
  rw [hi]; exact hab

/-! ## HB-4: the good-block counting (note §5 vs (21)) — THE new lemma

Note §5: "Call an outer `W` block good if it contains at least `A_(a_t)`
retained rows. If fewer than `p_t` blocks were good, the row count would be
at most the left side of (21), contradicting the retained row threshold.
Hence at least `p_t` blocks are good. Choose exactly `p_t` good blocks…"

Pure Finset/ℕ counting (imitate `NPCC.no_waste_row_partition`,
Control.lean:118): the row count is the sum of the `Q` fiber counts; each of
the `< p` good fibers caps at `m = |X|`, each bad fiber at `A - 1`, and the
cap is monotone in the good count because `A - 1 ≤ m` (`rowThreshold_le_succ`
under `hax` — where `hax` is consumed).

JUDGE FLAGS.
* `hAm : A ≤ m + 1` is the abstract residue of `hax`; the counting lemma is
  otherwise parameter-free (`A`, `p` abstract, not the entry values).
* All three ℕ-subtractions in `entryRowBound` are exact under
  `hA`/`hp1`/`hpQ` (file-header flag).
* `exists_good_block_choice` returns the CHOSEN block set with EXACT
  cardinality `p` (note: "Choose exactly `p_t` good blocks") plus the
  `IsEquipartitionedGE` fact `coord_projection` consumes; the enumeration
  `e : Fin p ≃ {q // q ∈ Qg}` is built at the use site from `Qg.card = p`
  (as in `member_max_projection`, Induction.lean:569). -/

/-- **HB-4(a), the note-literal direction.** With fewer than `p` good blocks,
the row count is at most the (21) left side
`(p-1)·m + (Q-p+1)·(A-1)`. -/
theorem card_le_entryRowBound_of_few_good {X : Type*} [Fintype X] {Q : ℕ}
    (R : Finset (Fin Q × X)) (A p : ℕ)
    (hA : 1 ≤ A) (hAm : A ≤ Fintype.card X + 1) (hp1 : 1 ≤ p) (hpQ : p ≤ Q)
    (hfew : (goodBlocks R A).card < p) :
    R.card ≤ entryRowBound Q (Fintype.card X) p A := by
  classical
  -- `R.card` is the sum of the `Q` first-component fiber counts.
  have hsum : R.card =
      ∑ q : Fin Q, (R.filter (fun r => r.1 = q)).card :=
    Finset.card_eq_sum_card_fiberwise (fun r _ => Finset.mem_univ (r.1))
  -- Each fiber injects into `X` via the second component, so caps at `|X|`.
  have hfib_le : ∀ q : Fin Q,
      (R.filter (fun r => r.1 = q)).card ≤ Fintype.card X := by
    intro q
    rw [← Finset.card_univ]
    apply Finset.card_le_card_of_injOn (fun r => r.2)
    · intro r _; exact Finset.mem_univ _
    · intro a ha b hb hab
      rw [Finset.mem_coe, Finset.mem_filter] at ha hb
      exact Prod.ext (ha.2.trans hb.2.symm) hab
  -- A bad block (not good) has fewer than `A` retained rows, hence `≤ A - 1`.
  have hbad : ∀ q : Fin Q, q ∉ goodBlocks R A →
      (R.filter (fun r => r.1 = q)).card ≤ A - 1 := by
    intro q hq
    have hnot : ¬ A ≤ (R.filter (fun r => r.1 = q)).card := by
      intro hle
      exact hq (by
        rw [goodBlocks, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hle⟩)
    omega
  -- Split the total over good blocks and their complement.
  have hsplit :
      (∑ q : Fin Q, (R.filter (fun r => r.1 = q)).card) =
        (∑ q ∈ goodBlocks R A, (R.filter (fun r => r.1 = q)).card) +
        (∑ q ∈ (goodBlocks R A)ᶜ, (R.filter (fun r => r.1 = q)).card) :=
    (Finset.sum_add_sum_compl (goodBlocks R A)
      (fun q => (R.filter (fun r => r.1 = q)).card)).symm
  -- Good part `≤ g · |X|`, bad part `≤ (Q - g)·(A-1)`.
  set g := (goodBlocks R A).card with hgdef
  have hgood_le :
      (∑ q ∈ goodBlocks R A, (R.filter (fun r => r.1 = q)).card)
        ≤ g * Fintype.card X := by
    calc (∑ q ∈ goodBlocks R A, (R.filter (fun r => r.1 = q)).card)
          ≤ ∑ _q ∈ goodBlocks R A, Fintype.card X :=
            Finset.sum_le_sum (fun q _ => hfib_le q)
      _ = g * Fintype.card X := by rw [Finset.sum_const, hgdef, smul_eq_mul]
  have hcomplcard : (goodBlocks R A)ᶜ.card = Q - g := by
    rw [Finset.card_compl, Fintype.card_fin, hgdef]
  have hbad_le :
      (∑ q ∈ (goodBlocks R A)ᶜ, (R.filter (fun r => r.1 = q)).card)
        ≤ (Q - g) * (A - 1) := by
    calc (∑ q ∈ (goodBlocks R A)ᶜ, (R.filter (fun r => r.1 = q)).card)
          ≤ ∑ _q ∈ (goodBlocks R A)ᶜ, (A - 1) :=
            Finset.sum_le_sum (fun q hq => hbad q (Finset.mem_compl.mp hq))
      _ = (Q - g) * (A - 1) := by rw [Finset.sum_const, hcomplcard, smul_eq_mul]
  -- Assemble, then push the good-count up to `p - 1` (row cap is monotone
  -- in the good count because `A - 1 ≤ |X|`).
  have hcombine :
      R.card ≤ g * Fintype.card X + (Q - g) * (A - 1) := by
    rw [hsum, hsplit]; exact Nat.add_le_add hgood_le hbad_le
  refine le_trans hcombine ?_
  unfold entryRowBound
  have hgle : g ≤ p - 1 := by omega
  obtain ⟨d1, hd1⟩ : ∃ d1, p - 1 = g + d1 := ⟨p - 1 - g, by omega⟩
  have hAm' : A - 1 ≤ Fintype.card X := by omega
  have hmul : d1 * (A - 1) ≤ d1 * Fintype.card X := Nat.mul_le_mul (le_refl d1) hAm'
  have e1 : (p - 1) * Fintype.card X
      = g * Fintype.card X + d1 * Fintype.card X := by rw [hd1, Nat.add_mul]
  have e2 : (Q - g) * (A - 1) = (Q - p + 1) * (A - 1) + d1 * (A - 1) := by
    rw [show Q - g = (Q - p + 1) + d1 by omega, Nat.add_mul]
  rw [e1, e2]
  omega

/-- **HB-4(b), the consumable contrapositive.** A row count strictly above
the (21) left side forces at least `p` good blocks. -/
theorem good_blocks_count {X : Type*} [Fintype X] {Q : ℕ}
    (R : Finset (Fin Q × X)) (A p : ℕ)
    (hA : 1 ≤ A) (hAm : A ≤ Fintype.card X + 1) (hp1 : 1 ≤ p) (hpQ : p ≤ Q)
    (hcard : entryRowBound Q (Fintype.card X) p A < R.card) :
    p ≤ (goodBlocks R A).card := by
  by_contra hlt
  push_neg at hlt
  have hcap := card_le_entryRowBound_of_few_good R A p hA hAm hp1 hpQ hlt
  omega

/-- **HB-4(c), the extraction.** From `≥ p` good blocks, choose EXACTLY `p`
of them (`Finset.exists_subset_card_eq`); on the chosen set the row set is
`(Qg, A)`-equipartitioned — the shape `coord_projection` consumes. -/
theorem exists_good_block_choice {X : Type*} {Q : ℕ}
    (R : Finset (Fin Q × X)) (A p : ℕ)
    (h : p ≤ (goodBlocks R A).card) :
    ∃ Qg : Finset (Fin Q), Qg.card = p ∧ IsEquipartitionedGE R Qg A := by
  classical
  obtain ⟨Qg, hsub, hcard⟩ := Finset.exists_subset_card_eq h
  refine ⟨Qg, hcard, ?_⟩
  intro q hq
  have hqg : q ∈ goodBlocks R A := hsub hq
  rw [goodBlocks, Finset.mem_filter] at hqg
  exact hqg.2

/-! ## HB-5: `D`-comparison from projection provenance

Re-proof, in the EthBridge namespace, of the PRIVATE
`NPCC.D_projected_subgame_le` (Control.lean:83) — the exact companion of
`coord_projection` (consumed that way at Control.lean:319–334). Body is
`D_mapNodes_le` (Twin.lean:132) along the provenance maps. -/

/-- **HB-5.** If every row of `(R', C')` arises from a row of `(R, C)` along
`emb` and every column of `C'` is the `emb`-projection of a column of `C`,
the projected subgame is no harder (the PRIVATE original's `[Fintype X]
[Fintype Y]` are dropped as unused — subtype `Fintype`s come from
`FinsetCoe`):
`D(subgame(Interlace(f,r), R', C')) ≤ D(subgame(Interlace(f,q), R, C))`. -/
theorem projected_subgame_le {X Y : Type*}
    (f : X → Y → Bool) {q r : ℕ}
    {R : Finset (Fin q × X)} {C : Finset (Fin q → Y)}
    {R' : Finset (Fin r × X)} {C' : Finset (Fin r → Y)}
    (emb : Fin r → Fin q)
    (hRows : ∀ a ∈ R', (emb a.1, a.2) ∈ R)
    (hCols : ∀ c' ∈ C', ∃ c ∈ C, ∀ j : Fin r, c' j = c (emb j)) :
    D (subgame (interlaceFun f r) R' C') ≤
      D (subgame (interlaceFun f q) R C) := by
  classical
  let ρ : {a // a ∈ R'} → {a // a ∈ R} :=
    fun a => ⟨(emb a.1.1, a.1.2), hRows a.1 a.2⟩
  let σ : {c // c ∈ C'} → {c // c ∈ C} :=
    fun c => ⟨(Classical.choose (hCols c.1 c.2)),
      (Classical.choose_spec (hCols c.1 c.2)).1⟩
  have hσ : ∀ (c : {c // c ∈ C'}) (j : Fin r), c.1 j = (σ c).1 (emb j) := by
    intro c j
    exact (Classical.choose_spec (hCols c.1 c.2)).2 j
  have heq :
      subgame (interlaceFun f r) R' C' =
        (fun a c => (subgame (interlaceFun f q) R C) (ρ a) (σ c)) := by
    funext a c
    simp only [subgame, interlaceFun]
    exact congrArg (fun y => f a.1.2 y) (hσ c a.1.1)
  rw [heq]
  exact D_mapNodes_le (subgame (interlaceFun f q) R C) ρ σ

/-! ## HB-6: `bracketGE` at the projected parameters lands in the Theorem-1
state family

Rows: the `p`-copy bracket at row parameter `2^a·x` has threshold
`⌈m·(2^a·x)⌉₊ = rowThreshold m x a` (associativity only). Columns:
`|C| ≥ ⌈n^p·x_out⌉₊ ≥ n^p·x_out ≥ n^p·e^{-c_a(p)λ}` since
`e^{-c_a(p)λ} ≤ e^{-L} = x_out` under the defect budget `L ≤ c_a(p)·λ`
(note §5: "the projected column defect is at most `L`. By (19) and (20),
`L ≤ dλ = c_(a_t)(p_t)λ`"). -/

/-- **HB-6.** Under the defect budget `L = ln(1/x_out) ≤ c_a(p)·λ`, the
`p`-copy bracket at row parameter `2^a·x` and column density `x_out` is a
subfamily of the level-`a` Theorem-1 state family. -/
theorem bracket_subset_stateDensity {X Y : Type*} [Fintype X] [Fintype Y]
    (p a : ℕ) (x lam x_out : ℝ) (hx_out0 : 0 < x_out)
    (hdef : entryDefect x_out ≤ cExcess a p * lam) :
    bracketGE X Y p ((2 : ℝ) ^ a * x) x_out ⊆ stateDensity X Y p a x lam := by
  intro RC hRC
  obtain ⟨hrow, hcol⟩ := hRC
  refine ⟨?_, ?_⟩
  · have hthr : rowThreshold (Fintype.card X) x a
        = ⌈(Fintype.card X : ℝ) * ((2 : ℝ) ^ a * x)⌉₊ := by
      unfold rowThreshold; rw [← mul_assoc]
    rw [hthr]; exact hrow
  · have hexp : Real.exp (-(cExcess a p * lam)) ≤ x_out := by
      have hEq : entryDefect x_out = - Real.log x_out := by
        unfold entryDefect; rw [one_div, Real.log_inv]
      have hle : -(cExcess a p * lam) ≤ Real.log x_out := by
        rw [hEq] at hdef; linarith
      calc Real.exp (-(cExcess a p * lam))
          ≤ Real.exp (Real.log x_out) := Real.exp_le_exp.mpr hle
        _ = x_out := Real.exp_log hx_out0
    have hcard_ge : ((Fintype.card Y : ℝ) ^ p) * x_out ≤ (RC.2.card : ℝ) := by
      calc ((Fintype.card Y : ℝ) ^ p) * x_out
          ≤ (⌈((Fintype.card Y : ℝ) ^ p) * x_out⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ (RC.2.card : ℝ) := by exact_mod_cast hcol
    calc ((Fintype.card Y : ℝ) ^ p) * Real.exp (-(cExcess a p * lam))
        ≤ ((Fintype.card Y : ℝ) ^ p) * x_out :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ (RC.2.card : ℝ) := hcard_ge

/-! ## The projected-defect lemma (note §5, the projection step)

"Choose exactly `p_t` good blocks and project the column set to those
coordinates. Coordinate projection preserves total density at least `x_out`,
so the projected column defect is at most `L`."

Composition of `NPCC.coord_projection` (CoordProjection.lean:26 — the
density-PRESERVING projection; its `hfiberbound`/`hglobal` pigeonhole
`|C| ≤ n^{Q-p}·|proj C|` is exactly "preserves total density", NOT the
`y^{ℓ/p}` power-scaling of `member_max_projection`) with HB-6.

JUDGE FLAGS.
* `T := rowThreshold m x a` instantiates `coord_projection`'s `hxT` as an
  EQUALITY (up to `mul_assoc`), so no slack enters on the row side.
* The provenance conjuncts are verbatim `coord_projection`'s, in the shape
  HB-5 consumes with `emb := fun j => (e j).val`.
* Ambient block count is an abstract `Qw` (the consumer passes `Qw = 2^R`);
  the column hypothesis is on the FULL `Qw`-fold column space — density
  `x_out` there, density `≥ x_out` after projection, defect `≤ L ≤ c_a(p)λ`
  folded via `hdef`. -/

/-- **The projected-defect lemma.** From `p` good blocks `Qg` (each holding
`≥ A_a` rows of `RV`) and total column density `≥ x_out` on the `Qw`-fold
interlace, coordinate projection to `Qg` produces a member of the level-`a`
Theorem-1 state family on `p` copies, with row/column provenance into
`(RV, CV)`.

JUDGE REVISION (E4 global-sweep verdict, applied): the conclusion now records
the note's actual §5 preservation property — "coordinate projection preserves
total density at least `x_out`" — as an EXPLICIT first conjunct
`RC' ∈ bracketGE X Y p (2^a·x) x_out` (the exact `⌈n^p·x_out⌉₊ ≤ RC'.2.card`
column preservation), from which the `stateDensity` membership then follows via
`bracket_subset_stateDensity` under `hdef`. Without this the signature would
silently weaken the note to bare `stateDensity` membership (density
`exp(-c_a(p)λ)`, possibly strictly below `x_out`). -/
theorem entry_projected_state {X Y : Type*} [Fintype X] [Fintype Y]
    {Qw p a : ℕ} (hp : 0 < p)
    {Qg : Finset (Fin Qw)} (e : Fin p ≃ {q // q ∈ Qg})
    {RV : Finset (Fin Qw × X)} {CV : Finset (Fin Qw → Y)}
    (x lam x_out : ℝ) (hx_out0 : 0 < x_out)
    (hdef : entryDefect x_out ≤ cExcess a p * lam)
    (hrow : IsEquipartitionedGE RV Qg (rowThreshold (Fintype.card X) x a))
    (hcol : ⌈((Fintype.card Y : ℝ) ^ Qw) * x_out⌉₊ ≤ CV.card) :
    ∃ RC' : Finset (Fin p × X) × Finset (Fin p → Y),
      RC' ∈ bracketGE X Y p ((2 : ℝ) ^ a * x) x_out ∧
      RC' ∈ stateDensity X Y p a x lam ∧
      (∀ r ∈ RC'.1, ((e r.1).val, r.2) ∈ RV) ∧
      (∀ c' ∈ RC'.2, ∃ c ∈ CV, ∀ j : Fin p, c' j = c (e j).val) := by
  classical
  -- `T := rowThreshold m x a` instantiates `coord_projection`'s `hxT` as an
  -- EQUALITY (up to `mul_assoc`): no slack enters on the row side.
  have hxT : ⌈(Fintype.card X : ℝ) * ((2 : ℝ) ^ a * x)⌉₊ ≤
      rowThreshold (Fintype.card X) x a := by
    unfold rowThreshold
    rw [← mul_assoc]
  obtain ⟨RC', hbr, hrows, hcols⟩ := NPCC.coord_projection hp e hrow hcol hxT
  exact ⟨RC', hbr,
    bracket_subset_stateDensity p a x lam x_out hx_out0 hdef hbr,
    hrows, hcols⟩

/-! ## `eth:thm-entry` — Theorem 2 (note §5, (22)), V-side core

Note §5 Theorem 2, after transposing a member of the (22) bracket family:
"This gives a restriction of `V` with at least `⌈Qm·y/2^t⌉` rows and at least
`⌈n^Q·x_out⌉` columns" — the V-side statement below takes exactly such a
restriction and yields `C + (R-t)`.

Proof route: `good_blocks_count` (via (21) = `h21` + the row count, with
`hA`/`hAm` from `rowThreshold_pos`/`rowThreshold_le_succ` under `hax`) →
`exists_good_block_choice` (exactly `p_t` good blocks, `e` built from
`Qg.card = p_t`) → `entry_projected_state` (defect budget from
`entryDefect_le_excess` + `cExcess_entryCopies`) → `theorem_one` (Main.lean:665,
at `p := p_t`, `a := R - t`, `hp` from `entryCopies_hp`) → `projected_subgame_le`
back to `(RV, CV)`.

JUDGE FLAGS.
* `hax` at level `R - t` only (the one level a fixed `t` touches); consumed
  twice (file-header flag).
* Theorem-1 hypothesis block (`hx0`…`hTwo`) verbatim from `theorem_one`; `y`
  here is BOTH the two-copy bundle parameter and the (21)/row-count density
  (the note's single `y = 1/2 + δ`).
* Thresholds are stated as ℕ-ceilings of the note's real counts
  (`⌈Qm·y/2^t⌉`, `⌈n^Q·x_out⌉`), matching `bracketGE`'s convention; the
  wrapper produces them verbatim from the transposed bracket member.
* `hpQ : p_t ≤ Q` is note (20)'s standing assumption ("Assume `p_t ≤ Q`");
  discharged for all three `t` by `uniform_package`. -/

/-- **`eth:thm-entry`, V-side core (note §5 Theorem 2 / (22), transposed
member form).** Under the Theorem-1 hypotheses and (19)–(21), every
restriction of `Interlace(W, 2^R)` with at least `⌈Qm·y/2^t⌉` rows and at
least `⌈n^Q·x_out⌉` columns has communication complexity at least
`C + (R - t)`. -/
theorem theorem_two_V {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (C R t : ℕ) (x y lam x_out : ℝ)
    (hR : 4 ≤ R) (ht : t ≤ 2)
    (hx_out0 : 0 < x_out) (hx_out1 : x_out < 1)
    (hax : (2 : ℝ) ^ (R - t) * x ≤ 1)
    (hx0 : 0 < x) (hx : x ≤ 1 / 4) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hlam : 0 < lam)
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y) (hC : 3 ≤ C)
    (hmargin : 3 * lam + (7 / 5) * Real.log 2 ≤ -2 * Real.log y)
    (hNear : NearFull W C x lam) (hTwo : TwoCopyBundle W C x y)
    (hpQ : entryCopies R t x_out lam ≤ 2 ^ R)
    (h21 : ((entryRowBound (2 ^ R) (Fintype.card X)
        (entryCopies R t x_out lam)
        (rowThreshold (Fintype.card X) x (entryLevel R t)) : ℕ) : ℝ)
      < (2 : ℝ) ^ R * (Fintype.card X : ℝ) * y / 2 ^ t)
    (RV : Finset (Fin (2 ^ R) × X)) (CV : Finset (Fin (2 ^ R) → Y))
    (hRV : ⌈((2 ^ R * Fintype.card X : ℕ) : ℝ) * (y / 2 ^ t)⌉₊ ≤ RV.card)
    (hCV : ⌈((Fintype.card Y : ℝ) ^ (2 ^ R : ℕ)) * x_out⌉₊ ≤ CV.card) :
    C + (R - t) ≤ D (subgame (interlaceFun W (2 ^ R)) RV CV) := by
  classical
  have htR : t < R := by omega
  have ha1 : 1 ≤ entryLevel R t := by unfold entryLevel; omega
  -- `p_t ≥ 1` (a genuine copy count)
  have hp1 : 1 ≤ entryCopies R t x_out lam := by
    have h2 := Nat.two_pow_pos (entryLevel R t - 1)
    unfold entryCopies
    omega
  -- `1 ≤ A_(a_t) ≤ m + 1` (the `hax` residue feeding the counting)
  have hA : 1 ≤ rowThreshold (Fintype.card X) x (entryLevel R t) :=
    rowThreshold_pos (Fintype.card X) x (entryLevel R t) hX hx0
  have hAm : rowThreshold (Fintype.card X) x (entryLevel R t) ≤
      Fintype.card X + 1 :=
    rowThreshold_le_succ (Fintype.card X) x (entryLevel R t) hax
  -- the retained row count strictly beats the (21) cap
  have hcard : entryRowBound (2 ^ R) (Fintype.card X)
      (entryCopies R t x_out lam)
      (rowThreshold (Fintype.card X) x (entryLevel R t)) < RV.card := by
    have hle : (2 : ℝ) ^ R * (Fintype.card X : ℝ) * y / 2 ^ t ≤
        (RV.card : ℝ) := by
      calc (2 : ℝ) ^ R * (Fintype.card X : ℝ) * y / 2 ^ t
          = ((2 ^ R * Fintype.card X : ℕ) : ℝ) * (y / 2 ^ t) := by
            push_cast; ring
        _ ≤ (⌈((2 ^ R * Fintype.card X : ℕ) : ℝ) * (y / 2 ^ t)⌉₊ : ℝ) :=
            Nat.le_ceil _
        _ ≤ (RV.card : ℝ) := by exact_mod_cast hRV
    exact_mod_cast lt_of_lt_of_le h21 hle
  -- ≥ p_t good blocks (note §5 counting); choose EXACTLY p_t of them
  have hgood : entryCopies R t x_out lam ≤
      (goodBlocks RV (rowThreshold (Fintype.card X) x (entryLevel R t))).card :=
    good_blocks_count RV _ _ hA hAm hp1 hpQ hcard
  obtain ⟨Qg, hQg, hEq⟩ := exists_good_block_choice RV _ _ hgood
  let e : Fin (entryCopies R t x_out lam) ≃ {q // q ∈ Qg} :=
    (finCongr hQg.symm).trans Qg.equivFin.symm
  -- the (19)–(20) defect budget `L ≤ d·λ = c_(a_t)(p_t)·λ`
  have hd1 : 1 ≤ entryExcess x_out lam :=
    entryExcess_pos x_out lam hx_out0 hx_out1 hlam
  have hdef : entryDefect x_out ≤
      cExcess (entryLevel R t) (entryCopies R t x_out lam) * lam := by
    have hce := cExcess_entryCopies (entryLevel R t) (entryExcess x_out lam) ha1
    calc entryDefect x_out
        ≤ (entryExcess x_out lam : ℝ) * lam :=
          entryDefect_le_excess x_out lam hlam
      _ = cExcess (entryLevel R t) (entryCopies R t x_out lam) * lam := by
          unfold entryCopies
          rw [hce]
  -- project onto the chosen good blocks, landing in the Theorem-1 family
  obtain ⟨RC', _hbr, hstate, hrowsProv, hcolsProv⟩ :=
    entry_projected_state hp1 e x lam x_out hx_out0 hdef hEq hCV
  -- Theorem 1 at `(p_t, a_t)`
  have hone : C + entryLevel R t ≤
      D (subgame (interlaceFun W (entryCopies R t x_out lam)) RC'.1 RC'.2) :=
    theorem_one W C (entryCopies R t x_out lam) (entryLevel R t) x y lam
      (entryCopies_hp R t x_out lam htR hd1) hax hx0 hx hy0 hy1 hlam
      hX hY hC hmargin hNear hTwo RC' hstate
  -- descend along the projection provenance back to `(RV, CV)`
  have hproj : D (subgame (interlaceFun W (entryCopies R t x_out lam))
        RC'.1 RC'.2) ≤
      D (subgame (interlaceFun W (2 ^ R)) RV CV) :=
    projected_subgame_le W (fun j => (e j).val) hrowsProv hcolsProv
  exact le_trans hone hproj

/-! ## `eth:thm-entry` — Theorem 2, the thin transpose wrapper (note (22))

The note-literal (22): `comp(bracket(R_next,1,x_out,y/2^t)) ≥ C+R-t`.

Proof route (SPLIT FLAG, file header): `dfamily_one_transpose` (HB-1, at
`f := interlaceFun W (2^R)`, densities `(y/2^t, x_out)`) rewrites the goal to
the one-copy V-side family; `le_Dfamily` (HB-2, nonemptiness from
`bracketGE.nonempty` under `y/2^t ≤ 1`, `x_out ≤ 1`, `hX`) reduces to an
arbitrary member `(R0, C0)`; the one-copy collapse
(`NPCC.M1_interlace_one_project_le` + HB-3: `filter_fst_fin_one` reads the
equipartition threshold on `R0.card`, the two image-cardinality lemmas move
the thresholds to `RV := R0.image (·.2)`, `CV := C0.image (· 0)`, with
`card (Fin 1 × Z) = card Z` and `card (Fin 1 → Z) = card Z` aligning the
ceiling arguments) lands exactly in `theorem_two_V`. -/

/-- **`eth:thm-entry` (note §5 Theorem 2, (22)).** Under the hypotheses of
Theorem 1 and (19)–(21), `comp(bracket(R_next, 1, x_out, y/2^t)) ≥ C + (R-t)`
for the fixed `t ≤ 2`. -/
theorem theorem_two {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (C R t : ℕ) (x y lam x_out : ℝ)
    (hR : 4 ≤ R) (ht : t ≤ 2)
    (hx_out0 : 0 < x_out) (hx_out1 : x_out < 1)
    (hax : (2 : ℝ) ^ (R - t) * x ≤ 1)
    (hx0 : 0 < x) (hx : x ≤ 1 / 4) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hlam : 0 < lam)
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y) (hC : 3 ≤ C)
    (hmargin : 3 * lam + (7 / 5) * Real.log 2 ≤ -2 * Real.log y)
    (hNear : NearFull W C x lam) (hTwo : TwoCopyBundle W C x y)
    (hpQ : entryCopies R t x_out lam ≤ 2 ^ R)
    (h21 : ((entryRowBound (2 ^ R) (Fintype.card X)
        (entryCopies R t x_out lam)
        (rowThreshold (Fintype.card X) x (entryLevel R t)) : ℕ) : ℝ)
      < (2 : ℝ) ^ R * (Fintype.card X : ℝ) * y / 2 ^ t) :
    C + (R - t) ≤
      Dfamily (interlaceFun (Rnext W (2 ^ R)) 1)
        (bracketGE (Fin (2 ^ R) → Y) (Fin (2 ^ R) × X) 1 x_out (y / 2 ^ t)) := by
  classical
  -- ambient nonemptiness of the transposed row/column types
  have hcardX' : 1 ≤ Fintype.card (Fin (2 ^ R) × X) := by
    rw [Fintype.card_prod, Fintype.card_fin]; exact Nat.mul_pos (Nat.two_pow_pos R) hX
  have hcardY' : 1 ≤ Fintype.card (Fin (2 ^ R) → Y) := by
    rw [Fintype.card_fun, Fintype.card_fin]; exact Nat.one_le_pow _ _ hY
  have h2t_pos : (0 : ℝ) < 2 ^ t := by positivity
  have h2t_one : (1 : ℝ) ≤ 2 ^ t := by
    calc (1 : ℝ) = (2 : ℝ) ^ 0 := by norm_num
      _ ≤ (2 : ℝ) ^ t := pow_le_pow_right₀ (by norm_num) (Nat.zero_le t)
  have hyx0 : 0 < y / 2 ^ t := div_pos hy0 h2t_pos
  have hyx1 : y / 2 ^ t ≤ 1 := by rw [div_le_one h2t_pos]; linarith [hy1, h2t_one]
  -- HB-1: transpose the one-copy family (note §8 one-copy transpose symmetry)
  have htrans := dfamily_one_transpose (X := Fin (2 ^ R) × X) (Y := Fin (2 ^ R) → Y)
    (interlaceFun W (2 ^ R)) (x := y / 2 ^ t) (y := x_out)
    hyx0 hyx1 hx_out0 (le_of_lt hx_out1) hcardX' hcardY'
  have key : Dfamily (interlaceFun (Rnext W (2 ^ R)) 1)
      (bracketGE (Fin (2 ^ R) → Y) (Fin (2 ^ R) × X) 1 x_out (y / 2 ^ t))
      = Dfamily (interlaceFun (interlaceFun W (2 ^ R)) 1)
        (bracketGE (Fin (2 ^ R) × X) (Fin (2 ^ R) → Y) 1 (y / 2 ^ t) x_out) := htrans
  rw [key]
  -- HB-2: descend to an arbitrary one-copy member
  apply le_Dfamily
  · exact bracketGE.nonempty 1 (y / 2 ^ t) x_out hyx1 (le_of_lt hx_out1) hcardX'
  · intro RC hmem
    obtain ⟨hR0, hC0⟩ := hmem
    -- HB-3 + `M1_interlace_one_project_le`: collapse the single copy
    have hcardprod : Fintype.card (Fin (2 ^ R) × X) = 2 ^ R * Fintype.card X := by
      rw [Fintype.card_prod, Fintype.card_fin]
    have hR0card : ⌈(Fintype.card (Fin (2 ^ R) × X) : ℝ) * (y / 2 ^ t)⌉₊ ≤ RC.1.card := by
      have h := hR0 0 (Finset.mem_univ 0)
      rwa [filter_fst_fin_one] at h
    have hRV : ⌈((2 ^ R * Fintype.card X : ℕ) : ℝ) * (y / 2 ^ t)⌉₊
        ≤ (RC.1.image (fun a => a.2)).card := by
      rw [card_image_snd_fin_one]
      have hc : ((2 ^ R * Fintype.card X : ℕ) : ℝ)
          = (Fintype.card (Fin (2 ^ R) × X) : ℝ) := by rw [hcardprod]
      rw [hc]; exact hR0card
    have hcardfun : Fintype.card (Fin (2 ^ R) → Y) = Fintype.card Y ^ (2 ^ R) := by
      rw [Fintype.card_fun, Fintype.card_fin]
    have hCV : ⌈((Fintype.card Y : ℝ) ^ (2 ^ R : ℕ)) * x_out⌉₊
        ≤ (RC.2.image (fun c => c 0)).card := by
      rw [card_image_apply_zero_fin_one]
      have hconv : ((Fintype.card (Fin (2 ^ R) → Y) : ℝ)) ^ 1
          = (Fintype.card Y : ℝ) ^ (2 ^ R : ℕ) := by
        rw [pow_one, hcardfun]; push_cast; ring
      rw [← hconv]; exact hC0
    -- theorem_two_V on the collapsed V-restriction, then re-lift the one copy
    have hV := theorem_two_V W C R t x y lam x_out hR ht hx_out0 hx_out1 hax
      hx0 hx hy0 hy1 hlam hX hY hC hmargin hNear hTwo hpQ h21
      (RC.1.image (fun a => a.2)) (RC.2.image (fun c => c 0)) hRV hCV
    have hcollapse := M1_interlace_one_project_le (interlaceFun W (2 ^ R)) RC.1 RC.2
    exact le_trans hV hcollapse

/-! ## `eth:lem-uniform-package` — (23) ⟹ (21) + `p_t ≤ Q` (note §6)

Note §6: with `y = 1/2 + δ`, the package
`Q ≥ 8L/(δλ)`, `Q ≥ 8/δ`, `Qx < δ/2` (23) implies the three exact entry
inequalities (21) AND `p_t ≤ Q`, for `δ < 1/2` and all `t = 0,1,2`
simultaneously. Pure real/ℕ arithmetic; the note's own route: `d-1 < L/λ`
and `(A_a - 1)/m < 2^a·x` bound the normalized few-good row count strictly
below `2^(-t-1) + L/(Qλ) + Qx/2^t`, and (23) drives that below
`2^(-t-1) + δ/2^t = y/2^t`; the first two package bounds give `p_t ≤ Q`.

JUDGE FLAGS.
* Conclusion quantifies `∀ t ≤ 2` — the "all three simultaneously" form the
  §7 specialization consumes (one package choice serves every rung).
* `y` is carried as a variable pinned by `hyδ : y = 1/2 + δ` so the (21)
  conclusion is syntactically the `h21` hypothesis of `theorem_two`/`_V`.
* `hR : 4 ≤ R` is consumed in `p_t ≤ Q` (`2^(R-4) + 1 ≤ 2^(R-1)` headroom);
  `hm : 1 ≤ m` in the `(A_a-1)/m` normalization. Off-by-one care: `d - 1 <
  L/λ` (ℕ-ceiling) and `A_a < m·2^a·x + 1` (`Nat.ceil_lt_add_one`), per the
  note's §6 "watch the ceilings" derivation. -/

/-- **`eth:lem-uniform-package` (note §6, (23)).** For `y = 1/2 + δ`,
`0 < δ < 1/2`: the package `Q ≥ 8L/(δλ)`, `Q ≥ 8/δ`, `Qx < δ/2` (`Q = 2^R`,
`R ≥ 4`) implies, for every `t ≤ 2` simultaneously, `p_t ≤ Q` and the exact
entry inequality (21). -/
theorem uniform_package (R : ℕ) (m : ℕ) (x lam x_out δ y : ℝ)
    (hR : 4 ≤ R) (hm : 1 ≤ m)
    (hδ0 : 0 < δ) (hδ : δ < 1 / 2) (hyδ : y = 1 / 2 + δ)
    (hlam : 0 < lam) (hx0 : 0 < x)
    (hx_out0 : 0 < x_out) (hx_out1 : x_out < 1)
    (hQL : 8 * entryDefect x_out / (δ * lam) ≤ (2 : ℝ) ^ R)
    (hQδ : 8 / δ ≤ (2 : ℝ) ^ R)
    (hQx : (2 : ℝ) ^ R * x < δ / 2) :
    ∀ t : ℕ, t ≤ 2 →
      entryCopies R t x_out lam ≤ 2 ^ R ∧
      ((entryRowBound (2 ^ R) m (entryCopies R t x_out lam)
          (rowThreshold m x (entryLevel R t)) : ℕ) : ℝ)
        < (2 : ℝ) ^ R * (m : ℝ) * y / 2 ^ t := by
  intro t ht
  -- real setup
  have hmr : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hL0 : 0 < entryDefect x_out := entryDefect_pos x_out hx_out0 hx_out1
  have hd1 : 1 ≤ entryExcess x_out lam :=
    entryExcess_pos x_out lam hx_out0 hx_out1 hlam
  have hQr_pos : (0 : ℝ) < (2 : ℝ) ^ R := by positivity
  have hP1_pos : (0 : ℝ) < (2 : ℝ) ^ (R - t - 1) := by positivity
  -- `p_t` as a real: `2^(a_t-1) + d`
  have hpr : (entryCopies R t x_out lam : ℝ)
      = (2 : ℝ) ^ (R - t - 1) + (entryExcess x_out lam : ℝ) := by
    unfold entryCopies entryLevel
    push_cast; ring
  -- ceiling upper bound `d < L/λ + 1`
  have hLlam0 : 0 ≤ entryDefect x_out / lam := le_of_lt (div_pos hL0 hlam)
  have hdceil : (entryExcess x_out lam : ℝ) < entryDefect x_out / lam + 1 := by
    unfold entryExcess
    exact_mod_cast Nat.ceil_lt_add_one hLlam0
  -- `L/λ ≤ 2^(R-3)·δ ≤ 2^(a_t-1)·δ` from the first package bound
  have hpow2 : (2 : ℝ) ^ (R - 3) ≤ (2 : ℝ) ^ (R - t - 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hLlam_le : entryDefect x_out / lam ≤ (2 : ℝ) ^ (R - t - 1) * δ := by
    have hδlam : 0 < δ * lam := mul_pos hδ0 hlam
    have h8L : 8 * entryDefect x_out ≤ (2 : ℝ) ^ R * (δ * lam) :=
      (div_le_iff₀ hδlam).mp hQL
    have hpowR3 : (2 : ℝ) ^ R = 8 * (2 : ℝ) ^ (R - 3) := by
      rw [show (8 : ℝ) = (2 : ℝ) ^ 3 by norm_num, ← pow_add]
      congr 1; omega
    have h3 : entryDefect x_out / lam ≤ (2 : ℝ) ^ (R - 3) * δ := by
      rw [div_le_iff₀ hlam]
      rw [hpowR3] at h8L
      nlinarith [h8L]
    calc entryDefect x_out / lam ≤ (2 : ℝ) ^ (R - 3) * δ := h3
      _ ≤ (2 : ℝ) ^ (R - t - 1) * δ :=
          mul_le_mul_of_nonneg_right hpow2 (le_of_lt hδ0)
  have hd_final : (entryExcess x_out lam : ℝ) - 1 < (2 : ℝ) ^ (R - t - 1) * δ := by
    linarith [hdceil, hLlam_le]
  -- PART (A): `p_t ≤ Q`
  have hApart : entryCopies R t x_out lam ≤ 2 ^ R := by
    have hP1half : (2 : ℝ) ^ (R - t - 1) ≤ (2 : ℝ) ^ R / 2 := by
      have hle : (2 : ℝ) ^ (R - t - 1) ≤ (2 : ℝ) ^ (R - 1) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have heq : (2 : ℝ) ^ (R - 1) = (2 : ℝ) ^ R / 2 := by
        rw [eq_div_iff (by norm_num : (2 : ℝ) ≠ 0), ← pow_succ]
        congr 1; omega
      linarith [hle, heq]
    have hR4 : (16 : ℝ) ≤ (2 : ℝ) ^ R := by
      calc (16 : ℝ) = (2 : ℝ) ^ 4 := by norm_num
        _ ≤ (2 : ℝ) ^ R := pow_le_pow_right₀ (by norm_num) hR
    have hdrbound : (entryExcess x_out lam : ℝ) < (2 : ℝ) ^ (R - t - 1) / 2 + 1 := by
      have hδP1 : (2 : ℝ) ^ (R - t - 1) * δ < (2 : ℝ) ^ (R - t - 1) * (1 / 2) :=
        mul_lt_mul_of_pos_left hδ hP1_pos
      have hhalf : (2 : ℝ) ^ (R - t - 1) * (1 / 2) = (2 : ℝ) ^ (R - t - 1) / 2 := by ring
      linarith [hd_final, hδP1, hhalf]
    have hlt : (entryCopies R t x_out lam : ℝ) < (2 : ℝ) ^ R := by
      rw [hpr]; linarith [hP1half, hdrbound, hR4]
    have h2 : ((2 ^ R : ℕ) : ℝ) = (2 : ℝ) ^ R := by push_cast; ring
    rw [← h2] at hlt
    exact le_of_lt (by exact_mod_cast hlt)
  -- ingredients for PART (B)
  have hp1nat : 1 ≤ entryCopies R t x_out lam := by
    have h2 : 1 ≤ 2 ^ (entryLevel R t - 1) := Nat.one_le_two_pow
    unfold entryCopies; omega
  have hA1nat : 1 ≤ rowThreshold m x (entryLevel R t) :=
    rowThreshold_pos m x (entryLevel R t) hm hx0
  have hAlo : (0 : ℝ) ≤ (rowThreshold m x (entryLevel R t) : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (rowThreshold m x (entryLevel R t) : ℝ) := by exact_mod_cast hA1nat
    linarith
  have hpr1 : (1 : ℝ) ≤ (entryCopies R t x_out lam : ℝ) := by exact_mod_cast hp1nat
  have h2a : (2 : ℝ) ^ (entryLevel R t) = 2 * (2 : ℝ) ^ (R - t - 1) := by
    have hel : entryLevel R t = (R - t - 1) + 1 := by unfold entryLevel; omega
    rw [hel, pow_succ]; ring
  have hAup2 : (rowThreshold m x (entryLevel R t) : ℝ) - 1
      < 2 * (m : ℝ) * (2 : ℝ) ^ (R - t - 1) * x := by
    have h0 : 0 ≤ (m : ℝ) * (2 : ℝ) ^ (entryLevel R t) * x := by positivity
    have hc : (rowThreshold m x (entryLevel R t) : ℝ)
        < (m : ℝ) * (2 : ℝ) ^ (entryLevel R t) * x + 1 := by
      unfold rowThreshold
      exact_mod_cast Nat.ceil_lt_add_one h0
    rw [h2a] at hc; nlinarith [hc]
  have hterm1 : ((entryCopies R t x_out lam : ℝ) - 1) * (m : ℝ)
      < (2 : ℝ) ^ (R - t - 1) * (m : ℝ) + (2 : ℝ) ^ (R - t - 1) * δ * (m : ℝ) := by
    rw [hpr]
    have hmul := mul_lt_mul_of_pos_right hd_final hmpos
    nlinarith [hmul]
  have hterm2 : ((2 : ℝ) ^ R - (entryCopies R t x_out lam : ℝ) + 1)
        * ((rowThreshold m x (entryLevel R t) : ℝ) - 1)
      < (m : ℝ) * (2 : ℝ) ^ (R - t - 1) * δ := by
    have hstep1 : ((2 : ℝ) ^ R - (entryCopies R t x_out lam : ℝ) + 1)
          * ((rowThreshold m x (entryLevel R t) : ℝ) - 1)
        ≤ (2 : ℝ) ^ R * ((rowThreshold m x (entryLevel R t) : ℝ) - 1) := by
      apply mul_le_mul_of_nonneg_right _ hAlo
      linarith [hpr1]
    have hstep2 : (2 : ℝ) ^ R * ((rowThreshold m x (entryLevel R t) : ℝ) - 1)
        ≤ (2 : ℝ) ^ R * (2 * (m : ℝ) * (2 : ℝ) ^ (R - t - 1) * x) :=
      mul_le_mul_of_nonneg_left (le_of_lt hAup2) (le_of_lt hQr_pos)
    have hstep3 : (2 : ℝ) ^ R * (2 * (m : ℝ) * (2 : ℝ) ^ (R - t - 1) * x)
        < (m : ℝ) * (2 : ℝ) ^ (R - t - 1) * δ := by
      have hpos : (0 : ℝ) < 2 * (m : ℝ) * (2 : ℝ) ^ (R - t - 1) := by positivity
      have key : (2 : ℝ) ^ R * (2 * (m : ℝ) * (2 : ℝ) ^ (R - t - 1) * x)
          = (2 * (m : ℝ) * (2 : ℝ) ^ (R - t - 1)) * ((2 : ℝ) ^ R * x) := by ring
      rw [key]
      calc (2 * (m : ℝ) * (2 : ℝ) ^ (R - t - 1)) * ((2 : ℝ) ^ R * x)
          < (2 * (m : ℝ) * (2 : ℝ) ^ (R - t - 1)) * (δ / 2) :=
            mul_lt_mul_of_pos_left hQx hpos
        _ = (m : ℝ) * (2 : ℝ) ^ (R - t - 1) * δ := by ring
    linarith [hstep1, hstep2, hstep3]
  have hcast : ((entryRowBound (2 ^ R) m (entryCopies R t x_out lam)
        (rowThreshold m x (entryLevel R t)) : ℕ) : ℝ)
      = ((entryCopies R t x_out lam : ℝ) - 1) * (m : ℝ)
        + ((2 : ℝ) ^ R - (entryCopies R t x_out lam : ℝ) + 1)
          * ((rowThreshold m x (entryLevel R t) : ℝ) - 1) := by
    unfold entryRowBound
    push_cast [Nat.cast_sub hp1nat, Nat.cast_sub hA1nat, Nat.cast_sub hApart]
    ring
  have hRHS : (2 : ℝ) ^ R * (m : ℝ) * y / 2 ^ t
      = 2 * (2 : ℝ) ^ (R - t - 1) * (m : ℝ) * y := by
    have hdiv : (2 : ℝ) ^ R / (2 : ℝ) ^ t = (2 : ℝ) ^ (R - t) :=
      (pow_sub₀ (2 : ℝ) (by norm_num) (by omega)).symm
    have h2rt : (2 : ℝ) ^ (R - t) = 2 * (2 : ℝ) ^ (R - t - 1) := by
      cases' hc : R - t with n
      · omega
      · simp only [Nat.succ_sub_one, pow_succ]; ring
    have hfactor : (2 : ℝ) ^ R * (m : ℝ) * y / 2 ^ t
        = ((2 : ℝ) ^ R / 2 ^ t) * ((m : ℝ) * y) := by ring
    rw [hfactor, hdiv, h2rt]; ring
  have hBpart : ((entryRowBound (2 ^ R) m (entryCopies R t x_out lam)
        (rowThreshold m x (entryLevel R t)) : ℕ) : ℝ)
      < (2 : ℝ) ^ R * (m : ℝ) * y / 2 ^ t := by
    rw [hcast, hRHS]
    have hy2 : 2 * (2 : ℝ) ^ (R - t - 1) * (m : ℝ) * y
        = (2 : ℝ) ^ (R - t - 1) * (m : ℝ)
          + 2 * (2 : ℝ) ^ (R - t - 1) * (m : ℝ) * δ := by rw [hyδ]; ring
    nlinarith [hterm1, hterm2, hy2]
  exact ⟨hApart, hBpart⟩

/-- **Package side condition (note §6/§7 glue).** The third package bound
`Qx < δ/2` already yields the note §2 side condition `2^(R-t)·x ≤ 1` at every
entry level — so a package choice discharges `theorem_two`'s `hax` as well.
JUDGE FLAG: not part of the note's literal (23)⟹(21) claim; provided
because §7 ("Choose `Q` and the first-wrapper row depth so that (2) and (23)
hold") consumes exactly this composition. -/
theorem package_row_scale (R t : ℕ) (x δ : ℝ)
    (hx0 : 0 < x) (hδ : δ < 1 / 2)
    (hQx : (2 : ℝ) ^ R * x < δ / 2) :
    (2 : ℝ) ^ (R - t) * x ≤ 1 := by
  have h1 : (2 : ℝ) ^ (R - t) ≤ (2 : ℝ) ^ R :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le R t)
  have h2 : (2 : ℝ) ^ (R - t) * x ≤ (2 : ℝ) ^ R * x :=
    mul_le_mul_of_nonneg_right h1 hx0.le
  linarith

end EthBridge
