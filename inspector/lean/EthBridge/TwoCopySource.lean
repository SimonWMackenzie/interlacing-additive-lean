import Mathlib
import NPCC.Defs
import NPCC.DefsAux
import NPCC.Complexity
import NPCC.ComplexityAux
import NPCC.Engine
import NPCC.CoordProjection
import EthBridge.Arith
import EthBridge.Defs
import EthBridge.Hypotheses
import EthBridge.Entry

/-! # EthBridge `(Two)` from three top H3 clauses (Tranche E5)

Statement-only (`sorry`) signatures for the E5 obligation, drafted for
faithfulness sign-off BEFORE any proving (source:
`eth-docs/REENTRY_TWO_COPY_BASE_FROM_TOP_H3.md`, §2 "Setup And Hypotheses",
§3 "Extraction Of The Three One-Copy U Bounds" (5)–(6), §4 "Transposition And
The Two-Copy Ladder" (7)–(8)/(TB-Lambda)).

E5 is the MIRROR IMAGE of E4: `Entry.lean` CONSUMES `TwoCopyBundle` (the
first-wrapper `(Two)` input of Theorems 1–2); this file PRODUCES it — the
note "removes the re-entry two-copy base `(TB)` as an independent q-layered
`M3` obligation", deriving it from three top-rung first-wrapper H3 clauses
for the inner game `N` at active levels `r, r-1, r-2`.

Cast of parameters (note §2, with `q = 2^r`):

* `N : X → Y → Bool`   — the inner `m_N × n_N` game (`m_N = card X`,
                          `n_N = card Y`);
* `U = Interlace(N,q)` — `interlaceFun N (2^r)`;
* `W = transpose(U)`   — `Rnext N (2^r)` (the E4 def `Rnext`, Entry.lean:181,
                          reused: `Rnext N q c r = interlaceFun N q r c`.
                          JUDGE FLAG: in E4 `Rnext W Q` was the NEXT-round
                          robust test built from the current `W`; here the
                          SAME def applied to the inner `N` is this note's
                          `W` itself. Same formal object, shifted role);
* `m_W = n_N^q`        — `Fintype.card Y ^ 2^r = card (Fin (2^r) → Y)`;
* `C = D_* + r`        — carried as an equation `hC : C = Dstar + r`
                          (fidelity, cf. `hyδ` in `uniform_package`);
* `y = 1/2 + δ`        — `hyδ`, with `0 < δ ≤ 1/√2 - 1/2` (note §2: "The
                          upper bound on `delta` is the usual condition
                          `2y^2 ≤ 1`");
* `x = T_1^W/(2m_W)`   — note (1), carried as `hxdef`; `1 ≤ T_1^W ≤ m_W`
                          gives `0 < x ≤ 1/2`;
* `T : ℕ → ℕ`          — the first-wrapper integer row thresholds `T_a^N`,
                          indexed by the active level `a` (the note writes
                          `T_(r-t)^N`; here `T (entryLevel r t)`);
* `Y_0`                — the common first-wrapper top column density,
                          note (2): "Fix a first-wrapper top column density
                          `Y_0` satisfying `0 < Y_0 <= x`."  (see the
                          DENSITY FLAG below);
* for `t = 0,1,2`      — `a_t = r-t` (reuse `entryLevel`),
                          `p_t = 2^(a_t-1)+1 = q/2^(t+1)+1` (`srcCopies`),
                          `ρ_t = y/2^t` (inlined, as in E4).

New defs (each with unit tests below, BtL discipline):

* `srcCopies`     — `p_t = 2^(a_t-1) + 1`                        (note (3));
* `TopH3Clauses`  — the hypothesis bundle `(H3_t)`, `t = 0,1,2`  (note §2);
* `RowCountSmall` — the row-count inequalities (4), `t = 0,1,2`.

Sorry-signature decomposition of the note proof:

* `src_rowbound_lt`       — §3's division argument: under (4) the few-good
                            row cap (6) is strictly below `ρ_t·q·m_N`
                            (single-`t` real arithmetic; stripped-down analog
                            of `uniform_package` Part B);
* `source_one_copy_V`     — §3 Lemma, per-member V-side core (the OUTER-COPY
                            COUNTING step): good-block counting (HB-4 reuse)
                            → `coord_projection` at target density `Y_0` →
                            `(H3_t)` + `Dfamily_le_member` →
                            `projected_subgame_le` (HB-5 reuse);
* `source_one_copy_U`     — §3 Lemma (5) note-literal:
                            `comp(bracket(U,1,ρ_t,x)) ≥ C-1-t`, the thin
                            one-copy `Dfamily` wrapper (HB-2 + HB-3 reuse,
                            same collapse idiom as `theorem_two`);
* `source_one_copy_W`     — §4 TRANSPOSE step: one-copy transpose symmetry
                            turns (5) into (7), the three one-copy states of
                            `W` at column densities `y, y/2, y/4` (= row
                            densities `ρ_0, ρ_1, ρ_2` in `U`) at row scale
                            `x` (HB-1 reuse; stated generically in the
                            target `k` and density `ρ`);
* `two_copy_bundle_of_rungs` — §4 TWO-COPY LADDER application + (TB-Lambda)
                            assembly: `NPCC.two_copy_ladder` (Engine.lean:43,
                            the manuscript ORDINARY ladder — NOT
                            `robust_two_copy_ladder`, whose rungs come from
                            `IsRobust`) at `M = W`, `H = C-1`, then the three
                            ℝ-cast rungs (8) reassemble to
                            `C ≤ LambdaGE W 2 (2x) (y²)` (the inverse of the
                            `TwoCopyBundle.{top,mid,bottom}_rung` accessors,
                            UnitTests.lean:159/166/174);
* `two_copy_from_H3`      — the CAPSTONE: `TopH3Clauses` + (2) + (4) ⟹
                            `TwoCopyBundle (Rnext N (2^r)) C x y`.

Small arithmetic helpers (`sorry`): `srcCopies_le_pow`, `srcCopies_eq_div`,
`ceil_mul_div_self`, `two_x_row_threshold`, `Dfamily_le_member`.

GLOBAL JUDGE FLAGS (individual flags at each declaration).

* **DENSITY FLAG (the exact `Y_0` correspondence).** The note fixes ONE
  common column density for all three H3 clauses, constrained only by
  note (2): `0 < Y_0 <= x`.  Its §5 "Standard Threshold Specialization"
  then says the INTENDED size-dependent value is note (10):
  `Y_0 = 2^(-B_W)` — "This is the intended size-dependent rung. It may be
  inverse-polynomial in the current construction size; it is not required
  to be a constant."  This file keeps `Y0` an abstract ℝ parameter with (2)
  as use-site hypotheses (`hY00 : 0 < Y0`, `hY0x : Y0 ≤ x`) and does NOT
  bake in (10) — the §5 specialization (standard thresholds
  `T_a^N = ⌈2^(a-B_N)·m_N⌉`, condition (9), choice (10)) is a separate,
  not-yet-drafted convenience layer. The judge confirms this is the right
  cut (it matches the note's §2/§6 phrasing "at the common density
  `Y_0 <= x`").
* **H3-MENU FLAG.** The note §6 keys the three clauses to the first-wrapper
  H3 menu as `(a,j) = (r,0), (r-1,0), (r-2,0)` — a `j`-indexed menu that has
  NO formal counterpart in this repo yet. `TopH3Clauses` therefore states
  the three clauses directly as a `∀ t ≤ 2` bundle of `Dfamily` lower
  bounds (the same quantifier shape as `uniform_package`'s conclusion), with
  `j = 0` ("top-rung") reflected only in using the single top density `Y_0`.
  The judge signs off that this is the faithful rendering of `(H3_t)` absent
  the menu formalization; an alternative is three named fields.
* **ℕ-subtraction discipline.** The `(H3_t)` target `D_* + a_t - 1` is
  rendered `Dstar + entryLevel r t - 1` (left-assoc: `(Dstar + a_t) - 1`),
  exact whenever `1 ≤ Dstar + a_t` — automatic under `t ≤ 2 < 3 ≤ r`
  (`a_t ≥ 1`), no extra hypothesis needed. The (5) target `C - 1 - t`
  appears in `source_one_copy_*` as the SAME expression
  `Dstar + entryLevel r t - 1` (equality `D_*+a_t-1 = D_*+r-t-1 = C-1-t`
  is the note's own §3 last display; the capstone converts via `hC` and
  `omega`). The rung targets in `two_copy_bundle_of_rungs` are `C - 1`,
  `C - 2`, `C - 3`, exact under `hC4 : 4 ≤ C` (note §4: "Since `r>=3` and
  `D_*>=1`, we have `C>=4`, so the lowest target in (7) is positive and
  there is no zero-target first-bit issue" — `hC4` also discharges the
  ladder guard `hH : 1 < H` at `H = C-1`).
* **Threshold-range flag.** `good_blocks_count` needs `1 ≤ A ≤ m_N + 1` for
  `A = T (entryLevel r t)`. The note never states a range for `T_a^N`
  explicitly, but (4) + `δ ≤ 1/√2 - 1/2 < 1/2` forces
  `T_a^N - 1 < m_N·2δ < m_N`, i.e. `T_a^N ≤ m_N`. The counting core carries
  `hT1`/`hTm` explicitly (abstract residue, as E4 carried `hAm`); the
  capstone derives `hTm` from (4) and carries only `hT1 : 1 ≤ T …`
  (positivity of an "integer row threshold" — judge confirms reading
  `T_a^N ≥ 1` into the note's §2).
* **(4) rendering.** Strict `<`, LHS the real `(T_(r-t)^N - 1)/m_N` with ℕ
  values cast (`T ≥ 1` keeps the numerator's `- 1` faithful in ℝ — it is
  REAL subtraction here, no ℕ truncation), RHS `2δ/(2^(t+1) - 1)` with
  `(2:ℝ)^(t+1)` a real power. Literal to the note.
* **Where each §2 bound is consumed.** `hδhi : δ ≤ 1/√2 - 1/2` is consumed
  ONLY for `y ≤ 1` (`y = 1/2 + δ ≤ 1/√2 < 1`) and for the `hTm` derivation
  (`δ < 1/2`); the ladder itself needs only `y ≤ 1`, strictly weaker than
  the note's `2y² ≤ 1` (which the DOWNSTREAM direct-stopping theorem, not
  this reduction, requires). `1 ≤ T_1^W ≤ m_W` + `hxdef` give
  `0 < x ≤ 1/2` (note (1)), the ladder's `hx0`/`hx`.
* **(1)'s row-threshold remark is scaffolding.** The note's "the two-copy
  row threshold at parameter `2x` is exactly `T_1^W`" (`⌈m_W·2x⌉ = T_1^W`)
  is NOT needed to conclude `TwoCopyBundle` (which is density-parametrized);
  it is recorded as the fidelity helper `two_x_row_threshold` for the
  downstream `(TB)` reader. Similarly `ceil_mul_div_self` pins the H3
  bracket's row threshold to the literal integer `T_(a_t)^N`.
* **Wrapper-agnostic §4 (note update 2026-07-11).** For the materialized
  rectangle-reservoir wrapper, eqs (17)–(18) of
  `RELAXED_FIRST_WRAPPER_PROTOCOL_INVARIANT.md` request the same three
  one-copy `W` bounds (7) directly; `source_one_copy_W` +
  `two_copy_bundle_of_rungs` (and hence the §4 half of the capstone) apply
  unchanged. Only `TopH3Clauses`/`source_one_copy_V/U` (§3) are
  full-product-proof-model specific.
* **`r ≥ 3` vs E4's `R ≥ 4`.** This note's §2 fixes `r ≥ 3` (enough for
  `a_2 = r - 2 ≥ 1` and `C ≥ 4`); E4's `hR : 4 ≤ R` came from ITS note §5.
  Not a discrepancy — different notes, different ambient interlace.

DISCIPLINE: statements only; every load-bearing body is `sorry` until the
faithfulness judge signs off against the note's literal §2–§4 text. The one
new def is ℕ-valued (`srcCopies`); its inhabitation/sanity unit lemmas are
inline below (the judge may relocate them to `EthBridge/UnitTests.lean` per
E0 convention). Trivial fidelity tests (`rfl`/`Iff.rfl`/`omega`) are
discharged; everything else is `sorry`.
-/

namespace EthBridge

open NPCC
open Workspace.Types.Interlace
open Workspace.Types.CommComplexity

/-! ## Note (3): the source copy counts `p_t`

`a_t = r - t` is the E4 def `entryLevel` reused (same ℕ-subtraction
discipline: exact under `t ≤ 2 < 3 ≤ r`). -/

/-- **Note (3)**: `p_t = 2^(a_t-1) + 1`. The excess over the base power
`2^(a_t-1)` is the LITERAL `+ 1` here (contrast E4's `entryCopies`, whose
excess is the defect-paid `d = ⌈L/λ⌉`): the H3 clauses hand the projection
a column set that is ALREADY `Y_0`-dense, so one excess copy suffices.
Equivalent form `q/2^(t+1) + 1` in `srcCopies_eq_div`. -/
def srcCopies (r t : ℕ) : ℕ :=
  2 ^ (entryLevel r t - 1) + 1

/-! ## The H3-clause hypothesis bundle (note §2, `(H3_t)`)

> Assume the three top-rung H3 clauses
>
> ```
> comp(bracket(N,p_t,T_(a_t)^N/m_N,Y_0)) >= D_*+a_t-1.        (H3_t)
> ```

Stated as a bare predicate `def` for the faithfulness judge, mirroring
`NearFull`/`TwoCopyBundle` (Hypotheses.lean). See the DENSITY FLAG and
H3-MENU FLAG in the file header: `Y0` is the note (2) common density
(`0 < Y_0 ≤ x` at use sites; intended §5 value (10) `Y_0 = 2^(-B_W)` NOT
baked in), and the `∀ t ≤ 2` quantifier renders the §6 menu entries
`(a,j) = (r,0), (r-1,0), (r-2,0)`. -/

/-- **Note §2 `(H3_t)`, all three clauses** (`t = 0,1,2`): the `p_t`-copy
first-wrapper family of `N` at row density `T_(a_t)^N/m_N` (row threshold
literally `T_(a_t)^N`, cf. `ceil_mul_div_self`) and top column density `Y_0`
has complexity at least `D_* + a_t - 1`. -/
def TopH3Clauses {X Y : Type*} [Fintype X] [Fintype Y]
    (N : X → Y → Bool) (Dstar r : ℕ) (T : ℕ → ℕ) (Y0 : ℝ) : Prop :=
  ∀ t : ℕ, t ≤ 2 →
    Dstar + entryLevel r t - 1 ≤
      Dfamily (interlaceFun N (srcCopies r t))
        (bracketGE X Y (srcCopies r t)
          ((T (entryLevel r t) : ℝ) / (Fintype.card X : ℝ)) Y0)

/-- **Note (4), all three inequalities** (`t = 0,1,2`):
`(T_(r-t)^N - 1)/m_N < 2δ/(2^(t+1) - 1)`. Real subtraction and division;
strict, literal to the note. -/
def RowCountSmall (m : ℕ) (T : ℕ → ℕ) (r : ℕ) (δ : ℝ) : Prop :=
  ∀ t : ℕ, t ≤ 2 →
    ((T (entryLevel r t) : ℝ) - 1) / (m : ℝ) < 2 * δ / ((2 : ℝ) ^ (t + 1) - 1)

/-! ## Sanity / unit lemmas for the new defs (BtL discipline)

JUDGE FLAG: inline rather than in `UnitTests.lean` because several are
load-bearing helper obligations (E4 precedent); the judge may relocate the
pure fidelity checks. -/

/-- `p_t ≥ 1` (a genuine copy count); feeds `good_blocks_count`'s `hp1` and
`coord_projection`'s `hr`. -/
theorem srcCopies_pos (r t : ℕ) : 1 ≤ srcCopies r t :=
  Nat.le_add_left 1 _

/-- Fidelity to note (3)'s second form: `p_t = q/2^(t+1) + 1` (`q = 2^r`,
exact ℕ division for `t < r`). Also certifies §3's "`p_t - 1 = q/2^(t+1)`". -/
theorem srcCopies_eq_div (r t : ℕ) (htr : t < r) :
    srcCopies r t = 2 ^ r / 2 ^ (t + 1) + 1 := by
  unfold srcCopies entryLevel
  rw [Nat.pow_div (by omega) (by norm_num), show r - t - 1 = r - (t + 1) from by omega]

/-- `p_t ≤ q` — the standing block-count bound `good_blocks_count` needs
(`2^(r-t-1) + 1 ≤ 2^r` for `t < r`; the note's §1 "q/2+1, q/4+1, q/8+1"
outer-copy counts all fit inside the `q` outer blocks). -/
theorem srcCopies_le_pow (r t : ℕ) (htr : t < r) :
    srcCopies r t ≤ 2 ^ r := by
  unfold srcCopies entryLevel
  have h1 : 2 ^ (r - t - 1) ≤ 2 ^ (r - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ r = 2 * 2 ^ (r - 1) := by
    conv_lhs => rw [show r = (r - 1) + 1 from by omega]
    rw [pow_succ]; ring
  have h3 : 1 ≤ 2 ^ (r - 1) := Nat.one_le_two_pow
  omega

/-- Numeric spot checks at `r = 3` (`q = 8`): `p_0, p_1, p_2 = 5, 3, 2`
(note §1: densities `y, y/2, y/4` "force respectively `q/2+1, q/4+1, q/8+1`
outer copies"). -/
example : srcCopies 3 0 = 5 := rfl
example : srcCopies 3 1 = 3 := rfl
example : srcCopies 3 2 = 2 := rfl

/-- Statement fidelity: `TopH3Clauses` is definitionally the `∀ t ≤ 2` bundle
of the three `(H3_t)` `Dfamily` bounds. -/
example {X Y : Type*} [Fintype X] [Fintype Y] (N : X → Y → Bool)
    (Dstar r : ℕ) (T : ℕ → ℕ) (Y0 : ℝ) :
    TopH3Clauses N Dstar r T Y0 ↔
      ∀ t : ℕ, t ≤ 2 →
        Dstar + entryLevel r t - 1 ≤
          Dfamily (interlaceFun N (srcCopies r t))
            (bracketGE X Y (srcCopies r t)
              ((T (entryLevel r t) : ℝ) / (Fintype.card X : ℝ)) Y0) :=
  Iff.rfl

/-- Well-formedness / inhabitability: `TopH3Clauses` holds vacuously at
`Dstar = 0`, `r = 0` (every target ℕ-truncates to `0`). -/
example {X Y : Type*} [Fintype X] [Fintype Y] (N : X → Y → Bool)
    (T : ℕ → ℕ) (Y0 : ℝ) :
    TopH3Clauses N 0 0 T Y0 := by
  intro t _
  have h : 0 + entryLevel 0 t - 1 = 0 := by unfold entryLevel; omega
  rw [h]
  exact Nat.zero_le _

/-- Statement fidelity: `RowCountSmall` is definitionally the `∀ t ≤ 2`
bundle of the three (4) inequalities. -/
example (m : ℕ) (T : ℕ → ℕ) (r : ℕ) (δ : ℝ) :
    RowCountSmall m T r δ ↔
      ∀ t : ℕ, t ≤ 2 →
        ((T (entryLevel r t) : ℝ) - 1) / (m : ℝ)
          < 2 * δ / ((2 : ℝ) ^ (t + 1) - 1) :=
  Iff.rfl

/-! ## Small arithmetic helpers -/

/-- The H3 bracket's row threshold is the LITERAL integer `T`:
`⌈m·(T/m)⌉₊ = T` for `m ≥ 1`. Instantiates `coord_projection`'s `hxT` as an
equality (no slack on the row side; the E5 analog of E4's
`rowThreshold`-equality flag) and certifies `TopH3Clauses`'s density
`T_(a_t)^N/m_N` reads back as row threshold `T_(a_t)^N`. -/
theorem ceil_mul_div_self (m T : ℕ) (hm : 1 ≤ m) :
    ⌈(m : ℝ) * ((T : ℝ) / (m : ℝ))⌉₊ = T := by
  have hm0 : (m : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    linarith
  have hmul : (m : ℝ) * ((T : ℝ) / (m : ℝ)) = (T : ℝ) := by
    field_simp
  rw [hmul, Nat.ceil_natCast]

/-- **Note (1)'s closing remark** (fidelity scaffolding, NOT consumed by the
capstone — see file-header flag): at `x = T_1^W/(2m_W)` the two-copy row
threshold at parameter `2x` is exactly `T_1^W`: `⌈m_W·(2x)⌉₊ = T_1^W`. -/
theorem two_x_row_threshold (mW T1W : ℕ) (hm : 1 ≤ mW) :
    ⌈(mW : ℝ) * (2 * ((T1W : ℝ) / (2 * (mW : ℝ))))⌉₊ = T1W := by
  have hm0 : (mW : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (mW : ℝ) := by exact_mod_cast hm
    linarith
  have hmul : (mW : ℝ) * (2 * ((T1W : ℝ) / (2 * (mW : ℝ)))) = (T1W : ℝ) := by
    field_simp
  rw [hmul, Nat.ceil_natCast]

/-- The dual of `le_Dfamily` (HB-2): `Dfamily` is at most the complexity of
any member (`Nat.sInf_le`). §3's "Apply `(H3_t)`" composes this with the
clause: `target ≤ Dfamily ≤ D(projected member)`. -/
theorem Dfamily_le_member {A B : Type*} (f : A → B → Bool)
    (Φ : Set (Finset A × Finset B)) (RC : Finset A × Finset B) (hRC : RC ∈ Φ) :
    Dfamily f Φ ≤ D (subgame f RC.1 RC.2) := by
  unfold Dfamily
  exact Nat.sInf_le ⟨RC, hRC, rfl⟩

/-! ## §3's division argument: (6) `< ρ_t·q·m_N` under (4)

Note §3: "After division by `qm_N`, expression (6) is
`1/2^(t+1) + (1-1/2^(t+1))(T_(a_t)^N-1)/m_N`. By (4), this is strictly less
than `1/2^(t+1) + δ/2^t = (1/2+δ)/2^t = ρ_t`. Hence (6) is strictly less
than `ρ_t q m_N`."

Stripped-down single-`t` analog of `uniform_package` Part B
(Entry.lean:949–1002); the RHS is stated in the exact shape of E4's `h21`
(`2^r·m·y/2^t`, ℕ-cast LHS, strict `<`) so the consuming site converts to
`good_blocks_count`'s `hcard` by the same `Nat.le_ceil` chain as
`theorem_two_V`. JUDGE FLAG: `hA : 1 ≤ A` keeps the ℝ-cast of
`entryRowBound`'s ℕ-subtraction `A - 1` exact (`Nat.cast_sub`), as in E4's
`hcast`. -/

/-- **Note §3, the division argument.** Under a single (4) inequality at
level `a_t`, the few-good row cap `(p_t-1)·m_N + (q-p_t+1)·(T_(a_t)^N-1)`
(= `entryRowBound q m_N p_t T_(a_t)^N`, note (6)) is strictly below
`ρ_t·q·m_N = q·m_N·y/2^t`. -/
theorem src_rowbound_lt (r t m A : ℕ) (δ y : ℝ)
    (hr : 3 ≤ r) (ht : t ≤ 2) (hm : 1 ≤ m) (hA : 1 ≤ A)
    (hδ0 : 0 < δ) (hyδ : y = 1 / 2 + δ)
    (h4 : ((A : ℝ) - 1) / (m : ℝ) < 2 * δ / ((2 : ℝ) ^ (t + 1) - 1)) :
    ((entryRowBound (2 ^ r) m (srcCopies r t) A : ℕ) : ℝ)
      < (2 : ℝ) ^ r * (m : ℝ) * y / 2 ^ t := by
  have htr : t < r := by omega
  have hp_pos : 1 ≤ srcCopies r t := srcCopies_pos r t
  have hp_le : srcCopies r t ≤ 2 ^ r := srcCopies_le_pow r t htr
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hPpos : (0 : ℝ) < (2 : ℝ) ^ (r - t - 1) := by positivity
  have hSpos : (0 : ℝ) < (2 : ℝ) ^ (t + 1) - 1 := by
    have h1 : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ (t + 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    simp only [pow_one] at h1; linarith
  have hsplit : (2 : ℝ) ^ r = (2 : ℝ) ^ (t + 1) * (2 : ℝ) ^ (r - t - 1) := by
    rw [← pow_add]; congr 1; omega
  -- cast the ℕ few-good cap to reals
  have hpcast : ((srcCopies r t : ℕ) : ℝ) = (2 : ℝ) ^ (r - t - 1) + 1 := by
    simp only [srcCopies, entryLevel]; push_cast; ring
  have hcast : ((entryRowBound (2 ^ r) m (srcCopies r t) A : ℕ) : ℝ)
      = (2 : ℝ) ^ (r - t - 1) * (m : ℝ)
        + ((2 : ℝ) ^ r - (2 : ℝ) ^ (r - t - 1)) * ((A : ℝ) - 1) := by
    unfold entryRowBound
    push_cast [Nat.cast_sub hp_pos, Nat.cast_sub hA, Nat.cast_sub hp_le]
    rw [hpcast]; ring
  -- (4) cleared of denominators
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  have hS0 : (2 : ℝ) ^ (t + 1) - 1 ≠ 0 := ne_of_gt hSpos
  have h4' : ((A : ℝ) - 1) * ((2 : ℝ) ^ (t + 1) - 1) < 2 * δ * (m : ℝ) := by
    have hlt := mul_lt_mul_of_pos_right h4 (mul_pos hmpos hSpos)
    have e1 : ((A : ℝ) - 1) / (m : ℝ) * ((m : ℝ) * ((2 : ℝ) ^ (t + 1) - 1))
        = ((A : ℝ) - 1) * ((2 : ℝ) ^ (t + 1) - 1) := by field_simp
    have e2 : 2 * δ / ((2 : ℝ) ^ (t + 1) - 1) * ((m : ℝ) * ((2 : ℝ) ^ (t + 1) - 1))
        = 2 * δ * (m : ℝ) := by field_simp
    rw [e1, e2] at hlt; exact hlt
  -- RHS in terms of `2^(r-t-1)`
  have hRHS : (2 : ℝ) ^ r * (m : ℝ) * y / (2 : ℝ) ^ t
      = 2 * (2 : ℝ) ^ (r - t - 1) * (m : ℝ) * y := by
    rw [div_eq_iff (by positivity : (2 : ℝ) ^ t ≠ 0), hsplit, pow_succ]; ring
  rw [hcast, hRHS, hyδ, hsplit]
  nlinarith [mul_pos hPpos (sub_pos.mpr h4'), hPpos, hmpos, hδ0]

/-! ## §3 Lemma — the outer-copy counting core (V side)

Note §3 proof, per fixed member of `bracket(U,1,ρ_t,x)` with row set
`R ⊆ [q] × Rows(N)` and column set `K ⊆ Cols(N)^q`:

good blocks (`≥ T_(a_t)^N` retained rows) → fewer than `p_t` good caps the
row count at (6) (`card_le_entryRowBound_of_few_good`) → contradiction with
`|R| ≥ ⌈ρ_t·q·m_N⌉` via `src_rowbound_lt` (so `good_blocks_count` yields
`≥ p_t` good blocks) → "Choose exactly `p_t` of them"
(`exists_good_block_choice`) → "project `K` to those coordinates" — DIRECTLY
`NPCC.coord_projection` at target column density `Y_0` (NOT via E4's
`entry_projected_state`/HB-6: the note lands straight in the `Y_0`-dense
bracket, no `exp(-c_a·λ)` defect budget; `hcol` from
`⌈n^q·Y_0⌉₊ ≤ ⌈n^q·x⌉₊ ≤ |K|` under (2), `hxT` the EQUALITY
`ceil_mul_div_self`) → the projected member is in
`bracket(N,p_t,T_(a_t)^N/m_N,Y_0)` → "Apply `(H3_t)`"
(`Dfamily_le_member` + `hH3`) → "the original restriction of `U` is no
easier" (`projected_subgame_le`, HB-5, `emb := fun j => (e j).val`).

JUDGE FLAGS.
* Target `Dstar + entryLevel r t - 1` = the note's `D_*+a_t-1 = C-1-t`
  (§3's last display; ℕ-exact under `t ≤ 2 < 3 ≤ r`, file-header flag).
* `hT1`/`hTm` are the abstract threshold-range residue (file-header flag);
  `hY00` is note (2)'s strict positivity, carried for fidelity though only
  `hY0x` is consumed by the projection.
* Thresholds on `(RU, CU)` are stated as ℕ-ceilings of the note's real
  counts (`⌈ρ_t·q·m_N⌉` with `ρ_t = y/2^t`, `⌈n^q·x⌉`), in the exact E4
  `theorem_two_V` shape, so the U-wrapper's HB-3 collapse lands verbatim. -/

/-- **Note §3 Lemma, V-side core (per-member form).** Under (2), (4) at
level `a_t`, and the `(H3_t)` clauses, every restriction of
`Interlace(N, 2^r)` with at least `⌈q·m_N·(y/2^t)⌉` rows and at least
`⌈n_N^q·x⌉` columns has communication complexity at least
`D_* + a_t - 1 = C - 1 - t`. -/
theorem source_one_copy_V {X Y : Type*} [Fintype X] [Fintype Y]
    (N : X → Y → Bool) (Dstar r t : ℕ) (T : ℕ → ℕ) (Y0 δ y x : ℝ)
    (hr : 3 ≤ r) (ht : t ≤ 2)
    (hm : 1 ≤ Fintype.card X) (hn : 1 ≤ Fintype.card Y)
    (hδ0 : 0 < δ) (hyδ : y = 1 / 2 + δ)
    (hY00 : 0 < Y0) (hY0x : Y0 ≤ x)
    (hT1 : 1 ≤ T (entryLevel r t))
    (hTm : T (entryLevel r t) ≤ Fintype.card X + 1)
    (h4 : ((T (entryLevel r t) : ℝ) - 1) / (Fintype.card X : ℝ)
        < 2 * δ / ((2 : ℝ) ^ (t + 1) - 1))
    (hH3 : TopH3Clauses N Dstar r T Y0)
    (RU : Finset (Fin (2 ^ r) × X)) (CU : Finset (Fin (2 ^ r) → Y))
    (hRU : ⌈((2 ^ r * Fintype.card X : ℕ) : ℝ) * (y / 2 ^ t)⌉₊ ≤ RU.card)
    (hCU : ⌈((Fintype.card Y : ℝ) ^ (2 ^ r : ℕ)) * x⌉₊ ≤ CU.card) :
    Dstar + entryLevel r t - 1 ≤ D (subgame (interlaceFun N (2 ^ r)) RU CU) := by
  classical
  have htr : t < r := by omega
  have hp1 : 1 ≤ srcCopies r t := srcCopies_pos r t
  have hpQ : srcCopies r t ≤ 2 ^ r := srcCopies_le_pow r t htr
  -- the retained row count strictly beats the (6) cap (`src_rowbound_lt`)
  have hcard : entryRowBound (2 ^ r) (Fintype.card X) (srcCopies r t)
      (T (entryLevel r t)) < RU.card := by
    have hle : (2 : ℝ) ^ r * (Fintype.card X : ℝ) * y / 2 ^ t ≤ (RU.card : ℝ) := by
      calc (2 : ℝ) ^ r * (Fintype.card X : ℝ) * y / 2 ^ t
          = ((2 ^ r * Fintype.card X : ℕ) : ℝ) * (y / 2 ^ t) := by
            push_cast; ring
        _ ≤ (⌈((2 ^ r * Fintype.card X : ℕ) : ℝ) * (y / 2 ^ t)⌉₊ : ℝ) :=
            Nat.le_ceil _
        _ ≤ (RU.card : ℝ) := by exact_mod_cast hRU
    have hlt := src_rowbound_lt r t (Fintype.card X) (T (entryLevel r t)) δ y
      hr ht hm hT1 hδ0 hyδ h4
    exact_mod_cast lt_of_lt_of_le hlt hle
  -- ≥ p_t good blocks (note §3 counting); choose EXACTLY p_t of them
  have hgood : srcCopies r t ≤ (goodBlocks RU (T (entryLevel r t))).card :=
    good_blocks_count RU _ _ hT1 hTm hp1 hpQ hcard
  obtain ⟨Qg, hQg, hEq⟩ := exists_good_block_choice RU _ _ hgood
  let e : Fin (srcCopies r t) ≃ {q // q ∈ Qg} :=
    (finCongr hQg.symm).trans Qg.equivFin.symm
  -- project the columns to the chosen blocks at target density `Y_0`
  have hxT : ⌈(Fintype.card X : ℝ)
        * ((T (entryLevel r t) : ℝ) / (Fintype.card X : ℝ))⌉₊
      ≤ T (entryLevel r t) :=
    le_of_eq (ceil_mul_div_self (Fintype.card X) (T (entryLevel r t)) hm)
  have hcol : ⌈((Fintype.card Y : ℝ) ^ (2 ^ r : ℕ)) * Y0⌉₊ ≤ CU.card := by
    refine le_trans (Nat.ceil_mono ?_) hCU
    exact mul_le_mul_of_nonneg_left hY0x (by positivity)
  obtain ⟨RC', hbr, hrowsProv, hcolsProv⟩ :=
    NPCC.coord_projection hp1 e hEq hcol hxT
  -- "Apply (H3_t)": target ≤ Dfamily ≤ D(projected member)
  have hH3t := hH3 t ht
  have hmem := Dfamily_le_member (interlaceFun N (srcCopies r t))
    (bracketGE X Y (srcCopies r t)
      ((T (entryLevel r t) : ℝ) / (Fintype.card X : ℝ)) Y0) RC' hbr
  -- "the original restriction of U is no easier" (HB-5)
  have hproj := projected_subgame_le N (fun j => (e j).val) hrowsProv hcolsProv
  exact le_trans hH3t (le_trans hmem hproj)

/-! ## §3 Lemma (5) — the note-literal one-copy `U` bound

`comp(bracket(U,1,ρ_t,x)) ≥ C-1-t`, `U = Interlace(N,q)`. Thin `Dfamily`
wrapper over the V-side core: `le_Dfamily` (HB-2; nonemptiness from
`bracketGE.nonempty` under `ρ_t ≤ 1`, `x ≤ 1`) + the HB-3 `Fin 1` collapse
(`filter_fst_fin_one`, `card_image_snd_fin_one`,
`card_image_apply_zero_fin_one`, `M1_interlace_one_project_le`) — the exact
double-interlace idiom of `theorem_two` (Entry.lean:790–828) for
`interlaceFun (interlaceFun N (2^r)) 1`. -/

/-- **Note §3 Lemma, (5).** Under (2), (4) at level `a_t`, and `(H3_t)`:
`comp(bracket(U, 1, y/2^t, x)) ≥ D_* + a_t - 1` (`= C - 1 - t`). -/
theorem source_one_copy_U {X Y : Type*} [Fintype X] [Fintype Y]
    (N : X → Y → Bool) (Dstar r t : ℕ) (T : ℕ → ℕ) (Y0 δ y x : ℝ)
    (hr : 3 ≤ r) (ht : t ≤ 2)
    (hm : 1 ≤ Fintype.card X) (hn : 1 ≤ Fintype.card Y)
    (hδ0 : 0 < δ) (hyδ : y = 1 / 2 + δ) (hy1 : y ≤ 1)
    (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hY00 : 0 < Y0) (hY0x : Y0 ≤ x)
    (hT1 : 1 ≤ T (entryLevel r t))
    (hTm : T (entryLevel r t) ≤ Fintype.card X + 1)
    (h4 : ((T (entryLevel r t) : ℝ) - 1) / (Fintype.card X : ℝ)
        < 2 * δ / ((2 : ℝ) ^ (t + 1) - 1))
    (hH3 : TopH3Clauses N Dstar r T Y0) :
    Dstar + entryLevel r t - 1 ≤
      Dfamily (interlaceFun (interlaceFun N (2 ^ r)) 1)
        (bracketGE (Fin (2 ^ r) × X) (Fin (2 ^ r) → Y) 1 (y / 2 ^ t) x) := by
  classical
  have hy0 : 0 < y := by rw [hyδ]; linarith
  have h2t_one : (1 : ℝ) ≤ (2 : ℝ) ^ t := by
    calc (1 : ℝ) = (2 : ℝ) ^ 0 := by norm_num
      _ ≤ (2 : ℝ) ^ t := pow_le_pow_right₀ (by norm_num) (Nat.zero_le t)
  have h2t_pos : (0 : ℝ) < (2 : ℝ) ^ t := by linarith
  have hyx0 : 0 < y / 2 ^ t := div_pos hy0 h2t_pos
  have hyx1 : y / 2 ^ t ≤ 1 := by
    rw [div_le_one h2t_pos]; linarith
  have hcardX' : 1 ≤ Fintype.card (Fin (2 ^ r) × X) := by
    rw [Fintype.card_prod, Fintype.card_fin]
    exact Nat.mul_pos (Nat.two_pow_pos r) hm
  -- HB-2: descend to an arbitrary one-copy member
  apply le_Dfamily
  · exact bracketGE.nonempty 1 (y / 2 ^ t) x hyx1 hx1 hcardX'
  · intro RC hmem
    obtain ⟨hR0, hC0⟩ := hmem
    -- HB-3 + `M1_interlace_one_project_le`: collapse the single copy
    have hcardprod : Fintype.card (Fin (2 ^ r) × X) = 2 ^ r * Fintype.card X := by
      rw [Fintype.card_prod, Fintype.card_fin]
    have hR0card : ⌈(Fintype.card (Fin (2 ^ r) × X) : ℝ) * (y / 2 ^ t)⌉₊
        ≤ RC.1.card := by
      have h := hR0 0 (Finset.mem_univ 0)
      rwa [filter_fst_fin_one] at h
    have hRV : ⌈((2 ^ r * Fintype.card X : ℕ) : ℝ) * (y / 2 ^ t)⌉₊
        ≤ (RC.1.image (fun a => a.2)).card := by
      rw [card_image_snd_fin_one]
      have hc : ((2 ^ r * Fintype.card X : ℕ) : ℝ)
          = (Fintype.card (Fin (2 ^ r) × X) : ℝ) := by rw [hcardprod]
      rw [hc]; exact hR0card
    have hcardfun : Fintype.card (Fin (2 ^ r) → Y) = Fintype.card Y ^ (2 ^ r) := by
      rw [Fintype.card_fun, Fintype.card_fin]
    have hCV : ⌈((Fintype.card Y : ℝ) ^ (2 ^ r : ℕ)) * x⌉₊
        ≤ (RC.2.image (fun c => c 0)).card := by
      rw [card_image_apply_zero_fin_one]
      have hconv : ((Fintype.card (Fin (2 ^ r) → Y) : ℝ)) ^ 1
          = (Fintype.card Y : ℝ) ^ (2 ^ r : ℕ) := by
        rw [pow_one, hcardfun]; push_cast; ring
      rw [← hconv]; exact hC0
    -- V-side core on the collapsed restriction, then re-lift the one copy
    have hV := source_one_copy_V N Dstar r t T Y0 δ y x hr ht hm hn hδ0 hyδ
      hY00 hY0x hT1 hTm h4 hH3
      (RC.1.image (fun a => a.2)) (RC.2.image (fun c => c 0)) hRV hCV
    have hcollapse := M1_interlace_one_project_le (interlaceFun N (2 ^ r))
      RC.1 RC.2
    exact le_trans hV hcollapse

/-! ## §4, the transpose step — (5) becomes (7)

Note §4: "One-copy transpose symmetry turns (5) into (7)":

```
comp(bracket(W,1,x,y))   >= C-1,
comp(bracket(W,1,x,y/2)) >= C-2,
comp(bracket(W,1,x,y/4)) >= C-3.                                        (7)
```

`W = Rnext N (2^r)`. Stated generically in the target `k` and the `U`-row
density `ρ` (instantiate `ρ := y/2^t`, `k := Dstar + entryLevel r t - 1` for
the three rungs). Body: `dfamily_one_transpose` (HB-1, at
`f := interlaceFun N q`; `Rnext N q` is definitionally
`fun yy xx => interlaceFun N q xx yy`, cf. `Rnext_apply`). -/

/-- **Note §4, one-copy transpose symmetry.** A one-copy lower bound for
`U = Interlace(N,q)` at (row, col) densities `(ρ, x)` transports to the same
lower bound for `W = transpose(U) = Rnext N q` at densities `(x, ρ)`. -/
theorem source_one_copy_W {X Y : Type*} [Fintype X] [Fintype Y]
    (N : X → Y → Bool) (q k : ℕ) (x ρ : ℝ)
    (hq : 1 ≤ q)
    (hx0 : 0 < x) (hx1 : x ≤ 1) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hm : 1 ≤ Fintype.card X) (hn : 1 ≤ Fintype.card Y)
    (h5 : k ≤ Dfamily (interlaceFun (interlaceFun N q) 1)
        (bracketGE (Fin q × X) (Fin q → Y) 1 ρ x)) :
    k ≤ Dfamily (interlaceFun (Rnext N q) 1)
        (bracketGE (Fin q → Y) (Fin q × X) 1 x ρ) := by
  have hcardX : 1 ≤ Fintype.card (Fin q × X) := by
    have hX : Nonempty X := Fintype.card_pos_iff.mp hm
    have hq' : Nonempty (Fin q) := ⟨⟨0, by omega⟩⟩
    exact Fintype.card_pos_iff.mpr ⟨(hq'.some, hX.some)⟩
  have hcardY : 1 ≤ Fintype.card (Fin q → Y) := by
    have hY : Nonempty Y := Fintype.card_pos_iff.mp hn
    exact Fintype.card_pos_iff.mpr ⟨fun _ => hY.some⟩
  have key := dfamily_one_transpose (f := interlaceFun N q) (x := ρ) (y := x)
    hρ0 hρ1 hx0 hx1 hcardX hcardY
  -- `Rnext N q` is defeq `fun yy xx => interlaceFun N q xx yy`, so `key`'s LHS is
  -- definitionally the goal's RHS.
  rw [show Dfamily (interlaceFun (Rnext N q) 1) (bracketGE (Fin q → Y) (Fin q × X) 1 x ρ)
        = Dfamily (interlaceFun (fun yy xx => interlaceFun N q xx yy) 1)
            (bracketGE (Fin q → Y) (Fin q × X) 1 x ρ) from rfl,
     key]
  exact h5

/-! ## §4, the two-copy ladder application + (TB-Lambda) assembly

Note §4: "Set `H = C-1`. … Apply the manuscript's two-copy ladder to `M=W`,
row parameter `x`, column parameter `y`, and target `H`. It gives the full
bundle (8) … Equivalently, `Lambda_W(2,2x,y^2) >= C`. (TB-Lambda)"

Reuses THE manuscript ordinary `NPCC.two_copy_ladder` (Engine.lean:43) —
NOT `robust_two_copy_ladder` (Engine.lean:218), whose rungs are sourced from
an `IsRobust` structure this note does not have. The guard `hH : 1 < H` is
discharged by `hC4 : 4 ≤ C` (note §4's `C ≥ 4` remark). The assembly half is
the INVERSE of `TwoCopyBundle.{top,mid,bottom}_rung` (UnitTests.lean):
the ladder's three ℝ-cast conclusions `H+1, H, H-1 = C, C-1, C-2` at
densities `y², y²/2, y²/4` fold into `C ≤ LambdaGE W 2 (2x) (y²)` via
`le_min_iff` + `exact_mod_cast` (targets stay on the complexity side —
`1 + comp`, `2 + comp` — per the truncation-safe convention,
Hypotheses.lean doc). -/

/-- **Note §4, (7) ⟹ (8)/(TB-Lambda).** From the three one-copy rungs (7)
for any game `W` (row scale `x ≤ 1/2`, column densities `y, y/2, y/4`,
targets `C-1, C-2, C-3`), the manuscript two-copy ladder at `H = C-1` yields
the bundled two-copy bound `TwoCopyBundle W C x y`, i.e.
`Λ_W(2, 2x, y²) ≥ C`. Wrapper-agnostic (file-header flag). -/
theorem two_copy_bundle_of_rungs {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (C : ℕ) (x y : ℝ)
    (hC4 : 4 ≤ C)
    (hx0 : 0 < x) (hx : x ≤ 1 / 2) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (h1 : C - 1 ≤ Dfamily (interlaceFun W 1) (bracketGE X Y 1 x y))
    (h2 : C - 2 ≤ Dfamily (interlaceFun W 1) (bracketGE X Y 1 x (y / 2)))
    (h4 : C - 3 ≤ Dfamily (interlaceFun W 1) (bracketGE X Y 1 x (y / 4))) :
    TwoCopyBundle W C x y := by
  -- ℝ-cast the three ℕ rungs (exact under `4 ≤ C`), shaped for `H = C - 1`
  have hCr : (4 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC4
  have hH : (1 : ℝ) < (C : ℝ) - 1 := by linarith
  have hcast1 : ((C - 1 : ℕ) : ℝ) = (C : ℝ) - 1 := by
    have h : (1 : ℕ) ≤ C := by omega
    push_cast [Nat.cast_sub h]
    ring
  have hcast2 : ((C - 2 : ℕ) : ℝ) = (C : ℝ) - 2 := by
    have h : (2 : ℕ) ≤ C := by omega
    push_cast [Nat.cast_sub h]
    ring
  have hcast3 : ((C - 3 : ℕ) : ℝ) = (C : ℝ) - 3 := by
    have h : (3 : ℕ) ≤ C := by omega
    push_cast [Nat.cast_sub h]
    ring
  have l1 : (C : ℝ) - 1 ≤
      (Dfamily (interlaceFun W 1) (bracketGE X Y 1 x y) : ℝ) := by
    have h := (Nat.cast_le (α := ℝ)).mpr h1
    rw [hcast1] at h
    exact h
  have l2 : (C : ℝ) - 1 - 1 ≤
      (Dfamily (interlaceFun W 1) (bracketGE X Y 1 x (y / 2)) : ℝ) := by
    have h := (Nat.cast_le (α := ℝ)).mpr h2
    rw [hcast2] at h
    linarith
  have l4 : (C : ℝ) - 1 - 2 ≤
      (Dfamily (interlaceFun W 1) (bracketGE X Y 1 x (y / 4)) : ℝ) := by
    have h := (Nat.cast_le (α := ℝ)).mpr h4
    rw [hcast3] at h
    linarith
  -- the manuscript ordinary two-copy ladder at `M = W`, `H = C - 1`
  obtain ⟨hbottom, hmid, htop⟩ :=
    NPCC.two_copy_ladder W (H := (C : ℝ) - 1) hH hx0 hx hy0 hy1 l4 l2 l1
  -- (TB-Lambda) assembly: fold the three rungs back into `C ≤ LambdaGE`
  unfold TwoCopyBundle LambdaGE
  rw [le_min_iff, le_min_iff]
  refine ⟨?_, ?_, ?_⟩
  · -- top rung: `C ≤ comp(bracket(W,2,2x,y²))`
    have h : (C : ℝ) ≤
        (Dfamily (interlaceFun W 2) (bracketGE X Y 2 (2 * x) (y ^ 2)) : ℝ) := by
      linarith
    exact_mod_cast h
  · -- middle rung: `C ≤ 1 + comp(bracket(W,2,2x,y²/2))`
    have h : (C : ℝ) ≤
        1 + (Dfamily (interlaceFun W 2) (bracketGE X Y 2 (2 * x) (y ^ 2 / 2)) : ℝ) := by
      linarith
    exact_mod_cast h
  · -- bottom rung: `C ≤ 2 + comp(bracket(W,2,2x,y²/4))`
    have h : (C : ℝ) ≤
        2 + (Dfamily (interlaceFun W 2) (bracketGE X Y 2 (2 * x) (y ^ 2 / 4)) : ℝ) := by
      linarith
    exact_mod_cast h

/-! ## The capstone — `(Two)` from the three top H3 clauses

Note §1: "The direct-stopping re-entry theorem asks for
`comp(bracket(W,2,T_1^W/m_W,y^2)) >= C` (TB) … This two-copy bound follows
from the manuscript's ordinary two-copy ladder." §6: "The re-entry two-copy
base is no longer a separate q-layered `M3` input. It follows from only
these members of the first-wrapper H3 menu: `(a,j) = (r,0), (r-1,0),
(r-2,0)`, at the common density `Y_0 <= x`, together with (4)."

Route: for each `t ≤ 2`, `source_one_copy_U` (§3, needs `hy1`, `hx1` derived
from `hδhi`/`hxdef`/`hT1W_hi`) → `source_one_copy_W` (§4 transpose, at
`ρ := y/2^t`) → convert the targets `Dstar + (r-t) - 1` to `C-1, C-2, C-3`
via `hC`/`omega` → `two_copy_bundle_of_rungs` (§4 ladder + assembly).

PARAMETER CORRESPONDENCE with the E4 consumers (`theorem_one`/`theorem_two`,
which take `TwoCopyBundle W C x y` as `hTwo`): the `W, C, x, y` produced
here are exactly the note's `W = transpose(Interlace(N,q)), C = D_*+r,
x = T_1^W/(2m_W), y = 1/2+δ`; discharging E4's `hTwo` with this capstone
additionally requires reconciling E4's ambient game with this note's `W` —
an OBLIGATION-LEDGER wiring question, not part of this statement (flag).

JUDGE FLAGS.
* `hTm` (threshold cap) is DERIVED here from (4) + `δ < 1/2` (file-header
  threshold-range flag), so only `hT1` is carried.
* `hC : C = Dstar + r` and `hxdef : x = T_1^W/(2m_W)` are fidelity
  equations (note §2/(1)); `hDstar`/`hr` give `C ≥ 4`.
* `m_W = n_N^q` enters only through `hT1W_hi` and `hxdef`
  (`(Fintype.card Y : ℝ) ^ (2^r)` = the card of `W`'s row type
  `Fin (2^r) → Y`).
* `δ ≤ 1/√2 - 1/2` is the note's exact bound (2y² ≤ 1); only `y ≤ 1` and
  `δ < 1/2` are consumed here (file-header flag). -/

/-- **The Tranche E5 capstone (note §1/§4/§6).** The three top-rung
first-wrapper H3 clauses for `N` at active levels `r, r-1, r-2` and common
column density `Y_0` (with (2) `0 < Y_0 ≤ x`), together with the row-count
inequalities (4), imply the re-entry two-copy base `(TB-Lambda)`:
`TwoCopyBundle W C x y` for `W = transpose(Interlace(N, 2^r))`,
`C = D_* + r`, `x = T_1^W/(2m_W)`, `y = 1/2 + δ`. -/
theorem two_copy_from_H3 {X Y : Type*} [Fintype X] [Fintype Y]
    (N : X → Y → Bool) (Dstar r C : ℕ) (T : ℕ → ℕ) (T1W : ℕ)
    (Y0 δ y x : ℝ)
    (hr : 3 ≤ r) (hDstar : 1 ≤ Dstar) (hC : C = Dstar + r)
    (hm : 1 ≤ Fintype.card X) (hn : 1 ≤ Fintype.card Y)
    (hδ0 : 0 < δ) (hδhi : δ ≤ 1 / Real.sqrt 2 - 1 / 2)
    (hyδ : y = 1 / 2 + δ)
    (hT1W_lo : 1 ≤ T1W) (hT1W_hi : T1W ≤ Fintype.card Y ^ (2 ^ r))
    (hxdef : x = (T1W : ℝ) / (2 * (Fintype.card Y : ℝ) ^ (2 ^ r : ℕ)))
    (hY00 : 0 < Y0) (hY0x : Y0 ≤ x)
    (hT1 : ∀ t : ℕ, t ≤ 2 → 1 ≤ T (entryLevel r t))
    (h4 : RowCountSmall (Fintype.card X) T r δ)
    (hH3 : TopH3Clauses N Dstar r T Y0) :
    TwoCopyBundle (Rnext N (2 ^ r)) C x y := by
  have hC4 : 4 ≤ C := by omega
  -- §2 bounds actually consumed: `y ≤ 1` and `δ < 1/2` (file-header flag)
  have hsqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt2_ge1 : (1 : ℝ) ≤ Real.sqrt 2 := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 2 by norm_num)
    rwa [Real.sqrt_one] at h
  have hsqrt2_gt1 : (1 : ℝ) < Real.sqrt 2 := by
    have h := (Real.sqrt_lt_sqrt_iff (by norm_num : (0 : ℝ) ≤ 1)).mpr
      (by norm_num : (1 : ℝ) < 2)
    rwa [Real.sqrt_one] at h
  have hinv_le : 1 / Real.sqrt 2 ≤ 1 := by
    rw [div_le_one hsqrt2_pos]; exact hsqrt2_ge1
  have hinv_lt : 1 / Real.sqrt 2 < 1 := by
    rw [div_lt_one hsqrt2_pos]; exact hsqrt2_gt1
  have hy0 : 0 < y := by rw [hyδ]; linarith
  have hy1 : y ≤ 1 := by rw [hyδ]; linarith
  have hδhalf : δ < 1 / 2 := by linarith
  -- note (1): `1 ≤ T_1^W ≤ m_W` gives `0 < x ≤ 1/2`
  have hmW1 : (1 : ℝ) ≤ (Fintype.card Y : ℝ) ^ (2 ^ r : ℕ) := by
    exact_mod_cast Nat.one_le_pow (2 ^ r) (Fintype.card Y) hn
  have hT1Wr : (1 : ℝ) ≤ (T1W : ℝ) := by exact_mod_cast hT1W_lo
  have hT1Whi : (T1W : ℝ) ≤ (Fintype.card Y : ℝ) ^ (2 ^ r : ℕ) := by
    exact_mod_cast hT1W_hi
  have hx0 : 0 < x := by
    rw [hxdef]
    exact div_pos (by linarith) (by linarith)
  have hx : x ≤ 1 / 2 := by
    rw [hxdef, div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hx1 : x ≤ 1 := by linarith
  -- threshold cap `hTm` DERIVED from (4) + `δ < 1/2` (file-header flag)
  have hTm : ∀ t : ℕ, t ≤ 2 → T (entryLevel r t) ≤ Fintype.card X + 1 := by
    intro t ht2
    have h4t := h4 t ht2
    have hden : (1 : ℝ) ≤ (2 : ℝ) ^ (t + 1) - 1 := by
      have h2 : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ (t + 1) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      simp only [pow_one] at h2; linarith
    have hrhs : 2 * δ / ((2 : ℝ) ^ (t + 1) - 1) ≤ 2 * δ :=
      div_le_self (by linarith) hden
    have hmr : (0 : ℝ) < (Fintype.card X : ℝ) := by exact_mod_cast hm
    have h5 : ((T (entryLevel r t) : ℝ) - 1) / (Fintype.card X : ℝ) < 1 := by
      calc ((T (entryLevel r t) : ℝ) - 1) / (Fintype.card X : ℝ)
          < 2 * δ / ((2 : ℝ) ^ (t + 1) - 1) := h4t
        _ ≤ 2 * δ := hrhs
        _ < 1 := by linarith
    have h6 : (T (entryLevel r t) : ℝ) - 1 < (Fintype.card X : ℝ) :=
      by have := (div_lt_one hmr).mp h5; linarith
    have h7 : (T (entryLevel r t) : ℝ) < ((Fintype.card X + 1 : ℕ) : ℝ) := by
      push_cast; linarith
    exact le_of_lt (by exact_mod_cast h7)
  -- the three rungs (7): §3 (`source_one_copy_U`) + §4 transpose (`…_W`)
  have hrung : ∀ t : ℕ, t ≤ 2 →
      Dstar + entryLevel r t - 1 ≤
        Dfamily (interlaceFun (Rnext N (2 ^ r)) 1)
          (bracketGE (Fin (2 ^ r) → Y) (Fin (2 ^ r) × X) 1 x (y / 2 ^ t)) := by
    intro t ht2
    have h2t_one : (1 : ℝ) ≤ (2 : ℝ) ^ t := by
      calc (1 : ℝ) = (2 : ℝ) ^ 0 := by norm_num
        _ ≤ (2 : ℝ) ^ t := pow_le_pow_right₀ (by norm_num) (Nat.zero_le t)
    have h2t_pos : (0 : ℝ) < (2 : ℝ) ^ t := by linarith
    have hρ0 : 0 < y / 2 ^ t := div_pos hy0 h2t_pos
    have hρ1 : y / 2 ^ t ≤ 1 := by
      rw [div_le_one h2t_pos]; linarith
    have hU := source_one_copy_U N Dstar r t T Y0 δ y x hr ht2 hm hn hδ0 hyδ
      hy1 hx0 hx1 hY00 hY0x (hT1 t ht2) (hTm t ht2) (h4 t ht2) hH3
    exact source_one_copy_W N (2 ^ r) (Dstar + entryLevel r t - 1) x (y / 2 ^ t)
      Nat.one_le_two_pow hx0 hx1 hρ0 hρ1 hm hn hU
  -- convert the targets `Dstar + a_t - 1` to `C-1, C-2, C-3` via `hC`
  have hrA := hrung 0 (by norm_num)
  have hrB := hrung 1 (by norm_num)
  have hrC := hrung 2 (by norm_num)
  rw [show Dstar + entryLevel r 0 - 1 = C - 1 from by unfold entryLevel; omega]
    at hrA
  rw [show Dstar + entryLevel r 1 - 1 = C - 2 from by unfold entryLevel; omega]
    at hrB
  rw [show Dstar + entryLevel r 2 - 1 = C - 3 from by unfold entryLevel; omega]
    at hrC
  simp only [pow_zero, div_one] at hrA
  simp only [pow_one] at hrB
  rw [show ((2 : ℝ) ^ (2 : ℕ)) = 4 from by norm_num] at hrC
  -- §4 ladder + (TB-Lambda) assembly
  exact two_copy_bundle_of_rungs (Rnext N (2 ^ r)) C x y hC4 hx0 hx hy0 hy1
    hrA hrB hrC

end EthBridge
