import Mathlib
import NPCC.Defs
import NPCC.Complexity
import NPCC.Engine
import EthBridge.Defs

/-! # EthBridge two construction-input hypotheses (Tranche E1)

The note's §2 supplies the whole re-entry argument with exactly TWO
first-wrapper lower bounds for `W` at a common row scale `x`
(`eth-docs/REENTRY_ROBUSTIFICATION_BY_DIRECT_DEFECT_ACCOUNTING.md`, §2):

* `(Near)`  — a near-full ONE-COPY bound `comp(bracket(W,1,x,exp(-λ))) ≥ C`
              after only a tiny column fraction is deleted (note (Near));
* `(Two)`   — a bundled TWO-COPY three-rung bound `Λ_W(2,2x,y²) ≥ C`
              (note (Two)), whose min-of-three-rungs shape hands out the
              targets `C, C-1, C-2` at densities `y², y²/2, y²/4`.

Both are stated in NPCC vocabulary so Theorems 1–2 are proved
HYPOTHESIS-CONDITIONALLY on them (no new axioms; the construction that
discharges them is a later obligation, per `eth-obligations.json` policy).

`(Two)` is phrased through `NPCC.LambdaGE` — the typed
`Λ_f(p,x,y) = min(comp y, 1+comp(y/2), 2+comp(y/4))` (Engine.lean:299) —
so the "three explicit rungs" are literally the three branches of that
`min`. A bound `C ≤ LambdaGE …` is thus, by `le_min_iff`, exactly the
conjunction of the three note rungs — and, crucially, it keeps the `C-1`,
`C-2` offsets on the COMPLEXITY side (`1 + comp`, `2 + comp`) rather than
subtracting from `C` in ℕ, which is the truncation-safe convention the
manuscript uses for `C-k` bounds (cf. `NPCC.Robust` doc-comment). The rung
accessors are proved in `UnitTests.lean`.

DISCIPLINE: these are STATEMENTS (predicate `def`s) only; the faithfulness
judge signs off on them against the note's literal `(Near)`/`(Two)` before
any downstream proving.
-/

namespace EthBridge

open NPCC
open Workspace.Types.Interlace

/-! ## Note (Near): the near-full one-copy lower bound -/

/-- **Note (Near).** `comp(bracket(W,1,x,exp(-λ))) ≥ C`.

The one-copy family complexity of `W` at row scale `x` and column density
`exp(-λ)` is at least `C`. In NPCC vocabulary a one-copy bound is
`Dfamily (interlaceFun · 1) (bracketGE · 1 x y)` (cf. `NPCC.IsRobust` R2–R4,
Robust.lean:21); here the density argument is the near-full `exp(-λ)`
(`λ > 0` the deletion tolerance of note §2). The `C ≤ …` orientation gives
"complexity ≥ C". -/
def NearFull {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (C : ℕ) (x lam : ℝ) : Prop :=
  C ≤ Dfamily (interlaceFun W 1) (bracketGE X Y 1 x (Real.exp (-lam)))

/-! ## Note (Two): the bundled two-copy three-rung lower bound -/

/-- **Note (Two).** `Λ_W(2,2x,y²) ≥ C`, the bundled two-copy bound at row
scale `2x` and base density `y²`.

Encoded as `C ≤ LambdaGE W 2 (2·x) (y²)`. Since
`LambdaGE W 2 (2x) (y²) = min (comp y²) (min (1 + comp (y²/2)) (2 + comp (y²/4)))`
(all `comp` at `interlaceFun W 2` over `bracketGE X Y 2 (2x) ·`), this single
inequality unfolds (via `le_min_iff`, see `UnitTests.lean`) to the note's
three explicit rungs:

* top rung `comp(bracket(W,2,2x,y²)) ≥ C`          (target `C`,   density `y²`);
* middle  `1 + comp(bracket(W,2,2x,y²/2)) ≥ C`     (target `C-1`, density `y²/2`);
* bottom  `2 + comp(bracket(W,2,2x,y²/4)) ≥ C`     (target `C-2`, density `y²/4`).

The bottom rung is what the three-copy base (`eth:lem-three-copy-base`)
consumes (`C-2 ≥ 1` after `C ≥ 3`, then row-parameter monotonicity `2x ≤ 4x`);
the top rung is what the `a = 1` Bob step consumes. -/
def TwoCopyBundle {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (C : ℕ) (x y : ℝ) : Prop :=
  C ≤ LambdaGE W 2 (2 * x) (y ^ 2)

/-! ## Rung accessors for `(Two)` (proved in `UnitTests.lean`)

`TwoCopyBundle.top_rung`, `.mid_rung`, `.bottom_rung` are the three `min`
branches; they are the reusable form the E1/E2 lemmas call. Kept as lemmas
(not `def`s) next to the unit tests so the predicate here stays a bare
statement for the judge. -/

end EthBridge
