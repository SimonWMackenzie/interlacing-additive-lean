# Independent review: standalone finite-field list

**Verdict: pass for the exact standalone v42 lemma.** All five frozen author
sources independently compiled from copied source, with the author's object
directory excluded from the import path. The final theorem and its machine
theorems use only `propext`, `Classical.choice`, and `Quot.sound`. No actionable
statement, probability, indexing, machine, or runtime defect was found.

The target is `yao:finite-field-list` and its proof in the selected v42
`source/main.tex`, lines 5108--5139 at review time. The exact source block is
preserved under `pins/`; its SHA256 is
`963F94843152C364FA2341B8859F918CF4455B8AF432B155E598C79D78DE748B`.
The reviewed API is
`CurrentAdditive.V42FiniteFieldBinary.finite_field_list`.

## What the checked statement covers

The theorem takes only natural numbers `n,r` and proofs `1 <= n`, `1 <= r`.
There is no alternating-model parameter relation, supplied field, supplied
irreducibility proof, desired bias certificate, execution certificate, or
runtime certificate among its premises.

It defines `N = n*2^r`, `d = Nat.clog 2 N`, and `R = 2^d`. It proves
`N <= R < 2N` and the leastness of `d` among degrees reaching `N`.
Since `n,r >= 1`, `N > 1` and `d > 0`, so the field construction is not
vacuous at a zero degree.

The actual searched modulus is the same `TrialSearch.firstPassing d` result
used by the physical search and the printed-array semantics. Its monicity,
degree, and irreducibility are derived internally from the search result.
The quotient-field/basis bridge identifies the executable bit with
`dot(u, vec(y^j))`; exponent zero is explicitly one. The existing polynomial
root argument bounds each nonempty parity, and the checked pattern conversion
gives the source bound for every coordinate set and every prescribed pattern.
The empty coordinate set is included.

The label set is exactly `Fin(R^2)` with its uniform law. The row-major
pair equivalence sends each position to its own seed `(u,y)`. Repeated arrays
remain distinct row positions; there is no deduplication or renormalization.
The final theorem identifies each row with its entry in the ordered labelled
list and each physical packed bit with that row's word. The physical output
format uses row positions as labels; it does not claim to print separate seed
headers. Given the public `n,d`, the row position determines the seed pair.

## Actual algorithm and charged work

`V42FiniteFieldBinary.machine` and its coefficient are fixed constants,
independent of `n,r`. The input consists of three framed binary integer fields
`n.bits`, `r.bits`, and `0.bits`. The wrapper physically decodes these fields
and prepares the unary expression compiler's input.

The parameter machine computes `clog 2 (n*2^r)` itself. The next fixed finite
Boolean-stack machine parses the degree/width, initializes the search bank,
executes the first-passing monic binary polynomial search, and prints every
row and every bit. The clock includes those phases and charged composition
handoffs. The final bounds are:

* actual machine time at most `C*(n*2^r+1)^5`, for one universal fixed `C`;
* exact packed output length `R^2*n`, at most `4*(n*2^r+1)^3`;
* a nonempty labelled list of exactly `R^2` words, each of length `n`.

The search term `55*2^d*2^(d/2)*(d+1)^2` is present in the physical clock
and in the polynomial comparison. It has not been dropped into a host-language
oracle or an uncharged setup step.

The independent audit additionally proves that every queried index
`label*n+coordinate` is strictly below the exact packed output length.
Consequently the final theorem's `getD false` equation cannot gain its content
from an out-of-range default bit.

## Replay and boundaries

`replay/` contains exact copies of the five frozen sources and the independent
`V42FiniteFieldReviewAudit.lean`. `compile.ps1` uses pinned Lean 4.30.0, the
review's own newly built objects, production dependency objects, and package
objects. It contains no path to the author's `finite-field` directory.
The five source hashes match the author's manifest before and after replay.
The audit log prints the complete final theorem type and transitive axiom
sets. One unused `hr` warning occurs in a private arithmetic helper; it does
not alter the statement or proof.

Selected existing algebra, indexing, search, printer, and arithmetic sources
were read and pinned in `pins/FOUNDATION_PINS.json`. This review replays the
new packet, not the entire older dependency cone. A fresh production build,
canonical admission, and any broader paper-completion claim remain root-owned.

This result is more general than the earlier specialized application at
`n=K_a H_a`, `r=4(b+3t)`: those substitutions are not hypotheses here.
The present acceptance concerns the standalone finite-field lemma. It does
not itself certify every later alternating-table endpoint or the whole paper.

`RECEIPT.json` records the exact replay sources, objects, logs, pinned source
block, and successful checks. No author source, production source, Git state,
or shared build was changed by this reviewer.
