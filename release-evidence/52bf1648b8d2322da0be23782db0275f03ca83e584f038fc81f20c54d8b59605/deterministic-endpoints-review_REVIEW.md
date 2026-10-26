# Independent deterministic growing-error endpoint review

Status: accepted for endpoint composition. Independent statement/proof
read-back found no correctness blocker. All six frozen source snapshots
replayed with exit code zero, followed by an independent theorem-type,
transitive-dependency and axiom audit. Root production integration and the full
campaign replay remain separate.

## Target and genuine assumptions

The target is v42 `det:eth` (main.tex lines 340-345 and its proof beginning at
line 2744): an effective positive constant rules out every permitted
deterministic polynomial-time estimator with eventual additive
c*log_2(log_2(T)) accuracy on explicit total Boolean tables, under the adopted
sparse deterministic ETH assumption. The final theorem is
`CurrentAdditive.V42DeterministicETHEndpoint.deterministic_growing_hardness`.
Its external inputs are the approved Dinur/BOT source records and
`DeterministicSparseETH.Holds`; the prospective estimator and accuracy promise
are contradicted rather than assumed as construction certificates.

## Statement and proof read-back

* `V42ActualLower.threshold` is exactly
  `LookupSeed.exponent (4*k)+1+K*(40*k)`. The midpoint numerator is twice this
  public threshold plus K. The polynomial bound for its rational encoding is
  derived from dimensions of the actual generated table.
* `V42PermittedExtraction.extract_all` preserves every valid-table estimator
  output and value, including outside the accuracy guarantee. It provides a
  physical midpoint comparator on the actual table family. It does not assume
  the estimated value or the desired answer.
* The same `StoredMatrix.squareWord` occurs in `V42ActualSource.word`, the
  estimator request, the table target-cost theorem, the source YES/NO bounds,
  and the actual physical pipeline. The NO value is public threshold plus K;
  the YES value is at most the threshold.
* `V42ETHSourceLaw.constructionError` depends only on the fixed source records
  and the actual constructor amplification. It is fixed before the estimator,
  accuracy cutoff, formula or sparsity density. Its positive rational recipe
  is `1/(4*clog_2(amplification))`. This is an explicit witness for the
  existential headline, rather than an assertion that it equals the displayed
  manuscript proof witness for its abstract amplification constant.
* `V42ETHNumerics.actual_numerics` derives both the eventual size condition and
  the strict inequality `2*c*log_2(log_2(T))<K` for the actual table. The size
  upper bound comes from the actual square-output machine bound; it is not
  silently treated as an execution-time bound.
* `V42ETHPhysical.main_outputs` separately composes the current threshold
  formatter and actual estimator/classifier as the tail of the current
  generated-table pipeline. Its clock includes that tail. The construction
  amplification is fixed independently of the estimator; the constant
  polynomial exponent may depend on the estimator, as permitted.
* The final algorithm physically routes sparse formulas, compiles the approved
  graph source, computes the round count from the original variable count,
  constructs the table and compares at its public midpoint. The semantic
  answer field is tied to this physical output by `algorithm_runs`.
* Sparse routing supplies all-input SAT correctness, including finitely many
  small formulas. The clock proof only needs to be eventual. It restores the
  original formula above its cutoff and applies the inherited, independently
  stated subexponential table-bound theorem to the actual composed clock.
* `deterministic_growing_class` transfers the square-table contradiction to
  universal total-table accuracy. The final existential chooses c before
  quantifying over any estimator or eventual-size cutoff.

## Source-proof variation retained explicitly

The manuscript proof chooses its public padding size to be at least the
original variable count and displays a corresponding square lower bound.
This implementation keeps the canonical least padding selected from the graph
vertex count. It instead uses `M <= Delta*n` from the approved source and
`Delta*T0 <= M` beyond a fixed cutoff to prove `T0 <= actual entryCount`.
No `M^2 <= T` claim is exposed. This proves exactly the eventual-size condition
needed by the headline theorem and preserves the actual implemented selector.

## Review boundary

The incoming/alignment, source-gap, actual constructor, uniform generated
program, CNF source interface, and earlier physical primitives have separate
owners and independent reviews. This review checks their final endpoint
composition and does not reconstruct Dinur/BOT source theorems, prove the ETH
assumption, or equate an adopted machine-model assumption with a stronger
unrecorded complexity claim. Production integration and the full campaign
replay remain root responsibilities.


## Frozen verification evidence

The six endpoint source hashes match the owner's `FREEZE.json`. The current
selected `main.tex` SHA-256 is
`ec8af5767eccc1184e7a1b5f88979ab0a7ee9be60d91be4e61ec80aa66861f78`. The owner records that the change from its
initial-read manuscript hash was an authorized formalization paragraph and
website/bibliography update; this review opened the current target statements,
estimator model, generated recipe and endpoint proof directly. The complete
source inventory comparison is separately owned by root.

`FROZEN_SOURCES.json` pins the six target snapshots and their 48-source private
dependency closure. `REPLAY_RECEIPTS.json` records six successful sequential
private compiles plus `EndpointReviewAudit`. The post-replay source stability
check reports no drift in any of the 48 sources or in the selected manuscript.
`RECEIPT.json` hashes every replayed source, generated object and log.

The audit visited **83,413 declarations**. It checks theorem types and proof
values, requires the current actual source NO bound, physical output theorem,
new weighted incoming endpoint and new actual dyadic machine clock, and rejects
legacy endpoint theorem/algorithm shortcuts and the obsolete sharp incoming
and alignment path. Its axiom allowlist is exactly `propext`,
`Classical.choice`, and `Quot.sound`.

The printed final theorem type takes only the approved `DinurReduction`, the
corresponding `BOTReduction`, and `DeterministicSparseETH.Holds` before its
existential positive constant and universal permitted-estimator contradiction.
No desired target matrix property, profile, cost, execution receipt, time
certificate or source-output promise remains a theorem parameter.

The only independent replay warning is an unused lambda variable `x` at
`V42PermittedExtraction.lean:42`. It does not change a statement or proof;
frozen sources were not edited for cosmetic cleanup.

This is a private replay of the six endpoint modules against recorded private
and production dependency objects. It is not a fresh reconstruction of every
inherited lower-layer module. No production/manuscript source, Git state or
shared build output was changed by this reviewer, and no subagent was spawned.
