# Independent review: sample access for every natural round count

**Accepted for integration at the frozen hashes in `RECEIPT.json`.** The proof covers every `K : Nat`, including zero, on the actual sampler, reserved tape, packed machine input, printer, and recursive matrix at that same `K`. It proves the error bound for every event on the complete typed row/column label tuple, before those labels are mapped to a table. No mathematical gap or additional positive-round premise was found within this interface.

This is a private replay and proof review. Production integration and the repository-wide build remain the parent task's responsibility. This review changed no author proof, manuscript, shared object, or Git state.

## Exact source and declarations

The reviewed source is `papers/randomized-additive-hardness/versions/v42/source/main.tex`, SHA256 `ec8af5767eccc1184e7a1b5f88979ab0a7ee9be60d91be4e61ec80aa66861f78`: `lem:sample-access` at lines 3024–3031 and its proof at lines 4665–4762. `SOURCE_COMPARE.json` binds these blocks to the supplied author attachment. Their text agrees after removing hyperlink anchors and collapsing whitespace; the statement agrees literally. The comparison also records the adjacent compression and uniform-reduction blocks, without claiming that this packet alone proves those theorems.

The main source is `private-provenance-refs/b456a1765e03038d9f2bd485dc09136670c087e2a706d5c48f6a3569d5076d7d/V42AllRoundSampleAccess.lean`, SHA256 `4e9b5ff7c93f0f7bafd9a80b7cfdea597f6aae3501dce0f9469b592f473e5bf7`:

| Declaration in `CurrentAdditive.V42ZeroAccess` | Line | Content |
| --- | ---: | --- |
| `labels_event_error_all` | 20 | Every event on the complete actual typed label tuple has error at most `1/200` from its original independent law. |
| `sample_access_all` | 62 | Every tape executes the fixed packed machine within the stated polynomial clock, uses the bounded number of random bits, and decodes to the exact sampled recursive table; every joint-label event has error strictly below `1/100`. |
| `promised_sample_access_all` | 100 | Discharges the numerical tests from the stated source graph conditions and fixed effective cutoff, for every natural `K`. |

The first root assumes a valid encoded graph, nonzero vertex count, and `FullTests` for the public numerical schedule. Those tests contain numerical bounds; they do not supply a desired machine run, clock, table, sampling law, or success event. They do not assume `K >= 1`. The promised root replaces the tests by positive fixed `gamma` and `Delta`, `n <= 2m <= Delta*n`, graph validity, and the effective source-size cutoff. These are genuine source and numerical premises, not the desired sample-access conclusion.

## Zero-round execution

`V42ZeroArithmetic` proves evaluation and peak monotonicity by structural induction on the actual arithmetic expressions. The zero-round arithmetic peaks are bounded by the already proved scalar envelope at round one. It then derives the clock of the actual batch at round zero from the generic `Expr.clock_le_of_peak`, whose statement has no positive-iteration premise. This avoids applying a theorem that requires positive expression inputs to the zero iteration field.

`sampler_clock_zero` keeps the actual graph input, constructor, sampler clock, reservation, and precision at zero. Only the scalar upper envelope and its exponent use the round-one bound. The all-round sampler theorem separates `K=0` from `K>=1`; the old positive-round clock is used only in the latter branch. No one-round program, sample, tape, label, or matrix replaces the zero-round object.

The independent `ReviewAudit.lean` contains two direct checks of this seam:

1. `literal_empty_iteration_input` proves execution of the same finite machine on the literal bank encoding `[encoded graph, [], actual zero-round tape]`, with the zero-round output and clock. Thus the unary iteration field really is empty.
2. `literal_zero_entries` proves by reflexivity that the actual zero-round printed matrix entry is `rowLabel columnLabel`, with both labels taken from the zero-round joint tuple. This is the literal base matrix, not a one-round surrogate.

## Joint law and exact output

`labels_event_error_all` calls `V39PhysicalSample.budget_labels_event_error_200` on the actual `K`, actual reservation and precision, new public widths, and actual sample count. Its predicate ranges over `V42WRaw.Sample g K`, the full typed tuple of sampled rows and columns. It therefore controls arbitrary joint-label events, including events that the printed table cannot distinguish. The strict `1/100` bound follows from the proved `1/200` bound. The independent `literal_zero_joint_event` instantiates that same assertion at zero.

For every physical tape, `every_output_valid` identifies the decoded payload as the square table of side `sampleSide (clog2 n) K`, threshold `B (clog2 n) K`, and row-major entries of `sampledMatrix` on the same actual labels. `sampledMatrix` uses the literal graph edge activity and `V39RecursiveTable.matrix` at the same `K`. Typed labels ensure legal recursive inputs even at zero. The physical output theorem is used directly; no desired output or execution is an input assumption.

## Resources

The new table and packet bounds include the raw graph/sampler setup, repeat and entry evaluation, table writer, and packed-input framing, including the reserved tape. `packetExponentAll` is a closed natural constant depending on fixed programs, not on the graph, promise, or round count.

The root states, on every tape:

- execution time at most `(n+2)^((2*packetExponentAll)*(K+1))`;
- tape length at most `(n+2)^(544*(K+1))`;
- exact output of the same sampled table.

These are the claimed `n^O(K+1)` resources. Under the public tests, `n>=2`; the independent helper `nplus_two_power` proves `(n+2)^(E*(K+1)) <= n^((2*E)*(K+1))`. Thus explicit bounds are `n^((4*packetExponentAll)*(K+1))` time and `n^(1088*(K+1))` bits. The number of bits is fixed by `n,K`, uniformly across all tapes.

## Replay and dependency checks

The author manifest was pinned at SHA256 `d23a6c8984768edd45d399534483a8ea1995d9e06b5e3281c1d16e416a1eb4c7`. All six author sources were copied byte-for-byte to this review's `replay/` and compiled sequentially with Lean 4.30.0 into fresh private objects. All six returned exit zero, with zero warnings. The independent `ReviewAudit.lean` also returned exit zero with zero warnings. The first draft of one review-only helper was corrected before the successful audit; its unsuccessful log is preserved separately and was not used as evidence.

`PROVIDERS.json` pins 30 private imported providers by source and object hashes; copies are in this review's `providers/`. `SHARED_IMPORTS.json` pins 26 immediate shared-library imports by object hash. These imported providers were read and reused, not independently rebuilt here. The replay search path contains only this review's fresh objects, its provider copies, and the pinned shared/package libraries. It does not search author scratch directories or other review directories. `FREEZE.json`, `REPLAY.json`, `LEAN_PATH.json`, and the post-review verification record make this boundary explicit.

The independent audit checks all 49 declarations in `CurrentAdditive.V42ZeroAccess` for the allowlisted axioms `propext`, `Classical.choice`, and `Quot.sound`. Its transitive type/body traversal covers 26,693 declarations for the two main roots and 16,746 for the zero-sampler clock. The main roots must include the new zero-round arithmetic and clocks, actual packet execution, and original typed joint-label error theorem. They exclude the former positive-only packet/table endpoints and the word-only output-event shortcut. The zero clock specifically excludes the old positive-round sampler and schedule clock theorems. The old scalar peak bound at one is intentionally permitted and was read as an arithmetic envelope only. Direct printed axiom checks of the main roots and literal zero-round identities contain only the standard three axioms. The new proof sources contain no `sorry`, `admit`, new `axiom`, or `opaque` declaration.

The receipt records a final comparison against the frozen originals and copied providers. Acceptance applies to those exact sources and dependencies; it is not a claim that all shared production dependencies were rebuilt in this review.
