# Independent review: generated decoding, rank and arbitrary-base execution

26 October 2026. Reviewer `v42_proof_review`. **Accept all four frozen
modules for integration at their stated interface scope. No mathematical
revision is required.**

The missing generated rank statement uses the current widths. Every generated
input has separate local row/column maps into the corresponding two-tag
full-product matrix with exactly the same entry. The original indexed weights
are retained. The complete one-round physical program is polynomial for every
stored rationally weighted base, including graph-context preparation and every
printed output bit, with an exponent independent of the round.

## Frozen inputs and independent checks

The selected v42 manuscript was reopened at `thm:amplifier` (line 1266),
`prop:iteration` (1316), `lem:amplifier-rank` (2326), and `det:amplifier`
(2543). Its SHA256 is
`ec8af5767eccc1184e7a1b5f88979ab0a7ee9be60d91be4e61ec80aa66861f78`.
The inventory worker independently identified the same literal contracts.

| Module | Accepted source SHA256 |
| --- | --- |
| `V42GeneratedEmbedding` | `4be52ebd168e1fc96bbd243b4c4163e27a45f71039e0a45ed29b1ea2923a92ed` |
| `V42GeneratedRank` | `d882b7bbe4f5b94ad8ba8175f02db888e1c0460762e25a833bcafe535fd7deb3` |
| `V42GeneratedRound` | `82e768e749baedceabaa5a4f1805048bbab1df2c1cdfbbc537a66f5d8a101f05` |
| `V42GeneratedRoundFromGraph` | `5356621b6c50973b70773e1f40b990ea5b05dbd62d2d6ae302b972f673b7af06` |

All four reviewer snapshots independently compiled in that order using pinned
Lean 4.30.0, exit 0. All principal printed axiom cones contain only `propext`,
`Classical.choice`, and `Quot.sound`. The reviewer independently matched every
source hash against `WORKER_FREEZE.json`. No `sorry`, `admit`, new axiom or
opaque conclusion certificate occurs in the four sources.

`GeneratedInterfaceProofReviewAudit.lean` reads actual theorem types and proof
values. Its complete traversal passed over **54,062 declarations**, rejecting
old schedule-specific full/generated/runtime endpoints while requiring the
new constructor, decoder/rank, complete weighted encoding and actual physical
step. The separate strongest combined-program endpoint traversal passed over
**42,873 declarations** and requires actual graph counts, derived width,
scalar/source printers, stored step, complete base encoding and uniform
polynomial bound in that endpoint's own dependency chain. Both checks passed,
exit 0. The first-three audit and receipt are separately preserved.

## Accepted statements and genuine premises

- **Embedding:** `successor_decoded_entry` and `numbered_decoded_entry` use
  explicit local maps preserving both ordinary and diagonal column families,
  the same base entry and the same activity function. Duplicates keep their
  original indices. The original-law exports are definitional equalities,
  independently reproduced by the reviewer. There is no claim of equality
  between the complete decoded generated law and an iid product law.
- **Rank:** generic raw-source rank, pullback rank, transposes and interlace
  rank prove the factor `Q*w*(s*q1*q2+ni)`. Public arithmetic gives
  `ni<=2*s*q2`, and the actual widths `q2=s^6,w=s^8,Q=s^24` give exactly
  `2^(40*k)` per round. `storedIterate_rank` is for arbitrary weighted bases;
  `graphRun_rank` is for the same actual graph constructor and proves exactly
  `rank<=2^(generatedB-1)`. No rank, cost, profile or graph-promise conclusion
  is supplied as a premise.
- **Resources:** `one_round_size_and_time_polynomial` chooses `C,E` before
  the graph, public `k` and arbitrary `StoredMatrix R`. One fixed physical
  machine takes only graph bytes, unary `k` and the complete `encode R`;
  it computes counts, widths, original item weights and activity, then runs
  the actual stored step. Both time and output length are bounded by
  `C*(N+|encode R|+1)^E`. Every Boolean cell and both complete rational weight
  tables are charged. The final premises are only graph validity,
  `0<n<=N=2^(4k)`, `k>=2`, `2m<=Delta*n`, and `2*Delta<=k`. Width equality is
  derived. No prepared context, desired run, desired output, output-size cap
  or runtime certificate is assumed. These public guards are discharged by
  the previously checked source/parameter path.

`READBACK.md` records the detailed source and dependency reasoning. Positive
normalized laws rule out empty base carriers; no vacuity or quantifier reversal
was found. This is independent private component acceptance. Production
admission, fresh canonical dependency builds, source-map/ledger updates and
whole-paper release gates remain root-owned. No production/manuscript edit,
shared build, Git operation or subdelegation was performed.
