# Final randomized quantitative endpoint review

The frozen Runtime and Endpoint modules pass independent semantic review
and private Lean 4.30.0 replay. Together with the separately reviewed
support closure, their final theorem proves the full statement of v43
Corollary 1.4 (`thm:quantitative`) relative to the approved named source
interfaces and declared finite-machine models. It returns an actual
bounded-error sparse 3-SAT algorithm for every real `8c<alpha<1`, and proves
the complete charged worst-case runtime of that same algorithm is
`2^{O(N^alpha)}`. It does not assume a final probability, clock, execution,
or completed-decider certificate.

## Exact frozen pair and replay

| File in `randomized-outer/` | SHA-256 |
| --- | --- |
| `V43RandomizedRuntime.lean` | `3b58fe48088297459ec39ad20c22732d23112875bc76fd0eb692b465e259a569` |
| `V43RandomizedEndpoint.lean` | `9dd3ef4ea78ff2d55651a0e536ed84ff2db5fa96febb4e27a491c4bab99e703f` |

The worker confirmed this pair frozen after compilation; hashes were
checked directly on the private copies. Runtime and Endpoint were replayed
serially against the freshly replayed private ten-file randomized support
closure and existing reviewed dependency objects. Both exited
successfully. All three printed theorem axiom reports contain only
`propext`, `Classical.choice`, and `Quot.sound`. Logs are adjacent to the
private sources. The final-pair receipt is
`randomized-outer/FINAL_RECEIPT.json`; the supporting group remains
`randomized-outer/RECEIPT.json`.

The only compiler warning is an unused `hc : c<1/8` hypothesis in the square
endpoint proof. It is retained in the theorem's source-faithful statement;
the chosen `alpha` interval already gives the needed strict upper bound.
There is no mathematical or statement-fidelity defect in this redundancy.

This is a private replay using existing dependency objects, not a clean
production replay. Root production/source-bound gates remain separate.

## Literal statement compared with the manuscript

Selected source: `papers/randomized-additive-hardness/versions/v43/source/main.tex`,
SHA-256 `bfde23b90f50785939095a6d37b7b247965ee6c45beaca9011a8963dec3cc9d6`.
The comparison is to `thm:quantitative` at lines 338-348 and its proof at
lines 3306-3365. The manuscript states at lines 1043-1044 that logarithms
are binary; the formal error is exactly
`c*(logb 2 T / logb 2 (logb 2 T))`.

`quantitative_square_algorithm` has exactly these substantive parameters
and conclusions:

- Any permitted polynomial-time randomized estimator, any sufficiently-large
  accuracy threshold, and every real `0<=c<1/8`.
- Accuracy only on positive explicit square tables whose side is a power
  of two, with success probability at least `2/3` and the stated additive
  error at the actual entry count.
- Every real target exponent `alpha` satisfying `8c<alpha<1`, followed by
  every fixed natural sparse clause-density bound.
- An actual `FairBitAlgorithm.Algorithm` with YES acceptance at least
  `2/3` and NO acceptance at most `1/3` on **all** valid formulas at that
  density, including every small size.
- For that same algorithm, fixed natural `K,N0` such that its full
  `totalTime` is at most `ceil(2^(K*N^alpha))` on every promised sparse
  input with original variable count at least `N0`.

The last conclusion is the ordinary eventual worst-case bound expressed
by `2^{O(N^alpha)}`. It does not weaken correctness to sufficiently large
inputs. The formula's original variable count is used in the runtime
bound, not the source graph's vertex count.

`quantitative_algorithm` proves the same statement from accuracy on all
positive rectangular explicit total tables, by restricting the premise to
the square dyadic domain. Thus both the general premise and the paper's
"it suffices" square restriction are covered.

The final theorem contains no final success-probability, execution, or
runtime hypothesis. Its only mathematical interfaces are the named
approved source reductions and the permitted estimator's ordinary
polynomial-machine, rational-comparison, and accuracy data. There is no
ETH assumption, hardness assumption based on a known SAT upper bound, or
claim about a restricted rational-only target exponent.

## Actual rational schedule and sharp coefficient

The endpoint chooses fixed positive integers `a<b` with
`8c<a/b<alpha`, so the implemented schedule is fixed before the formula and
tapes. The physical schedule uses the checked dyadic recipe

`k(N)=floor(2^floor(a*ceil(log2 N)/b) / ceil(log2 N))`.

This is not a claim that its finite values equal the proof text's
`floor(N^(a/b)/ceil(log2 N))`. The already reviewed arithmetic proves the
required logarithmic slope, strict gap, and runtime rate for this **actual**
dyadic schedule. The corollary's statement does not prescribe the finite
schedule values; the implementation therefore proves the same full claim
without an unimplemented integer-root oracle.

The source-law theorem applies the sharp error inequality at the actual
sample entry count, rather than replacing it by a coarser source-power
budget. This preserves the coefficient `1/8`. The source graph's actual
quasi-linear bound, actual sample table, and physical midpoint are all
the ones already checked in the support review. The chosen rational
exponent is an internal implementation parameter; the final theorem
quantifies over every allowed real `alpha`.

## Full charged runtime of the same machine

`algorithm_power_time` obtains a polynomial bound on the actual inner
`ResourceFit.totalClock`, including the physical gap/resource/carrier
printers, fair bits, table construction, estimator, midpoint comparison,
copying and framing. It does not assume this desired clock as a premise.

It then uses the exact totalTime identity for the concrete routed
algorithm. Both router executions and their transfers are retained.
OuterClock absorbs this extra cubic routing work into a fixed polynomial
of the actual resource word. The input-polynomial clock conversion
applies the source geometry and the proved rational-schedule rate to
obtain `ceil(2^(K*N^alpha))` on the original sparse input.

Every constant/exponent used in this absorption is fixed before the
input formula and random values. The underlying caller has a uniform
clock on all fair tapes, so the result is worst-case runtime rather than
an expected-time bound. The complete carrier-generation and random-bit
charges remain present in `Algorithm.totalTime`.

Finally the Endpoint first obtains all-size correctness of the actual
concrete algorithm, then applies this runtime theorem to that identical
algorithm with the same estimator, rational schedule, density, and finite
cutoff. The finite prefix is decided by the actual charged sparse router
and its SAT-preservation theorem. There is no existential replacement by a
different fast or correct machine.

No blocking semantic defect or remaining consumer premise was found for
this corollary statement at the reviewed source/model boundary. Full
production admission, clean release replay, and public status updates
remain with the root. Earlier reviews and frozen snapshots were retained;
only the private review directory was written.
