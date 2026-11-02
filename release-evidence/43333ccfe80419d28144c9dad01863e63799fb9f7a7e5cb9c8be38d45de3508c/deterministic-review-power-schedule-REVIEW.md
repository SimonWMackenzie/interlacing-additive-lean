# Independent review: physical dyadic gap schedule

Verdict: **accept this component**. Both frozen candidate modules and a new
independent composition theorem replayed successfully with Lean 4.30.0.
No corrective source changes are requested. No production files, Git state,
shared build objects, or frozen deterministic endpoint files were changed.

## Reviewed identities and independent replay

| Candidate | SHA256 | Replay |
| --- | --- | --- |
| `V43PowerSchedule.lean` | `4d3b480f64bcaef3c13e0bb6460def6410a22ca3472fe06737b503852d11177e` | exit 0, `core-replay.log` |
| `V43PowerSchedulePaid.lean` | `03e6d3d2ee9d3373d3f898474b0ecb6512933833028eb0f071354e5d67132d52` | exit 0, `paid-replay.log` |
| `Audit.lean` | recorded in `REPLAY.json` | exit 0, `audit-replay.log` |

The candidates were copied byte-for-byte into this independent private review
directory. Their original source hashes were rechecked after replay and match
the frozen input hashes. At most one reviewer compiler ran at any time.
Existing checked dependency objects were reused; no full dependency cold
rebuild is claimed.

Every printed axiom list contains only `propext`, `Classical.choice`, and
`Quot.sound`. This includes the candidate declarations, the inherited physical
power constructor, and the independent source-input/clock composition theorem.
No `sorry`, `admit`, or new `axiom` occurs in the reviewed sources.

## Semantic review

The exact schedule is

```
gap(a,b,N) = floor(2^floor(a*clog2(N)/b) / clog2(N)).
```

The machine parameters `a,b` are fixed before the input word or formula.
Consequently the polynomial degree and constants may depend on `a,b`, while
they are uniform in `N`. No claim of a polynomial with degree independent of
variable machine parameters is made or needed.

1. **Actual source input.** `formula` composes the checked original-variable
   extractor with the unary schedule machine. `formula_result` proves the
   exact output is `List.replicate (gap a b Phi.variables) true` on the canonical
   encoded formula. It uses the original variable count, not encoded byte
   length or a supplied logarithm/power. The result identity holds for every
   encoded formula; validity/sparsity enter only the later size bound.
2. **Actual arithmetic.** Ceiling logarithm, multiplication, and quotient use
   inherited finite Boolean-stack implementations. `boundedPower` explicitly
   composes with `MatrixUnaryPower.machine`; its execution theorem outputs
   `2^exponent` unary bits in at most `16*2^exponent` steps. This output-sensitive
   power cost is included, rather than treated as a unit-cost operation.
3. **The power cost is discharged.** `numerator_bound` proves, for all inputs,
   `2^floor(a*clog2(N)/b) <= 2^a*(N+1)^a`. `powerUnary` instantiates
   `boundedPower` with this proved bound. Its polynomial clock therefore
   includes the full exponential-output construction. There is no unproved
   power implementation or runtime premise in the delivered schedule.
4. **Composition is paid.** The clock proof includes the exponent producer's
   clock, its physically produced output length, the original input-length
   term from `output_length_bound`, and all serial-composition overhead.
   The chosen degree `P.degree+d+1` dominates each needed polynomial term.
   The final quotient uses the checked unary quotient implementation and its
   charged producer composition.
5. **Paid source bound.** For each fixed density, `sparse_input_bound` derives
   an encoded-length bound directly from `EncodedCNF.encode_length_upper`:
   `len(encode Phi)+1 <= (14*density+4)*(N+1)^2`. `formula_paid` then bounds the
   actual local producer clock by `c*(N+gap+1)^d` for all sparse valid formulas,
   without a large-input cutoff. This is a clock theorem, not merely an output
   size bound.
6. **Independent combined readback.** `Audit.source_input_with_paid_clock`
   chooses the single concrete formula schedule machine before the formula,
   and proves its literal dyadic unary output within the paid polynomial
   `N+gap` clock. It combines the two independent advertised interfaces into
   one actual `OutputsWithin` statement.
7. **Boundary cases and hypotheses.** The implementation and its paid clock
   are total at `N=0`, `N=1`, `a=0`, and `b=0` under Lean's natural-number
   division convention. Those cases need no hidden promise. The analytic
   randomized consumer must separately impose its positive rational-exponent
   conditions and prove growth/margin estimates.

## Scope retained

This is the explicitly identified dyadic replacement schedule. It does not
compute the source proof's literal integer-root schedule. The new schedule's
analytic asymptotics and the complete randomized estimator/SAT composition
are outside these two modules and remain the responsibility of their owning
proofs. Nothing in this review independently certifies those endpoints.

The reviewed component supplies the actual polynomial-time schedule producer,
the exact canonical formula-input identity, and its polynomial `N+gap` charged
clock without a hidden exponentiation-cost assumption.
