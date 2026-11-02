# Independent randomized-rate arithmetic review

Reviewer: `/root/v43_rate_review`, 2 November 2026.

Accept the submitted arithmetic component. Independent private replay passed,
and no mathematical defect was found in its numeric claims. It covers every
requested exponent `8c < alpha < 1`, including the case `c = 0`, at the
actual public square-sample entry count. This acceptance does not certify a
SAT machine, its probability of error, schedule-computation runtime, or the
complete v43 corollary.

## Frozen source and replay

- Submitted source: `private-provenance-refs/2fd2af620307a890d6f117ce31e02ec70729d22869f81694f8379f9d57f2512c/V43RandomizedRate.lean`.
- Independent copy: `private-provenance-refs/ea354996c438fbd0c3fcd70b681abe86d9ad42a7cea7c3accf78d8ca5f118269/V43RandomizedRate.lean`.
- Both source SHA256: `0F3D9110B1D2E38C9874A20225E2F6D9A30FE64C76A4E3A62382DDD20FE5893D`.
- Private output SHA256: `A805AC038B9FF3BD8EB967760D0A6B902870A5CC52B69AA9273A2353C2FF576A`.
- Replay log: `randomized-replay.log`, SHA256 `4483946BC5F0BF889DD0233A08471348C226A5C93887C05B7E54BEAB0DF5F6CA`.
- Lean 4.30.0, commit `d024af099ca4bf2c86f649261ebf59565dc8c622`.
- Command: `lean -o <private>/V43RandomizedRate.olean <private>/V43RandomizedRate.lean`.
- `LEAN_PATH`: private root, root `.lake/build/lib/lean`, then existing package build-library directories.
- Exit status 0. This re-elaborated the frozen submitted source using existing dependency objects; it is not a fresh transitive production rebuild.

Source anchor: `papers/randomized-additive-hardness/versions/v43/source/main.tex`,
SHA256 `bfde23b90f50785939095a6d37b7b247965ee6c45beaca9011a8963dec3cc9d6`,
`thm:quantitative` at lines 337--347 and its proof at 3306--3359. The exact
sample definition at 3191--3195 agrees with the numerical public sample
recipe used through the existing `V42PublicSchedule` interface.

## Main quantified conclusion

`CurrentAdditive.V43RandomizedRate.quantitative_rate_arithmetic` takes
arbitrary real `c >= 0` and `8c < alpha < 1`, fixed natural source constants
`Delta,p`, a fixed construction-clock exponent `E`, and an arbitrary natural
estimator entry-count threshold `T0`, with `Delta > 0`. It returns fixed
natural `a,b,K,N0` before quantifying over formula size `N` or graph size `n`.
It proves `0 < a < b` and `8c < a/b < alpha`. For all `N >= N0` and all
`n >= 1` satisfying

```
N <= Delta*n
n <= N*(Nat.clog 2 (N+2))^p,
```

putting

```
k = 2^((a*Nat.clog 2 N)/b) / Nat.clog 2 N
T = V42PublicSchedule.sampleEntries (Nat.clog 2 n) k
```

it proves `k >= 1`, `T >= T0`, `T >= 4`,

```
2*c*(log2(T)/log2(log2(T))) < k,
(n+2)^(E*(k+1)) <= ceil(2^(K*N^alpha)).
```

Thus the quantified exponent range is the complete range in the manuscript
corollary, not a single chosen exponent or a bounded check. The coefficient
four underlying `c < 1/8` comes from the checked
`V42PublicSize.sample_sharp`, not a hypothesis asserting the desired size
or gap. `rate_core` is an intermediate conditional inequality; the main
theorem actually discharges its numeric hypotheses.

## Source and degenerate-case checks

- The source theorem gives `2*N <= Delta*n`; the module uses the weaker
  `N <= Delta*n`. The source's upper bound with real `log2(N+2)` implies
  the module's upper bound with `Nat.clog`. These are legitimate source
  accounting premises, rather than assumptions of the desired gap.
- `exists_rational_rate` constructs positive natural numerator and
  denominator from rational density in `(8c,alpha)`. It proves `a < b`,
  so there is no zero-denominator or nonpositive-exponent branch.
- `c = 0` is covered: `alpha > 0` follows from the hypotheses, a positive
  rational exponent is selected, and eventually positive `k` gives strict
  separation from zero error.
- Explicit finite cutoffs ensure the logarithmic size, iteration, and
  public sample estimates apply. `entries_eventually_ge` works for every
  fixed table threshold and every graph logarithmic-size parameter.
  The joint theorem includes both the arbitrary estimator threshold and
  `T >= 4`, so division by a nonpositive iterated logarithm is not used
  to justify the endpoint.
- `construction_power_time` proves the numeric conversion of a fixed
  `(n+2)^(E*(k+1))` clock to the desired exponential-power clock.
  `polynomial_clock_power_time` also pays fixed polynomial overhead in
  an input length bounded by `(n+2)^(q*(k+1))`. Neither assumes the target
  `2^(O(N^alpha))` bound.

## Required correspondence qualification

The candidate uses a dyadic integer-arithmetic alternative to the manuscript's
literal choice `floor(N^beta/ceil(log2 N))` at lines 3325--3327. In general
the two integers differ. The submitted numerator has logarithm between
`beta*log2(N)-1` and `beta*(log2(N)+1)` and, for `beta <= 1`, is at most
`2*N^beta`. Those proved bounds preserve the headline exponent range and
coefficient. This is therefore an alternative constructive numeric proof of
the same corollary, not exact algorithm identity with the displayed
integer-root recipe. Root explicitly accepted this correspondence boundary;
no manuscript change is proposed or required by this component review.

## Trust and remaining endpoint work

All nine printed theorem audits report exactly `propext`,
`Classical.choice`, and `Quot.sound`: `numerator_log_bounds`,
`iterations_log_lower`, `rate_core`, `gap_exceeds_twice_error`,
`construction_power_time`, `quantitative_rate_arithmetic`,
`polynomial_clock_power_time`, `entries_eventually_ge`, and
`exists_rational_rate`. No admission or new axiom appears in the submitted
file. The cutoff existence may use real-number mathematics; all constants
are fixed before `N`, and no uniform computation from real `c,alpha` is
claimed.

The full endpoint must still connect this computable schedule to an actual
costed schedule program, the sparse-SAT source, the same encoded table and
entry count, independent estimator calls and majority comparison, the
actual every-tape construction and total runtime, and finite-small-size
exhaustive search. Those are distinct from the arithmetic proved here.
Root integration, production dependency rebuilding and source-bound release
gates remain separate.

Only this private review directory was written. No production source,
manuscript, Git state, shared Lake build, or subagent was touched.
