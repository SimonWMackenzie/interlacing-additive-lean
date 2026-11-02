# Independent numeric resource review

Reviewer: `/root/v43_rate_review`, 2 November 2026.

Accept this file as a numeric component only. The private replay passed,
and the statements faithfully express the resource accounting at v43
`thm:time-tradeoff`. This is not acceptance of an estimator-to-SAT endpoint,
an actual machine runtime, or a checked v43 release.

## Frozen inputs and replay

- Submitted source: `private-provenance-refs/79b0ac14f356a2152f2c2f8b02e0411d901771b4234fc6a49abd583c66be5d9b/Numerics.lean`.
- Independent copy: `private-provenance-refs/f68ab3ea3226d2ba274f7c6852786b868b4f5d6bb5c332bc0158be2fc40120ed/Numerics.lean`.
- Both source SHA256: `6ACB56159C5FFCE9B01CB67DDA09963945F703FAFEA4080E1FE87469D3FF5D4E`.
- Private output SHA256: `42E8818CDD9EA677ACF9A363A25B5A50CA094DA50B23A16C9C1FE7A83B9F09E3`.
- Replay log: `general-replay.log`, SHA256 `9AE8302F97783591155FB92F38EA646CC427F49523019C0E2E2D95BCEDBCF16B`.
- Lean 4.30.0, commit `d024af099ca4bf2c86f649261ebf59565dc8c622`.
- Command: `lean -o <private>/V43TimeTradeoff/Numerics.olean <private>/V43TimeTradeoff/Numerics.lean`.
- `LEAN_PATH`: private root, root `.lake/build/lib/lean`, then existing package build-library directories.
- Exit status 0. Existing dependency objects were reused; this is a private component replay, not a fresh transitive rebuild.

Source anchor: `papers/randomized-additive-hardness/versions/v43/source/main.tex`,
SHA256 `bfde23b90f50785939095a6d37b7b247965ee6c45beaca9011a8963dec3cc9d6`,
lines 3229--3279, especially the two size bounds at 3242--3243 and charging
computing the gap to `S` at 3276--3278.

## Statement read-back

- `CurrentV43.TimeTradeoff.randomizedSize_dominates`: for all natural `N,k`
  and fixed `C >= 1`, `(N+2)^(C*(k+1)) >= N+k+2`.
- `CurrentV43.TimeTradeoff.deterministicSize_dominates`: for all natural `N,k`,
  `A >= 2` and `C >= 1`, `(N+2)^(C*A^k) >= N+k+2`.
- `CurrentV43.TimeTradeoff.polynomial_charge`: an ordinary fixed polynomial
  of a natural quantity bounded by `S >= 1` is bounded by a fixed polynomial
  of `S`.
- `CurrentV43.TimeTradeoff.charged_composition`: assuming the actual source
  time is at most `cs*(N+1)^ds`, actual gap computation time is at most
  `cg*(N+k+1)^dg`, actual construction time is at most `S`, and actual
  estimator/comparison time is at most `ce*(S+1)^de`, the sum is at most
  `(cs+cg+1+ce*2^de)*S^(ds+dg+de+1)` whenever `N+k+2 <= S`.

All constants and exponents are explicit parameters; for a complexity
application the caller fixes them independently of `N,k`. There is no
`k <= polynomial(N)` restriction. In particular, gap functions growing
faster than every polynomial in `N` remain permitted. Natural zero cases
do not invalidate the domination lemmas; the source theorem separately
requires `k >= 1` for its construction.

## Trust and remaining obligations

The three printed theorem audits, for `randomizedSize_dominates`,
`deterministicSize_dominates`, and `charged_composition`, report exactly
`propext`, `Classical.choice`, and `Quot.sound`. There is no new axiom,
admission, gap hypothesis disguised as a proved conclusion, or runtime
hypothesis beyond the explicit abstract resource inputs just listed.

The file neither constructs the source graph nor computes a variable gap,
executes either table constructor, runs or amplifies an estimator, compares
its actual output, proves finite-small-size handling, or produces a SAT
algorithm. Those consumers must supply their actual programs and resource
bounds. Root integration and source-bound production gates remain separate.

No production source, manuscript, Git state, or shared Lake build was changed.
