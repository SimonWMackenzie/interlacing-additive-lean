# Independent v42 schedule and numerical-margin review

The frozen numerical packet is accepted at the scope below. Its widths,
tolerances, common margins, full-product schedule, least-dyadic generated
schedule, and sample-size arithmetic agree with the selected replacement v42.
All twelve reviewed implementation modules replayed successfully in a private
snapshot. There is no remaining arithmetic blocker in this packet.

This is not acceptance of a matrix constructor, an iteration theorem, a
sampler, a physical machine or its running time, or an end-to-end reduction.
Those consumers and production admission remain with the root.

## Frozen source and checks

- Manuscript: `papers/randomized-additive-hardness/versions/v42/source/main.tex`.
- SHA256: `1C7F0FEDC92989087219C2773411A42F610503846C6CF1E2DEA5AC18961684F7`.
- Exact source copy: `snapshot/source-main.tex`; this is immutable review evidence.
- Main anchors: `def:amplification-parameters` (line 1349),
  `eq:common-budgets` (4781), `eq:conditioning-size-bound` (4787),
  `lem:common-schedule` (4796), `eq:width-margins` (4808),
  `lem:full-schedule` (4891), `lem:generated-schedule` (4940),
  `prop:iteration`, and `thm:compression`.
- Compiler: Lean 4.30.0, commit `d024af099ca4bf2c86f649261ebf59565dc8c622`.
- Commands: `replay.ps1`, then `replay-final.ps1`, then
  `replay-restoration.ps1`. Compilers ran sequentially, never against shared
  output paths. Every command exited 0. The expected unqualified module names
  resolve to the private `snapshot/` directory before production objects.
- Receipts: `REPLAY.json`, `REPLAY_FINAL.json`, `REPLAY_RESTORATION.json`,
  `SNAPSHOT.json`, `FROZEN_STATUS.json`, and `DEPENDENCIES.json`.
  `DEPENDENCY_OBJECTS_AFTER_REPLAY.json` additionally records the observed
  object hashes of the direct production helper modules after replay.
- `StatementReadback.lean` printed each public definition and theorem of the
  first eleven modules; `RestorationReadback.lean` printed the final module
  and both numerical guard structures. Axiom queries cover 92 packet
  theorems, plus five independent consumer checks in `ReviewChecks.lean`.
  Only `propext`, `Classical.choice`, and `Quot.sound` occur.
- There are ten harmless tactic-lint warnings in the original packet replay;
  no compiler error, admission, `sorryAx`, or custom axiom was found.
- All twelve live packet files still matched their private snapshot hashes
  at the final comparison; the manuscript hash also remained unchanged.

No Git operation, production edit, shared build, or subdelegation was used.

## Literal recipe and fixed graph constants

The Lean width exponent `k` means `s=2^k`; `b` means `rho=2^-b`.
It is separate from the number `i` of amplification rounds. The recipe is
literal: `q1=s-2`, `q2=2^(b+2k)=s^2/rho`, `w=s^8`, `Q=s^24`,
`x=rho^8`, `eta=s^-2`, `theta=1/(512Q)`, and
`deltaU=eta/(16w)=1/(16s^10)`. The definition of `q1` uses natural
subtraction; the admitted cutoff implies `s>=256`, so no truncation arises.

`commonCutoff(deltaV,zeta,Delta)` is a sufficient integer exponent cutoff,
not an assumption that any desired inequality holds. Its rational allowance
is exactly `2^-16 min(1,deltaV,zeta/256)`.

An issue identified during review was repaired in the separately frozen
`V42FixedPromiseCutoff`: the final public cutoff is

```
k0 = fixedPromiseCutoff gamma Delta
   = commonCutoff (gamma/(4*Delta)) (gamma/24) Delta.
s0 = 2^k0.
```

For positive fixed `gamma,Delta`, the promised lower edge bound `n<=2m`
gives `gamma/(4Delta)<=sourceDeltaV gamma Delta n m`.
`sourceAllowance_mono`, `commonCutoff_antitone`, and
`fixedPromiseCutoff_graph` transport the fixed cutoff to the actual graph.
It therefore depends on neither graph size/edge count, base matrix, nor
round count. The upper edge bound `2m<=Delta*n` is used separately for the
encoding width. Both promise inequalities remain visible caller inputs.

## Every common-table allowance is accounted for

The following table concerns the required allowance column of
`eq:width-margins`. Some proofs use stronger direct power-of-two bounds
instead of reproducing each intermediate real-power upper estimate.

| Source quantity | Checked owner and scope |
| --- | --- |
| `s*eta <= 2^-16 min(1,deltaV,mu*zeta)` | `cutoff_small`, `source_eta`, `allowance_bounds`, `numeric_margins`; `mu=1/256` exactly |
| `4s|E|/q2 <= 1` | `source_width`, using `n<=2^b`, `2m<=Delta*n`, `2Delta<=k`; proves the stronger dyadic ceiling fits |
| `s^2*rho <= 1/4` | `scalar_smallness` proves `4s^2*rho<=1` |
| `s*q1/q2 <= zeta/128` | `collision_margin` |
| `max(q2*x,s*x,w*x) <= 10^-4` | Three separate conclusions of `scalar_smallness` |
| `w^2*x/eta <= 1/(32lambda)` | `scalar_smallness`; `lambda=255/256` exactly |
| `w^2*q2*x <= 1` | `scalar_smallness` |
| `w*q2*x/eta <= 1/(128mu)` | `scalar_smallness` |
| `e(theta/4)/(s*q2) <= 1` | `quarter_count_bound`, then `exception_common` |
| `C128*s^-128/theta <= 1/4` | `flag_margin`; `C128` agrees with the real incoming constant after rational casting |
| `2s*Eexc/(eta*w) <= 1/16` | `owner_count_bound`, `exception_common`, and `V42AlignmentGuards.guards`; see budget distinction below |

`sourceQ0_dvd`, `repetition_exact`, and `repetition_pos` additionally prove
that the actual power-of-two width is an integral positive repetition of
`pow2Ceil(4s|E|)`. `item_labels_fit` proves
`4s(n+s-3)<=2s*q2` using the promised lower edge bound and positive `n`.

The packet also supplies the source's item-deletion and collision margins,
the two threshold smallness bounds, and the block/profile scalar margins.
The review identified that the initial dominant-row theorem only concluded
`>=998/1000`; the frozen `dominant_margin_strict` now gives the literal
strict `>998/1000` in the source. The primitive `s*x<=1/10000` had sufficient
slack throughout, so no manuscript change was needed.

## Exceptional-coordinate budgets and real conversion

The source's literal `2^84` estimate is a separate proof obligation owned by
`exception-budget/V42ExceptionBudget.lean`; its independent certification is
not claimed by this review. It is not required as an unproved hypothesis
of any accepted cutoff theorem here.

This packet uses the older, looser **proved** dyadic `2^90` budget.
`V39GeneralExceptionBudget.exception_le_ebar` is applied to the actual
nonunit tolerance `eta/2`, not to tolerance one. The exact ceiling gives

```
ownerBudget = 2^(92+4k+(72+24k)/64),
EexcBudget = 2*ownerBudget.
```

`owner_count_bound` proves `e(theta,eta/2)<=ownerBudget`, so the source's
actual `Eexc=2e(theta,eta/2)` is bounded by `EexcBudget`. For `k>=200` and
`b>=4k`, `exception_common` proves the required incoming receipt margin
with this larger budget. There is no substitution of a desired conclusion
or hidden exception-cap hypothesis.

`cast_rho_dyadic`, `theta_real`, `theta_quarter_real`, the actual rational
`eta/2` cast, and the generated `deltaU/2` cast are explicit identities.
The guard structures use real quantities but derive their inequalities
from these rational formulas. Natural-number count divisions are handled
by integer inequalities; no real/natural division was silently interchanged.

`V42AlignmentGuards.Guards` matches every numerical premise of the current
`V42IndexedAlignment.alignment` and `V42ActualInternal.indexed_restoration`
interfaces, including the finite cap, exceptional copies, incoming receipt,
foreign mass, exact powers, strict pair margin, and profile thresholds.
Its theorem assumes only `k>=200,b>=4k`, with no profile, matrix, protocol,
target conclusion, or desired-constraint record as input.

`V42RestorationGuards.GeneratedGuards` supplies the generated final
interlace's actual exceptional count at `(rho,deltaU/2)`, exact `Q` power,
positive `rho,deltaU`, `rho<=1`, `deltaU<=1/64`, and `Q*theta<=1/20`.
These are derived numerical fields, not asserted restoration conclusions.

## Public full and generated schedules

For full products, the selected source recipe is exactly

```
ell = clog2(L+1),  k = 16+ell,
h = L+36k,  p0 = 2^(6+ell),  d0 = ell+7.
```

`fullS_rounding` proves `2^16(L+1)<=s<2^17(L+1)`.
`fullOverhead_exact` accounts for all four widths and both occurrences of
`log s`. `fullLengthCutoff K = 2^max(K,300)` gives `k>=K`,
`L>=16`, `d0<=L`, `h<=7L`, and `4k<=L`. With `K=k0`, it implies the common
cutoff and `rho<=s^-4`. A sufficient graph-size cutoff can consequently be
the fixed integer `2^(fullLengthCutoff k0)`.

The same packet proves the full block threshold from `u>=s/2`, the final
restoration product `Q*deltaU>=80L`, and linear bounds on all width
exponents. The rational finite caps are also privately replayed in
`ReviewChecks.finite_caps`; they include the source's strict
`deltaU<1/64` and `Q*theta<1/20`.

For generated lists,

```
k = max(k0,(clog2(n)+3)/4),  N=s^4=2^(4k),
rho=1/N,  q2=s^6,  w=s^8,  Q=s^24,
h=40k=10log2(N).
```

`generatedExponent_minimal` proves the exact least-dyadic condition by
integer fourth-power comparison. `generated_padding` gives
`n<=N<16max(n,N0)` with `N0=(2^k0)^4`.
`generated_width_polynomials` gives `q2^2=N^3,w=N^2,Q=N^6`.
`generated_tuple_count` and `generated_restoration_count` supply the two
additional exceptional-coordinate inequalities for this choice.

All core recipe, common-cutoff, fixed-promise-cutoff, full-cutoff, generated
exponent and sample-size definitions use computable integer/rational
operations. This review does not turn exponent-size bounds into an
already proved physical polynomial-time width printer. The real-accuracy
cutoffs `V42PublicSize.lengthCutoff` and `iterationCutoff` are explicitly in
a **noncomputable** section: `sample_sharp` is an analytic inequality, not
an executable arbitrary-real-accuracy cutoff function. A machine consumer
must use fixed integer/rational sufficient constants or its own computation
proof if it needs an executable cutoff.

## Iteration budgets and final sample

The numerical definitions are `B_i=d0+i*h`, `H_i=B_i+i`, and
`r_i=2^(B_i-1)`, with their exact successor recurrences. The sample side is
the literal power-of-two ceiling of
`16(r_i+1)clog2(r_i+2)2^H_i`, and `T=sampleSide^2`.

`sampleEntries_clog_upper` proves
`clog2(T)<=4B_i+2i+2clog2(B_i+2)+8`.
The packet proves `T<=2^(40(i+1)L)` and, for the indicated large source
cutoff and `n>=2`, `T<=n^(80(i+1))`. The sharp estimate
`clog2(T)<=(4+epsilon)iL` uses explicit sufficient length and iteration
cutoffs, with `0<epsilon<=1`. These are numeric bounds on this exact sample
formula. They do not assume a successful sample or claim the actual output
table has been connected to these definitions.

## Remaining conditions and acceptance boundary

1. The root must admit these frozen modules under production module paths,
   replay the combined target, and run its production/transitive audits.
2. Callers must expose the promised graph's positivity and both edge bounds,
   bind `L=clog2(n)` or the least generated exponent, and connect the recipe
   to the actual source/stream/table objects. The private `ReviewChecks`
   proves the fixed-promise full/generated numerical guard instantiations,
   but constructs no matrix.
3. Source profiles, source near-full hardness, matrix alignment/restoration,
   iteration, rounded sampling, actual printer identity, running time,
   random bits and estimator/complexity consequences need their separate
   consumer proofs. None is a premise hidden in these numerical proofs.
4. The exact `2^84` source estimate remains governed by its separate review.
   The present successful cutoff review uses its own proved `2^90` bound.
5. Claims of literal *intermediate* real-power upper estimates in the middle
   column are narrower than the proved allowance conclusions: this packet
   does not newly formalize every displayed middle-column estimate. It
   proves sufficient direct dyadic inequalities for every required allowance.

## Reviewed module hashes

Paths below are under `private-provenance-refs/a9f16373d50e14bf6f32557806135817f3f5703c34665a7b4fc4b5428dc29292/v42-formal-refresh`; the identical private
copies and hashes are listed in `FROZEN_STATUS.json`.

| Module | SHA256 |
| --- | --- |
| `parameters/V42Schedule.lean` | `8EC1AFE59D8B716EF5D2D804B8C6DC334529B1508AAA13CA9FFD3498999944B4` |
| `parameters/V42CommonMargins.lean` | `4C66571EB21410B4CAC0BA65F66085A479C04EF8EC614F2E5B291E16CDAAD458` |
| `parameters/V42ExceptionMargins.lean` | `031B557553E110A6A6882F603F57AC7E03226B318F4E36F5C5611743F031954B` |
| `parameters/V42SourceWidths.lean` | `B65F28094B5CB1C596FD03D581961A0B2E50EE945EDE7096995BFEE7EDA947D1` |
| `parameters/V42NearFullMargins.lean` | `C6A8794950753D540AC696BF9FFD4CD5913740D9BEDF68601B9C38FDDF5D42B3` |
| `parameters/V42AlignmentGuards.lean` | `AE10A4B20541C1F2B5E8834F0A86F15763F4232A959D47D50C7CD1BDB6767179` |
| `parameters/V42FixedPromiseCutoff.lean` | `B7208FC4281FBD5E554F81D1968E4FD1165CB8DC7661921D041BD2453EF08299` |
| `parameters/V42RestorationGuards.lean` | `F2004BE886A5BC708F4732CAE49C4C6A24AE0288F6E4C0AF01615E72BBCAD0AA` |
| `public-schedule/V42PublicSchedule.lean` | `EEF0803CC9EE45AD481DEA5649A33023AC4FDC29688BCDAF7EE22D921A62F6F2` |
| `public-schedule/V42PublicCutoff.lean` | `260435BAF15E881374D21E4E8AF4ADF40B3F9B049C63FAC0846B772F6399B9EE` |
| `public-schedule/V42PublicSize.lean` | `DEAAFCA1E44E09EE83587ADA8461533A8B64F14A4F3BA353860903C8236E43F2` |
| `alignment/V42IncomingGuard.lean` | `CD0A588443CC4BF663991590DBDD867E49D09835A152A1C4930AE8910D66CE27` |
