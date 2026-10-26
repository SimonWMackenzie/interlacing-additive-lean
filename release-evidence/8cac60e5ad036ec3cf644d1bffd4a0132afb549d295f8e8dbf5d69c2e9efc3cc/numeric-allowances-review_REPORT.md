# Independent review of the complete literal numerical chain

Both frozen modules are accepted. Together with the independently replayed
exact-numeric packet, they prove all eleven displayed chains

```
actual quantity <= printed middle expression <= required allowance
```

on the actual v42 recipe and the **unchanged original common cutoff**.
The fixed graph-promise specialization also compiles privately, so one
cutoff depending only on `gamma,Delta` works for every admitted graph,
base matrix and round count. No mathematical issue was found.

The two module replays, independent statement readback, fixed-promise
specialization and dependency audit all passed. Eight packet theorem axiom
queries plus the private specialization use only `propext`,
`Classical.choice`, and `Quot.sound`. There is one harmless tactic-lint
warning. No source or dependency drift was found at receipt creation.

## Source and exact modules

The source is replacement v42
`papers/randomized-additive-hardness/versions/v42/source/main.tex`,
SHA256 `EC8AF5767ECCC1184E7A1B5F88979AB0A7EE9BE60D91BE4E61EC80AA66861F78`.
The source-bound comparison in
`../numeric-margins-review/SOURCE_COMPARE.json` proves that the amplification
recipe, common-parameter section and exceptional-count definition are
byte-identical to the earlier reviewed `1C7F0FED...` source. The anchors are
`def:amplification-parameters`, `lem:common-schedule`, `eq:common-budgets`,
`eq:conditioning-size-bound`, and `eq:width-margins`.

`V42NumericAllowances.middle_allowances` proves each printed middle
expression is at most its allowance.
`V42WidthMarginsChain.width_margins_chain` joins those conclusions to the
previous exact quantity-to-middle theorem, with the same parameters and
ordering. The tenth quantity-to-middle identity is converted to an inequality;
no other quantity, constant or exponent is changed in the join.

All ten private module source/object entries in the author's manifest were
checked before snapshotting. The unmodified manifest and receipt are saved
as `MANIFEST_ORIGINAL.json` and `RECEIPT_ORIGINAL.md`. The two sources were
copied to this review's `snapshot/`; author files and previous reviews were
not edited.

## Exact eleven-row statement

In this table all quantities are the actual current `V42Schedule` values,
all powers are real, `C=C128`, `lambda=255/256`, `mu=1/256`, and
`Eexc=2*exceptionCount(theta,eta/2)` is the actual ceiling-defined count.

| Actual quantity | Printed middle expression | Required allowance |
| --- | --- | --- |
| `s*eta` | `s^(-1)` | `2^(-16)*min(1,deltaV,mu*zeta)` |
| `4*s*m/q2` | `2*Delta/s` | `1` |
| `s^2*rho` | `s^(-2)` | `1/4` |
| `s*q1/q2` | `s^(-4)` | `zeta/128` |
| `max(q2*x,s*x,w*x)` | `s^(-24)` | `1/10000` |
| `w^2*x/eta` | `s^(-14)` | `1/(32*lambda)` |
| `w^2*q2*x` | `s^(-10)` | `1` |
| `w*q2*x/eta` | `s^(-16)` | `1/(128*mu)` |
| `exceptionCount(theta/4,1)/(s*q2)` | `2^85*s^(-53/8)` | `1` |
| `C*s^(-128)/theta` | `512*C*s^(-104)` | `1/4` |
| `2*s*Eexc/(eta*w)` | `2^89*s^(-5/8)` | `1/16` |

The joined theorem has exactly these twenty-two inequalities. Its inputs
are positive rational `deltaV,zeta`, natural `k,b,n,m,Delta`, and

```
commonCutoff(deltaV,zeta,Delta) <= k,
4*k <= b,
n <= 2^b,
2*m <= Delta*n.
```

The original recipe is `s=2^k`, `rho=2^-b`, `q1=s-2`, `q2=s^2/rho`,
`w=s^8`, `Q=s^24`, `x=rho^8`, `eta=s^-2`, and `theta=1/(512Q)`.
The cutoff supplies `k>=200`, which in particular justifies the exact
real cast of natural subtraction in `q1`. No matrix, round, desired guard,
exception-budget certificate or future conclusion is an input.

## Why the original cutoff suffices

The allowance is exactly the frozen rational definition

```
A = sourceAllowance(deltaV,zeta)
  = 2^-16 * min(1,deltaV,zeta/256).
commonCutoff(deltaV,zeta,Delta)
  = 200+2*Delta+ceil(1/A)+ceil(128/zeta).
```

`sourceAllowance_real` proves the literal real minimum expression equals
the cast of this rational definition. `cutoff_small` gives
`k>=200`, `2Delta<=k`, `s^-1<=A`, and `s^-1<=zeta/128`.
This proves the first allowance exactly and the collision allowance by
`s^-4<=s^-1`, since `s>=1`. The edge allowance follows from
`2Delta<=k<=2^k=s`.

The remaining powers are compared through the exact real identity

```
(2^k)^a = 2^(k*a).
```

No fractional exponent is rounded. In particular, at every `k>=200`,
`85-53k/8<=0` and `89-5k/8<=-4`. These prove the exact exceptional-row
allowances `1` and `1/16` with the source's coefficients.

For the flag row the proof establishes the explicit true bound
`C128<=2^2176` from its literal source definition. Thus
`512*C128*s^-104<=2^2185*s^-104<=2^-2=1/4` at the same cutoff.
The intermediate coefficient bound does not replace the source constant
in the displayed chain.

The smaller integer-power comparisons give exactly `1/4`, `1/10000`,
`1/(32lambda)`, `1`, and `1/(128mu)` in their corresponding rows. The
cutoff was not enlarged and no assumption that the middle expressions
already satisfy their allowances was introduced.

## Fixed graph-promise cutoff

The existing frozen definition remains

```
k0 = fixedPromiseCutoff(gamma,Delta)
   = commonCutoff(gamma/(4*Delta),gamma/24,Delta),
s0 = 2^k0.
```

For positive rational `gamma`, positive natural `Delta`, and a graph with
`n>0,n<=2m`, the actual source tolerance
`deltaV=gamma*m/(2*Delta*n)` is positive and at least `gamma/(4Delta)`.
The prior `fixedPromiseCutoff_graph` theorem therefore derives

```
commonCutoff(actual deltaV,gamma/24,Delta) <= k
```

from the single fixed premise `k0<=k`.

The independent private `FixedPromiseReadback.lean` defines
`V42AllowanceReview.fixed_promise_chain`, applying this theorem to the complete joined
chain with the actual `sourceDeltaV` and `zeta=gamma/24`. It assumes only
the fixed positivity/graph-size conditions, `b>=4k`, `n<=2^b`, and
`2m<=Delta*n`. It derives all eleven complete chains, rather than merely
returning a cutoff comparison. This specialization passed the compiler
and axiom audit.

This makes the cutoff independent of actual vertex/edge counts, the base
matrix and the number of rounds. Its use in the full and generated public
schedules remains covered by the earlier schedule review; those modules
were not changed here.

## Replay and proof-graph audit

Lean 4.30.0, commit `d024af099ca4bf2c86f649261ebf59565dc8c622`, was used with
`relaxedAutoImplicit=false,maxHeartbeats=1500000` and source-local options.
The independent compiler path searches this snapshot, then the previously
replayed exact-numeric snapshot, then the previously replayed schedule
snapshot, before production/package objects. All compilers ran sequentially
and wrote only review-local objects/logs.

Both frozen implementation modules passed on their first private replay.
The eight public theorem statement/axiom queries passed. One initial
reviewer-only fixed-promise check had a tactic-semicolon error; it was
corrected in the review file, without altering either author module. The
initial log and failed checkpoint remain preserved. The final fixed-promise
check and independent dependency audit passed.

The final audit traversed **17,390 declarations**. It requires both
`width_margins_middle` and `middle_allowances`, the exact `2^84` count
theorem, the original `commonCutoff`, and the fixed-promise graph
specialization. It rejects active `ebar`, `ownerBudget`, `EexcBudget`, or
older exceptional-budget substitutions. All roots use only the three
permitted standard axioms.

`DEPENDENCIES.json` pins thirteen resolved source/object modules plus the
toolchain, Lake manifest and manuscript. The receipt checks final frozen
hashes and dependency drift. The single final warning is an unused
`congr 1` tactic in a completed equality proof; it affects no statement
or proof obligation.

## Scope

Accepted: the complete literal eleven-row numerical chain and its
specialization through the unchanged fixed graph-promise cutoff. The two
post-table exceptional-count substitutions are supplied by the separately
accepted exact-numeric receipt. These together close the exact source
intermediates assigned in this review.

Separate: matrix semantics, actual algorithms and clocks, estimator or
complexity consequences, production integration, and complete-manuscript
release gates. No such conclusion is inferred from these numerical checks.

| Frozen source under `private-provenance-refs/113a7d0232c7846c5e7745181c6b52f7934d8c4a940f20d3334009aac01839e0/numeric-allowances` | SHA256 |
| --- | --- |
| `V42NumericAllowances.lean` | `A6C5DD4E6C6CFA471B8B5B2CC1D98EE21A7667E0800079A63ADC8C39ECF3FC21` |
| `V42WidthMarginsChain.lean` | `F0BB438F705373FA8C77ACC340F71D5CE9E3E2D3D1EE92E1918CC6F8876EC940` |

No Git operation, production edit, shared build or subdelegation was used.
