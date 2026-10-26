# Independent review of the literal v42 width estimates

The frozen exact-numeric packet is accepted for all eleven
quantity-to-middle-column bounds in `eq:width-margins`, together with the
two exceptional-count substitutions immediately after the table. The actual
current dyadic recipe is used throughout the public source-facing theorem.
All constants and real exponents match the manuscript exactly.

The three implementation modules, the author's audit module, and the exact
`2^84` exceptional-count foundation all passed fresh private replay.
Independent statement and dependency audits also passed. The 18 public
theorem axiom queries use only `propext`, `Classical.choice`, and `Quot.sound`;
there are zero warnings and no admitted declarations.

This adds the literal estimates missing from the earlier sufficient-budget
review. It does not replace the earlier fixed-cutoff and required-allowance
proofs, and it does not claim the separately owned comparison of every
printed middle expression to its allowance at a particular cutoff.

## Source and freeze

The original review context was replacement v42 `main.tex`, SHA256
`1C7F0FEDC92989087219C2773411A42F610503846C6CF1E2DEA5AC18961684F7`.
The full manuscript changed during this review to SHA256
`EC8AF5767ECCC1184E7A1B5F88979AB0A7EE9BE60D91BE4E61EC80AA66861F78`.
`SOURCE_COMPARE.json` verifies that all three relevant source regions are
byte-identical between these two files:

| Region | SHA256 of UTF-8 region text |
| --- | --- |
| Common-parameter section through the full-product subsection | `8EE1EECECA5ACDEE2E75FCEF19ABFF2D2EF715CFFDAA4BE3D4DF149D003BFF04` |
| Amplification recipe and its following explanation | `6328972F647229B3B41DD505FBC2C4D1A2D257B55D4C8511D36AAE22772F3C49` |
| Exceptional-count definition before the conditioning lemma | `B2B5750187C6824CF76B6EB46575C5854567CBCA05183BCB316350939E04CF6F` |

The relevant anchors are `def:amplification-parameters`,
`eq:conditioning-size-bound`, `lem:common-schedule`, `eq:width-margins`,
and the two estimates in the following paragraph. In the original snapshot,
the table begins at line 4808 and the substitutions at lines 4824--4827.
`SOURCE_TARGETS.md` records the independent target inventory established
before the new proofs were frozen.

The original packet manifest is preserved as `MANIFEST_ORIGINAL.json`.
Only frozen sources were copied into this review's `snapshot/`; neither the
authoring packet nor the earlier numerical/schedule review was edited.

## Exact actual-parameter statement and domain

The public declaration is
`CurrentAdditive.V42NumericMargins.width_margins_middle`.
Its assumptions are precisely:

```
k,b,n,m,Delta : Nat,
1 <= k,
4*k <= b,
n <= 2^b,
2*m <= Delta*n.
```

Here `k` is the width exponent, not the number of amplification rounds.
The actual `V42Schedule` parameters are

```
s=2^k, rho=2^-b, q1=s-2, q2=s^2/rho,
w=s^8, Q=s^24, x=rho^8, eta=s^-2, theta=1/(512Q).
```

The private `recipe_real` lemma derives all rational-to-real recipe
identities from `V42Schedule.recipe_exact`. `real_domain` derives
`s>=1`, `rho>0`, and `rho<=s^(-4)` from the dyadic exponent comparison.
The graph inequalities are cast exactly to real inequalities, including
`n<=1/rho`; no rounded real graph size or new input-dependent parameter is
introduced.

The condition `k>=1` proves `s>=2`, so natural subtraction in `q1=s-2`
casts to real `s-2` exactly. This avoids the false identity that would occur
at `k=0`. The existing common cutoff gives the stronger `k>=200`, so the
public theorem covers every source application.

All negative and fractional exponents below are explicitly real in the
Lean statements. In particular `3/8`, `35/8`, `-53/8`, and `-5/8` cannot
be interpreted as natural-number division.

## All eleven table rows

The theorem returns the following eleven conclusions on the actual
`V42Schedule` quantities. Rows 1 and 10 are proved by identities, which are
stronger than the table's upper-bound claims.

| Source row | Exact conclusion | Generic proof |
| --- | --- | --- |
| 1 | `s*eta <= s^(-1)` | `source_eta`, equality |
| 2 | `4*s*m/q2 <= 2*Delta/s` | `edge_width` |
| 3 | `s^2*rho <= s^(-2)` | `small_mass` |
| 4 | `s*q1/q2 <= s^(-4)` | `collision` |
| 5 | `max(q2*x,s*x,w*x) <= s^(-24)` | `max_width_x` |
| 6 | `w^2*x/eta <= s^(-14)` | `w2x_over_eta` |
| 7 | `w^2*q2*x <= s^(-10)` | `w2q2x` |
| 8 | `w*q2*x/eta <= s^(-16)` | `wq2x_over_eta` |
| 9 | `exceptionCount(theta/4,1)/(s*q2) <= 2^85*s^(-53/8)` | `quarter_exception_ratio` |
| 10 | `C128*s^(-128)/theta = 512*C128*s^(-104)` | `flag_ratio_identity` |
| 11 | `2*s*Eexc/(eta*w) <= 2^89*s^(-5/8)` | `owner_exception_ratio` |

The real `C128` is the exact cast of `V38Schedule.C128`, namely
`(2^14/((255/256-1/2)^2))^128`, as in `eq:common-budgets`.
The flag identity is valid for any real constant; its specialization uses
this exact source constant.

The algebra is source-faithful. The monomials after substituting the recipe
are `s^2*rho^7`, `s*rho^8`, `s^8*rho^8`, `s^18*rho^8`,
`s^18*rho^7`, and `s^12*rho^7`. Applying `rho<=s^(-4)` gives the
stated negative exponents; the first two terms of the maximum have still
smaller exponents and are bounded using `s>=1`.
The edge-width row uses only the displayed edge upper bound and
`n<=1/rho`, with positive denominators. No graph-hardness fact is needed.

## Exact exceptional counts and constants

The actual source count is

```
epsilon(v,tau) = min(tau,2^-30*v^(1/256)),
exceptionCount(v,tau) = 8*ceil(2^20*epsilon(v,tau)^(-2)*v^(-1/512)).
```

`V42ExceptionBudget.exceptionCount_real_bound` proves, including that
natural ceiling,

```
exceptionCount(v,tau) <= 2^84*tau^(-2)*v^(-1/64)
```

for `0<v,tau<=1`. The foundation's earlier three-term bound is also
replayed. It splits the minimum and charges the ceiling by an added eight;
the larger coefficient is not assumed as a budget premise.

The new packet's `Eexc s` is exactly

```
2*exceptionCount(1/(512*s^24),(1/s^2)/2),
```

with the natural count cast to real. It is not `ownerBudget` or
`EexcBudget`. Positivity and upper bound one for the actual masses and
tolerances are proved from `s>=1` before invoking the `2^84` theorem.

For the first substitution,
`theta/4=1/(2^11*s^24)`. Its negative `1/64` power is exactly
`2^(11/64)*s^(3/8)`. Bounding `2^(11/64)<=2` yields

```
exceptionCount(theta/4,1) <= 2^85*s^(3/8).
```

For the second, `(eta/2)^(-2)=4*s^4`, while
`theta^(-1/64)=2^(9/64)*s^(3/8)`. After doubling the actual count and
using `2^(9/64)<=2`, this yields

```
Eexc <= 2^88*s^(35/8).
```

`exception_substitutions k` proves both statements on the actual current
`theta k`, `eta k`, and `s k` for every natural `k`.

For table row 9, `s*q2=s^3/rho` and `rho<=s^-4`, so dividing the first
estimate contributes seven powers of `s`; `3/8-7=-53/8`.
For row 11, the ratio simplifies to `2*Eexc/s^5`, hence
`35/8-5=-5/8` and the coefficient is exactly `2^89`.
No exponent is rounded and no larger dyadic budget is substituted.

## Private checking and dependency audit

Fresh private checks passed for:

1. `V42ExceptionBudget`, the exact foundation.
2. `V42NumericPowerMargins`.
3. `V42NumericExceptionMargins`.
4. `V42ExactWidthMargins`.
5. `V42ExactWidthMarginsAudit`, the frozen author audit.
6. Independent `StatementReadback` and `DependencyAudit`.

The compiler was Lean 4.30.0, commit
`d024af099ca4bf2c86f649261ebf59565dc8c622`, with
`relaxedAutoImplicit=false,maxHeartbeats=3000000` and the frozen source's
own options. Compilers ran sequentially and wrote only review-local objects
and logs. The exact current recipe resolves through the earlier independently
replayed private schedule snapshot. No shared dependency was rebuilt here.

The independent statement readback covers all 18 public theorems, including
the two foundation theorems. All axiom cones contain only the allowed
standard axioms. There are zero warnings, no `sorry`, no `admit`, and no
custom axiom.

The proof-graph audit traversed **17,338 declarations** from the two
source-facing roots. It requires the actual `V38Moments.exceptionCount`,
the exact `2^84` theorem and the actual `V42Schedule.recipe_exact`.
It rejects active references to `ebar`, `ownerBudget`, `EexcBudget`, and
the older `exception_le_ebar` theorems. The audit passed. Merely importing
an older dependency did not silently replace an actual count by its budget.

`DEPENDENCIES.json` pins nine resolved source/object modules and the
toolchain, Lake manifest and current manuscript hash. The original packet
manifest, independent replay logs, axiom audit and `RECEIPT.json` retain
the exact reviewed sources and checked scope.

## Boundary

Accepted: the eleven literal quantity-to-middle estimates and the two
following actual exceptional-count estimates, with exact constants, real
powers, current dyadic parameters and explicit graph-size hypotheses.

Separate: the earlier required-allowance/fixed-cutoff proofs, the new
middle-expression-to-allowance comparisons assigned to another packet,
matrix constructions and all semantic/runtime/complexity consequences,
production integration and complete-source release gates.
In particular, a proof that a quantity is below both a middle expression
and an allowance does not itself prove that the middle expression is below
that allowance. This receipt makes no such inference.

## Reviewed hashes

| Source | SHA256 |
| --- | --- |
| `numeric-margins/V42NumericPowerMargins.lean` | `126F82517788665533BFE448CC467085F52ECB3036864F02C4157ABECFCA5A5C` |
| `numeric-margins/V42NumericExceptionMargins.lean` | `B3CF457179ED706EC9A92031D9CDB04C1C73F326297DE5C14F84D2E3F892340E` |
| `numeric-margins/V42ExactWidthMargins.lean` | `88855A26F6E5DE7C6C7A52BF771D81D03C0B2C27A3A5D9B20F3919790966D3CC` |
| `numeric-margins/V42ExactWidthMarginsAudit.lean` | `8545C87AB4E9D9B335C6DB09C22DEF968DCA515EDE77F5187EF524D0099DD55D` |
| `exception-budget/V42ExceptionBudget.lean` | `12ABFFC9652C35F08A01912F95DA5F859EC0D846D3432F997E46A05805DD43F9` |

Paths in this table are under `private-provenance-refs/a9f16373d50e14bf6f32557806135817f3f5703c34665a7b4fc4b5428dc29292/v42-formal-refresh`. No Git operation,
production edit, shared build or subdelegation was used for this review.
