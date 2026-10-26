# Independent review of the v42 generated source profiles

Accept the four frozen source-profile modules as a **local proof segment**, conditional on the separately owned parameter theorems and the stated base-matrix and graph inputs. I found no mathematical or literal-statement defect. The new template profiles are proved from the base profile, and the NO lower bound concerns the actual generated graph matrix. An independent review-only theorem also verifies the YES bound on that identical matrix.

The segment proves `H₁=d+k`, `H₂=d+7*k`, and `C=d+8*k+1`, with YES cost at most `C-1` and NO cost at least `C` after deleting at most `eta=s^-2` from each original input law. It contains no premise supplying the target template profiles, target source hardness, or hardness of a different interlaced matrix.

This worker modified only `private-provenance-refs/d9f21fd443cc2bd24fc958b86da388678e1e9996801a1d1ec4bbbd86b051bf11/source-review`, ran no Git command or shared build, and launched no workers. The four implementation sources remained read-only throughout review.

## Frozen sources and source correspondence

[FREEZE.json](FREEZE.json) records the worker-agreed hashes of:

1. `V42GeneratedProfileGuards.lean`: `105eb42402d758eb5962ef99a9862b8f20c8a097a1328a88855e28ab6b2bbc88`.
2. `V42GeneratedSourceProfiles.lean`: `cec87f962ea4ea8a8e1d39b688e7a42a888f1f8253816e451b17f3f02d352526`.
3. `V42SourceNearFullGuards.lean`: `f71b24b09cba0b42daa045c77c3bb2f4b17e2841ae3d56496dba6f3621110492`.
4. `V42ActualGeneratedSource.lean`: `7a091a44f617279113666f131c4cf875a964654ad3bd29a01b99d14858300721`.

The author attachment has SHA-256 `e9eb48925f087a64141c4b756ae3293856a87b353acae33f3fdc802b33f0f535`. The inspected current source has SHA-256 `1c7f0fedc92989087219c2773411a42f610503846c6cf1e2dea5ac18961684f7`. [SOURCE_COMPARE.json](SOURCE_COMPARE.json) records byte-identical decoded-text comparisons for all six checked source blocks:

| Source object | Author attachment lines | Inspected current source lines |
| --- | --- | --- |
| Amplification recipe | 1342–1362 | 1349–1369 |
| Source costs | 1507–1510 | 1514–1517 |
| Template-profile statement | 1693–1710 | 1705–1722 |
| Source deletion-hardness statement | 1781–1794 | 1796–1809 |
| Full source deletion-hardness proof | 1795–1920 | 1810–1935 |
| Explicit-list schedule statement | 4890–4904 | 4940–4954 |

The root still owns the final whole-manuscript source lock. This review does not assume that concurrent authorized signposting/verification-paragraph work leaves the whole file hash fixed.

## Literal recipe, conclusions, and premises

The imported `V42Schedule` definitions are exactly

```text
s=2^k, rho=2^(-4*k), N=2^(4*k)=s^4,
q1=s-2, q2=2^(4*k+2*k)=s^6,
x=2^(-32*k)=rho^8=N^-8, eta=2^(-2*k)=s^-2.
```

`sourceCost_eq` and `sourceCost_logs` prove the exact source-cost formulas, rather than retaining the old recipe's logarithmic expression uninstantiated. They give

```text
C = d+k+(4*k+2*k)+k+1 = d+8*k+1
  = d+2*clog_2(s)+clog_2(q2)+1.
```

`costs_and_profiles` has only the following mathematical inputs beyond finite positive rational laws and the source-list data: `k≥200`, `d≥2`, `D(R)=d`, and the current two-threshold profile of the **base** matrix `R` at `rho`. It outputs:

- exact whole-template costs `D(A)=H₁=d+k` and `D(T)=H₂=d+7*k`;
- the two-threshold profile of `A` at `x,H₁`;
- the two-threshold profile of `T` at `x,H₂`;
- the two-threshold profile of the ordinary reference restriction at `x,C-1`.

The `CostsAndProfiles` definition is a conjunction of outputs, not an input certificate. The theorem's proof constructs its components by `A_profile`, then `T_profile`, then `reference_profile`, and derives exact costs from those proved profiles and the actual selector protocols. The code works for `d≥2`, which is stronger than the manuscript's requested `d≥3`; it therefore covers the source statement without weakening it.

`three_tail_cost` separately proves cost at least `H₁+1` for the first `q₁` gamma positions and the three distinct tail positions. Its remaining premises are the base profile, two distinct active tail positions, original base-row masses at least `2*s*rho`, and retained original gamma-label weight strictly greater than one half. It does not assume a collision-cost bound.

`nearfull` and `source_exact` take the following additional explicit inputs:

1. Positive rational graph gap `gamma`, positive degree bound `Delta`, and positive vertex and edge counts.
2. A cutoff `k≥commonCutoff(sourceDeltaV gamma Delta n m, sourceZeta gamma, Delta)` and `s≥4`.
3. The exact public width identity `q₂ = LiteralEdgeEncoder.Width s m rep`.
4. The actual edge map, looplessness, maximum degree at most `Delta`, and the external graph violation gap: every three-coloring leaves at least `gamma*m` monochromatic edges.
5. The base-matrix cost and its two-threshold profile, as above.
6. For `nearfull`, arbitrary retained actual row/column sets with original weights at least `1-eta` under the actual graph item row law and actual two-family column law.

There is no target-source profile, source communication lower bound, supplied protocol prefix, fixed-item-assignment certificate, collision witness, usable-mark family, or desired tracking state among these premises. The genuine graph gap remains an external mathematical input. The exact public width identity and cutoff must still be supplied by the public constructor/schedule join; neither is inferred merely from the chosen exponent.

## Numerical-guard read-back

The parameter theorems are under independent review elsewhere. This worker checked that the source join instantiates their precise quantities; it did not claim to re-prove their full arithmetic closure. [PARAMETER_DEPENDENCY_HASHES.json](PARAMETER_DEPENDENCY_HASHES.json) pins the observed source and object files used during the private replay.

| Required guard | How the new source modules obtain and consume it |
| --- | --- |
| Positive `rho,x`, `x≤1`, and legal layer exponents | `scalar_parameters k hk` obtains them at `b=4*k`; it uses `k≥200`, not the old generated parameter scale. |
| Small scalar products | It proves `s*rho≤1/1000`, `q₂*x≤1/10000`, and `s*x≤1/10000` using `scalar_smallness` and the exact new powers. |
| Cap-one exceptions at the whole retained label event | `generated_tuple_count` supplies `128*exceptionCount(x,1)≤s`. The cast in `scalar_parameters` is exactly `exceptionCount(x,1)≤s/128`; no alternative event or tolerance is substituted. |
| All three profile scale bounds | `profile_guards` proves `2^(k-j)*rho<1`, `2^(6*k-j)*x<1`, and `2^(k-j)*x<1` for each `j:Fin 2`. |
| All three block-population budgets | It combines the exact populations `q₁=s-2`, `q₂=2^(6*k)`, and `s=2^k` with `source_population_margins` and `budget_of_population`. The exception term is included in every required `2^(a-1)+1+e(x,1)` count. Reference retention uses the template fraction `(beta-(1-lambda))/lambda`, with `lambda=255/256`. |
| Genuine positive source deletion allowance | `source_guards_common` casts `numeric_margins` at positive graph `deltaV` and `zeta=gamma/24`. It proves an exact equality between the rational `sourceAllowance/s` and the historical real `deletionAllowance`. There is no unexplained change of allowance. |
| Near-full losses | It supplies `0<eta<1/100`, `(256/255)*s*eta≤1/1000`, and `eta≤deletionAllowance`, with `eta=s^-2`. |
| Assignment threshold and collision margin | It supplies `4*s²*rho≤1` and `8*s*q₁+1024*s*eta*q₂ < (gamma/24)*q₂/4`. Both expressions have the new `q₂=s^6`. |
| Remaining recursion and prefix margins | It supplies `2*q₂*x≤1/8`, `2*2^k*x<999/1000`, and `998/1000≤999/1000-2*(s-1)*x`. |
| Generic versus explicit specialization | `source_guards_common` supports arbitrary `b≥4*k`, while `source_guards` explicitly specializes it to `b=4*k`. The four reviewed source-profile/lower-bound modules themselves cover the explicit-list specialization. They do not by themselves prove the full-product profile variant. |

The final `nearfull` theorem supplies all these guards internally to `V39GeneratedNearFullCast.restriction_lower`; it exposes only the cutoff, graph data, base profile and exact width relation. Thus its user does not have to supply the target numerical budgets or target template profiles separately.

## Same matrix, weights, and ordering

`SourceData` contains three exact indexed lists: gamma, inner, and outer. An `ExactList` contains a finite ordinal label set, a positive rational law, its decoder, and equality of the prescribed bounded-wise event laws. Neither record contains a matrix hardness conclusion. `sourceData` obtains the three lists by literal Code D calls, with no graph promise, coloring, cost, profile, protocol, or target matrix conclusion as a construction argument.

The reviewed theorem is uniform over every such `SourceData`; this is a legitimate abstract source interface. The constructor owner must still instantiate it with the actual `executableCodeD` source. This review does not certify the physical printer or its runtime.

The actual endpoint is

```text
C ≤ restrictionD
  (fun col row => src.B R (graphActivity ... hwidth edge) row col) U W.
```

Here `B` is the actual two-family raw matrix decoded from those unchanged ordinal source labels. Its row and column laws are the actual mixtures with template/ordinary weight `255/256` and item/diagonal weight `1/256`. Duplicate decoded source values remain different labels with their original weights.

`toSources` reuses precisely those labels, laws and decoders. `matrix_eq` proves literal entries agree with `SourceData.B`; `columnLaw_eq` proves equality of its original column law. `row_mass_eq` and the explicit item-number equivalence transfer the original graph item law without changing weights. The generated selector permutation only reorders the same public coordinates. `V39GeneratedNearFullCast` uses the same `Fin.cast hwidth` as `graphActivity`, so no different activity map is introduced by the width cast.

## Prefix and collision timing

The inherited proof was read at its actual declarations, not accepted from its module comments alone.

1. `V39IndexedNearFull.restriction_lower` starts from a hypothetical short protocol for the actual retained matrix, transposes it, and obtains the actual finite protocol `P`.
2. `indexed_two_threshold_separation` projects the retained ordinary family only onto its original outer-list index. It chooses a retained gamma completion for each such index **independently of the row**. Template entries ignore this completion. It pulls back the original protocol without pruning its tree.
3. The separation theorem proves `CompleteAlicePrefix k P` for the original protocol. The pullback equivalence transfers the prefix for all retained inputs, including item rows and diagonal columns; it is not merely a prefix on the projected template restriction. Dominant template bins retain more than `998/1000` of their original inner-label mass.
4. The code then sets `rawCode P`, a fixed function of each original row. `itemBranch` selects each retained item's branch from that fixed function and its original retained base-row masses. Neither function takes the later activity coordinate as an argument.
5. Only after that assignment is fixed does `witnessCoordinates_card_ge` use the external graph gap to find many collision coordinates. `collision_items` proves that the chosen active/active/inactive rows have distinct active tail positions and each retains original base-row mass at least `x_cap=2*s*rho` in its assigned branch.
6. `select_marks_from_actual_retention` constructs the bad-coordinate set, a branch, and usable collision marks. It proves the required counts from the actual original retained row/column masses; it does not assume them.
7. `branchProtocol`, `branch_cost`, and `branch_correct` use the actual complete Alice prefix to obtain the residual protocol with the correct remaining depth and correctness on the original retained columns. Arbitrary defaults are confined to inputs outside the retained columns and do not enter correctness assertions.
8. `V39IndexedNoState` constructs the starting tracking state from actual diagonal gamma fibers. `no_short_remaining_protocol` supplies the three distinct local bounds: before Alice's next bit, after that bit, and the collision bound **before** that bit. The marked bound uses original gamma support and the current base profile via `marked_protocol_cost`. There is no use of a post-Alice row family to justify the pre-Alice extra bit.

These checks support the manuscript's timing: the assignment is fixed before choosing a coordinate, and the collision bound is used at the correct stage.

## Exact YES bound checked independently

The implementation packet exposes a general upper bound `D(N)≤C` and NO equality. Its YES protocol already exists in the generic constructor library and is also used by the constructor owner's new round wrappers.

To remove ambiguity about the local one-bit gap, this review compiled [SourceReview.actual_source_yes](replay/SourceAudit.lean) independently. It concludes

```text
D (fun col row => src.B R (graphActivity ... hwidth edge) row col)
  ≤ sourceCost d k - 1.
```

It takes only the same source data/width relation, a proper three-coloring, and the base cost `D(R)=d`; it assumes no base or target hardness profile. It applies `graphActivity_yes` and the actual `SourceData.B_yes` protocol, then checks `q₁+2=s`, `clog₂(s)=k`, and `clog₂(q₂)=6*k`. Thus the YES and NO statements concern the identical source matrix and activity map, with costs `d+8*k` and `d+8*k+1` respectively.

This is a review-only executable demonstration, not a mutation of the frozen implementation. The root may retain it as verification evidence or add a suitable production wrapper during its authorized integration.

## Compiler evidence and acceptance boundary

[REPLAY.json](REPLAY.json) records fresh private recompilation of all four frozen modules, each with exit code zero and no warnings. The pinned compiler is Lean 4.30.0, commit `d024af099ca4bf2c86f649261ebf59565dc8c622`, with `relaxedAutoImplicit=false`. The private output directory supplies all four reviewed new modules; [LEAN_PATH.json](LEAN_PATH.json) records the paths. Parameter and existing production/package dependencies were reused from their observed cached objects, not rebuilt by this worker.

The final [SourceAudit.compile.log](SourceAudit.compile.log) has exit code zero and no warnings. It prints the exact profile/collision/NO/YES signatures and checks fourteen transitive axiom surfaces, including the review-only YES theorem. Every surface contains only `propext`, `Classical.choice`, and `Quot.sound`. A first review-helper attempt needed one missing namespace opened; the failed review-only attempt is preserved as `SourceAudit.attempt-1.log`. No frozen implementation source needed a repair.

The root should now perform production import renaming, fresh dependency builds, axiom gates and statement read-back. Before claiming the complete generated reduction, it must join the public graph-dependent choice of `k`, the exact repeated-width identity, the actual Code D outputs, the induction's base cost/profile, and the graph gap to these endpoints. Full-product source profiles, the subsequent interlaces, full algorithms/runtime/ETH composition and final manuscript release remain outside this review. The separately assigned parameter review owns the proof and uniformity of the imported cutoff and margin theorems.
