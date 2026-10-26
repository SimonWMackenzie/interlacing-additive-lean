# Independent review: standalone indexed near-full source theorem

Accept the three frozen proof modules for root integration. They supply the standalone indexed `src:near-full` implication using the stated template profiles, original-weight collision bound, graph promise, numerical margins and source laws of order at least eight. **No restriction profile of the base matrix `R` is an additional premise.** I found no mathematical, statement or same-matrix defect.

The final named theorem, `CurrentAdditive.V42IndexedSourceHardness.hardness`, proves both the exact whole-matrix cost

```text
D M = C,   C = d+t+ell+t+1,
```

and cost at least `C` for every restriction retaining original row and column weight at least `1-eta`. Here `s=2^t`, `q₂=2^ell`, and `H₁=d+t`, so this is precisely the source formula `C=H₁+log₂(q₂)+log₂(s)+1`.

This worker modified only `private-provenance-refs/26c9acd6198a46c643fcddb75cc163722f91588ccd809b6c812db83a991a3eb7/nearfull-review`, ran no Git command or shared build, and launched no workers. Each compiler ran sequentially. The implementation files and old production modules remained read-only.

## Frozen inputs and replay

[FREEZE.json](FREEZE.json) records the worker-confirmed source hashes:

| Module | SHA-256 |
| --- | --- |
| `V42IndexedCollisionInterface` | `a61c93c84eabfd085f2d5a7ae6574ba0536fb940e36e4fbab61986fe93ff1d91` |
| `V42IndexedNearFullInterface` | `827c5de766a386516f2d84d956b4b04021a64e1d59ad2a49ccbf119d0c1fe8ab` |
| `V42IndexedSourceHardness` | `bd0d6715614ce27a373c2724f152d203b5410d24a19f52667b29da676ba84d2f` |

All three were copied to `replay/` and independently compiled there under pinned Lean 4.30.0. No implementation-worker private object was imported for these three modules. [REPLAY.json](REPLAY.json) records the three successful proof compilations and the successful independent audit, with output hashes. [LEAN_PATH.json](LEAN_PATH.json) records the private replay directory followed by the existing production/package libraries. [SHARED_IMPORTS.json](SHARED_IMPORTS.json) pins the three immediate production imports, source and object; their full source closure was not freshly rebuilt by this worker.

## Exact collision hypothesis

`ThreeTailBound src R H cap` is a transparent definition of the following **local** statement:

- Choose any embedding of three distinct positions into `Fin(s+1)`, the original tail positions.
- Take all original first `q₁` positions, followed by those three tail positions.
- Let `Rows` be a retained set of `(position,baseRow)` pairs and let `Words` be a retained set of complete original Gamma labels.
- If every position's original `muX` fiber weight is at least `cap`, and the original `src.gamma.law` weight of `Words` is strictly greater than one half, the corresponding selected interlace of `R` has cost at least `H+1`.

The displayed definition and full endpoint signatures are in [Audit.compile.log](Audit.compile.log). This is not a cost/profile assertion about the whole target source matrix. It is exactly the collision hypothesis in `src:profiles` that `src:near-full` is permitted to assume.

`threeTailWord` reads the actual `head` and `tail` of `src.gamma.decode gamma`; it neither collapses equal decoded words nor changes the complete Gamma label law. Its row-mass premise is `muX.prob {u | (i,u) ∈ Rows}` for each block, not a uniform-block total with a missing width factor. Its column-mass premise is on the original Gamma event, not a conditional, projected, or resampled law.

`selected_cost` instantiates that bound at the two different active tail positions and the inactive last tail position. The injection follows from `p != p'`; both active positions are distinct from the last position. A pointwise equality identifies `threeTailWord` with the existing actual `selectedGamma` decoder. The selected Gamma labels and original masses are unchanged.

## Proof use of the callback

`marked_protocol_cost` constructs the exact row set `indexedWitnessRows` from the retained template projection and the three actual item-row sets. It proves the required original base-row mass separately for every head and tail block. Those sets depend on the fixed coordinate, retained template set and item rows, but **not on Gamma**. The finite support `S` is a set of original Gamma labels; `SourceSupportStep.mass` is changed directly to its original-law event probability, with no renormalization.

It then calls `selected_cost` with the supplied callback. `witness_source_cost_le` maps that selected interlace into the actual retained diagonal family, and the actual protocol's correctness supplies its communication upper bound. This yields the local `H+1` cost at the marked coordinate. It does not derive the collision cost from a hidden base profile.

`no_short_remaining_protocol` provides the three distinct local bounds to the existing sharp collision recursion:

1. Before Alice's next bit, the first template profile supplies the ordinary `H` bound.
2. After that bit, the first-template profile and original eight-wise inner-source law supply the exact-block bound.
3. Before that bit, the supplied three-tail collision callback supplies the marked `H+1` bound just described.

Only the first-template profile is used by the first two suppliers. The third supplier calls the **new** callback-based marked proof. It does not call the old marked theorem requiring a restriction profile of `R`.

`no_short_with_usable_collision_coordinates` constructs its own starting tracking state from the actual retained diagonal Gamma fibers, the actual bad coordinates and the constructed marks. The standalone source theorem does not assume a starting state, successful tracking, collision witness, protocol prefix or target lower bound.

## Actual near-full source lower bound

`V42IndexedNearFullInterface.restriction_lower` assumes:

- actual source data `Sources` at independence order `D_source >= 8`;
- the graph's actual activity map, a fixed selector permutation, a NO graph violation gap, positive sizes, looplessness and the degree bound;
- the displayed dyadic widths, deletion allowance, assignment/collision, prefix and recursion margins;
- the first template profile at `(x,H)` and second template profile at `(x,H+ell)`;
- the exact `ThreeTailBound` above at cap `2*s*rho`;
- original retained row and column weights at least `1-eta`.

It concludes `H+ell+t+1 <= restrictionD` for the **actual two-family indexed matrix**, the same graph activity and selector permutation, and those actual retained row and column sets.

The original source's reference profile is not used by this lower-bound proof. Omitting that unused premise strengthens the conditional implication; it does not introduce a new assumption. The generic lower theorem also keeps `H` independent of `D(R)`; it does not claim whole-matrix equality for free `H`.

I checked the inherited timing and identity steps at their actual declarations:

- The proof obtains a hypothetical short protocol for the actual retained matrix.
- Original ordinary-family labels are projected onto their original outer index; one retained Gamma completion is chosen per outer label, independently of rows. The original protocol is pulled back without pruning its tree.
- Separation proves a complete Alice prefix on the **original** protocol, including all retained item rows and diagonal inputs, and gives dominant template bins with original mass above `998/1000`.
- `rawCode P` fixes a row-to-branch map. The retained-item branch assignment is fixed before any activity coordinate is chosen.
- The external graph gap and numerical margins construct actual collision coordinates and usable marks. All retained item and template weights use the original laws.
- The original prefix yields the actual residual protocol, with the correct remaining cost and correctness on the original retained columns.
- The new callback-based recursion contradicts that remaining cost.

There is no insertion of an auxiliary row family in the lower bound, and no call to a theorem already assuming the whole target source is hard.

## Named exact-cost theorem

`V42IndexedSourceHardness.hardness` supplies the manuscript specialization `H₁=d+t`. Its only additional mathematical inputs are the genuine source assumptions `D(R)=d>=3` and `q₁+2=2^t`.

The independent upper bound `source_upper` uses the transparent identity that the actual two-tag matrix is precomposition of the general indexed source by `oldTag`. It applies the already proved universal protocol only for an **upper** bound. This does not transfer a lower bound from a larger or different matrix. The exact dyadic logarithms and

```text
clog₂(q₁+2^t+1) <= t+1
```

give the stated `C=d+2*t+ell+1` upper bound. Applying the new lower theorem to the full original row and column sets gives the reverse inequality; the same theorem supplies every allowed retained restriction. Thus the final theorem proves equality and deletion stability for the same actual matrix.

The base **cost** assumption is part of the source statement. The base **restriction-profile** assumption is absent from the final elaborated signature and from its required proof path.

## Independent dependency and axiom audit

The final independent [Audit.lean](replay/Audit.lean) checks both the generic lower theorem and the named exact-cost theorem. It traverses types and proof values across **21,136 declarations**. It requires the new selected-cost, marked, remaining-protocol and no-state callback chain, and the independent source upper bound.

It rejects the old `V39IndexedNearFull` and `V39IndexedNoState` proof namespaces, and the old `V38IndexedTwoTag.marked_protocol_cost` and `no_short_remaining_protocol` declarations that used the extra base profile. None occurs in the traversed proof graph, despite old modules being imported for unrelated reusable definitions and lemmas.

All seven principal transitive axiom surfaces contain only `propext`, `Classical.choice`, and `Quot.sound`. All three proof compilations and the final independent audit have zero warnings and zero errors. Source scanning finds no `sorry`, `admit`, new axiom or opaque assumed conclusion. An initial review-only audit used the reserved token `prefix` as a local variable; that parser issue was corrected to `guardPrefix`, and the failed review attempt is preserved separately. No frozen proof source needed repair.

## Source correspondence and admission boundary

[SOURCE_COMPARE.json](SOURCE_COMPARE.json) binds the source recipe, source costs, `src:profiles`, and the complete `src:near-full` statement and proof to the author attachment. All six compared blocks are unchanged. The author attachment hash is `e9eb48925f087a64141c4b756ae3293856a87b353acae33f3fdc802b33f0f535`; the current source snapshot hash for this review is `ec8af5767eccc1184e7a1b5f88979ab0a7ee9be60d91be4e61ec80aa66861f78`. The relevant current statement/proof lines are 1705–1722 and 1796–1935; the cost formula is at 1514–1517. The root owns the final whole-manuscript lock.

The collision callback remains a **stated hypothesis of this standalone theorem**. This packet consumes it faithfully; it does not itself prove the template/collision hypotheses from a base profile or a concrete recipe. In particular, the earlier `V42GeneratedSourceProfiles.three_tail_cost` mentions two active positions and the fixed inactive last position; it must not silently be identified with the stronger any-three-tail callback without the separate generalization/bridge now owned by the source worker.

Admit these three exact hashes with qualified imports, then run the root's fresh production dependency and axiom gates. Keep the generated/full-product hypothesis providers, numerical schedule instantiations, concrete source/printer transport, runtime, reductions and final release claims within their separately reviewed scopes. No mathematical gap was found in this standalone conditional near-full interface.
