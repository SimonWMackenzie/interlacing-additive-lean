# Independent review: arbitrary three tail positions on original Gamma labels

Accept the frozen `V42GeneratedThreeTail.lean` proof for production integration. It proves the full arbitrary-three-tail clause of generated `src:profiles` / `det:profiles`, returning precisely the collision hypothesis used by the reviewed standalone near-full theorem. I found no mathematical, law, quantifier or statement-fidelity defect.

The exact declaration anchor is:

```text
CurrentAdditive.V42GeneratedThreeTail.generated_three_tail_bound
scratch/v42-formal-refresh/generated-tail/V42GeneratedThreeTail.lean:122
```

Its source SHA-256 is `ed6387351a67e921969c368113b5fe550487229630bf5a9f14af7645a86ada48`.

## Literal statement and remaining premises

The theorem assumes the actual generated source at independence order 8192 and the revised widths `s=2^k`, `q₁=s-2`, `q₂=2^(6*k)`, together with `k>=200`, `d>=2`, and the current two-threshold **base** profile of `R` at `rho=2^(-4*k)` and cost `d`.

It concludes exactly

```text
V42IndexedCollisionInterface.ThreeTailBound src R (d+k) (2*s*rho).
```

Unfolding that definition quantifies every embedding `Fin 3 ↪ Fin(s+1)`. It keeps the first `q₁` original positions, appends the three selected distinct tail positions, and takes arbitrary retained rows and a retained event of **complete original Gamma labels**. If each block has original base-row weight at least `2*s*rho`, and that event has original Gamma weight greater than one half, the selected interlace has cost at least `d+k+1`.

There is no assumed collision conclusion, retained-event success certificate or target source-hardness conclusion. The base profile is the genuine hypothesis of `src:profiles` used to prove its collision clause. This does not reintroduce a base profile as an extra premise of the separate standalone `src:near-full` theorem: that theorem consumes the proved local clause instead.

## Mathematical read-back

| Check | Evidence and result |
| --- | --- |
| Every choice of three distinct tails | `positions` is arbitrary and is used only through its embedding. There is no restriction that one position be the inactive last coordinate. |
| Head positions unchanged | `coordinate` sends a head index `r` to original position `r.val`. It sends tail slot `j` to original position `q₁+(positions j).val`. The tail's last allowed index maps to `q₁+s`, the last position of the original `q₁+s+1` word. |
| No coordinate collision | `coordinate_injective` handles all head/head, head/tail, tail/head and tail/tail cases. Head and tail ranges are disjoint; tail/tail equality uses `positions.injective`. Thus distinct selected addresses are genuinely distinct original addresses, even when their decoded values happen to agree. |
| Literal Gamma decoder | `word_eq_coordinate` proves pointwise equality with `threeTailWord`. The source is still `src.gamma.Label`, with unchanged `src.gamma.law`; no labels are quotiented or reweighted. |
| Only bounded-wise independence used | For each queried set `J` of at most eight selected coordinates, `original_gamma_eightwise` forms its image in the original word and applies `src.gamma.exactLaw` to that image. Its induced map is injective, so product marginal restriction gives the correct eight-wise law. The proof does not assume a product law on the entire decoded word. |
| No independence after event restriction | The eight-wise statement is on the original Gamma law. The event `Words` is passed separately to the current `V38Fin2Exact.exactboost`; no claim is made that the selected coordinates remain independent after retaining `Words`. |
| Original within-block weights | `fibers i={u | (i,u)∈Rows}` is measured under the original `muX` law. The full row rectangle on those fibers is proved equal to the arbitrary input `Rows`; there is no missing uniform block factor or renormalization. |
| Exact count and threshold | From `s=2^a` and `q₁+3=s+1`, all `q₁+3` blocks meet the exact-boost count `2^((a+1)-1)+1=s+1`. Their threshold is `2^(a+1)*rho=2*s*rho`. The retained original Gamma event has mass `>1/2>9/25`. The theorem therefore yields `d+(a+1)=(d+a)+1`, exactly the required callback cost. |
| Generated guards instantiated | `generated_three_tail_bound` uses the revised `scalar_parameters` at `b=4*k`: positive `rho` and `s*rho<=1/1000` imply the scale `2*s*rho<=1`. The actual width identity `q₁=s-2` gives the required count. The returned `H=d+k` and cap `2*s*rho(4*k)` match the frozen near-full interface without a proposition conversion or a different Gamma law. |

The code permits `d>=2`, which strengthens the manuscript's requested `d>=3` case. The broader generic helper is still an indexed source at order 8192; this packet's acceptance concerns the actual generated-source clause, not a separate full-product release.

## Independent replay and provenance

[FREEZE.json](FREEZE.json) pins the single proof source. [PROVIDERS.json](PROVIDERS.json) pins all six new private dependency providers, source and object, including the previously reviewed exact `ThreeTailBound` definition and generated profile guards. [SHARED_IMPORTS.json](SHARED_IMPORTS.json) pins eight immediate production imports. No private provider had a shadowing source.

The proof was copied to `replay/` and independently recompiled there. The six new provider sources/objects were copied to `providers/`; their original private paths are absent from the replay import path. Existing production/package objects were reused, rather than recompiling their whole source closure. [LEAN_PATH.json](LEAN_PATH.json) and [REPLAY.json](REPLAY.json) record the exact import order and output hashes.

The proof and independent [Audit.lean](replay/Audit.lean) both pass under pinned Lean 4.30.0 with `relaxedAutoImplicit=false`, zero warnings and zero errors. The audit checks all **20 local declarations** against only `propext`, `Classical.choice`, and `Quot.sound`. Its dependency traversal visits **19,890 declarations** and requires the arbitrary-coordinate injection, original-Gamma eight-wise proof, current exact boost and exact `ThreeTailBound` interface.

It excludes all three narrow special-tail paths:

- `V42GeneratedSourceProfiles.three_tail_cost`;
- `DeterministicIndexedMatrix.Sources.selectedGamma`;
- `Paper2.SourceProjectionDiagonal.collisionTailPosition`.

Thus the new theorem does not relabel the earlier two-active-plus-inactive result as an arbitrary-three statement. Source scanning found no `sorry`, `admit`, new axiom or opaque assumed conclusion. Only this worker's own `generated-tail-review/` directory was changed; no Git command, shared build or worker launch occurred.

## Source correspondence and admission boundary

[SOURCE_COMPARE.json](SOURCE_COMPARE.json) confirms exact text equality with the author attachment for the complete `src:profiles` statement and its final arbitrary-three-tail proof paragraph. The author attachment hash is `e9eb48925f087a64141c4b756ae3293856a87b353acae33f3fdc802b33f0f535`; the inspected current source hash is `ec8af5767eccc1184e7a1b5f88979ab0a7ee9be60d91be4e61ec80aa66861f78`. Current source anchors are lines 1705–1722 for the statement and 4058–4064 for the operative proof paragraph.

This closes the generated arbitrary-tail callback-provider boundary called out by the independent near-full review. The root must still connect this exact declaration to the admitted source-profile/near-full statement map, rename private imports appropriately, and run fresh production dependency/axiom gates. Concrete constructor joins, full-product counterparts, runtime and whole-paper release retain their own scopes. No mathematical gap was found in this generated ANY-three-tail clause.
