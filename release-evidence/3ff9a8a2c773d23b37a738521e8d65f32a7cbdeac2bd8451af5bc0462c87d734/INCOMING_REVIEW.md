# Independent review of the v42 incoming-weight proof

The six frozen files pass this independent review as a **local, conditional proof segment**. The endpoint proves the literal strict bound on original incoming diagonal weight, `< 2*s*κ`, for every collection of copies. I found no mathematical or statement-fidelity defect in this segment. Numerical schedule discharge, its use at actual protocol stopping nodes, production integration, and the complete manuscript theorem remain separate work.

This review changed only `private-provenance-refs/de40867d2c3423ac8ed0b0c9c5f85641151dc0e69e17a0fa32334e81e1cc2bec/incoming-review`. It ran no Git command or shared build, launched no workers, and used one private compiler at a time.

## Objects and source checked

The stable review inputs are the five files in `../incoming/` and `../weighted-moment/V42WeightedMoment.lean`. Their agreed SHA-256 values are in [FREEZE.json](FREEZE.json). They were copied into [replay/](replay/) and independently recompiled there, in dependency order, without importing the author's private `.olean` files.

The author's attachment has SHA-256 `e9eb48925f087a64141c4b756ae3293856a87b353acae33f3fdc802b33f0f535`. The inspected current source has SHA-256 `1c7f0fedc92989087219c2773411a42f610503846c6cf1e2dea5ac18961684f7`. [SOURCE_COMPARE.json](SOURCE_COMPARE.json) records executable block comparisons:

- `res:incoming`: attachment lines 2131–2137; current source lines 2148–2154. The statement is byte-identical as decoded text.
- Its proof: attachment lines 4189–4254; current source lines 4230–4296. The only difference is the added `\phantomsection\label{proof:res:incoming}` hyperlink anchor.
- `lem:conditioning-moment`: attachment lines 4327–4341; current source lines 4372–4386. The statement is byte-identical as decoded text.

The final manuscript source lock remains the root's responsibility because authorized signposting and verification-paragraph work are concurrent. This review is anchored to the stable author attachment and the named blocks, rather than assuming that the whole current source hash will remain unchanged.

## Literal endpoint and all substantive premises

`CurrentAdditive.V42IncomingSharpBound.incoming_diagonal_mass_lt` concludes

```text
∑ i ∈ I₀, V39IncomingDensity.receipt (diagonalLaw src).toFiniteLaw w R i
  < 2*(s : ℝ)*κ
```

Its complete elaborated signature is in [Audit.compile.log](Audit.compile.log). The substantive premises are:

1. The actual indexed source `src` and complete independent stream record `streams`, at independence order 8192; the ordinary positive rational row laws and finite carriers; and positive natural `s`, `q₁`, `q₂`.
2. `w = 2^r`, `1 ≤ κ`, `1 ≤ a`, `2 ≤ d`, and `2^a = 2*s*κ*q₂`.
3. `x > 0`, `θ > 0`, and `w²*q₂*x ≤ 1`.
4. `TwoThresholdProfile (A src R₀)` at the original gamma and selector-coordinate laws, threshold `x`, and cost `d`.
5. The actual retained complete-label column event `Ystar` has original weight at least `θ/2`.
6. For every real `W ≥ 512*s*κ`, the explicit number
   `((2^14*W)^128) / (((255/256-1/2)*W)^256)` is at most `θ/4`.
7. The cap-one budget `V38Moments.exceptionCount (θ/4) 1 ≤ s*q₂`.
8. The same actual restricted matrix has communication cost `< d+a` on `R × Ystar`.

These premises contain no assumed incoming bound, assumed desired moment, preselected template section, assumed heavy-block family, or opaque record carrying the conclusion. Premises 6 and 7 are genuine numerical integration obligations, not yet discharged by this review. Premise 8 is the short remaining protocol needed for the source's contradiction argument; this segment does not construct that residual protocol.

## Adversarial checks

| Required property | Actual evidence and conclusion |
| --- | --- |
| Literal original receipt | `V39IncomingDensity.receipt` is `(1/256) * Pr_gamma,alpha[(i,inr(alpha,gamma)) ∈ R]`. `V39IndexedIncomingLocal.diagonal_receipt_eq_actual_mass` identifies it with precisely the diagonal part of the original two-tag input law, in complete-copy units. There is no omitted extra factor, protected-family split, or dyadic-grouping factor in the endpoint. |
| Fractions fixed before metadata | `d i` is `density` of the fixed row set `R`, zero outside `I₀`. It does not depend on the metadata or selector label. The theorem proves `0 ≤ d i ≤ 1` and the exact receipt identity before drawing flags. The contradiction gives `D₀ ≥ 512*s*κ`; summing `d i ≤ 1` gives `D₀ ≤ w`. |
| Weighted moment genuinely derived | `V42WeightedMoment.bounded_wise_moment_256` proves the desired 256th moment from boundedness, centering, fixed coefficients, and joint event-law equality with genuine independent whole-source draws. The comparison law is `ν.iid m`. `metadata_weighted_half_template_tail` constructs the joint event-law premise from `metadataStream.exactLaw` and disjoint singleton blocks, proves the exact mean `255/256`, and applies Markov's inequality. The final endpoint supplies `d` and derives the tail internally. |
| Complete-stream conditioning order | `complete_weighted_template_section` uses the actual product of the metadata, base and selector **complete-label** laws. It intersects `Ystar` with the good weighted-mass event and then applies `exists_complete_stream_section` to fix a complete metadata index and a complete base index. No decoded-word quotient or adaptive source change occurs. The selector section still has original ambient selector weight at least `θ/4`. |
| Original independent selector law | `incoming_fin_dwise` reindexes the flattened coordinates by a literal equivalence `Fin(w*q₂) ≃ Fin w × Fin q₂`. Its input is the unchanged `selectorStream` law. `selector_flatten_dwise` follows from the two exact source laws. The product-law conditioning identity is also available as `fixed_stream_flatten_dwise`; fixing complete independent metadata/base labels leaves this selector law unchanged before conditioning on the retained section. |
| Exact original fiber masses | `sum_fibreMass` proves `sum_alpha fibreMass = q₂ * original diagonal density`, using the uniform original alpha law. `retainedFibreMass` only sets a fiber to zero when it is outside `I₀` or its fixed metadata is not a template flag. `sum_retainedFibreMass` proves total retained fiber mass is exactly `q₂ * sum_i d_i*T_i`. Gamma weights are not renormalized or replaced. |
| Heavy fibers at `K₀*x` | `many_heavy_fibres` uses `K₀=2*s*κ*q₂`, threshold `t=K₀*x`, and the exact original fiber masses. Total retained fiber mass is at least `128*K₀`. The elementary upper bound is heavy count plus `w*q₂*t`. The proof weakens the source's loss `K₀/w` to `K₀`, valid since `w ≥ 1`, leaving heavy count at least `127*K₀ > K₀`. Thus this harmless proof variation preserves the source threshold and conclusion. |
| One exception set at cap one | Selection applies `conditioning_outside_exception` once to the chosen selector section, with `v=θ/4` and `τ=1`. Its set has size at most `s*q₂`. It is selected before the good family. At every later small projection outside this same set, the conditional law has the required error bound. There is no reuse of a witness from a different event. |
| Selected count and inequality direction | More than `K₀` heavy coordinates exist. Removing at most `s*q₂ ≤ K₀/2` leaves at least `K₀/2+1 = s*κ*q₂+1` coordinates. `Q.card` is exactly that number. Every selected coordinate lies outside the same exception set, is a template flag, and has original gamma mass at least `K₀*x`. The positive threshold prevents a zeroed-out or non-template fiber from being selected. |
| Same actual rows and matrix | `selected_diagonal_section_cost` maps `(flatAddress,gamma)` to `(originalCopy,inr(originalAlpha,gamma)) ∈ R` and each selector label to `(fixedMetadata,(fixedBase,selector)) ∈ Ystar`. `diagonal_section_entry` proves the matrix entry is literally `A(gamma,z_i,alpha)`, independent of its fixed bin. There is no auxiliary fixed-tail row insertion. Distinct flattened images are distinct actual row addresses. |
| Same actual communication cost | The existing rare-boost lower bound is transferred by `SourceProjection.restrictionD_map_le` to the exact `internal src streams R₀ activity ξ₀` appearing in the endpoint's short-cost premise. Its row threshold is `2^a*x=K₀*x`, its count is `2^(a-1)+1`, and the same original source profile is used. The code derives the required scale bound from `w²*q₂*x ≤ 1` and the contradiction's `D₀ ≤ w`. It obtains `d+a ≤ restrictionD` and contradicts the literal strict short-cost premise. |
| Quantifiers and exceptional cases | `I₀` is arbitrary, including empty; the proof needs no assigned-node property for its selected copies. Natural positivity is enforced by `NeZero` and `κ ≥ 1`; `w=2^r` supplies `w ≥ 1`. Positive section mass follows from `θ>0`, so all conditional laws are legitimate. The bound is strict, matching the source. |

The moment helper reviewed here covers half-orders at least three and the required order 128. It does **not** by itself formalize the source's general weighted-moment lemma at half-orders one and two or on arbitrary probability spaces. Separate general weighted-moment work owns that broader statement. This restriction creates no gap in this incoming proof.

## Independent compiler evidence

Every frozen source was compiled afresh in `replay/`, with the pinned Lean `4.30.0`, commit `d024af099ca4bf2c86f649261ebf59565dc8c622`. [REPLAY.json](REPLAY.json) records six exit-zero results and the private output hashes. [LEAN_PATH.json](LEAN_PATH.json) records the import roots. Only the private replay directory supplied the six new modules; existing production dependencies came from the root and package library caches. Their entire source closure was not rebuilt by this worker; the root must run its fresh production dependency build after integration.

The final independent [Audit.lean](replay/Audit.lean) checks the full endpoint type and eleven transitive axiom surfaces. All are exactly `propext`, `Classical.choice`, and `Quot.sound`. There are no new mathematical axioms, `sorry`, `admit`, or opaque assumed conclusions in the reviewed sources.

The six proof compilations produce three non-blocking lint warnings in `V42IncomingHeavyFibres.lean`: unused `← Finset.sum_ite`, unused `Bool.true_eq`, and an unused automatically included `NeZero s` instance in `sum_fibreMass`. They do not change elaborated premises or the proof. The first review audit attempt used an unsupported pretty-printer option; that review-only option was removed and the successful rerun is retained separately from [Audit.attempt-1.log](Audit.attempt-1.log).

## Acceptance boundary and handoff

Accept the frozen proof files for root integration, subject to the root's normal production import renaming, fresh build and axiom gates. No proof-source edit is requested by this review.

Before marking `res:incoming` complete for the manuscript, the root must check the exact application that supplies the actual source profile, the real-valued tail guard, the cap-one exception margin, the dyadic relation `2^a=2*s*κ*q₂`, and the remaining-depth bound for both kinds of actual stopping node. The parameter worker reports corresponding source schedule margins; this review has not certified their integrated application. The final manuscript lock, full common-interlace theorem, algorithms, reductions, runtime and ETH consequences are outside this local acceptance.
