# Independent review of the V42 alternating public packet

## Decision

Accepted for the concrete alternating array construction, same printed-table
gap, fixed-gap literal-CNF reduction, and permitted numerical-estimator
consequences for all four stated conventions, relative to the existing explicit
external coloring-source contract and literal-CNF hardness boundary. No proof
or same-object defect was found in these scopes.

There is one source-map qualification: the new declarations linked to
`yao:finite-field-list` instantiate that lemma at
`n=2^b*(2^t*2^t)` and `r=4*(b+3*t)`. They do not themselves state the
standalone lemma for every `n,r≥1`. The generic standalone lemma should keep a
separate coverage row, with its generic bias/search/printer proof components
or a new all-parameter join. This qualification does not invalidate the
concrete array list or any final endpoint reviewed here.

## Frozen inputs and private replay

Every artifact hash recorded by `deterministic/PUBLIC_TRACE.json` matched
before replay. Its own SHA256 was
`85373d13f8e949b26e2478f81e560467ca7525cdb7ee005cc4aa7eaa90df7148`.
The exact three source files were copied into this review directory:

- `AlternatingV42.lean`: `0a5654f81be3450df5056c94448558333954c8ae3e2265649ce09c81a4f4fbe6`
- `AlternatingPublicV42.lean`: `32967c52f84643f62b786c6a1711436aab9da350c8288e025069c420d5d79015`
- `AlternatingAuditV42.lean`: `5bfe151a5526542402d0ec28605edd1456f73a845498b4e8f6626fa4a5686e34`

All three recompiled sequentially with Lean 4.30.0, private output objects,
and read-only shared dependency objects. The author's private `.olean`
directory was excluded from the review Lean path. `IndependentAudit.lean`
and `SameObjectReadback.lean` also compiled. Final logs are under `logs/`.

The independent audit requires exactly 61 declarations in
`CurrentAdditive.SmallBias.V42` and checks every declaration's transitive
axioms against exactly `propext`, `Classical.choice`, and `Quot.sound`.
It traverses seven public gap/final endpoints and requires the new lookup,
complete-address lift, concrete/public bound and selected-instance gap in
every closure. It excludes an expanded set of old lower bounds, old selected
cost/gap results, old source-decider correctness, and old final hardness
endpoints. All checks passed. The first attempts at the review-only audit
and read-back files had local syntax/name-resolution errors; their corrected
final versions compiled without changing any reviewed implementation file.

## Literal statement and source comparison

1. The concrete array law is uniform on all `R²` seed labels. Every decoded
   word has exactly the genuine `H*K` positions. Equal words keep separate
   labels. The bit-to-field and streaming-index bridges identify the same
   arrays used by the lower-bound matrix. No small-bias-after-conditioning
   claim is made or needed.
2. `concrete_matrix_yes_no` uses the original exact field/printer equations.
   Its YES result invokes the unchanged actual protocol. Its NO result invokes
   the new `V42.lower_bound_complete_addresses`, whose lookup dependency was
   independently reviewed previously and was replayed here.
3. `selectedInstance_costs` rewrites the selected executable modulus to the
   first successful public search result and uses the same serialized table
   on both truth values. Its threshold is exactly `2*b+4*t+2`, and its gap is
   exactly `2*t-8`. `source_instance_same` is definitional identity, not a
   cost-only equivalence.
4. The table contains every address tuple once, zero outside an edge and at
   unused edge indices, and the actual source's distinct-vertex edge
   embeddings. These are inherited unchanged entry and indexing definitions,
   not newly assumed semantic equalities.
5. `source_table_outputs` and `source_table_run_and_gap` use the actual
   source/clone/field/table machine. Its clock is
   `sourceTime + 2*sourceCode.length + 2 + renderer.clock`. The polynomial
   theorem bounds this complete clock in the original input length for fixed
   `t`, including transfers, field search and full table output.
6. The midpoint is the literal numerator `2*B+(2*t-8)`, representing
   `B+(2*t-8)/2`. The source-word/header machine prints that numerator with the
   same matrix word. The rational header length bound is
   `(20*t+101)*(entries+1)`. This discharges the numerical-comparison
   extraction premise; no residual comparison or printer oracle is present
   in the permitted final endpoints.
7. The endpoint parameter is the exact four-constructor `YaoMeasure` type:
   `dA`, `dB`, `dFree`, `yFree`. The existing two-bit comparison theorem is
   used on the same valid nonempty table. The error margin is strictly
   `2*(u+2)<gap`. Deterministic extraction starts from the original
   deterministic matrix-input machine and constructs its zero-tape wrapper.

## External and quantitative boundaries

`GLSourceDraft` is still an explicit record input. It supplies only the
external occurrence-source machine, its complete polynomial clock, the
balanced coloring completeness promise, and the strict measure-form
independent-set soundness promise. `ofDraft` derives the needed color
obstruction at the same edge arity before the checked clone step. The packet
does not assume a matrix lower bound, protocol impossibility or final class
separation in that record.

The literal-CNF specialization retains `G.L=EncodedCNF.Language`. The class
endpoints also retain `NPHard EncodedCNF.Language`, as authorized. No existence
of the source record or Cook--Levin theorem is asserted here. Running-time
degrees may depend on the fixed gap/`t`; no growing-error strict-alternation
claim is supplied.

## Final declaration map

All new names below have prefix `CurrentAdditive.SmallBias.V42`:

| Source label | Accepted new declarations |
| --- | --- |
| `prop:alternating-upper` | `concrete_matrix_yes_no` (YES component) |
| `yao:small-bias-escape` | `no_short_lookup_v42` and `lower_bound_complete_addresses` from the accepted base packet |
| `yao:array-list` | `concrete_array_pattern`, `public_array_pattern`, `public_array_field_bounds`, `public_array_label_shape`, together with actual physical field/renderer clocks |
| `yao:finite-field-list` | Same declarations certify the selected `H*K`, `4*(b+3*t)` instance only; keep the standalone all-`n,r` coverage separate |
| `def:alternating-table` | `source_instance_same`, `selectedInstance_costs`, `source_table_outputs`, `source_table_run_and_gap` |
| `yao:lift` | `concrete_matrix_yes_no`, `public_printed_matrix_yes_no`, `selectedInstance_gap`, `source_table_run_and_gap`, `source_table_time_polynomial` |
| `yao:source` | `selectedInstance_costs` and `literal_cnf_fixed_gap_reduction` consume the explicit external source and proved clone adapter; they do not establish external source existence |
| `yao:main` | `fixed_gap_reduction`, `literal_cnf_fixed_gap_reduction` |
| `yao:comparison` | Existing `V39RationalMidpoint.four_model_comparison`, consumed through `ValidYaoEstimator.matrix_law`; new `sourceDecider_decides` joins it to the current gap |
| `yao:bpp` | `source_decides`, `source_inP`, `permitted_randomized_np_subset_bpp`, `permitted_deterministic_p_equals_np`, `literal_cnf_permitted_randomized`, `literal_cnf_permitted_deterministic` |

Root-owned production import changes, full rebuild, source inventory, final
source lock and release receipts remain separate integration gates.
