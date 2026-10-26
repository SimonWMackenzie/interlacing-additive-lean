# Independent review of the v42 source-facing packet

**PASS for the frozen packet's stated scope. No actionable correctness or statement-fidelity defect found.** The projected-restriction observation and Kraft count are covered in full. The parameter theorem covers the scalar recipe and its dyadic input constraints; the effective common cutoff and the cross-referenced hardness theorems remain at their separate owners, as the packet explicitly records.

## Frozen inputs and independent replay

Author module: `V42SourceFacing.lean`, SHA256 `AF1ED7A000DD7FA12A8F436915C61597B3C4C345D1681AF1A08D558D3506E1BB`.
Private dependency: `V42Schedule.lean`, SHA256 `8EC1AFE59D8B716EF5D2D804B8C6DC334529B1508AAA13CA9FFD3498999944B4`.
Frozen v42 main source at initial review: SHA256 `1C7F0FEDC92989087219C2773411A42F610503846C6CF1E2DEA5AC18961684F7`.
Final live main-source SHA256: `EC8AF5767ECCC1184E7A1B5F88979AB0A7EE9BE60D91BE4E61EC80AA66861F78`.

The complete main-source hash matched at the initial check. During the final check the root made the user-requested formal-verification paragraph and bibliography-inspector update, so the whole-file hash changed. Both copied Lean source hashes and all three exact source-block hashes still match the frozen author manifest. This review remains bound to those unchanged target blocks; it makes no separate audit claim about the prose changes elsewhere. `HASH_CHECKS_INITIAL.json`, `HASH_CHECKS_FINAL.json` and `verify_packet.py` record the independent checks.

Copied only the two Lean sources to `replay/`, excluded both author private directories and their objects from `LEAN_PATH`, then compiled `V42Schedule`, `V42SourceFacing` and reviewer-owned `V42SourceFacingIndependentReadback` sequentially using the pinned Lean 4.30.0 binary. All final compilations exited zero. The seven author roots and two independent source-shaped consumer theorems print only `propext`, `Classical.choice`, `Quot.sound`.

## Literal read-back

### Arbitrary weighted-list restrictions (`obs:representatives`, main.tex 1181–1195)

The source's label set is the actual carrier `L`; `K : Set L` retains its original indices and weights, even when distinct labels decode to the same tuple. Selection `e : Fin l -> Fin q` is injective, so it represents an arbitrary set of distinct selected blocks. `selectedRows e U` is exactly the original retained row set within those blocks, relabelled by the selection.

The theorem constructs a map from every tuple in the projected image into the original retained label subtype `K`. Both that map and the selected-row map are injective. Its matrix-entry equation uses the same chosen label for every retained row; there is no separate completion chosen for each entry. The actual projected matrix has communication cost at most the original retained matrix, with the direction needed to transfer every lower bound back to the original restriction.

Per-block row masses are measured with the original base row law `muX` on exactly the same retained base rows. Column mass is measured with the ambient product law on the actual projected tuple image. The original label law is never replaced by a law on representatives or by a conditional independent law. The only product-law hypothesis in the generic theorem is an ambient projection pushforward; `dwise_project_pushes` derives it from the exact original D-wise law whenever `l <= D`, and `projected_weight_full_product` proves the full-product case. These are the source's precise qualifications.

The reviewer independently compiled `weighted_list_consumer` on arbitrary finite positive rational row/column/label laws, arbitrary retained `U,K`, arbitrary decoder and arbitrary injective block selection. It obtains both the cost inequality and the original-law mass inequality directly. Empty retained sets and zero selected coordinates are allowed; no hidden nonempty-restriction or singleton-mass premise appears.

### Kraft count (`lem:kraft-count`, main.tex 1731–1738)

The theorem ranges over an arbitrary finite index type and arbitrary actual finite binary paths with the true prefix-free property. It assumes `q=2^r`, every depth at most `r`, natural object and marked counts, `z_v <= h_v`, and the source's strict total excess. The source counts are integers; nonnegativity is supplied by their natural-number type.

It derives the Kraft capacity sum from the actual prefix-free paths, rather than assuming a capacity certificate or an overloaded node. It finds one node and proves the overload and both source cases for that same node. When its capacity is at least two, the proof explicitly establishes its evenness; the capacity-one branch returns either at least two objects or one object with one mark. The empty frontier is included and cannot satisfy the strict total excess.

`capacity_real` identifies the natural capacity `2^(r-depth)` with `q/2^depth` in the reals under exactly the depth guard. The reviewer independently compiled `kraft_real_readback`, obtaining the complete source conclusion in real capacity notation while retaining natural object counts. It does not incorrectly extend the half-capacity-plus-one conclusion to arbitrary real object counts.

### Amplification recipe (`def:amplification-parameters`, main.tex 1349–1369)

The exponents parameterize the source powers as `s=2^k`, `rho=2^-b` and a dyadic threshold `s0=2^k0`. From `n<=2^b`, `k0<=k` and `4k<=b`, the theorem derives the three initial inequalities and all eight displayed definitions: `q1=s-2`, `q2=s^2/rho`, `w=s^8`, `Q=s^24`, `x=rho^8`, `eta=s^-2`, `theta=(512Q)^-1`, `deltaU=eta/(16w)`. The definitions are proved by exact rational/power identities, not supplied as a desired recipe certificate.

The scalar wrapper deliberately does not claim that every small exponent is an admissible amplifier or prove the referenced hardness results. In particular, its natural subtraction `s-2` is the source's ordinary subtraction on the actual common-cutoff range; the separately owned common-cutoff construction has exponent at least 200. Keep that existing owner link when admitting the scalar wrapper. No author edit is required for its declared scalar-definition scope.

## Disposition

The frozen packet can be admitted after the root's production import/build and normal source/status gates. This independent review does not run those shared gates, choose an effective cutoff anew, or certify unrelated amplification/hardness statements. No production file, source manuscript, Git state or shared build was changed, and no subagent was used.

