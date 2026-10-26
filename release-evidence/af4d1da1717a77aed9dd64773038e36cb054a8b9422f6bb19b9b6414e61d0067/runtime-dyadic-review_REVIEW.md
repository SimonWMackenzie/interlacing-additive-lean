# Independent V42RuntimeDyadic admission review

Accepted; no defect found in the two theorems or the intervening exponent
definition. The reviewed source SHA256 is
`1d53235a3749ed0335da3dec15f6cadb489927b54722605be41fefcb0727508d`.
The exact source was replayed with Lean 4.30.0 into this private directory,
excluding the author's `runtime-followup` object directory. No production
file, shared build, Git state, or other worker's file was changed.

`base_le_dyadic` uses the actual new selection
`N=2^(4*selected(k₀,g))` and the actual runtime base
`N+encode(g).length+2`. The public selector proves `g.vertices≤N`; the
bounded-degree hypothesis proves `edges≤ΔN`. The graph codec's proved bound
`encode(g).length≤vertices+2+edges*(4*vertices+4)`, together with `N≥2`,
then gives `base≤(8Δ+6)N²`. No old selected-base theorem, graph-size
certificate, or runtime conclusion is assumed.

`dyadic_outputs_with_tail` calls the actual new `outputs_with_tail` on the
same graph, selected exponent, width proof, tail input and output word `Y`.
It converts both the complete machine clock and `Y.length` from a power of
that actual base to a power of the same `N`. The reused
`V40GraphConstructorInputBounds.dyadic_clock_bound` is purely scalar:
`B≤cN²` and `time≤B^(C*A^K)` imply
`time≤N^(((c+2)C+1040)*A^K)` for `N≥2`. Its proof uses only power
monotonicity and `c≤N^c`, so its reuse does not import an old schedule or
machine statement. The new exponent substitutes exactly `c=8Δ+6`; the
amplification `A` and round count `K` are unchanged.

The explicit tail-execution premise is appropriate for this generic
composition theorem. Its actual deterministic ETH consumer supplies it
with `(tail E).outputs` on the same retained envelope and rewrites by the
proved new request identity before applying this theorem; it is not a
remaining run premise of that endpoint.

`Audit.lean` checks all three new declarations against only `propext`,
`Classical.choice`, and `Quot.sound`. It checks that the output theorem's
dependency graph includes the actual V42 base estimate, actual V42 runtime,
graph encoding bound and generic scalar conversion, while excluding the old
selected-base estimate. The root still owns production admission and its
fresh dependency build.
