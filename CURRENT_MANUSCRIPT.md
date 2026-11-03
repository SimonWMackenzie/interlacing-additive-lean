# Lean companion: deterministic communication complexity

This repository accompanies *NP-Hardness and Additive Inapproximability of
Deterministic Communication Complexity*, by Serge Gaspers, Tao Zixu He and
Simon Mackenzie.

Start with the [interactive paper and Lean proof inspector](https://simonwmackenzie.github.io/interlacing-additive-lean/inspector/).
It connects the paper's statements to checked Lean declarations, definitions,
proofs and hypotheses. It presents recorded verification; it does not run Lean
in the browser.

- [Current manuscript PDF](manuscript-v44/output/INTERLACING_AND_ADDITIVE_INAPPROXIMABILITY_v44.pdf)
- [LaTeX source](manuscript-v44/source/main.tex) and [bibliography](manuscript-v44/source/references.bib)
- [Statement-to-Lean correspondence](manuscript-v44/INSPECTOR_STATEMENTS.json)
- [Manuscript correspondence review](manuscript-v44/CORRESPONDENCE_REBINDING.json) and [source identities](manuscript-v44/SOURCE_LOCK.json)
- [Build instructions](BUILD.md), [checked proof-source manifest](SOURCE_MANIFEST.json), and [recorded proof verification](release-status.json)

The formalization covers the unrestricted and strictly alternating
constructions and the implications from communication-cost estimation to
3-SAT algorithms. Cited source reductions remain explicit hypotheses.

The current manuscript is v44. Its editorial changes and figure layouts were
checked against the accepted proof release; no Lean declarations or proof
statuses changed. The proof archive is pinned to commit
`fb9e87da52d95ba56e20b4ebb5fb4c8217f93a65`. Existing build and audit records
describe that checked code. The v43 source and its evidence are retained for
reproducibility; they are not the current PDF.

Run `python verify_release.py` to check the accepted proof package's recorded
identities. [BUILD.md](BUILD.md) distinguishes the canonical checked build
from an optional cold replay. The effective and raw audits permit only
`propext`, `Classical.choice` and `Quot.sound` in the checked proof closure.

The separate Beyond the Library formalization of the corrected
Mackenzie–Saffidine direct-sum result has its own
[public inspector](https://beyondthelibrary.github.io/formal_archive/p/Refuting/).
Original project notices and dependency licenses are retained.
