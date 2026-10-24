# Interlacing and additive inapproximability: Lean companion

Companion to *Interlacing and Additive Inapproximability of Deterministic
Communication Complexity*, by Serge Gaspers, Tao Zixu He, and Simon Mackenzie.

## Release status

**The public code release is being prepared.** This repository currently
provides its status, not a downloadable or independently reproducible proof
package. Correspondence with manuscript v42 has not yet been checked.

The earlier local development has a completion record dated 22 October 2026.
That record covers a specific v40 source snapshot, identified by SHA-256
`8cfdd735e5703682f98c840df96397dea74ef2795716f7bdddb3b7e562e64cb0`.
It records checked proofs for the deterministic fixed-gap and growing-error
constructions, the randomized growing-error result, and the strictly
alternating construction, relative to explicit external hardness interfaces.
This is a report of the earlier verification, not a verification of v42.

The external boundaries include the cited Dinur and Bogdanov--Obata--Trevisan
reductions, the Guruswami--Lee source and its CNF interpretation, and the
NP-hardness or deterministic/randomized ETH assumptions used by each result.
The adopted source interfaces still require confirmation against the cited
external theorems. The recorded theorem-dependency audit permits Lean's
standard `propext`, `Classical.choice`, and `Quot.sound` axioms.

Before the code release, we will provide the exact source and dependency
versions, build instructions checked in a fresh checkout, an assumption audit,
and a statement-to-Lean correspondence identifying the covered manuscript.
The [machine-readable status](release-status.json) keeps these unfinished
steps explicit.

The independent Beyond the Library formalization of the corrected
Mackenzie--Saffidine direct-sum result is a separate development; its
[public proof inspector](https://beyondthelibrary.github.io/formal_archive/p/Refuting/)
provides the corresponding statements and proofs.

