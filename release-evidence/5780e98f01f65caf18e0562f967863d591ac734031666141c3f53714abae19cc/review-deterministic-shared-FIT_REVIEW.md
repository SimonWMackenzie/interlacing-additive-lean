# Independent resource-fit review

Accepted: frozen `V43ResourceFit.lean`, SHA256
`3EDC07026331BE48D0A0E1E0A174E4D1014BB57DC0B94BC06CB288BE10A63C7F`.
Its independent private replay passed with exit zero. All three printed main
theorems (`actual_source_resources`, `actual_tapes_fit`, and
`budget_manuscript_polynomial`) use exactly `propext`, `Classical.choice`,
and `Quot.sound`. No proof hole, new axiom, or runtime-conclusion certificate
occurs in the frozen source.

The source imports the frozen parametric source/carrier components and
`V43TimeTradeoff.SourceBounds`, source SHA256
`646AFB1B56B0D389C4F4AE9EA9EF1B87061F70F084DC1776D153488414894CEE`.
The replay uses copied private source/object dependencies and existing
repository imports; it is not a cold dependency replay.

The mathematical review confirms the following exact boundaries.

- One source-only exponent bounds the actual sampler precision times its
  reserved block count, the actual sampled table's entries, and the actual
  raw table printer's charged clock. The source graph size is paid in the
  original encoded formula length. This is the same graph and round count
  as the caller, not a nominal size family.
- `actual_tapes_fit` first bounds the literal sampler bit requirement. For
  every possible sampled bit block it then bounds the estimator's prescribed
  tape length using the actual printed midpoint request's length. It does
  not assume the estimator tape is small only on a successful sample.
- The chosen resource exponent may depend on the fixed estimator's tape
  polynomial. It is fixed before the input and random bits. This does not
  change the manuscript's construction-size constant: the estimator-dependent
  resource is absorbed as a fixed polynomial overhead in that size.
- `budget_manuscript_polynomial` proves
  `budget(E,S,Phi) <= randomizedSize(C0,N,gap(N))^(3*E)` for each `C0 >= 1`,
  above the explicit sparse encoding cutoff `N >= 28*cs+9`. Thus the total
  resource bound is ultimately a polynomial in the original-variable size
  expression, rather than merely a polynomial in a graph or table surrogate.
- The remaining premises are the explicit upstream Dinur/BOT records and
  the mathematical source admissibility tests. These tests contain no clock
  conclusion or supplied algorithm. They must still be produced for the
  concrete source by an endpoint consumer; this component alone is not an
  all-input algorithm or a probability theorem.

The proof does not assume a constructor run, whole-program clock, SAT
algorithm, ETH statement, or successful outcome. The raw printer's resource
bound is read from the existing proved physical theorem. The only runtime
obligations not covered by this fit component are the complete carrier,
schedule, copying, splitting and caller clock absorption; those are separate
modules still under review.

See `ResourceFit-replay.log` and `FIT_RECEIPT.json`. No production files,
shared builds or Git operations were performed by this reviewer.
