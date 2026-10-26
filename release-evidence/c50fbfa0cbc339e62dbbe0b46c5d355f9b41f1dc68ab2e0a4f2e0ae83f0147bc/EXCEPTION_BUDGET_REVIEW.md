# Independent review: the literal exceptional-coordinate bound

2026-10-26. Reviewer `v42_proof_review`. **Accept for integration.**

Reviewed `exception-budget/V42ExceptionBudget.lean`, copied as
`ExceptionBudgetSnapshot.lean`, SHA256
`12abffc9652c35f08a01912f95da5f859ec0d846d3432f997e46a05805dd43f9`.
Independent private replay exited 0 with only `propext`, `Classical.choice`,
and `Quot.sound` for both public endpoints. See `exception-budget-replay.log`.
No `sorry`, `admit`, new axiom, or opaque desired-bound certificate is present.

Source anchor: v42 `eq:conditioning-size-bound`, using the definitions before
`det:conditioning`. The source explicitly quantifies `0 < v,tau <= 1` for
the final bound. These actual definitions were also read in `V38Moments`:

```text
epsilon(v,tau) = min(tau, 2^(-30) v^(1/256))
exceptionCount(v,tau) = 8 ceil_nat(2^20 epsilon(v,tau)^(-2) v^(-1/512))
```

All powers of the positive real inputs in the exported inequalities are real
powers, including the inverse square. The natural ceiling is retained exactly.

| Declaration | Decision and exact scope |
| --- | --- |
| private `scaled_epsilon_term` | Accept. For every positive real `v`, exactly simplifies the second branch to `2^80 v^(-5/512)`. The real exponents and integer power of 2 are reconciled under positive bases. |
| `exceptionCount_three_term_bound` | Accept. For all positive real `v,tau`, proves the first displayed source inequality: `exceptionCount <= 8 + 2^23 tau^(-2) v^(-1/512) + 2^83 v^(-5/512)`. It splits the actual minimum, bounds its contribution by the sum of the two nonnegative branch contributions, and charges the ceiling by `ceil(z) <= z+1`. |
| `exceptionCount_real_bound` | Accept. For every real `0 < v <= 1` and `0 < tau <= 1`, proves exactly `exceptionCount <= 2^84 tau^(-2) v^(-1/64)`. It compares negative powers in the correct direction for bases at most 1, uses that the common factor is at least 1, and absorbs `8+2^23+2^83` into `2^84`. |

There is no dyadic, rational, sufficiently-small, asymptotic, or pre-assumed
exception-budget restriction. The endpoints `v=1` and `tau=1` are included.
Zero and negative inputs are excluded exactly as in the source. This is a
definition-level arithmetic proof, so it does not depend on an imported
exceptional-coordinate existence theorem or an assumed output estimate.

Replay from the repository root:

```powershell
lake env lean -o private-provenance-refs/ca160e21bca332ec22c34f07a7694bc0aa9976a214209540c168dd0ea8211fe7/ExceptionBudgetSnapshot.olean private-provenance-refs/5859a246c842e26ae7234bdcb80e59aad7612caea81d185f7285db56040cd76c/ExceptionBudgetSnapshot.lean
```

This acceptance covers the new exact estimate against the available production
dependency objects. Root-owned production integration, fresh dependency builds
and source-bound gates remain separate. Production files and the manuscript
were read-only; no shared build, Git operation or subdelegation was performed.
