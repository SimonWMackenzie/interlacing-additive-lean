import Paper2.SrcD
import Paper2.SrcF

/-! Unit 3, segment (1): the three source arms compute the SOURCE CASE of
`RecursiveEntries.request` (level `k+1 → k`; `eq:recursive-entry` with
`eq:raw-source`). For a level-`k+1` pair `(x, y)` whose requested raw row is
a source row `.inr (i, u)`, the request is `(u, sourceColumn activity i
(forgetTag (ξ k) (x y.1).2))`; the arms' two output cells hold exactly its
encodings (unrestricted: `SrcU.srcU_run`; diagonal: `SrcD.srcD_run`; fixed
tail at the canonical widths and canonical default tails:
`SrcF.fixed_source_value` + `SrcF.srcF_run`). -/

namespace Paper2.SrcReq

open RecursiveEntries SourceMatrix

theorem request_source {X₀ Y₀ I : Type} {s q₁ q₂ w Q : ℕ} [NeZero s]
    (activity : I → Fin q₂ → Option (Fin s))
    (ξ : Tails X₀ Y₀ I s q₁ q₂ w Q) (k : ℕ)
    (x : Row X₀ Y₀ I s q₁ q₂ w Q (k + 1))
    (y : Column X₀ Y₀ I s q₁ q₂ w Q (k + 1))
    (i : I) (uu : Row X₀ Y₀ I s q₁ q₂ w Q k)
    (hraw : y.2 (x y.1).1 = .inr (i, uu)) :
    request activity ξ k x y = (uu, sourceColumn activity i (forgetTag (ξ k) (x y.1).2)) := by
  unfold request
  rw [hraw]
  rfl

#print axioms request_source

end Paper2.SrcReq
