import EthInapproximability.CurrentPaper.MatrixWeightedArithmetic
import EthInapproximability.CurrentPaper.MatrixTableLookup

/-!
# Charged source-table read for a protected cell

Once the weighted row and column labels have been decoded into raw Stage--4
ordinals, the existing fixed lookup machine reads the correct source bit.
The labels and their unary ordinal words are explicit inputs at this stage;
their production is not charged by this theorem.
-/

namespace EthInapproximability.CurrentPaper.MatrixWeightedRawRead

open Construction MatrixStage4Codes MatrixWeightedTable WeightedDuplication

variable {rx cy : ℕ}

def sourceRow (s L nv nb rx : ℕ) (order : ItemOrder nv nb)
    (r : ProtectedRows s L nv nb (Fin rx)) : ℕ :=
  (rowCode s L nv nb rx order
    (rowForget (fun t : TemplateSupport s L => Sum.inl t.down)
      (fun v => Sum.inr (Sum.inl v)) (fun b => Sum.inr (Sum.inr b)) r)).val

def sourceColumn (a s q cy : ℕ)
    (c : ProtectedColumns a s q (Fin cy)) : ℕ :=
  (rawColumnCode a s q cy (columnForget diagonal c)).val

theorem source_lookup (R : Fin rx → Fin cy → Bool)
    (a s q L nv nb : ℕ) (hs : 0 < s)
    (family : SecondFamily a q L (Fin rx)) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (c : ProtectedColumns a s q (Fin cy))
    (r : ProtectedRows s L nv nb (Fin rx)) :
    (rawTable R a s q L nv nb hs family order vectors cap)[
      sourceRow s L nv nb rx order r * cols a s q cy +
      sourceColumn a s q cy c]?.getD false =
      protectedMatrix R a s q L nv nb hs family order vectors cap c r := by
  have h := rawTable_entry R a s q L nv nb hs family order vectors cap
    (rowForget (fun t : TemplateSupport s L => Sum.inl t.down)
      (fun v => Sum.inr (Sum.inl v)) (fun b => Sum.inr (Sum.inr b)) r)
    (columnForget diagonal c)
  simpa [sourceRow, sourceColumn, protectedMatrix,
    WeightedDuplication.transposedMatrix, WeightedDuplication.matrix] using
    congrArg (fun o => o.getD false) h

/-- A literal fixed-stack run returns the actual protected bit from the
explicit raw `B` table, preserving the table and the supplied coordinates. -/
theorem raw_read_run (R : Fin rx → Fin cy → Bool)
    (a s q L nv nb : ℕ) (hs : 0 < s)
    (family : SecondFamily a q L (Fin rx)) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (c : ProtectedColumns a s q (Fin cy))
    (r : ProtectedRows s L nv nb (Fin rx)) :
    ∃ t ≤ 32 * (sourceRow s L nv nb rx order r + cols a s q cy +
      sourceColumn a s q cy c +
      (rawTable R a s q L nv nb hs family order vectors cap).length + 1) ^ 2,
      MatrixTableLookup.run t
        (MatrixTableLookup.cfg (some MatrixTableLookup.start)
          MatrixTableLookup.initial
          (List.replicate (sourceRow s L nv nb rx order r) true)
          (List.replicate (cols a s q cy) true)
          (List.replicate (sourceColumn a s q cy c) true) []
          (rawTable R a s q L nv nb hs family order vectors cap) []) =
      MatrixTableLookup.cfg none MatrixTableLookup.initial
        (List.replicate (sourceRow s L nv nb rx order r) true)
        (List.replicate (cols a s q cy) true)
        (List.replicate (sourceColumn a s q cy c) true) []
        (rawTable R a s q L nv nb hs family order vectors cap)
        [protectedMatrix R a s q L nv nb hs family order vectors cap c r] := by
  obtain ⟨t, ht, he⟩ := MatrixTableLookup.lookup_run
    (sourceRow s L nv nb rx order r) (cols a s q cy)
    (sourceColumn a s q cy c)
    (rawTable R a s q L nv nb hs family order vectors cap) []
  refine ⟨t, ht, ?_⟩
  simpa [source_lookup R a s q L nv nb hs family order vectors cap c r] using he

end EthInapproximability.CurrentPaper.MatrixWeightedRawRead
