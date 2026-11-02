import EthInapproximability.CurrentPaper.MatrixWeightedEnumeration

/-!
# Row-major table of the current weighted protected matrix

This instantiates the four row-support and two column-support enumerators with
the actual `Construction.protectedMatrix`, not a generic replacement matrix.
The raw source table, graph order, sampler family, and scalar parameters remain
explicit inputs.  Machine production of those inputs and operational runtime
are separate obligations.
-/

namespace EthInapproximability.CurrentPaper.MatrixWeightedTable

open Construction MatrixStage4Codes MatrixWeightedEnumeration MatrixMaterialization

variable {rx cy : ℕ}

def rawRowCode (s L nv nb rx : ℕ) (order : ItemOrder nv nb) :
    RawRows s L nv nb (Fin rx) ≃ Fin (Fintype.card (RawRows s L nv nb (Fin rx))) :=
  (rowCode s L nv nb rx order).trans (finCongr (by simp [rows]; ring))

def templateCode (s L : ℕ) :
    TemplateSupport s L ≃ Fin (Fintype.card (TemplateSupport s L)) :=
  Equiv.ulift.trans (finProdFinEquiv.trans (finCongr (by simp [TemplateSupport])))

def vertexCode (nv rx : ℕ) :
    VertexRows nv (Fin rx) ≃ Fin (Fintype.card (VertexRows nv (Fin rx))) :=
  finProdFinEquiv.trans (finCongr (by simp [VertexRows]))

def auxiliaryCode (nb rx : ℕ) :
    AuxiliaryRows nb (Fin rx) ≃ Fin (Fintype.card (AuxiliaryRows nb (Fin rx))) :=
  finProdFinEquiv.trans (finCongr (by simp [AuxiliaryRows]))

def rawColumnCode' (a s q cy : ℕ) :
    RawColumns a s q (Fin cy) ≃ Fin (Fintype.card (RawColumns a s q (Fin cy))) :=
  (rawColumnCode a s q cy).trans (finCongr (by simp [cols]))

def diagonalCode (a s q cy : ℕ) :
    SecondRows a s q (Fin cy) ≃ Fin (Fintype.card (SecondRows a s q (Fin cy))) :=
  (secondRowCode a s q cy).trans (finCongr (by simp [SecondRows, FirstColumns]))

/-- Concrete row-major table, with the manuscript's final transpose built in. -/
def table (R : Fin rx → Fin cy → Bool) (a s q L nv nb : ℕ)
    (hs : 0 < s) (family : SecondFamily a q L (Fin rx))
    (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s) : List Bool :=
  rowMajor (entry
    (rawMatrix R a s q L nv nb hs family order vectors cap)
    (fun r : TemplateSupport s L => Sum.inl r.down)
    (fun r => Sum.inr (Sum.inl r)) (fun r => Sum.inr (Sum.inr r))
    diagonal (uniformCopies (Y := Fin cy) a s q)
    (rawRowCode s L nv nb rx order) (templateCode s L)
    (vertexCode nv rx) (auxiliaryCode nb rx)
    (rawColumnCode' a s q cy) (diagonalCode a s q cy))

theorem table_entry (R : Fin rx → Fin cy → Bool) (a s q L nv nb : ℕ)
    (hs : 0 < s) (family : SecondFamily a q L (Fin rx))
    (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (i : Fin (Fintype.card (ProtectedColumns a s q (Fin cy))))
    (j : Fin (Fintype.card (ProtectedRows s L nv nb (Fin rx)))) :
    (table R a s q L nv nb hs family order vectors cap)[
      i.val * Fintype.card (ProtectedRows s L nv nb (Fin rx)) + j.val]? =
      some (protectedMatrix R a s q L nv nb hs family order vectors cap
        (decodeRow (rawColumnCode' a s q cy) (diagonalCode a s q cy)
          (uniformCopies (Y := Fin cy) a s q) i)
        (decodeColumn (rawRowCode s L nv nb rx order) (templateCode s L)
          (vertexCode nv rx) (auxiliaryCode nb rx) j)) := by
  rw [table, rowMajor_entry]
  rfl

end EthInapproximability.CurrentPaper.MatrixWeightedTable
