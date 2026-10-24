import EthInapproximability.CurrentPaper.MatrixWeightedNumberingAgreement
import EthInapproximability.CurrentPaper.MatrixWeightedOrderWriter

/-!
Source: current-paper v8 Section 5 prescribed numbering and Appendix B
row-major materialization (CP-EFFECTIVE). The physical copy-major raw-row
order and the Iteration type-first order are related by explicit finite
permutations, not asserted identical. This module proves finite semantics;
it does not assign a machine cost to the permutations.
-/

namespace EthInapproximability.CurrentPaper.MatrixWeightedOrdinalConjugacy

open Construction WeightedDuplication
open MatrixWeightedTable MatrixWeightedNumberingAgreement
open MatrixWeightedArithmetic MatrixTableInterlaceWeightedNumbering

noncomputable section

set_option maxHeartbeats 1000000

def ordinalPermutation {Z : Type} [Fintype Z]
    (physical target : Iteration.Numbering Z) :
    Fin (Fintype.card Z) ≃ Fin target.size :=
  (finCongr physical.card_eq).trans (physical.equiv.trans target.equiv.symm)

theorem ordinalPermutation_decodes {Z : Type} [Fintype Z]
    (physical target : Iteration.Numbering Z)
    (i : Fin (Fintype.card Z)) :
    target.equiv (ordinalPermutation physical target i) =
      physical.equiv (i.cast physical.card_eq) := by
  simp [ordinalPermutation]

variable {X T V B Ω Δ : Type}
variable [Fintype X] [Fintype T] [Fintype V] [Fintype B]
variable [Fintype Ω] [Fintype Δ]

def physicalRowNumbering
    (eΩ : Ω ≃ Fin (Fintype.card Ω))
    (eΔ : Δ ≃ Fin (Fintype.card Δ)) (S : ℕ) :
    Iteration.Numbering (Columns Ω Δ S) :=
  columnNumbering eΩ eΔ S

def physicalColumnNumbering
    (eX : X ≃ Fin (Fintype.card X))
    (eT : T ≃ Fin (Fintype.card T))
    (eV : V ≃ Fin (Fintype.card V))
    (eB : B ≃ Fin (Fintype.card B)) :
    Iteration.Numbering (Rows X T V B) :=
  rowNumbering eX eT eV eB

theorem physical_row_decoder
    (eΩ : Ω ≃ Fin (Fintype.card Ω))
    (eΔ : Δ ≃ Fin (Fintype.card Δ)) (S : ℕ)
    (target : Iteration.Numbering (Columns Ω Δ S))
    (i : Fin (Fintype.card (Columns Ω Δ S))) :
    target.equiv
      (ordinalPermutation (physicalRowNumbering eΩ eΔ S) target i) =
        typedColumn eΩ eΔ S i := by
  rw [ordinalPermutation_decodes]
  exact (typed_column_eq_numbering eΩ eΔ S i).symm

theorem physical_column_decoder
    (eX : X ≃ Fin (Fintype.card X))
    (eT : T ≃ Fin (Fintype.card T))
    (eV : V ≃ Fin (Fintype.card V))
    (eB : B ≃ Fin (Fintype.card B))
    (target : Iteration.Numbering (Rows X T V B))
    (j : Fin (Fintype.card (Rows X T V B))) :
    target.equiv
      (ordinalPermutation (physicalColumnNumbering eX eT eV eB) target j) =
        typedRow eX eT eV eB j := by
  rw [ordinalPermutation_decodes]
  exact (typed_row_eq_numbering eX eT eV eB j).symm

theorem arithmetic_table_entry_conjugacy
    (H : X → Ω → Bool) (iT : T → X) (iV : V → X)
    (iB : B → X) (iD : Δ → Ω) (S : ℕ)
    (eX : X ≃ Fin (Fintype.card X))
    (eT : T ≃ Fin (Fintype.card T))
    (eV : V ≃ Fin (Fintype.card V))
    (eB : B ≃ Fin (Fintype.card B))
    (eΩ : Ω ≃ Fin (Fintype.card Ω))
    (eΔ : Δ ≃ Fin (Fintype.card Δ))
    (targetRows : Iteration.Numbering (Columns Ω Δ S))
    (targetColumns : Iteration.Numbering (Rows X T V B))
    (i : Fin (Fintype.card (Columns Ω Δ S)))
    (j : Fin (Fintype.card (Rows X T V B))) :
    (MatrixWeightedArithmetic.table H iT iV iB iD S
      eX eT eV eB eΩ eΔ)[
        i.val * Fintype.card (Rows X T V B) + j.val]? =
      some (transposedMatrix H iT iV iB iD S
        (targetRows.equiv
          (ordinalPermutation (physicalRowNumbering eΩ eΔ S) targetRows i))
        (targetColumns.equiv
          (ordinalPermutation
            (physicalColumnNumbering eX eT eV eB) targetColumns j))) := by
  rw [MatrixWeightedArithmetic.table_entry]
  rw [physical_row_decoder, physical_column_decoder]

theorem protectedWord_entry_conjugacy {rx cy : ℕ}
    (R : Fin rx → Fin cy → Bool) (a s q L nv nb : ℕ)
    (hs : 0 < s) (family : Construction.SecondFamily a q L (Fin rx))
    (order : Construction.ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (Construction.activeItems vectors α).card ≤ s)
    (targetRows : Iteration.Numbering
      (Construction.ProtectedColumns a s q (Fin cy)))
    (targetColumns : Iteration.Numbering
      (Construction.ProtectedRows s L nv nb (Fin rx)))
    (x : Fin (Fintype.card (Construction.ProtectedColumns a s q (Fin cy))))
    (z : Fin (Fintype.card (Construction.ProtectedRows s L nv nb (Fin rx)))) :
    (MatrixWeightedOrderWriter.protectedWord R a s q L nv nb hs family
      order vectors cap)[x.val *
      Fintype.card (Construction.ProtectedRows s L nv nb (Fin rx)) + z.val]? =
    some (Construction.protectedMatrix R a s q L nv nb hs family order vectors cap
      (targetRows.equiv
        (ordinalPermutation
          (physicalRowNumbering
            (MatrixWeightedTable.rawColumnCode' a s q cy)
            (MatrixWeightedTable.diagonalCode a s q cy)
            (Construction.uniformCopies (Y := Fin cy) a s q)) targetRows x))
      (targetColumns.equiv
        (ordinalPermutation
          (physicalColumnNumbering
            (MatrixWeightedTable.rawRowCode s L nv nb rx order)
            (MatrixWeightedTable.templateCode s L)
            (MatrixWeightedTable.vertexCode nv rx)
            (MatrixWeightedTable.auxiliaryCode nb rx)) targetColumns z))) := by
  exact arithmetic_table_entry_conjugacy
    (Construction.rawMatrix R a s q L nv nb hs family order vectors cap)
    (fun r : Construction.TemplateSupport s L => Sum.inl r.down)
    (fun r => Sum.inr (Sum.inl r))
    (fun r => Sum.inr (Sum.inr r))
    Construction.diagonal (Construction.uniformCopies (Y := Fin cy) a s q)
    (MatrixWeightedTable.rawRowCode s L nv nb rx order)
    (MatrixWeightedTable.templateCode s L)
    (MatrixWeightedTable.vertexCode nv rx)
    (MatrixWeightedTable.auxiliaryCode nb rx)
    (MatrixWeightedTable.rawColumnCode' a s q cy)
    (MatrixWeightedTable.diagonalCode a s q cy)
    targetRows targetColumns x z

section ActualIteration

open EthInapproximability.ParameterizedNP.GuardedSourceGraph

attribute [local irreducible] Iteration.nRowNumbering Iteration.nColNumbering

variable {VG EG : Type} [Fintype VG] [DecidableEq VG]
  [Fintype EG] [DecidableEq EG]
variable (G : EndpointGraph VG EG) (sourceConstant b y level : ℕ)
  (M : Iteration.Matrix)

private abbrev stageA := Iteration.a G sourceConstant b y level M
private abbrev stageS := Iteration.s G sourceConstant b y level M
private abbrev stageQ := Iteration.q₂ G sourceConstant b y level M
private abbrev stageL := Iteration.labels G sourceConstant b y level M
private abbrev stageNV := GraphVectors.vertexCount VG (stageS G sourceConstant b y level M)
private abbrev stageNB := GraphVectors.auxiliaryCount (stageS G sourceConstant b y level M)

def physicalProtectedWord : List Bool :=
  MatrixWeightedOrderWriter.protectedWord M.entry
    (stageA G sourceConstant b y level M)
    (stageS G sourceConstant b y level M)
    (stageQ G sourceConstant b y level M)
    (stageL G sourceConstant b y level M)
    (stageNV G sourceConstant b y level M)
    (stageNB G sourceConstant b y level M)
    (lt_of_lt_of_le (by decide : 0 < 4)
      (Iteration.bins_ge_four G sourceConstant b y level M))
    (Iteration.secondFamily G sourceConstant b y level M)
    (GraphVectors.itemOrder G (stageS G sourceConstant b y level M))
    (GraphVectors.vectors G (stageS G sourceConstant b y level M))
    (GraphVectors.supportCap G
      (le_trans (by decide : 3 ≤ 4)
        (Iteration.bins_ge_four G sourceConstant b y level M)))

def physicalProtectedMatrix :=
  Construction.protectedMatrix M.entry
    (stageA G sourceConstant b y level M)
    (stageS G sourceConstant b y level M)
    (stageQ G sourceConstant b y level M)
    (stageL G sourceConstant b y level M)
    (stageNV G sourceConstant b y level M)
    (stageNB G sourceConstant b y level M)
    (lt_of_lt_of_le (by decide : 0 < 4)
      (Iteration.bins_ge_four G sourceConstant b y level M))
    (Iteration.secondFamily G sourceConstant b y level M)
    (GraphVectors.itemOrder G (stageS G sourceConstant b y level M))
    (GraphVectors.vectors G (stageS G sourceConstant b y level M))
    (GraphVectors.supportCap G
      (le_trans (by decide : 3 ≤ 4)
        (Iteration.bins_ge_four G sourceConstant b y level M)))

theorem physicalProtectedMatrix_eq_iteration :
    physicalProtectedMatrix G sourceConstant b y level M =
      Iteration.protectedMatrix G sourceConstant b y level M := by
  rfl

def physicalNRowNumbering :
    Iteration.Numbering (Iteration.NRow G sourceConstant b y level M) :=
  columnNumbering
    (MatrixWeightedTable.rawColumnCode'
      (stageA G sourceConstant b y level M)
      (stageS G sourceConstant b y level M)
      (stageQ G sourceConstant b y level M) M.columns)
    (MatrixWeightedTable.diagonalCode
      (stageA G sourceConstant b y level M)
      (stageS G sourceConstant b y level M)
      (stageQ G sourceConstant b y level M) M.columns)
    (Construction.uniformCopies (Y := Fin M.columns)
      (stageA G sourceConstant b y level M)
      (stageS G sourceConstant b y level M)
      (stageQ G sourceConstant b y level M))

def physicalNColNumbering :
    Iteration.Numbering (Iteration.NCol G sourceConstant b y level M) :=
  rowNumbering
    (MatrixWeightedTable.rawRowCode
      (stageS G sourceConstant b y level M)
      (stageL G sourceConstant b y level M)
      (stageNV G sourceConstant b y level M)
      (stageNB G sourceConstant b y level M) M.rows
      (GraphVectors.itemOrder G (stageS G sourceConstant b y level M)))
    (MatrixWeightedTable.templateCode
      (stageS G sourceConstant b y level M)
      (stageL G sourceConstant b y level M))
    (MatrixWeightedTable.vertexCode
      (stageNV G sourceConstant b y level M) M.rows)
    (MatrixWeightedTable.auxiliaryCode
      (stageNB G sourceConstant b y level M) M.rows)

def rowPermutation :
    Fin (Fintype.card (Iteration.NRow G sourceConstant b y level M)) ≃
      Fin (Iteration.nRowNumbering G sourceConstant b y level M).size :=
  ordinalPermutation (physicalNRowNumbering G sourceConstant b y level M)
    (Iteration.nRowNumbering G sourceConstant b y level M)

def columnPermutation :
    Fin (Fintype.card (Iteration.NCol G sourceConstant b y level M)) ≃
      Fin (Iteration.nColNumbering G sourceConstant b y level M).size :=
  ordinalPermutation (physicalNColNumbering G sourceConstant b y level M)
    (Iteration.nColNumbering G sourceConstant b y level M)


end ActualIteration

end

end EthInapproximability.CurrentPaper.MatrixWeightedOrdinalConjugacy

