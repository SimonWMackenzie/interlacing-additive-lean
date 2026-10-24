import EthInapproximability.CurrentPaper.MatrixWeightedEntryCost
import EthInapproximability.CurrentPaper.MatrixWeightedEntrySemantic

/-!
# Charged writer callback for the literal protected matrix

The cell controller is one fixed finite program.  `case_run` combines its
eight physical branch certificates with the corresponding semantic address
equalities.  Its common bound is a maximum of explicit stage costs, not a
supremum of unknown halting times.  Polynomial domination of this bound by
the original-instance encoding length is a separate obligation.
-/

namespace EthInapproximability.CurrentPaper.MatrixWeightedEntryRuns

open Construction MatrixWeightedEntryController MatrixWeightedEntryCost
open MatrixWeightedEntrySemantic

private theorem direct_le_cell (d : Input) (x y : ℕ)
    (order : ItemOrder d.nv d.nb) :
    directCaseCost d x y ≤ cellCost d x y order := by
  exact le_max_left _ _

private theorem ordered_le_cell (d : Input) (x y : ℕ)
    (order : ItemOrder d.nv d.nb) (j : Fin (d.nv + d.nb)) :
    orderedCaseCost d x y order j ≤ cellCost d x y order := by
  have hj : orderedCaseCost d x y order j ≤
      Finset.univ.sup (fun z : Fin (d.nv + d.nb) =>
        orderedCaseCost d x y order z) :=
    Finset.le_sup (s := (Finset.univ : Finset (Fin (d.nv + d.nb))))
      (f := fun z => orderedCaseCost d x y order z) (Finset.mem_univ j)
  exact hj.trans (le_max_right _ _)

private theorem fullFull_le_cell (d : Input) (x y : ℕ)
    (order : ItemOrder d.nv d.nb) :
    fullFullCost d x y ≤ cellCost d x y order := by
  apply le_trans (b := directCaseCost d x y)
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact direct_le_cell d x y order

private theorem fullTemplate_le_cell (d : Input) (x y : ℕ)
    (order : ItemOrder d.nv d.nb) :
    fullTemplateCost d x y ≤ cellCost d x y order := by
  apply le_trans (b := directCaseCost d x y)
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · exact direct_le_cell d x y order

private theorem diagonalFull_le_cell (d : Input) (x y : ℕ)
    (order : ItemOrder d.nv d.nb) :
    diagonalFullCost d x y ≤ cellCost d x y order := by
  apply le_trans (b := directCaseCost d x y)
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact direct_le_cell d x y order

private theorem diagonalTemplate_le_cell (d : Input) (x y : ℕ)
    (order : ItemOrder d.nv d.nb) :
    diagonalTemplateCost d x y ≤ cellCost d x y order := by
  apply le_trans (b := directCaseCost d x y)
  · exact (le_max_right _ _).trans (le_max_right _ _)
  · exact direct_le_cell d x y order

private theorem fullVertex_le_cell (d : Input) (x y : ℕ)
    (order : ItemOrder d.nv d.nb) (j : Fin (d.nv + d.nb)) :
    fullVertexCost d x y order j ≤ cellCost d x y order := by
  apply le_trans (b := orderedCaseCost d x y order j)
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact ordered_le_cell d x y order j

private theorem fullAuxiliary_le_cell (d : Input) (x y : ℕ)
    (order : ItemOrder d.nv d.nb) (j : Fin (d.nv + d.nb)) :
    fullAuxiliaryCost d x y order j ≤ cellCost d x y order := by
  apply le_trans (b := orderedCaseCost d x y order j)
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · exact ordered_le_cell d x y order j

private theorem diagonalVertex_le_cell (d : Input) (x y : ℕ)
    (order : ItemOrder d.nv d.nb) (j : Fin (d.nv + d.nb)) :
    diagonalVertexCost d x y order j ≤ cellCost d x y order := by
  apply le_trans (b := orderedCaseCost d x y order j)
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact ordered_le_cell d x y order j

private theorem diagonalAuxiliary_le_cell (d : Input) (x y : ℕ)
    (order : ItemOrder d.nv d.nb) (j : Fin (d.nv + d.nb)) :
    diagonalAuxiliaryCost d x y order j ≤ cellCost d x y order := by
  apply le_trans (b := orderedCaseCost d x y order j)
  · exact (le_max_right _ _).trans (le_max_right _ _)
  · exact ordered_le_cell d x y order j

theorem case_run (d : Input) (order : ItemOrder d.nv d.nb)
    (horder : d.orderBits = MatrixWeightedRowOrderLookup.orderWord order)
    (x y : ℕ) (target : Bool)
    (hcase : ActualCase d order x y target) :
    ∃ t ≤ cellCost d x y order,
      run t (cfg (some start) initial (cellBank d x y [])) =
        cfg none initial (cellBank d x y [target]) := by
  cases hcase with
  | fullFull hc hr hbit =>
      obtain ⟨t, ht, he⟩ := full_full_bounded d x y hc hr
      refine ⟨t, ht.trans (fullFull_le_cell d x y order), ?_⟩
      change d.rawBits[fullLabel d y * d.rawWidth +
        ((x / d.uniform) / d.fullDivisor)]?.getD false = target at hbit
      simpa only [hbit] using he
  | fullTemplate hc h₁ hr hbit =>
      obtain ⟨t, ht, he⟩ := full_template_bounded d x y hc h₁ hr
      refine ⟨t, ht.trans (fullTemplate_le_cell d x y order), ?_⟩
      change d.rawBits[templateLabel d y * d.rawWidth +
        ((x / d.uniform) / d.fullDivisor)]?.getD false = target at hbit
      simpa only [hbit] using he
  | fullVertex j hw hc h₁ h₂ hr hj hbit =>
      obtain ⟨t, ht, he⟩ := full_vertex_bounded d x y order j
        horder hw hj hc h₁ h₂ hr
      refine ⟨t, ht.trans (fullVertex_le_cell d x y order j), ?_⟩
      change d.rawBits[(d.stagePrefixRows + (order j).val * d.rx +
        vertexLabel d y % d.rx) * d.rawWidth +
        ((x / d.uniform) / d.fullDivisor)]?.getD false = target at hbit
      simpa only [hbit] using he
  | fullAuxiliary j hw hc h₁ h₂ h₃ hj hbit =>
      obtain ⟨t, ht, he⟩ := full_auxiliary_cost_bounded d x y order j
        horder hw hj hc h₁ h₂ h₃
      refine ⟨t, ht.trans (fullAuxiliary_le_cell d x y order j), ?_⟩
      change d.rawBits[(d.stagePrefixRows + (order j).val * d.rx +
        auxiliaryLabel d y % d.rx) * d.rawWidth +
        ((x / d.uniform) / d.fullDivisor)]?.getD false = target at hbit
      simpa only [hbit] using he
  | diagonalFull hc hr hbit =>
      obtain ⟨t, ht, he⟩ := diagonal_full_bounded d x y hc hr
      refine ⟨t, ht.trans (diagonalFull_le_cell d x y order), ?_⟩
      change d.rawBits[fullLabel d y * d.rawWidth +
        diagonalColumnValue d x]?.getD false = target at hbit
      simpa only [hbit] using he
  | diagonalTemplate hc h₁ hr hbit =>
      obtain ⟨t, ht, he⟩ := diagonal_template_bounded d x y hc h₁ hr
      refine ⟨t, ht.trans (diagonalTemplate_le_cell d x y order), ?_⟩
      change d.rawBits[templateLabel d y * d.rawWidth +
        diagonalColumnValue d x]?.getD false = target at hbit
      simpa only [hbit] using he
  | diagonalVertex j hw hc h₁ h₂ hr hj hbit =>
      obtain ⟨t, ht, he⟩ := diagonal_vertex_cost_bounded d x y order j
        horder hw hj hc h₁ h₂ hr
      refine ⟨t, ht.trans (diagonalVertex_le_cell d x y order j), ?_⟩
      change d.rawBits[(d.stagePrefixRows + (order j).val * d.rx +
        vertexLabel d y % d.rx) * d.rawWidth +
        diagonalColumnValue d x]?.getD false = target at hbit
      simpa only [hbit] using he
  | diagonalAuxiliary j hw hc h₁ h₂ h₃ hj hbit =>
      obtain ⟨t, ht, he⟩ := diagonal_auxiliary_cost_bounded d x y order j
        horder hw hj hc h₁ h₂ h₃
      refine ⟨t, ht.trans (diagonalAuxiliary_le_cell d x y order j), ?_⟩
      change d.rawBits[(d.stagePrefixRows + (order j).val * d.rx +
        auxiliaryLabel d y % d.rx) * d.rawWidth +
        diagonalColumnValue d x]?.getD false = target at hbit
      simpa only [hbit] using he

/-- The actual protected cell contract for one fixed finite-stack program.
All coordinates, scalar words, the serialized order, and the raw table are
explicitly supplied in `persistentBank`; no semantic entry function is an
instruction of the program. -/
theorem actual_entry_runs {rx cy : ℕ}
    (R : Fin rx → Fin cy → Bool)
    (a s q L nv nb : ℕ) (hs : 0 < s)
    (family : SecondFamily a q L (Fin rx)) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (hcy : 0 < cy) (hbin : 2 ≤ MatrixStage4Digits.binBase a s q cy)
    (hrx : 0 < rx) :
    let d := actualInput R a s q L nv nb hs family order vectors cap
    MatrixTableWriter.EntryRuns program start initial (persistentBank d)
      (Fintype.card (ProtectedColumns a s q (Fin cy)))
      (Fintype.card (ProtectedRows s L nv nb (Fin rx)))
      (commonCost d
        (Fintype.card (ProtectedColumns a s q (Fin cy)))
        (Fintype.card (ProtectedRows s L nv nb (Fin rx))) order)
      (MatrixWeightedProtectedWriter.protectedEntry R a s q L nv nb hs
        family order vectors cap) := by
  dsimp only
  intro x hx y hy
  let d := actualInput R a s q L nv nb hs family order vectors cap
  let xf : Fin (Fintype.card (ProtectedColumns a s q (Fin cy))) := ⟨x, hx⟩
  let yf : Fin (Fintype.card (ProtectedRows s L nv nb (Fin rx))) := ⟨y, hy⟩
  have hcase := MatrixWeightedEntrySemantic.actual_cases R a s q L nv nb
    hs family order vectors cap hcy hbin hrx xf yf
  have horder : d.orderBits = MatrixWeightedRowOrderLookup.orderWord order := rfl
  obtain ⟨t, ht, he⟩ := case_run d order horder x y
    (MatrixWeightedProtectedWriter.protectedEntry R a s q L nv nb hs
      family order vectors cap x y) hcase
  refine ⟨t, ht.trans (cellCost_le_common d _ _ order xf yf), initial, ?_⟩
  exact he

/-- The row-major writer physically emits the literal protected matrix in
the frozen transpose convention, with the preceding output suffix intact.
The bound charges every cell callback by the explicit common stage-cost
maximum.  It does not charge production of the supplied input bank. -/
theorem write_actual_protected {rx cy : ℕ}
    (R : Fin rx → Fin cy → Bool)
    (a s q L nv nb : ℕ) (hs : 0 < s)
    (family : SecondFamily a q L (Fin rx)) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (hcy : 0 < cy) (hbin : 2 ≤ MatrixStage4Digits.binBase a s q cy)
    (hrx : 0 < rx) (output : List Bool) :
    let d := actualInput R a s q L nv nb hs family order vectors cap
    let rows := Fintype.card (ProtectedColumns a s q (Fin cy))
    let cols := Fintype.card (ProtectedRows s L nv nb (Fin rx))
    let T := commonCost d rows cols order
    ∃ t ≤ MatrixTableWriter.writerBound rows cols T, ∃ v,
      MatrixTableWriter.run program start initial t
        (MatrixTableWriter.cfg (some (.inr (.copy .rows))) (initial, none)
          (MatrixTableWriter.ready (persistentBank d)
            rows cols 0 0 0 0 [] output)) =
      MatrixTableWriter.cfg none v
        (MatrixTableWriter.ready (persistentBank d)
          rows cols 0 0 0 0 []
          (MatrixMaterialization.rowMajor (fun x y =>
            protectedMatrix R a s q L nv nb hs family order vectors cap
              (MatrixWeightedArithmetic.typedColumn
                (MatrixWeightedTable.rawColumnCode' a s q cy)
                (MatrixWeightedTable.diagonalCode a s q cy)
                (Construction.uniformCopies (Y := Fin cy) a s q) x)
              (MatrixWeightedArithmetic.typedRow
                (MatrixWeightedTable.rawRowCode s L nv nb rx order)
                (MatrixWeightedTable.templateCode s L)
                (MatrixWeightedTable.vertexCode nv rx)
                (MatrixWeightedTable.auxiliaryCode nb rx) y)) ++ output)) := by
  exact MatrixWeightedProtectedWriter.write_protected
    program start initial
    (persistentBank (actualInput R a s q L nv nb hs family order vectors cap))
    (commonCost (actualInput R a s q L nv nb hs family order vectors cap)
      (Fintype.card (ProtectedColumns a s q (Fin cy)))
      (Fintype.card (ProtectedRows s L nv nb (Fin rx))) order)
    R a s q L nv nb hs family order vectors cap
    (actual_entry_runs R a s q L nv nb hs family order vectors cap
      hcy hbin hrx) output

end EthInapproximability.CurrentPaper.MatrixWeightedEntryRuns
