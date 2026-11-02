import EthInapproximability.CurrentPaper.WeightedRowFields
import EthInapproximability.CurrentPaper.MatrixWeightedFullBankBridge

/-! Lane owner:b-weighted-level-3, unit 2, segment 1 (2c-ii), second piece
(semantics): the exit values of the generated row-field program are exactly
writer 7 = `|VG|`, writer 18 = `nv`, writers 47..53 = the row boundaries and
divisors of `ProtectedFullBankBridgeScratch.actualD`, and the two dimension
words `actualRows`, `actualCols` of the admitted physical step, when the
program's inputs are the words the checked level controller produces
(writer 9 = `4s`, 15 = `nb`, 16 = `s*L`, 17 = `rx`, 29 = `binBase`,
21 = `rawWidth`, 1 = `uniform`) and `|VG|`. -/

namespace EthInapproximability.CurrentPaper.WeightedRowFields

open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedDuplication

theorem erase0 : Finset.univ.erase (0 : Fin 4) = {1, 2, 3} := by decide
theorem erase1 : Finset.univ.erase (1 : Fin 4) = {0, 2, 3} := by decide
theorem erase2 : Finset.univ.erase (2 : Fin 4) = {0, 1, 3} := by decide
theorem erase3 : Finset.univ.erase (3 : Fin 4) = {0, 1, 2} := by decide

theorem copies_row (X T V B : Type) [Fintype X] [Fintype T] [Fintype V] [Fintype B] :
    copies (rowSupport X T V B) rowWeight 0 =
      4194300 * (Fintype.card T * (Fintype.card V * Fintype.card B)) ∧
    copies (rowSupport X T V B) rowWeight 1 =
      2 * (Fintype.card X * (Fintype.card V * Fintype.card B)) ∧
    copies (rowSupport X T V B) rowWeight 2 =
      Fintype.card X * (Fintype.card T * Fintype.card B) ∧
    copies (rowSupport X T V B) rowWeight 3 =
      Fintype.card X * (Fintype.card T * Fintype.card V) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> unfold copies
  · rw [erase0]; simp [rowWeight]
  · rw [erase1]; simp [rowWeight]
  · rw [erase2]; simp [rowWeight]
  · rw [erase3]; simp [rowWeight]

section Actual

variable {rx cy : ℕ}

/-- The seven row fields of the literal entry-controller input, as products. -/
theorem actualInput_row_fields (R : Fin rx → Fin cy → Bool)
    (a s q L nv nb : ℕ) (hs : 0 < s)
    (family : Construction.SecondFamily a q L (Fin rx))
    (order : Construction.ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (Construction.activeItems vectors α).card ≤ s) :
    let d := MatrixWeightedEntrySemantic.actualInput R a s q L nv nb hs family order vectors cap
    let A0 := s * L + (nv + nb) * rx
    d.rowDivisor₀ = 4194300 * (s * L * (nv * rx * (nb * rx))) ∧
    d.rowDivisor₁ = 2 * (A0 * (nv * rx * (nb * rx))) ∧
    d.rowDivisor₂ = A0 * (s * L * (nb * rx)) ∧
    d.rowDivisor₃ = A0 * (s * L * (nv * rx)) ∧
    d.rowBoundary₁ = A0 * (4194300 * (s * L * (nv * rx * (nb * rx)))) ∧
    d.rowBoundary₂ = s * L * (2 * (A0 * (nv * rx * (nb * rx)))) ∧
    d.rowBoundary₃ = nv * rx * (A0 * (s * L * (nb * rx))) := by
  intro d A0
  obtain ⟨h0, h1, h2, h3⟩ := copies_row (Construction.RawRows s L nv nb (Fin rx))
    (Construction.TemplateSupport.{0} s L) (Construction.VertexRows nv (Fin rx))
    (Construction.AuxiliaryRows nb (Fin rx))
  have cX : Fintype.card (Construction.RawRows s L nv nb (Fin rx)) = A0 := by
    rw [Construction.card_rawRows, Fintype.card_fin]
  have cT : Fintype.card (Construction.TemplateSupport.{0} s L) = s * L := by
    simp [Construction.TemplateSupport]
  have cV : Fintype.card (Construction.VertexRows nv (Fin rx)) = nv * rx := by
    simp [Construction.VertexRows]
  have cB : Fintype.card (Construction.AuxiliaryRows nb (Fin rx)) = nb * rx := by
    simp [Construction.AuxiliaryRows]
  simp only [cX, cT, cV, cB] at h0 h1 h2 h3
  refine ⟨h0, h1, h2, h3, ?_, ?_, ?_⟩
  · show Fintype.card (Construction.RawRows s L nv nb (Fin rx)) * _ = _
    rw [cX, h0]
  · show Fintype.card (Construction.TemplateSupport.{0} s L) * _ = _
    rw [cT, h1]
  · show Fintype.card (Construction.VertexRows nv (Fin rx)) * _ = _
    rw [cV, h2]

end Actual

variable {VG EG : Type} [Fintype VG] [DecidableEq VG] [Fintype EG] [DecidableEq EG]

/-- Same-object identification: with the inputs the checked level controller
produces for the SAME `(G, c, b, y, lvl, M)`, the exit values of the fixed
row-field program are the fields of `actualD` and the admitted dimension
words. -/
theorem actualD_row_fields (G : EndpointGraph VG EG) (c b y lvl : ℕ) (M : Iteration.Matrix) :
    let d := ProtectedFullBankBridgeScratch.actualD G c b y lvl M
    let s := Iteration.s G c b y lvl M
    let L := Iteration.labels G c b y lvl M
    let f := rowVals (Fintype.card VG) (4 * s) d.nb (s * L) M.rows d.binBase d.rawWidth d.uniform
    f 8 = Fintype.card VG ∧ f 9 = d.nv ∧
    f 10 = d.rowBoundary₁ ∧ f 11 = d.rowBoundary₂ ∧ f 12 = d.rowBoundary₃ ∧
    f 13 = d.rowDivisor₀ ∧ f 14 = d.rowDivisor₁ ∧ f 15 = d.rowDivisor₂ ∧
    f 16 = d.rowDivisor₃ ∧
    f 17 = ProtectedFullBankBridgeScratch.actualRows G c b y lvl M ∧
    f 18 = ProtectedFullBankBridgeScratch.actualCols G c b y lvl M := by
  intro d s L f
  have hnv : d.nv = 4 * s * Fintype.card VG := rfl
  have hnb : d.nb = 4 * s * (s - 3) := rfl
  obtain ⟨e0, e1, e2, e3, b1, b2, b3⟩ := actualInput_row_fields M.entry
    (Iteration.a G c b y lvl M) s (Iteration.q₂ G c b y lvl M) L
    (GraphVectors.vertexCount VG s) (GraphVectors.auxiliaryCount s)
    (lt_of_lt_of_le (by decide : 0 < 4) (Iteration.bins_ge_four G c b y lvl M))
    (Iteration.secondFamily G c b y lvl M) (GraphVectors.itemOrder G s)
    (GraphVectors.vectors G s)
    (GraphVectors.supportCap G
      (le_trans (by decide : 3 ≤ 4) (Iteration.bins_ge_four G c b y lvl M)))
  change d.rowDivisor₀ = _ at e0
  change d.rowDivisor₁ = _ at e1
  change d.rowDivisor₂ = _ at e2
  change d.rowDivisor₃ = _ at e3
  change d.rowBoundary₁ = _ at b1
  change d.rowBoundary₂ = _ at b2
  change d.rowBoundary₃ = _ at b3
  have hv : GraphVectors.vertexCount VG s = 4 * s * Fintype.card VG := rfl
  have hnb' : GraphVectors.auxiliaryCount s = d.nb := rfl
  simp only [hv, hnb'] at e0 e1 e2 e3 b1 b2 b3
  refine ⟨rfl, hnv.symm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [b1]; simp (config := { decide := true }) only [f, rowVals, Function.update_apply, ite_true, ite_false]; try ring
  · rw [b2]; simp (config := { decide := true }) only [f, rowVals, Function.update_apply, ite_true, ite_false]; try ring
  · rw [b3]; simp (config := { decide := true }) only [f, rowVals, Function.update_apply, ite_true, ite_false]; try ring
  · rw [e0]; simp (config := { decide := true }) only [f, rowVals, Function.update_apply, ite_true, ite_false]; try ring
  · rw [e1]; simp (config := { decide := true }) only [f, rowVals, Function.update_apply, ite_true, ite_false]; try ring
  · rw [e2]; simp (config := { decide := true }) only [f, rowVals, Function.update_apply, ite_true, ite_false]; try ring
  · rw [e3]; simp (config := { decide := true }) only [f, rowVals, Function.update_apply, ite_true, ite_false]; try ring
  · have hW21 : d.rawWidth = MatrixStage4Codes.cols (Iteration.a G c b y lvl M) s
        (Iteration.q₂ G c b y lvl M) M.columns := rfl
    have hW29 : d.binBase = MatrixStage4Digits.binBase (Iteration.a G c b y lvl M) s
        (Iteration.q₂ G c b y lvl M) M.columns := rfl
    have hW1 : d.uniform = Construction.uniformCopies (Y := Fin M.columns)
        (Iteration.a G c b y lvl M) s (Iteration.q₂ G c b y lvl M) := rfl
    show _ = Fintype.card (Construction.ProtectedColumns (Iteration.a G c b y lvl M) s
      (Iteration.q₂ G c b y lvl M) (Fin M.columns))
    rw [Construction.card_protectedColumns]
    simp (config := { decide := true }) only [f, rowVals, Function.update_apply, ite_true,
      ite_false]
    rw [hW21, hW29, hW1]
    simp only [MatrixStage4Codes.cols, MatrixStage4Digits.binBase, MatrixStage4Digits.wordBase,
      Construction.uniformCopies, Construction.card_secondRows, Fintype.card_fin]
    ring
  · show _ = Fintype.card (Construction.ProtectedRows s L (GraphVectors.vertexCount VG s)
      (GraphVectors.auxiliaryCount s) (Fin M.rows))
    rw [Construction.card_protectedRows]
    simp (config := { decide := true }) only [f, rowVals, Function.update_apply, ite_true,
      ite_false]
    simp only [hv, hnb', Fintype.card_fin]
    norm_num
    ring

#print axioms copies_row
#print axioms actualInput_row_fields
#print axioms actualD_row_fields

end EthInapproximability.CurrentPaper.WeightedRowFields
