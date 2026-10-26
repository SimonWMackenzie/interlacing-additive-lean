import Paper2.WTable
import Paper2.HeaderJoinX

/-! Unit 3, segment (5), partial: the successful table writer (`WEntry.table_run`, the
admitted `MatrixTableWriter` controller driven by the entry program `WEntry.P`) followed,
by ONE charged handoff, by the owner-7 header join `HeaderJoin.hjProg` on the SAME bank
(`HeaderJoin.JH Kw = MatrixTableWriter.Stack Kw ⊕ (HeaderA.HB ⊕ Fin 2)`). The writer's
exit `Data` record `MatrixTableWriter.ready bankW mX mY 0 0 0 0 [] (rowMajor f ++ output)`
is flattened onto the writer cells by `Data.contents` (its `rows`, `cols`, `output` cells
are `replicate mX true`, `replicate mY true`, `rowMajor f ++ output` by definition), which
discharges the three writer-cell hypotheses of `header_join` for this bank. -/

set_option maxHeartbeats 64000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.WEntry

noncomputable section

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open EthInapproximability.CurrentPaper.EncodedCommunication
open GeneratorCode GeneratorSerialization GeneratorSource
open RecursiveLabelCodecScratch RecursiveEntries
open Paper2.HeaderJoin (JH hjIn hjProg wOut thrM scrH liftG)

def inW : MatrixTableWriter.Stack Kw ↪ JH Kw := ⟨Sum.inl, Sum.inl_injective⟩

/-- The writer controller (driven by `P`) placed on the header-join bank. -/
def writerL := fun l => stackStmt inW (MatrixTableWriter.program P wStart wCtl l)

/-- Writer then header: ONE fixed program. -/
def tableHeader := BitMachineRawSequence.program writerL (hjProg Kw)
  (BitMachineRawSequence.leftLabel (.inl ⟨0, by omega⟩)) (wCtl, (none : Option Bool))
  ((none : Option Bool), HeaderA.progCtl)

/-- The explicit clock of `HeaderJoin.header_join`. -/
def hdrBd (rows cols thr : ℕ) : ℕ :=
  3 * (2 * (rows + cols + thr) + 3) + 1 +
    (UnaryBinaryEncoding.coefficient * (rows + 1) ^ 2 +
      UnaryBinaryEncoding.coefficient * (cols + 1) ^ 2 +
      UnaryBinaryEncoding.coefficient * (thr + 1) ^ 2 +
      (2 * (natField rows ++ natField cols ++ natField thr).length + 2) + 3) + 1

theorem hjIn_bank (T : MatrixTableWriter.Stack Kw → List Bool) (U : MatrixTableWriter.Stack Kw → List Bool)
    (thr : ℕ) : bank inW (hjIn U thr) T = hjIn T thr := by
  funext c
  rcases c with a | a
  · exact bank_at inW _ T a
  · exact bank_outside inW _ T (.inr a) (by rintro ⟨k, hk⟩; cases hk)

variable {p s q₁ q₂ w Q : ℕ} [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q] [NeZero s]

theorem table_header (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
    (hp : 0 < p) (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin g.edges.length) * r)
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q)
    (hfix : ∀ (k : ℕ) (i : SourceConstruction.Items s (Fin g.vertices))
      (js : Fin s → SourceMatrix.OuterColumn q₁ q₂ s (Column (Fin p → Bool) (Fin p)
        (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q k)),
      (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k).2.encode
        (SourceMatrix.sourceColumn (SourceActiveRank.scanAtCanonical
          (CanonicalEdgeTape.graphEdge g hg) (by omega) hq) i
          (SourceMatrix.forgetTag (ξ k) (.fixedTail js))) =
        (CanonicalDefaultWordScratch.words p s q₁ q₂ w Q k).2)
    (K mX mY : ℕ)
    (xs : Fin mX → Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q K)
    (ys : Fin mY → Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q K) (thr : ℕ) (output : List Bool) :
    let activity := SourceActiveRank.scanAtCanonical (CanonicalEdgeTape.graphEdge g hg)
      (by omega) hq
    let f : Fin mX → Fin mY → Bool := fun i j =>
      RecursiveEntries.matrix (LookupSeed.matrix p) activity ξ K (xs i) (ys j)
    let D := MatrixTableWriter.ready (bankW g r K mX mY xs ys) mX mY 0 0 0 0 []
      (MatrixMaterialization.rowMajor f ++ output)
    ∃ t ≤ MatrixTableWriter.writerBound mX mY (Tent g hg hs r hq ξ K mX mY xs ys) +
        hdrBd mX mY thr + 1,
      ∃ v, ∃ F : JH Kw → List Bool,
      ((advance tableHeader)^[t])
        (⟨some (BitMachineRawSequence.leftLabel (.inr (.copy .rows))),
          ((wCtl, (none : Option Bool)), ((none : Option Bool), HeaderA.progCtl)),
          hjIn (MatrixTableWriter.ready (bankW g r K mX mY xs ys) mX mY 0 0 0 0 [] output).contents
            thr⟩ : TM2.Cfg (fun _ : JH Kw => Bool) _ _) = ⟨none, v, F⟩ ∧
      F wOut = natField mX ++ natField mY ++ natField thr ++
        MatrixMaterialization.rowMajor f ++ output ∧
      (∀ a : MatrixTableWriter.Stack Kw, a ≠ .inr .output → F (.inl a) = D.contents a) ∧
      F thrM = List.replicate thr true ∧ F scrH = [] := by
  intro activity f D
  obtain ⟨t1, ht1, v1, r1⟩ := table_run g hg hp hs r hq ξ hfix K mX mY xs ys output
  set D0 := MatrixTableWriter.ready (bankW g r K mX mY xs ys) mX mY 0 0 0 0 [] output with hD0
  have r1' : ((advance (MatrixTableWriter.program P wStart wCtl))^[t1])
      (⟨some (.inr (.copy .rows)), (wCtl, none), D0.contents⟩ :
        TM2.Cfg (fun _ : MatrixTableWriter.Stack Kw => Bool) _ _) =
      ⟨none, v1, D.contents⟩ := r1
  have r1L := liftG inW (MatrixTableWriter.program P wStart wCtl) (hjIn D0.contents thr)
    D0.contents D.contents (fun _ => rfl) _ _ _ t1 r1'
  rw [hjIn_bank] at r1L
  obtain ⟨t2, ht2, v2, F, r2, hF, hfr, hthr, hscr⟩ := HeaderJoinX.header_join_exact
    D.contents mX mY thr (MatrixMaterialization.rowMajor f) output rfl rfl rfl
  obtain ⟨u, hu, hrun⟩ := BitMachineRawSequence.runs writerL (hjProg Kw)
    (.inr (.copy .rows)) (BitMachineRawSequence.leftLabel (.inl ⟨0, by omega⟩))
    (wCtl, (none : Option Bool)) v1 ((none : Option Bool), HeaderA.progCtl) v2
    (hjIn D0.contents thr) (hjIn D.contents thr) F t1 t2 r1L r2
  refine ⟨u, ?_, _, F, hrun, ?_, hfr, hthr, hscr⟩
  · have : t2 ≤ hdrBd mX mY thr := ht2
    omega
  · rw [hF]

end

#print axioms hjIn_bank
#print axioms table_header

end Paper2.WEntry
