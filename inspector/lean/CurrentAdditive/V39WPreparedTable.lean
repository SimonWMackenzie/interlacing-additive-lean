import CurrentAdditive.V39WTablePrepare

/-! Actual source-word preparation followed by the current complete table
printer, with one charged handoff and complete ambient-bank preservation. -/

namespace CurrentAdditive.V39WPreparedTable
noncomputable section
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384
open Paper2 Turing
open Paper2.RecursiveEntries
open EthInapproximability.CurrentPaper
open BitMachineEncoding BitMachineStackEmbedding
open V39WEntry
open V39WTablePrepare (Stack WriterStack writer sourceWords initial final)

def tableProgram := fun l => stackStmt writer (MatrixTableWriter.program P wStart wCtl l)
def tableStart := FetchIndexed.labelOf tableProgram (.inr (.copy .rows))
def tableControl := (wCtl,(none:Option Bool))
def program := BitMachineRawSequence.program V39WTablePrepare.program tableProgram tableStart
  V39WTablePrepare.control tableControl
def start := FetchIndexed.labelOf program (BitMachineRawSequence.leftLabel V39WTablePrepare.start)
def control := (V39WTablePrepare.control,tableControl)

theorem bank_writer (S : Fin 14 → List Bool) (T U : WriterStack → List Bool) :
    bank writer (final S T) U = final S U := by
  funext z
  rcases z with i | (j | i)
  · rw [bank_outside writer _ _ _ (by rintro ⟨j,h⟩; cases h)]
    rfl
  · exact bank_at writer _ _ j
  · rw [bank_outside writer _ _ _ (by rintro ⟨j,h⟩; cases h)]
    rfl

variable {p s q₁ q₂ w Q : Nat} [NeZero q₁] [NeZero q₂]
  [NeZero w] [NeZero Q] [NeZero s]

theorem physical_table (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
    (hp : 0 < p) (hs : 4 ≤ s) (r : Nat)
    (hq : q₂ = LiteralEdgeEncoder.Width s g.edges.length r)
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q)
    (K m : Nat)
    (xs : Fin m → V39RecursiveGenerator.Row g.vertices p q₁ q₂ s w Q K)
    (ys : Fin m → V39RecursiveGenerator.Column g.vertices p q₁ q₂ s w Q K) :
    let S := sourceWords g r K m xs ys
    let activity := V39EdgeSourceFront.edgeActivity g hg (by omega) r hq
    let f : Fin m → Fin m → Bool := fun i j => V39RecursiveTable.matrix activity K (xs i) (ys j)
    ∃ t ≤ V39WTablePrepare.clock S +
        MatrixTableWriter.writerBound m m (Tent g hg hs r hq ξ K m m xs ys)+1, ∃ v,
      ((advance program)^[t])
        (⟨some start,control,initial S⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,v,final S
          (MatrixTableWriter.ready (bankW g r K m m xs ys) m m 0 0 0 0 []
            (MatrixMaterialization.rowMajor f)).contents⟩ := by
  intro S activity f
  obtain ⟨a,ha,va,hprepare⟩ := V39WTablePrepare.physical_prepare g r K m xs ys
  obtain ⟨b,hb,vb,htable⟩ := table_run g hg hp hs r hq ξ K m m xs ys []
  rw [List.append_nil] at htable
  have he := BitMachineStackRun.run writer
    (final S (V39WTablePrepare.target g r K m xs ys))
    (MatrixTableWriter.program P wStart wCtl)
    (MatrixTableWriter.cfg (some (.inr (.copy .rows))) tableControl
      (MatrixTableWriter.ready (bankW g r K m m xs ys) m m 0 0 0 0 [] [])) b
  change ((advance (MatrixTableWriter.program P wStart wCtl))^[b]) _ = _ at htable
  dsimp only [tableControl] at he
  rw [htable] at he
  simp only [stackCfg,MatrixTableWriter.cfg] at he
  rw [bank_writer,bank_writer] at he
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs V39WTablePrepare.program tableProgram
    V39WTablePrepare.start tableStart V39WTablePrepare.control va tableControl vb
    _ _ _ a b hprepare (by simpa only [tableProgram,tableStart,tableControl,FetchIndexed.labelOf] using he)
  change a ≤ V39WTablePrepare.clock S at ha
  exact ⟨t,by omega,(V39WTablePrepare.control,vb),by
    simpa only [program,start,control,FetchIndexed.labelOf] using hr⟩

#print axioms bank_writer
#print axioms physical_table
end
end CurrentAdditive.V39WPreparedTable
