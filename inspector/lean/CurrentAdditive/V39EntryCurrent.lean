import CurrentAdditive.V39EntryCore
import Paper2.EntryCore

set_option maxHeartbeats 64000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace CurrentAdditive.V39RLoop
noncomputable section
open Paper2 Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open GeneratorSerialization GeneratorSource RecursiveLabelCodecScratch RecursiveEntries

variable {p s q₁ q₂ w Q : ℕ} [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q] [NeZero s]

theorem readyE_old_abi (g : EncodedGraph.Graph) (r : ℕ)
    (xw yw cR cC : List Bool) (K : ℕ) (out : List Bool) :
    readyE (p:=p) (s:=s) (q₁:=q₁) (q₂:=q₂) (w:=w) (Q:=Q) g r xw yw cR cC K out =
      Paper2.RLoop.readyE (p:=p) (s:=s) (q₁:=q₁) (q₂:=q₂) (w:=w) (Q:=Q)
        g r xw yw cR cC K out := rfl

/-- Fixed current evaluator, literal current input words, actual current
matrix bit, and exact restoration of every other prepared bank. -/
theorem core_run_current (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
    (hp : 0 < p) (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂ = LiteralEdgeEncoder.Width s g.edges.length r)
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q)
    (K : ℕ)
    (x : V39RecursiveGenerator.Row g.vertices p q₁ q₂ s w Q K)
    (y : V39RecursiveGenerator.Column g.vertices p q₁ q₂ s w Q K) :
    let c := seedRecursiveCodes g.vertices p s q₁ q₂ w Q K
    let activity := V39EdgeSourceFront.edgeActivity g hg (by omega) r hq
    ∃ t ≤ coreClock g hg hs r hq ξ K x y, ∃ v,
      ((advance coreProg)^[t])
        (⟨some coreStart,coreCtl,
          readyE (p:=p) (s:=s) (q₁:=q₁) (q₂:=q₂) (w:=w) (Q:=Q) g r
            (V39PhysicalSelect.rowWord K x) (V39PhysicalSelect.columnWord K y)
            (encodeCode c.1) (encodeCode c.2) K []⟩ :
          TM2.Cfg (fun _ : JE => Bool) _ _) =
        ⟨none,v,readyE (p:=p) (s:=s) (q₁:=q₁) (q₂:=q₂) (w:=w) (Q:=Q) g r
            (V39PhysicalSelect.rowWord K x) (V39PhysicalSelect.columnWord K y)
            (encodeCode c.1) (encodeCode c.2) K
            [V39RecursiveTable.matrix activity K x y]⟩ := by
  exact core_run g hg hp hs r hq ξ K x y

end
#print axioms readyE_old_abi
#print axioms core_run_current
end CurrentAdditive.V39RLoop
