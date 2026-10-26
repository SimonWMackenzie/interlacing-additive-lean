import CurrentAdditive.V39RLoopRun

set_option maxHeartbeats 64000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace CurrentAdditive.V39RLoop
noncomputable section
open Paper2 Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open GeneratorSource RecursiveLabelCodecScratch RecursiveEntries

variable {p s q₁ q₂ w Q : ℕ} [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q] [NeZero s]

/-- The concrete current-label loop bank; the auxiliary code words describe
only the navigation syntax, and are unrelated to the sampling law. -/
def bankCurrent (g : EncodedGraph.Graph) (r k : ℕ)
    (x : V39RecursiveGenerator.Row g.vertices p q₁ q₂ s w Q k)
    (y : V39RecursiveGenerator.Column g.vertices p q₁ q₂ s w Q k) : JL → List Bool :=
  bankL g r k ((V39PhysicalSelect.embedding g.vertices p q₁ q₂ s w Q k).1 x)
    ((V39PhysicalSelect.embedding g.vertices p q₁ q₂ s w Q k).2 y)

theorem body_run_current (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
    (hp : 0 < p) (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂ = LiteralEdgeEncoder.Width s g.edges.length r)
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q)
    (k : ℕ)
    (x : V39RecursiveGenerator.Row g.vertices p q₁ q₂ s w Q (k+1))
    (y : V39RecursiveGenerator.Column g.vertices p q₁ q₂ s w Q (k+1)) :
    let activity := V39EdgeSourceFront.edgeActivity g hg (by omega) r hq
    let req := V39RecursiveTable.request activity k x y
    ∃ t ≤ bodyClock g hg hs r hq ξ k x y, ∃ v,
      ((advance body)^[t])
        (⟨some bodyStart, bodyCtl,
          Function.update (bankCurrent g r (k+1) x y) ctr (List.replicate k true)⟩ :
          TM2.Cfg (fun _ : JL => Bool) _ _) =
        ⟨none,v,bankCurrent g r k req.1 req.2⟩ := by
  intro activity req
  obtain ⟨t,ht,v,hr⟩ := body_run g hg hp hs r hq ξ k x y
  rw [V39PhysicalSelect.request_embedding] at hr
  exact ⟨t,ht,v,hr⟩

end
#print axioms body_run_current
end CurrentAdditive.V39RLoop
