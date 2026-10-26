import CurrentAdditive.V39WEncodedTable

/-! The complete fixed encoded printer embedded in any physical caller bank.
The caller must supply the literal source fields and blank work cells; all
foreign cells are retained by the exact complete-bank endpoint. -/
namespace CurrentAdditive.V39WEncodedTable
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384
open Paper2 Turing EthInapproximability.CurrentPaper
open BitMachineEncoding BitMachineStackEmbedding EncodedCommunication
open Paper2.RecursiveEntries V39WEntry
local instance : DecidableEq Stack := Classical.decEq _
variable {p s q₁ q₂ w Q : Nat} [NeZero q₁] [NeZero q₂]
  [NeZero w] [NeZero Q] [NeZero s]

theorem physical_from_bank {J : Type*} [DecidableEq J]
    (ι : Stack ↪ J) (W : J → List Bool)
    (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
    (hp : 0 < p) (hs : 4 ≤ s) (r : Nat)
    (hq : q₂=LiteralEdgeEncoder.Width s g.edges.length r)
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q)
    (K m thr : Nat)
    (xs : Fin m → V39RecursiveGenerator.Row g.vertices p q₁ q₂ s w Q K)
    (ys : Fin m → V39RecursiveGenerator.Column g.vertices p q₁ q₂ s w Q K)
    (hW : ∀ j, W (ι j)=initial (V39WTablePrepare.sourceWords g r K m xs ys) thr j) :
    let S := V39WTablePrepare.sourceWords g r K m xs ys
    let activity := V39EdgeSourceFront.edgeActivity g hg (by omega) r hq
    let f : Fin m → Fin m → Bool := fun i j => V39RecursiveTable.matrix activity K (xs i) (ys j)
    let WB := (MatrixTableWriter.ready (bankW g r K m m xs ys) m m 0 0 0 0 []
      (MatrixMaterialization.rowMajor f)).contents
    ∃ t ≤ V39WTablePrepare.clock S+
        MatrixTableWriter.writerBound m m (Tent g hg hs r hq ξ K m m xs ys)+
        V39WHeaderExact.clock m m thr+2, ∃ v,
      ((advance (fun l => stackStmt ι (program l)))^[t])
        (⟨some start,control,W⟩ : TM2.Cfg (fun _ : J => Bool) _ _) =
        ⟨none,v,bank ι W (final S WB m m thr (MatrixMaterialization.rowMajor f))⟩ := by
  intro S activity f WB
  obtain ⟨t,ht,v,hr⟩ := physical_encoded g hg hp hs r hq ξ K m thr xs ys
  have he := HeaderJoin.liftG ι program W (initial S thr)
    (final S WB m m thr (MatrixMaterialization.rowMajor f))
    (fun j => (hW j).symm) start control v t hr
  exact ⟨t,ht,v,he⟩

theorem embedded_final_word {J : Type*} [DecidableEq J] (ι : Stack ↪ J)
    (W : J → List Bool) (S : Fin 14 → List Bool) (WB : V39WTablePrepare.WriterStack → List Bool)
    (rows cols thr : Nat) (table : List Bool) :
    bank ι W (final S WB rows cols thr table) (ι outputPort)=
      encodeInstance ⟨rows,cols,thr,table⟩ := by
  rw [bank_at,final_word]

#print axioms physical_from_bank
#print axioms embedded_final_word
end
end CurrentAdditive.V39WEncodedTable
