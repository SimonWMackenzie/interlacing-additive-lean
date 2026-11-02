import CurrentAdditive.V22FullTableWriter

set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 16384
namespace V22FullTableClock
noncomputable section
open Paper2 EthInapproximability.CurrentPaper CurrentAdditive
open V38Schedule V39PublicSchedule V39FullSampleResources V39WTablePublicClock
open Paper2.RecursiveEntries

theorem entry_le_writer (m E : ℕ) (hm : 1 ≤ m) : E ≤ MatrixTableWriter.writerBound m m E := by
  have h1 : E ≤ m*(E+2) := (Nat.le_mul_of_pos_left _ (by omega : 0 < m)).trans
    (Nat.mul_le_mul_left m (show E ≤ E+2 by omega))
  have h2 : m*(E+2) ≤ m*(E+2)+4*m+8 := by omega
  have h3 : m*(E+2)+4*m+8 ≤ m*(m*(E+2)+4*m+8) := Nat.le_mul_of_pos_left _ (by omega)
  unfold MatrixTableWriter.writerBound
  omega

theorem writer_mono (m a b : ℕ) (hab : a ≤ b) :
    MatrixTableWriter.writerBound m m a ≤ MatrixTableWriter.writerBound m m b := by
  unfold MatrixTableWriter.writerBound
  gcongr

theorem writer_le_whole (g : EncodedGraph.Graph) (p s q₁ q₂ w Q r k m thr : ℕ) :
    MatrixTableWriter.writerBound m m (entryClock g p s q₁ q₂ w Q r k m) ≤
      wholeClock g p s q₁ q₂ w Q r k m thr := by
  unfold wholeClock
  exact (Nat.le_add_left _ _).trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))

theorem entry_le_whole (g : EncodedGraph.Graph) (p s q₁ q₂ w Q r k m thr : ℕ) (hm : 1 ≤ m) :
    entryClock g p s q₁ q₂ w Q r k m ≤ wholeClock g p s q₁ q₂ w Q r k m thr :=
  (entry_le_writer m _ hm).trans (writer_le_whole g p s q₁ q₂ w Q r k m thr)

section Current
variable (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
variable (c δv ζ : ℚ) (L k : ℕ) (hn : g.vertices ≤ 2^L)
variable (ht : FullTests c L g.edges.length δv ζ)
variable (hs : 4 ≤ fullS L)
variable (hq : fullQ₂ L=LiteralEdgeEncoder.Width (fullS L) g.edges.length (fullRepeat L g.edges.length))
variable (ξ : Tails (Fin (seedWidth L) → Bool) (Fin (seedWidth L))
  (SourceConstruction.Items (fullS L) (Fin g.vertices)) (fullS L) (fullQ₁ L) (fullQ₂ L) (fullW L) (fullQ L))
variable (xs : Fin (sampleSide L k) → V39RecursiveGenerator.Row g.vertices
  (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L) (fullW L) (fullQ L) k)
variable (ys : Fin (sampleSide L k) → V39RecursiveGenerator.Column g.vertices
  (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L) (fullW L) (fullQ L) k)
include hn ht

theorem actual_Tent_full :
    V39WEntry.Tent g hg hs (fullRepeat L g.edges.length) hq ξ k (sampleSide L k) (sampleSide L k) xs ys ≤
      (graphSize g)^11*2^(tableExponent*T L k) := by
  have hTent := Tent_public g hg hs (fullRepeat L g.edges.length) hq ξ k (sampleSide L k) xs ys
  have hm : 1 ≤ sampleSide L k := Nat.one_le_two_pow
  exact (hTent.trans (entry_le_whole g _ _ _ _ _ _ _ _ _ (V39PublicSchedule.B L k) hm)).trans
    (whole_full g c δv ζ L k hn ht)

theorem actual_writer_full :
    MatrixTableWriter.writerBound (sampleSide L k) (sampleSide L k)
      (V39WEntry.Tent g hg hs (fullRepeat L g.edges.length) hq ξ k (sampleSide L k) (sampleSide L k) xs ys) ≤
      (graphSize g)^11*2^(tableExponent*T L k) := by
  have hTent := Tent_public g hg hs (fullRepeat L g.edges.length) hq ξ k (sampleSide L k) xs ys
  have hW : MatrixTableWriter.writerBound (sampleSide L k) (sampleSide L k)
      (V39WEntry.Tent g hg hs (fullRepeat L g.edges.length) hq ξ k (sampleSide L k) (sampleSide L k) xs ys) ≤
      MatrixTableWriter.writerBound (sampleSide L k) (sampleSide L k)
        (entryClock g (seedWidth L) (fullS L) (fullQ₁ L) (fullQ₂ L) (fullW L) (fullQ L)
          (fullRepeat L g.edges.length) k (sampleSide L k)) := by
    exact writer_mono _ _ _ hTent
  exact (hW.trans (writer_le_whole g _ _ _ _ _ _ _ _ _ _)).trans (whole_full g c δv ζ L k hn ht)

theorem actual_prep_writer_header_full :
    V39WTablePrepare.clock (V39WTablePrepare.sourceWords g (fullRepeat L g.edges.length) k (sampleSide L k) xs ys)+
      MatrixTableWriter.writerBound (sampleSide L k) (sampleSide L k)
        (V39WEntry.Tent g hg hs (fullRepeat L g.edges.length) hq ξ k (sampleSide L k) (sampleSide L k) xs ys)+
      V39WHeaderExact.clock (sampleSide L k) (sampleSide L k) (V39PublicSchedule.B L k)+2 ≤
      (graphSize g)^11*2^(tableExponent*T L k) :=
  (charge_public g hg hs (fullRepeat L g.edges.length) hq ξ k (sampleSide L k) (V39PublicSchedule.B L k) xs ys).trans
    (whole_full g c δv ζ L k hn ht)
end Current

#print axioms actual_Tent_full
#print axioms actual_writer_full
#print axioms actual_prep_writer_header_full
end
end V22FullTableClock
