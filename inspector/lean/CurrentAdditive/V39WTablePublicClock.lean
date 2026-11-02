import CurrentAdditive.V39WEncodedTable
import CurrentAdditive.V39EntryPublicClock
import Paper2.SCFetch

/-! Public clocks for the actual current entry/table/preparation/header.
These bounds depend on public counts and graph bytes, never on a maximum
over sampled labels or their execution times. -/
namespace CurrentAdditive.V39WTablePublicClock
noncomputable section
set_option maxHeartbeats 12000000
set_option maxRecDepth 16384
open Paper2 EthInapproximability.CurrentPaper
open GeneratorCode GeneratorSerialization GeneratorSource RecursiveLabelCodecScratch RecursiveEntries
open V39WEntry

def fetchSize (m R : Nat) : Nat := m*R+m*R+m+m+m+1
def entryClock (g : EncodedGraph.Graph) (p s q₁ q₂ w Q r K m : Nat) : Nat :=
  140*(V39RLoop.syntaxCap g.vertices p s q₁ q₂ w Q K *
    fetchSize m (V39RLoop.labelCap g.vertices p s q₁ q₂ w Q K))+
    V39RLoop.publicCoreClock g p s q₁ q₂ w Q r K+
    4*V39RLoop.labelCap g.vertices p s q₁ q₂ w Q K+6

def sourceLength (g : EncodedGraph.Graph) (p s q₁ q₂ w Q r K m : Nat) : Nat :=
  V39RLoop.publicScale g p s q₁ q₂ w Q r K+m+
    2*m*V39RLoop.labelCap g.vertices p s q₁ q₂ w Q K

def headerClock (m thr : Nat) : Nat :=
  (12*UnaryBinaryEncoding.coefficient+100)*(m+thr+1)^2

def wholeClock (g : EncodedGraph.Graph) (p s q₁ q₂ w Q r K m thr : Nat) : Nat :=
  V39WTablePrepare.N*(2*sourceLength g p s q₁ q₂ w Q r K m+3)+3+
    MatrixTableWriter.writerBound m m (entryClock g p s q₁ q₂ w Q r K m)+
    headerClock m thr+2

variable {p s q₁ q₂ w Q : Nat} [NeZero q₁] [NeZero q₂]
  [NeZero w] [NeZero Q] [NeZero s]

theorem sample_lengths (g : EncodedGraph.Graph) (K m : Nat)
    (xs : Fin m → V39RecursiveGenerator.Row g.vertices p q₁ q₂ s w Q K)
    (ys : Fin m → V39RecursiveGenerator.Column g.vertices p q₁ q₂ s w Q K) :
    let R := V39RLoop.labelCap g.vertices p s q₁ q₂ w Q K
    (rowWords g K m xs).flatten.length ≤ m*R ∧
    (colWords g K m ys).flatten.length ≤ m*R ∧
    (∀ i, (V39PhysicalSelect.rowWord K (xs i)).length ≤ R) ∧
    (∀ j, (V39PhysicalSelect.columnWord K (ys j)).length ≤ R) := by
  intro R
  obtain ⟨hr,hc⟩ := V39RLoop.labelCap_le g.vertices p s q₁ q₂ w Q K K (by omega)
  let C := defaultCarrierCodecs g.vertices p s q₁ q₂ w Q K
  have hrf := SuccessClock.ofFn_flatten_le C.1 m
    (fun i => (V39PhysicalSelect.embedding g.vertices p q₁ q₂ s w Q K).1 (xs i))
  have hcf := SuccessClock.ofFn_flatten_le C.2 m
    (fun j => (V39PhysicalSelect.embedding g.vertices p q₁ q₂ s w Q K).2 (ys j))
  refine ⟨hrf.trans (Nat.mul_le_mul_left m hr),hcf.trans (Nat.mul_le_mul_left m hc),?_,?_⟩
  · intro i
    exact (C.1.length_le ((V39PhysicalSelect.embedding g.vertices p q₁ q₂ s w Q K).1 (xs i))).trans hr
  · intro j
    exact (C.2.length_le ((V39PhysicalSelect.embedding g.vertices p q₁ q₂ s w Q K).2 (ys j))).trans hc

theorem entry_public (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
    (hs : 4 ≤ s) (r : Nat) (hq : q₂=LiteralEdgeEncoder.Width s g.edges.length r)
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q)
    (K m : Nat)
    (xs : Fin m → V39RecursiveGenerator.Row g.vertices p q₁ q₂ s w Q K)
    (ys : Fin m → V39RecursiveGenerator.Column g.vertices p q₁ q₂ s w Q K) (i j : Fin m) :
    entryBd g hg hs r hq ξ K m m xs ys i j ≤ entryClock g p s q₁ q₂ w Q r K m := by
  let A := V39RLoop.syntaxCap g.vertices p s q₁ q₂ w Q K
  let R := V39RLoop.labelCap g.vertices p s q₁ q₂ w Q K
  let c := seedRecursiveCodes g.vertices p s q₁ q₂ w Q K
  obtain ⟨hrf,hcf,hr,hc⟩ := sample_lengths g K m xs ys
  have hA := V39RLoop.syntaxCap_le g.vertices p s q₁ q₂ w Q K K (by omega)
  have hcol := SuccessClock.colBound_le c.1 (rowWords g K m xs) i.val (colWords g K m ys).flatten
  have hrow := SuccessClock.rowBound_le c.1 c.2 (rowWords g K m xs) (colWords g K m ys) j.val []
  have hrowlen : (rowWords g K m xs).length=m := by simp [rowWords]
  have hcollen : (colWords g K m ys).length=m := by simp [colWords]
  change (rowWords g K m xs).flatten.length ≤ m*R at hrf
  change (colWords g K m ys).flatten.length ≤ m*R at hcf
  have hfc : (rowWords g K m xs).flatten.length+(rowWords g K m xs).length+i.val+
      (colWords g K m ys).flatten.length+1 ≤ fetchSize m R := by
    rw [hrowlen]
    dsimp only [fetchSize]
    omega
  have hfr : (rowWords g K m xs).flatten.length+(colWords g K m ys).flatten.length+
      (rowWords g K m xs).length+(colWords g K m ys).length+j.val+0+1 ≤ fetchSize m R := by
    rw [hrowlen,hcollen]
    simp only [List.length_nil,fetchSize]
    omega
  have hC : FetchIndexed.colBound c.1 (rowWords g K m xs) i.val (colWords g K m ys).flatten ≤
      60*(A*fetchSize m R) := hcol.trans (Nat.mul_le_mul_left 60
        (Nat.mul_le_mul (by dsimp [A,c]; omega) hfc))
  have hR : FetchIndexed.rowBound c.1 c.2 (rowWords g K m xs) (colWords g K m ys) j.val [] ≤
      80*(A*fetchSize m R) := hrow.trans (Nat.mul_le_mul_left 80 (Nat.mul_le_mul hA hfr))
  dsimp only [c] at hC hR
  have hcore := V39RLoop.coreClock_public g hg hs r hq ξ K (xs i) (ys j)
  have hx := hr i
  have hy := hc j
  change (V39PhysicalSelect.rowWord K (xs i)).length ≤ R at hx
  change (V39PhysicalSelect.columnWord K (ys j)).length ≤ R at hy
  change _+_+V39RLoop.coreClock g hg hs r hq ξ K (xs i) (ys j)+_+3 ≤ _
  unfold entryClock
  change _ ≤ 140*(A*fetchSize m R)+V39RLoop.publicCoreClock g p s q₁ q₂ w Q r K+4*R+6
  omega

theorem Tent_public (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
    (hs : 4 ≤ s) (r : Nat) (hq : q₂=LiteralEdgeEncoder.Width s g.edges.length r)
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q)
    (K m : Nat)
    (xs : Fin m → V39RecursiveGenerator.Row g.vertices p q₁ q₂ s w Q K)
    (ys : Fin m → V39RecursiveGenerator.Column g.vertices p q₁ q₂ s w Q K) :
    Tent g hg hs r hq ξ K m m xs ys ≤ entryClock g p s q₁ q₂ w Q r K m := by
  unfold Tent
  apply Finset.sup_le
  intro ij _
  exact entry_public g hg hs r hq ξ K m xs ys ij.1 ij.2

theorem sourceLength_public (g : EncodedGraph.Graph) (r K m : Nat)
    (xs : Fin m → V39RecursiveGenerator.Row g.vertices p q₁ q₂ s w Q K)
    (ys : Fin m → V39RecursiveGenerator.Column g.vertices p q₁ q₂ s w Q K) :
    V39WTablePrepare.inputLength (V39WTablePrepare.sourceWords g r K m xs ys) ≤
      sourceLength g p s q₁ q₂ w Q r K m := by
  obtain ⟨hr,hc,_,_⟩ := sample_lengths g K m xs ys
  have hsx := V39RLoop.syntaxCap_le g.vertices p s q₁ q₂ w Q K K (by omega)
  simp only [V39WTablePrepare.inputLength,V39WTablePrepare.sourceWords,
    Fin.sum_univ_succ,List.length_replicate,List.length_append,List.length_nil,
    encodeCode_length,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero,Nat.add_zero]
  unfold sourceLength V39RLoop.publicScale V39RLoop.scalarSum
  rw [show 2*m*V39RLoop.labelCap g.vertices p s q₁ q₂ w Q K =
    m*V39RLoop.labelCap g.vertices p s q₁ q₂ w Q K+
    m*V39RLoop.labelCap g.vertices p s q₁ q₂ w Q K by ring]
  omega

theorem header_public (m thr : Nat) : V39WHeaderExact.clock m m thr ≤ headerClock m thr := by
  have hm := EncodedGraph.natField_length_upper m
  have ht := EncodedGraph.natField_length_upper thr
  let Y := m+thr+1
  have h1 : (m+1)^2 ≤ Y^2 := Nat.pow_le_pow_left (by dsimp [Y]; omega) 2
  have h2 : (thr+1)^2 ≤ Y^2 := Nat.pow_le_pow_left (by dsimp [Y]; omega) 2
  have h3 := Nat.mul_le_mul_left UnaryBinaryEncoding.coefficient h1
  have h4 := Nat.mul_le_mul_left UnaryBinaryEncoding.coefficient h2
  have hY : Y ≤ Y^2 := by simpa [pow_two] using Nat.le_mul_self Y
  have hY1 : 1 ≤ Y := by dsimp [Y]; omega
  unfold V39WHeaderExact.clock headerClock
  simp only [List.length_append]
  change _ ≤ (12*UnaryBinaryEncoding.coefficient+100)*Y^2
  have hlinear : 12*m+6*thr+20 ≤ 100*Y^2 := by dsimp [Y] at *; nlinarith
  nlinarith [Nat.zero_le (UnaryBinaryEncoding.coefficient*Y^2)]

theorem charge_public (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
    (hs : 4 ≤ s) (r : Nat) (hq : q₂=LiteralEdgeEncoder.Width s g.edges.length r)
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q)
    (K m thr : Nat)
    (xs : Fin m → V39RecursiveGenerator.Row g.vertices p q₁ q₂ s w Q K)
    (ys : Fin m → V39RecursiveGenerator.Column g.vertices p q₁ q₂ s w Q K) :
    V39WTablePrepare.clock (V39WTablePrepare.sourceWords g r K m xs ys)+
      MatrixTableWriter.writerBound m m (Tent g hg hs r hq ξ K m m xs ys)+
      V39WHeaderExact.clock m m thr+2 ≤ wholeClock g p s q₁ q₂ w Q r K m thr := by
  have hS := sourceLength_public g r K m xs ys
  have hT := Tent_public g hg hs r hq ξ K m xs ys
  have hH := header_public m thr
  unfold V39WTablePrepare.clock wholeClock MatrixTableWriter.writerBound
  gcongr

#print axioms entry_public
#print axioms Tent_public
#print axioms sourceLength_public
#print axioms header_public
#print axioms charge_public
end
end CurrentAdditive.V39WTablePublicClock
