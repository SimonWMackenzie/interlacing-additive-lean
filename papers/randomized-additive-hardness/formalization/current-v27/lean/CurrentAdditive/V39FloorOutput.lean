import CurrentAdditive.V39PublicFloor
import CurrentAdditive.V39ActualOutputPower
import CurrentAdditive.V39SupportLower

/-! Same actual table size bounds with the original-formula search floor.
In particular the printed square has enough entries for an eventual estimator
guarantee without identifying the graph vertex count and the formula size.
-/

namespace CurrentAdditive.V39GeneratedConstruction

open Paper2 V38Schedule CurrentAdditive.LiteralEdgeEncoder

theorem generatedGraphRun_public_side {L n m r : ℕ}
    [NeZero (generatedS L)] [NeZero (generatedQ₂ L)]
    [NeZero (generatedW L)] [NeZero (generatedQ L)]
    (hs : 4 ≤ generatedS L) (hn : 0 < n)
    (hq : generatedQ₂ L = LiteralEdgeEncoder.Width (generatedS L) m r)
    (edge : Fin m → Bool → Fin n) (k : ℕ) :
    generatedN L ≤ Paper2.SquarePadding.side
      (graphRun (w := generatedW L) (Q := generatedQ L) hs hn hq edge L k).rows
      (graphRun (w := generatedW L) (Q := generatedQ L) hs hn hq edge L k).cols := by
  haveI : NeZero (generatedS L-2) := ⟨by omega⟩
  let μI := indexedItemLaw (generatedS L) n hs hn
  let activity := graphActivity (by omega : 3 ≤ generatedS L) hq edge
  apply le_trans ?_ (Paper2.SquarePadding.max_le_side _ _)
  cases k with
  | zero =>
    have hw := Paper2.LookupSeed.width_admissible L
    have hL : L ≤ Paper2.LookupSeed.width L := by omega
    have hp := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hL
    exact hp.trans (le_max_left _ _)
  | succ k =>
    let prev := StoredMatrix.iterate (q₁ := generatedS L-2) (s := generatedS L)
      (w := generatedW L) (Q := generatedQ L) μI activity k (storedLookupSeed L)
    have h := executableStep_dimension_lower (q₁ := generatedS L-2) (s := generatedS L)
      (w := generatedW L) (Q := generatedQ L) μI activity prev.numbered
    have hc : generatedQ L*prev.rows ≤
        (graphRun (w := generatedW L) (Q := generatedQ L) hs hn hq edge L (k+1)).cols := h.2
    have hr : 1 ≤ prev.rows := law_size_pos prev.rowLaw
    have hbase : generatedN L ≤ generatedQ L := Nat.le_self_pow (by decide : 6 ≠ 0) _
    have hmul : generatedQ L ≤ generatedQ L*prev.rows := by
      simpa using Nat.mul_le_mul_left (generatedQ L) hr
    exact (hbase.trans (hmul.trans hc)).trans (le_max_right _ _)

theorem publicGraphRunFrom_size_bounds (p : SourceConstants) (floor : ℕ) {n m : ℕ}
    (hn : 0 < n) (hlow : n ≤ 2*m) (hdegree : 2*m ≤ p.degree*n)
    (edge : Fin m → Bool → Fin n) (k : ℕ) :
    let L := publicLogFrom p floor n m hn hlow hdegree
    let R := publicGraphRunFrom p floor hn hlow hdegree edge k
    floor^2 ≤ (Paper2.SquarePadding.side R.rows R.cols)^2 ∧
      R.rows*R.cols ≤ (generatedN L)^(516*supportAmplification^k) ∧
      R.squareWord.length ≤ (generatedN L)^(1040*supportAmplification^k) := by
  let L := publicLogFrom p floor n m hn hlow hdegree
  let N := generatedN L
  let R := publicGraphRunFrom p floor hn hlow hdegree edge k
  have ht := (publicLogFrom_spec p floor n m hn hlow hdegree).2
  have hs : 4 ≤ generatedS L := passing_s_ge_four _ _ _ _ _ ht
  have hN : 2 ≤ N := by have := hs.trans (generatedS_le_N L); omega
  have hN1 : 1 ≤ N := by omega
  haveI : NeZero (generatedS L) := ⟨by unfold generatedS; positivity⟩
  haveI : NeZero (generatedQ₂ L) := ⟨by unfold generatedQ₂ generatedN; positivity⟩
  haveI : NeZero (generatedW L) := ⟨by unfold generatedW generatedN; positivity⟩
  haveI : NeZero (generatedQ L) := ⟨by unfold generatedQ generatedN; positivity⟩
  have hnN : n ≤ N := (le_max_right floor n).trans (publicLogFrom_size p floor n m hn hlow hdegree)
  have hfN : floor ≤ N := (le_max_left floor n).trans (publicLogFrom_size p floor n m hn hlow hdegree)
  have hside : N ≤ Paper2.SquarePadding.side R.rows R.cols :=
    generatedGraphRun_public_side hs hn (passing_repetition_eq _ _ _ _ _ ht) edge k
  have hB : R.rows*R.cols ≤ N^(516*supportAmplification^k) :=
    generatedGraphRun_cells_power hs hn hnN (passing_repetition_eq _ _ _ _ _ ht) edge k
  have hlen := R.squareWord_length_rectangle
  have hBpow := Nat.pow_le_pow_left hB 2
  have hbase : 1 ≤ N^(516*supportAmplification^k) := Nat.one_le_pow _ _ hN1
  have h32 : 32 ≤ N^5 := by simpa using Nat.pow_le_pow_left hN 5
  have hA : 1 ≤ supportAmplification^k :=
    Nat.one_le_pow _ _ (by norm_num [supportAmplification])
  change floor^2 ≤ (Paper2.SquarePadding.side R.rows R.cols)^2 ∧
    R.rows*R.cols ≤ N^(516*supportAmplification^k) ∧
    R.squareWord.length ≤ N^(1040*supportAmplification^k)
  refine ⟨Nat.pow_le_pow_left (hfN.trans hside) 2, hB, ?_⟩
  calc
    R.squareWord.length ≤ 20*(R.rows*R.cols)^2+2 := hlen
    _ ≤ 32*(N^(516*supportAmplification^k))^2 := by nlinarith
    _ ≤ N^5*(N^(516*supportAmplification^k))^2 := Nat.mul_le_mul_right _ h32
    _ = N^(5+1032*supportAmplification^k) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      ring
    _ ≤ N^(1040*supportAmplification^k) := Nat.pow_le_pow_right (by omega) (by omega)

end CurrentAdditive.V39GeneratedConstruction

#print axioms CurrentAdditive.V39GeneratedConstruction.publicGraphRunFrom_size_bounds
