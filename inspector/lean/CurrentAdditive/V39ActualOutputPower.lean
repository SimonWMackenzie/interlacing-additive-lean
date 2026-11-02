import CurrentAdditive.V39ActualSquare
import CurrentAdditive.V39SupportPower
import CurrentAdditive.V39UniformResource

/-! The literal current functional constructor has the claimed uniform
power form for its actual padded table and canonical binary output length.
The bound is unconditional in the graph's YES/NO promise and uniform in k.
This counts the output; it does not replace the separately missing physical
printer and rational intermediate bit-clock theorem.
-/

namespace CurrentAdditive.V39GeneratedConstruction

open Paper2 V38Schedule
open CurrentAdditive.V39UniformResource
open CurrentAdditive.LiteralEdgeEncoder

theorem generatedS_le_N (L : ℕ) : generatedS L ≤ generatedN L := by
  unfold generatedS generatedN
  apply Nat.pow_le_pow_right (by decide)
  unfold quarterCeil
  omega

theorem graphSeed_supportEnvelope (L n : ℕ) (hN : 4 ≤ generatedN L)
    (hn : n ≤ generatedN L) :
    supportEnvelope (generatedS L-2) (generatedQ₂ L) (generatedS L)
      (generatedW L) (generatedQ L) (4*generatedS L*(n+(generatedS L-3)))
      (storedLookupSeed L) ≤ (generatedN L)^516 := by
  let N := generatedN L
  have hN1 : 1 ≤ N := by omega
  have hN2 : 2 ≤ N := by omega
  have hs : generatedS L ≤ N := generatedS_le_N L
  have hN512 : N ≤ N^512 := Nat.le_self_pow (by decide) N
  have hp (a : ℕ) (ha : a ≤ 512) : N^a ≤ N^512 :=
    Nat.pow_le_pow_right (by omega) ha
  have hq₁ : generatedS L-2 ≤ N^512 := (Nat.sub_le _ _).trans (hs.trans hN512)
  have hq₂ : generatedQ₂ L ≤ N^512 := hp 4 (by decide)
  have hs' : generatedS L ≤ N^512 := hs.trans hN512
  have hw : generatedW L ≤ N^512 := hp 2 (by decide)
  have hQ : generatedQ L ≤ N^512 := hp 6 (by decide)
  have hni : 4*generatedS L*(n+(generatedS L-3)) ≤ N^512 := by
    have hb : 4*generatedS L*(n+(generatedS L-3)) ≤ 8*N^2 := by
      calc
        _ ≤ 4*N*(N+N) := Nat.mul_le_mul (Nat.mul_le_mul_left 4 hs)
          (Nat.add_le_add hn ((Nat.sub_le _ _).trans hs))
        _ = 8*N^2 := by ring
    have h8 : 8 ≤ N^3 := by simpa using Nat.pow_le_pow_left hN2 3
    calc
      _ ≤ 8*N^2 := hb
      _ ≤ N^3*N^2 := Nat.mul_le_mul_right _ h8
      _ = N^5 := by rw [← pow_add]
      _ ≤ N^512 := hp 5 (by decide)
  have hc : Nat.clog 2 N = L := by
    exact Nat.clog_pow 2 L (by decide)
  have hr : 2^(Paper2.LookupSeed.width L) ≤ N^256 := by
    have h := Paper2.LookupSeed.rows_source_bound N hN
    rw [hc] at h
    exact h.le
  have hwidth : Paper2.LookupSeed.width L ≤ N^256 :=
    (self_le_two_pow _).trans hr
  have hcell : 2^(Paper2.LookupSeed.width L)*Paper2.LookupSeed.width L ≤ N^512 := by
    have h := Nat.mul_le_mul hr hwidth
    simpa only [← pow_add] using h
  have h4 : 4 ≤ N^512 := by
    exact (by omega : 4 ≤ N).trans hN512
  have hsum : supportEnvelope (generatedS L-2) (generatedQ₂ L) (generatedS L)
      (generatedW L) (generatedQ L) (4*generatedS L*(n+(generatedS L-3)))
      (storedLookupSeed L) ≤ 8*N^512 := by
    change generatedS L-2+generatedQ₂ L+generatedS L+generatedW L+generatedQ L+
      4*generatedS L*(n+(generatedS L-3))+
      2^(Paper2.LookupSeed.width L)*Paper2.LookupSeed.width L+4 ≤ 8*N^512
    omega
  have h16 : 8 ≤ N^4 := by
    have h := Nat.pow_le_pow_left hN2 4
    norm_num at h
    omega
  calc
    _ ≤ 8*N^512 := hsum
    _ ≤ N^4*N^512 := Nat.mul_le_mul_right _ h16
    _ = N^516 := by rw [← pow_add]

theorem generatedGraphRun_cells_power {L n m r : ℕ}
    [NeZero (generatedS L)] [NeZero (generatedQ₂ L)]
    [NeZero (generatedW L)] [NeZero (generatedQ L)]
    (hs : 4 ≤ generatedS L) (hn : 0 < n) (hnN : n ≤ generatedN L)
    (hq : generatedQ₂ L = LiteralEdgeEncoder.Width (generatedS L) m r)
    (edge : Fin m → Bool → Fin n) (k : ℕ) :
    (graphRun (w := generatedW L) (Q := generatedQ L) hs hn hq edge L k).rows *
      (graphRun (w := generatedW L) (Q := generatedQ L) hs hn hq edge L k).cols ≤
        (generatedN L)^(516*supportAmplification^k) := by
  have hN : 4 ≤ generatedN L := hs.trans (generatedS_le_N L)
  haveI : NeZero (generatedS L-2) := ⟨by omega⟩
  have hg := supportEnvelope_iterate (q₁ := generatedS L-2) (s := generatedS L)
    (w := generatedW L) (Q := generatedQ L) (indexedItemLaw _ n hs hn)
    (graphActivity (by omega) hq edge) (storedLookupSeed L) k
  have hb := graphSeed_supportEnvelope L n hN hnN
  have h := hg.trans (Nat.pow_le_pow_left hb (supportAmplification^k))
  rw [← pow_mul] at h
  change supportEnvelope (generatedS L-2) (generatedQ₂ L) (generatedS L)
    (generatedW L) (generatedQ L) (4*generatedS L*(n+(generatedS L-3)))
      (graphRun (w := generatedW L) (Q := generatedQ L) hs hn hq edge L k) ≤
        (generatedN L)^(516*supportAmplification^k) at h
  dsimp only [supportEnvelope] at h
  omega

theorem publicGraphRun_cells_power (p : SourceConstants) {n m : ℕ}
    (hn : 0 < n) (hlow : n ≤ 2*m) (hdegree : 2*m ≤ p.degree*n)
    (edge : Fin m → Bool → Fin n) (k : ℕ) :
    let L := publicLog p n m hn hlow hdegree
    let R := publicGraphRun p hn hlow hdegree edge k
    R.rows*R.cols ≤ (generatedN L)^(516*supportAmplification^k) := by
  let L := publicLog p n m hn hlow hdegree
  have ht := (publicLog_spec p n m hn hlow hdegree).2
  have hs : 4 ≤ generatedS L := passing_s_ge_four _ _ _ _ _ ht
  have hN : 4 ≤ generatedN L := hs.trans (generatedS_le_N L)
  haveI : NeZero (generatedS L) := ⟨by unfold generatedS; positivity⟩
  haveI : NeZero (generatedS L-2) := ⟨by omega⟩
  haveI : NeZero (generatedQ₂ L) := ⟨by unfold generatedQ₂ generatedN; positivity⟩
  haveI : NeZero (generatedW L) := ⟨by unfold generatedW generatedN; positivity⟩
  haveI : NeZero (generatedQ L) := ⟨by unfold generatedQ generatedN; positivity⟩
  have hg := supportEnvelope_iterate (q₁ := generatedS L-2) (s := generatedS L)
    (w := generatedW L) (Q := generatedQ L) (indexedItemLaw _ n hs hn)
    (graphActivity (by omega) (passing_repetition_eq _ _ _ _ _ ht) edge)
    (storedLookupSeed L) k
  have hb := graphSeed_supportEnvelope L n hN (publicLog_size p n m hn hlow hdegree)
  have h := hg.trans (Nat.pow_le_pow_left hb (supportAmplification^k))
  rw [← pow_mul] at h
  change supportEnvelope (generatedS L-2) (generatedQ₂ L) (generatedS L)
    (generatedW L) (generatedQ L) (4*generatedS L*(n+(generatedS L-3)))
      (publicGraphRun p hn hlow hdegree edge k) ≤
        (generatedN L)^(516*supportAmplification^k) at h
  change (publicGraphRun p hn hlow hdegree edge k).rows *
    (publicGraphRun p hn hlow hdegree edge k).cols ≤ (generatedN L)^(516*supportAmplification^k)
  exact (by dsimp [supportEnvelope] at h; omega)

/-- One effective exponent and power-of-two amplification bound the actual
encoded estimator input. This is an output-size theorem for the current
constructor, not an execution-time assumption in a purported endpoint. -/
theorem publicGraphWord_length_power (p : SourceConstants) {n m : ℕ}
    (hn : 0 < n) (hlow : n ≤ 2*m) (hdegree : 2*m ≤ p.degree*n)
    (edge : Fin m → Bool → Fin n) (k : ℕ) :
    let L := publicLog p n m hn hlow hdegree
    (publicGraphWord p hn hlow hdegree edge k).length ≤
      (generatedN L)^(1040*supportAmplification^k) := by
  let L := publicLog p n m hn hlow hdegree
  let N := generatedN L
  let R := publicGraphRun p hn hlow hdegree edge k
  have hs := passing_s_ge_four _ _ _ _ _ (publicLog_spec p n m hn hlow hdegree).2
  have hN : 2 ≤ N := by have := hs.trans (generatedS_le_N L); omega
  have hN1 : 1 ≤ N := by omega
  have hB : R.rows*R.cols ≤ N^(516*supportAmplification^k) :=
    publicGraphRun_cells_power p hn hlow hdegree edge k
  have hlen := R.squareWord_length_rectangle
  have hBpow := Nat.pow_le_pow_left hB 2
  have hbase : 1 ≤ N^(516*supportAmplification^k) := Nat.one_le_pow _ _ hN1
  have h32 : 32 ≤ N^5 := by simpa using Nat.pow_le_pow_left hN 5
  have hA : 1 ≤ supportAmplification^k := by
    exact Nat.one_le_pow _ _ (by norm_num [supportAmplification])
  change R.squareWord.length ≤ N^(1040*supportAmplification^k)
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

#print axioms CurrentAdditive.V39GeneratedConstruction.publicGraphRun_cells_power
#print axioms CurrentAdditive.V39GeneratedConstruction.publicGraphWord_length_power
