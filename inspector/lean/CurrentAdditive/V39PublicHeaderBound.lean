import CurrentAdditive.V39ActualSquare
import CurrentAdditive.V39SupportLower
import CurrentAdditive.V39UniformResource

/-! Charge the current public midpoint against the number of entries in the
actual padded table. The proof uses exact one-coordinate marginals of the
same computed sources, not a profile, promise, or desired final cost.
-/

namespace CurrentAdditive.V39GeneratedConstruction

open Paper2 V38Schedule
open CurrentAdditive.LiteralEdgeEncoder
open CurrentAdditive.V39UniformResource

variable {s n m r q₂ w Q : ℕ} [NeZero s] [NeZero q₂] [NeZero w] [NeZero Q]

theorem graphRun_entries_growth (hs : 4 ≤ s) (hn : 0 < n)
    (hq : q₂ = LiteralEdgeEncoder.Width s m r)
    (edge : Fin m → Bool → Fin n) (L k : ℕ) :
    (w*q₂*Q)^k*(2^(Paper2.LookupSeed.width L)*Paper2.LookupSeed.width L) ≤
      (graphRun (w := w) (Q := Q) hs hn hq edge L k).rows *
      (graphRun (w := w) (Q := Q) hs hn hq edge L k).cols := by
  haveI : NeZero (s-2) := ⟨by omega⟩
  exact storedIterate_entries_lower (q₁ := s-2) (s := s) (w := w) (Q := Q)
    (indexedItemLaw s n hs hn) (graphActivity (by omega) hq edge)
    (storedLookupSeed L) k

private theorem seed_numerical_bounds (L : ℕ) :
    L ≤ 2^(Paper2.LookupSeed.width L)*Paper2.LookupSeed.width L ∧
    Paper2.LookupSeed.exponent L+1 ≤
      2^(Paper2.LookupSeed.width L)*Paper2.LookupSeed.width L := by
  have hw := Paper2.LookupSeed.width_admissible L
  have hwpos : 0 < Paper2.LookupSeed.width L := by omega
  have htwopos : 1 ≤ 2^(Paper2.LookupSeed.width L) := Nat.one_le_two_pow
  have htwo : 2 ≤ 2^(Paper2.LookupSeed.width L) := by
    exact (by decide : 2 ≤ 2^1).trans
      (Nat.pow_le_pow_right (by decide) hwpos)
  have hexp : Paper2.LookupSeed.exponent L ≤ Paper2.LookupSeed.width L :=
    self_le_two_pow _
  constructor <;> nlinarith

theorem publicGraphRun_header_bounds (p : SourceConstants) {n m : ℕ}
    (hn : 0 < n) (hlow : n ≤ 2*m) (hdegree : 2*m ≤ p.degree*n)
    (edge : Fin m → Bool → Fin n) (k : ℕ) :
    let R := publicGraphRun p hn hlow hdegree edge k
    let T := (Paper2.SquarePadding.side R.rows R.cols)^2
    k ≤ T ∧ publicGraphThreshold p n m hn hlow hdegree k ≤ 15*T^2 ∧
      2*publicGraphThreshold p n m hn hlow hdegree k+k ≤ 31*T^2 := by
  let L := publicLog p n m hn hlow hdegree
  have ht := (publicLog_spec p n m hn hlow hdegree).2
  have hs := passing_s_ge_four _ _ _ _ _ ht
  haveI : NeZero (generatedS L) := ⟨by unfold generatedS; positivity⟩
  haveI : NeZero (generatedQ₂ L) := ⟨by unfold generatedQ₂ generatedN; positivity⟩
  haveI : NeZero (generatedW L) := ⟨by unfold generatedW generatedN; positivity⟩
  haveI : NeZero (generatedQ L) := ⟨by unfold generatedQ generatedN; positivity⟩
  have hg := graphRun_entries_growth (w := generatedW L) (Q := generatedQ L)
    hs hn (passing_repetition_eq _ _ _ _ _ ht) edge L k
  let R := publicGraphRun p hn hlow hdegree edge k
  let E := R.rows*R.cols
  have hg' : (generatedW L*generatedQ₂ L*generatedQ L)^k*
      (2^(Paper2.LookupSeed.width L)*Paper2.LookupSeed.width L) ≤ E := hg
  have hLpos : 0 < L := by
    by_contra h
    have hzero : L = 0 := by omega
    have h : 4 ≤ generatedS L := hs
    rw [hzero] at h
    norm_num [generatedS, quarterCeil] at h
  have hN : 2 ≤ generatedN L := by
    exact (by decide : 2 ≤ 2^1).trans
      (Nat.pow_le_pow_right (by decide) hLpos)
  have hfac : 2 ≤ generatedW L*generatedQ₂ L*generatedQ L := by
    have hw : 1 ≤ generatedW L := Nat.one_le_pow _ _ (by omega)
    have hq₂ : 1 ≤ generatedQ₂ L := Nat.one_le_pow _ _ (by omega)
    have hq : 2 ≤ generatedQ L :=
      hN.trans (Nat.le_self_pow (by decide : 6 ≠ 0) _)
    have hwq : 1 ≤ generatedW L*generatedQ₂ L := by
      simpa only [one_mul] using Nat.mul_le_mul hw hq₂
    exact hq.trans (by simpa only [one_mul] using Nat.mul_le_mul_right (generatedQ L) hwq)
  have hseed := seed_numerical_bounds L
  have hseedpos : 1 ≤ 2^(Paper2.LookupSeed.width L)*Paper2.LookupSeed.width L := by
    have h := Paper2.LookupSeed.width_admissible L
    have hp : 1 ≤ 2^(Paper2.LookupSeed.width L) := Nat.one_le_two_pow
    nlinarith
  have hpow : 1 ≤ (generatedW L*generatedQ₂ L*generatedQ L)^k :=
    Nat.one_le_pow _ _ (by omega)
  have hbase : 2^(Paper2.LookupSeed.width L)*Paper2.LookupSeed.width L ≤ E := by
    nlinarith [Nat.mul_le_mul_right
      (2^(Paper2.LookupSeed.width L)*Paper2.LookupSeed.width L) hpow]
  have hEpos : 1 ≤ E := hseedpos.trans hbase
  have hk : k ≤ E := by
    calc
      k ≤ 2^k := self_le_two_pow k
      _ ≤ (generatedW L*generatedQ₂ L*generatedQ L)^k :=
        Nat.pow_le_pow_left hfac k
      _ ≤ E := by nlinarith
  have hL : L ≤ E := hseed.1.trans hbase
  have hd : Paper2.LookupSeed.exponent L+1 ≤ E := hseed.2.trans hbase
  have hqceil : quarterCeil L ≤ L := by unfold quarterCeil; omega
  have hB : publicGraphThreshold p n m hn hlow hdegree k ≤ 15*E^2 := by
    change Paper2.LookupSeed.exponent L+1+k*(12*L+2*quarterCeil L) ≤ _
    have hh : 12*L+2*quarterCeil L ≤ 14*E := by omega
    have hmul := Nat.mul_le_mul hk hh
    nlinarith
  let T := (Paper2.SquarePadding.side R.rows R.cols)^2
  have hET : E ≤ T := by
    have h := Nat.mul_le_mul (Paper2.SquarePadding.rows_le_side R.rows R.cols)
      (Paper2.SquarePadding.cols_le_side R.rows R.cols)
    simpa only [E, T, pow_two] using h
  have hTpos : 1 ≤ T := hEpos.trans hET
  have hkT : k ≤ T := hk.trans hET
  have hBT : publicGraphThreshold p n m hn hlow hdegree k ≤ 15*T^2 :=
    hB.trans (Nat.mul_le_mul_left 15 (Nat.pow_le_pow_left hET 2))
  change k ≤ T ∧ publicGraphThreshold p n m hn hlow hdegree k ≤ 15*T^2 ∧
    2*publicGraphThreshold p n m hn hlow hdegree k+k ≤ 31*T^2
  have hksq : k ≤ T^2 := hkT.trans (Nat.le_self_pow (by decide : 2 ≠ 0) T)
  exact ⟨hkT, hBT, by omega⟩

end CurrentAdditive.V39GeneratedConstruction

#print axioms CurrentAdditive.V39GeneratedConstruction.publicGraphRun_header_bounds
