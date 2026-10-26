import CurrentAdditive.V42GraphRuntime
import CurrentAdditive.V39PublicHeaderBound
import CurrentAdditive.V39ActualETHNumerics

namespace CurrentAdditive.V42ActualLower
open Paper2 V42Schedule V39GeneratedConstruction V39UniformResource
open Workspace.Types.CommComplexity CurrentAdditive.LiteralEdgeEncoder

def threshold (k K : ℕ) : ℕ := LookupSeed.exponent (4*k)+1+K*(40*k)
def entryCount (R : StoredMatrix) : ℕ := (SquarePadding.side R.rows R.cols)^2

theorem seed_numerical_bounds (L : ℕ) :
    L   ≤   2^(LookupSeed.width L)*LookupSeed.width L ∧
    LookupSeed.exponent L+1   ≤   2^(LookupSeed.width L)*LookupSeed.width L := by
  have hw:=LookupSeed.width_admissible L
  have hwpos:0<LookupSeed.width L := by omega
  have ht:1  ≤  2^(LookupSeed.width L) := Nat.one_le_two_pow
  have htwo:2  ≤  2^(LookupSeed.width L) :=
    (by decide : 2  ≤  2^1).trans (Nat.pow_le_pow_right (by decide) hwpos)
  have hexp:LookupSeed.exponent L  ≤  LookupSeed.width L := self_le_two_pow _
  constructor <;> nlinarith

section
variable (k : ℕ) (hk : 2  ≤  k)
local instance : NeZero (s k) := ⟨(s_pos k).ne'⟩
local instance : NeZero (q₂ k (4*k)) := ⟨(q₂_pos k (4*k)).ne'⟩
local instance : NeZero (w k) := ⟨(w_pos k).ne'⟩
local instance : NeZero (Q k) := ⟨(Q_pos k).ne'⟩
variable {n m rep : ℕ} (hn:0<n)
  (hwidth:q₂ k (4*k)=LiteralEdgeEncoder.Width (s k) m rep)
  (edge:Fin m→Bool→Fin n)

def run (K:ℕ) := V42GeneratedConstruction.graphRun k (4*k) hk hn hwidth edge (4*k) K

theorem header_bounds (K:ℕ) :
    let T:=entryCount (run k hk hn hwidth edge K)
    K  ≤  T ∧ threshold k K  ≤  11*T^2 ∧ 2*threshold k K+K  ≤  23*T^2 := by
  have hs:=V42GeneratedConstruction.s_ge_four k hk
  have hg:=graphRun_entries_growth (w:=w k) (Q:=Q k) hs hn hwidth edge (4*k) K
  let R:=run k hk hn hwidth edge K
  let E:=R.rows*R.cols
  have hg':(w k*q₂ k (4*k)*Q k)^K*(2^(LookupSeed.width (4*k))*LookupSeed.width (4*k))  ≤  E := hg
  have hfac:2  ≤  w k*q₂ k (4*k)*Q k := by
    have hw:1  ≤  w k := by have h:=w_pos k;omega
    have hq:1  ≤  q₂ k (4*k) := by have h:=q₂_pos k (4*k);omega
    have hQ:2  ≤  Q k := by
      exact (by decide : 2  ≤  2^1).trans (Nat.pow_le_pow_right (by decide) (show 1  ≤  24*k by omega))
    have hwq:1  ≤  w k*q₂ k (4*k) := by simpa using Nat.mul_le_mul hw hq
    exact hQ.trans (by simpa using Nat.mul_le_mul_right (Q k) hwq)
  have hseed:=seed_numerical_bounds (4*k)
  have hseedpos:1  ≤  2^(LookupSeed.width (4*k))*LookupSeed.width (4*k) := by
    have h:=LookupSeed.width_admissible (4*k)
    have hp:1  ≤  2^(LookupSeed.width (4*k)) := Nat.one_le_two_pow
    nlinarith
  have hpow:1  ≤  (w k*q₂ k (4*k)*Q k)^K := Nat.one_le_pow _ _ (by omega)
  have hbase:2^(LookupSeed.width (4*k))*LookupSeed.width (4*k)  ≤  E := by nlinarith
  have hEpos:1  ≤  E := hseedpos.trans hbase
  have hK:K  ≤  E := by
    calc
      K  ≤  2^K := self_le_two_pow K
      _   ≤  (w k*q₂ k (4*k)*Q k)^K := Nat.pow_le_pow_left hfac K
      _   ≤  E := by nlinarith
  have hL:4*k  ≤  E := hseed.1.trans hbase
  have hd:LookupSeed.exponent (4*k)+1  ≤  E := hseed.2.trans hbase
  have hB:threshold k K  ≤  11*E^2 := by
    have hh:40*k  ≤  10*E := by omega
    have hm:=Nat.mul_le_mul hK hh
    unfold threshold
    nlinarith
  let T:=entryCount R
  have hET:E  ≤  T := by
    have h:=Nat.mul_le_mul (SquarePadding.rows_le_side R.rows R.cols) (SquarePadding.cols_le_side R.rows R.cols)
    simpa only [E,T,entryCount,pow_two] using h
  have hTpos:1  ≤  T := hEpos.trans hET
  have hKT:K  ≤  T := hK.trans hET
  have hBT:threshold k K  ≤  11*T^2 := hB.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hET 2))
  have hKsq:K  ≤  T^2 := hKT.trans (Nat.le_self_pow (by decide : 2≠0) T)
  change K  ≤  T ∧ threshold k K  ≤  11*T^2 ∧ 2*threshold k K+K  ≤  23*T^2
  exact ⟨hKT,hBT,by omega⟩

theorem public_side (K:ℕ) :
    2^(4*k)  ≤  SquarePadding.side (run k hk hn hwidth edge K).rows (run k hk hn hwidth edge K).cols := by
  have hs:=V42GeneratedConstruction.s_ge_four k hk
  haveI:NeZero (s k-2):=⟨by omega⟩
  let μI:=indexedItemLaw (s k) n hs hn
  let activity:=graphActivity (by omega : 3  ≤  s k) hwidth edge
  apply le_trans ?_ (SquarePadding.max_le_side _ _)
  cases K with
  | zero =>
    have hw:=LookupSeed.width_admissible (4*k)
    have hp:=Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (show 4*k  ≤  LookupSeed.width (4*k) by omega)
    exact hp.trans (le_max_left _ _)
  | succ K =>
    let prev:=StoredMatrix.iterate (q₁:=s k-2) (s:=s k) (w:=w k) (Q:=Q k) μI activity K (storedLookupSeed (4*k))
    have h:=executableStep_dimension_lower (q₁:=s k-2) (s:=s k) (w:=w k) (Q:=Q k) μI activity prev.numbered
    have hc:Q k*prev.rows  ≤  (run k hk hn hwidth edge (K+1)).cols := h.2
    have hr:1  ≤  prev.rows := law_size_pos prev.rowLaw
    have hbase:2^(4*k)  ≤  Q k := Nat.pow_le_pow_right (by decide) (by omega)
    have hm:Q k  ≤  Q k*prev.rows := by simpa using Nat.mul_le_mul_left (Q k) hr
    exact (hbase.trans (hm.trans hc)).trans (le_max_right _ _)
end

#print axioms header_bounds
#print axioms public_side
end CurrentAdditive.V42ActualLower



