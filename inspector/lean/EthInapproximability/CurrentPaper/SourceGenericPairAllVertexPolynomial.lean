import EthInapproximability.CurrentPaper.SourceGenericPairVertexPolynomial
import EthInapproximability.CurrentPaper.GenericPairVertexLoop

/-! Polynomial charge for the checked n-vertex physical pair loop. The
coefficient is fixed by a,q; all growth of the saved and count words is
charged before bounding the recursive vertex callbacks. -/

namespace EthInapproximability.CurrentPaper.SourceGenericPairEnumeration

open SourceGenericPrefixMachine SourceBooleanPrefix
open SourceClauseEncoding EncodedCNF
open SourceBooleanPrefix.PairMachineComposition
set_option maxHeartbeats 2000000

def vertexWordBound (n a q : Nat) : Nat :=
  (a*a)*wordBound n a q

private theorem foldSaved_length_le {α : Type} (p : α → List Bool)
    (xs : List α) (saved : List Bool) (L : Nat)
    (hp : ∀ x, (p x).length ≤ L) :
    (foldSaved p xs saved).length ≤ saved.length+xs.length*L := by
  induction xs generalizing saved with
  | nil => simp [foldSaved]
  | cons x xs ih =>
      change (foldSaved p xs (p x ++ saved)).length ≤ _
      have h := ih (p x ++ saved)
      simp only [List.length_append,List.length_cons,Nat.add_mul,
        Nat.one_mul] at h ⊢
      have hx := hp x
      omega

theorem pair_vertex_word_length_le {n a q : Nat} (v : Fin n) :
    (PairVertexLoop.word n a q v.val).length ≤
      vertexWordBound n a q := by
  have hv := v.isLt
  rw [PairVertexLoop.word_of_lt n a q v.val hv]
  have hp : ∀ st : Fin a × Fin a,
      (payload q v st).length ≤ wordBound n a q := by
    intro ⟨s,t⟩
    exact pair_word_length_le q v s t
  have hf := foldSaved_length_le (payload q v) (pairs a) []
    (wordBound n a q) hp
  rw [foldSaved_source q v (pairs a) []] at hf
  simp only [List.append_nil,List.length_reverse,pairs_length] at hf
  simpa [vertexWordBound,vertexChains] using hf

theorem savedAt_length_le (n a q k : Nat) (saved : List Bool)
    (hk : k ≤ n) :
    (PairVertexLoop.savedAt n a q saved k).length ≤
      saved.length+k*vertexWordBound n a q := by
  induction k with
  | zero => simp [PairVertexLoop.savedAt]
  | succ k ih =>
      have hlt : k<n := by omega
      have hprev := ih (by omega)
      have hw := pair_vertex_word_length_le
        (a := a) (q := q) (⟨k,hlt⟩ : Fin n)
      rw [PairVertexLoop.savedAt]
      simp only [List.length_append]
      nlinarith only [hprev,hw]

def maxSaved (n a q : Nat) (saved : List Bool) : List Bool :=
  List.replicate (n*vertexWordBound n a q) true ++ saved

def maxCount (n a : Nat) (count : List Bool) : List Bool :=
  List.replicate ((8*(a*a))*n) true ++ count

noncomputable def pairLoopEnvelope (n a q : Nat)
    (saved output count : List Bool) : Nat :=
  (n+1)*(2+vertexEnvelope n a q
    (maxSaved n a q saved) output (maxCount n a count)) +
    2*n+2

theorem pair_tail_cost_le {n a q k r : Nat}
    (saved output count : List Bool) (hkr : k+r=n) :
    PairVertexLoop.tailCost n a q saved output count k r ≤
      (r+1)*(2+vertexEnvelope n a q
        (maxSaved n a q saved) output (maxCount n a count)) := by
  let E := vertexEnvelope n a q
    (maxSaved n a q saved) output (maxCount n a count)
  induction r generalizing k with
  | zero =>
      change 1 ≤ (0+1)*(2+E)
      omega
  | succ r ih =>
      have hlt : k<n := by omega
      have hk : k≤n := by omega
      have hnext : k+1+r=n := by omega
      have hs := savedAt_length_le n a q k saved hk
      have hc : (PairVertexLoop.countAt a count k).length ≤
          (maxCount n a count).length := by
        dsimp [PairVertexLoop.countAt,maxCount]
        simp only [List.length_append,List.length_replicate]
        have hkn : k≤n := by omega
        exact Nat.add_le_add_right
          (Nat.mul_le_mul_left (8*(a*a)) hkn) _
      have hs' : (PairVertexLoop.savedAt n a q saved k).length ≤
          (maxSaved n a q saved).length := by
        dsimp [maxSaved]
        simp only [List.length_append,List.length_replicate]
        have hkn : k≤n := by omega
        have hmul := Nat.mul_le_mul_right (vertexWordBound n a q) hkn
        omega
      have he : vertexEnvelope n a q
          (PairVertexLoop.savedAt n a q saved k) output
          (PairVertexLoop.countAt a count k) ≤ E := by
        dsimp [E,vertexEnvelope]
        gcongr
      have hcall : PairVertexLoop.callCost n a q saved output count k ≤ E := by
        rw [PairVertexLoop.callCost,dif_pos hlt]
        exact (vertex_cost_le_poly (q := q) (⟨k,hlt⟩ : Fin n)
          _ output _).trans he
      have htail := ih hnext
      rw [PairVertexLoop.tailCost]
      nlinarith only [hcall,htail]

theorem pair_loop_cost_le (n a q : Nat)
    (saved output count : List Bool) :
    2*n+2+PairVertexLoop.tailCost n a q saved output count 0 n ≤
      pairLoopEnvelope n a q saved output count := by
  have h := pair_tail_cost_le (n := n) (a := a) (q := q)
    (k := 0) (r := n)
    saved output count (by omega)
  dsimp only [pairLoopEnvelope]
  omega

#print axioms pair_vertex_word_length_le
#print axioms pair_loop_cost_le

end EthInapproximability.CurrentPaper.SourceGenericPairEnumeration
