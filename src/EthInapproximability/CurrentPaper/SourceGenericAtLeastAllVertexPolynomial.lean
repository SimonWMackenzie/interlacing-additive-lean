import EthInapproximability.CurrentPaper.SourceGenericAtLeastVertexPolynomial

/-! Polynomial charge for the checked n-vertex physical at-least loop,
`2*n+2+AtLeastLoop.tailCost n a q saved output count 0 n`, exactly the
bound carried by `AtLeastLoop.run` / `PrefixLoopEndpoint.atLeast_run`.
It charges the per-vertex source word growth (`atWordBound` per vertex),
unary count growth `3*a+2` per vertex, the per-vertex check/increment
handoffs, the unary copy prelude and the final idle check. The coefficient
is fixed by `a,q` only; no positivity or bank premise is added. -/

namespace EthInapproximability.CurrentPaper.SourceGenericPrefixClock

open SourceGenericPrefixMachine SourceBooleanPrefix
open SourceClauseEncoding EncodedCNF
set_option maxHeartbeats 2000000

theorem atLeast_loop_word_length_le (n a q k : Nat) :
    (AtLeastLoop.word n a q k).length ≤ atWordBound n a q := by
  by_cases h : k < n
  · rw [AtLeastLoop.word_of_lt n a q k h,List.length_reverse]
    exact atLeast_word_length_le (q := q) (⟨k,h⟩ : Fin n)
  · simp [AtLeastLoop.word,h]

theorem at_savedAt_length_le (n a q k : Nat) (saved : List Bool) :
    (AtLeastLoop.savedAt n a q saved k).length ≤
      saved.length+k*atWordBound n a q := by
  induction k with
  | zero => simp [AtLeastLoop.savedAt]
  | succ k ih =>
      have hw := atLeast_loop_word_length_le n a q k
      simp only [AtLeastLoop.savedAt,List.length_append]
      rw [Nat.succ_mul]
      omega

theorem at_countAt_length (a : Nat) (count : List Bool) (k : Nat) :
    (AtLeastLoop.countAt a count k).length = (3*a+2)*k+count.length := by
  simp [AtLeastLoop.countAt]

theorem atVertexEnvelope_mono (n a q : Nat) {S O C S' O' C' : Nat}
    (hS : S ≤ S') (hO : O ≤ O') (hC : C ≤ C') :
    atVertexEnvelope n a q S O C ≤ atVertexEnvelope n a q S' O' C' := by
  unfold atVertexEnvelope atSize
  gcongr

/-- Per-vertex bound at the largest bank reached in the loop. -/
noncomputable def atLoopVertexBound (n a q S O C : Nat) : Nat :=
  atVertexEnvelope n a q (S+n*atWordBound n a q) O (C+(3*a+2)*n)

noncomputable def atLoopEnvelope (n a q S O C : Nat) : Nat :=
  (n+1)*(2+atLoopVertexBound n a q S O C)+2*n+2

theorem at_tail_cost_le {n a q k r : Nat}
    (saved output count : List Bool) (hkr : k+r=n) :
    AtLeastLoop.tailCost n a q saved output count k r ≤
      (r+1)*(2+atLoopVertexBound n a q
        saved.length output.length count.length) := by
  induction r generalizing k with
  | zero =>
      simp only [AtLeastLoop.tailCost]
      omega
  | succ r ih =>
      have hlt : k<n := by omega
      have hcall : AtLeastLoop.callCost n a q saved output count k ≤
          atLoopVertexBound n a q
            saved.length output.length count.length := by
        rw [AtLeastLoop.callCost,dif_pos hlt]
        refine (at_vertex_cost_le_poly (q := q) (⟨k,hlt⟩ : Fin n)
          _ output _).trans ?_
        apply atVertexEnvelope_mono
        · have hs := at_savedAt_length_le n a q k saved
          have hk : k*atWordBound n a q ≤ n*atWordBound n a q :=
            Nat.mul_le_mul_right _ (by omega)
          omega
        · exact le_rfl
        · rw [at_countAt_length]
          have hk : (3*a+2)*k ≤ (3*a+2)*n :=
            Nat.mul_le_mul_left _ (by omega)
          omega
      have htail := ih (k := k+1) (by omega)
      simp only [AtLeastLoop.tailCost]
      have e : (r+1+1)*(2+atLoopVertexBound n a q
            saved.length output.length count.length) =
          (r+1)*(2+atLoopVertexBound n a q
            saved.length output.length count.length) +
          (2+atLoopVertexBound n a q
            saved.length output.length count.length) := by ring
      omega

/-- Explicit envelope for the whole at-least loop, exactly the charged
bound `2*n+2+tailCost` of the checked loop run. -/
theorem atLeast_loop_cost_le (n a q : Nat)
    (saved output count : List Bool) :
    2*n+2+AtLeastLoop.tailCost n a q saved output count 0 n ≤
      atLoopEnvelope n a q saved.length output.length count.length := by
  have h := at_tail_cost_le (n := n) (a := a) (q := q) (k := 0) (r := n)
    saved output count (by omega)
  unfold atLoopEnvelope
  omega

/-! ## Closed form `C(a,q) * (n+|saved|+|output|+|count|+1)^9` -/

def atWordCoefficient (a q : Nat) : Nat :=
  (3*a+2)*(12*a+6*SourceBooleanEncoding.width a q+18)

theorem atWordBound_le (n a q X : Nat) (hn : n+1 ≤ X) :
    atWordBound n a q ≤ atWordCoefficient a q * X := by
  have hX : 1 ≤ X := by omega
  have hnX : n ≤ X := by omega
  have h1 : n*a ≤ X*a := Nat.mul_le_mul_right a hnX
  have h2 : n*(SourceBooleanEncoding.width a q+1) ≤
      X*(SourceBooleanEncoding.width a q+1) := Nat.mul_le_mul_right _ hnX
  have h3 : (a+1)*1 ≤ (a+1)*X := Nat.mul_le_mul_left _ hX
  have hv : atVariableBound n a q ≤
      (2*a+SourceBooleanEncoding.width a q+2)*X := by
    unfold atVariableBound
    nlinarith only [h1,h2,h3]
  have h6 : 6*atVariableBound n a q+6 ≤
      (12*a+6*SourceBooleanEncoding.width a q+18)*X := by
    nlinarith only [hv,hX]
  unfold atWordBound atWordCoefficient
  calc
    (3*a+2)*(6*atVariableBound n a q+6) ≤
        (3*a+2)*((12*a+6*SourceBooleanEncoding.width a q+18)*X) :=
      Nat.mul_le_mul_left _ h6
    _ = (3*a+2)*(12*a+6*SourceBooleanEncoding.width a q+18)*X := by ring

def atSizeCoefficient (a q : Nat) : Nat :=
  2*atWordCoefficient a q+8*a+SourceBooleanEncoding.width a q+16

theorem atLoopSize_le (n a q S O C X : Nat) (hXd : n+S+O+C+1 ≤ X) :
    atSize n a q (S+n*atWordBound n a q+atWordBound n a q) O
        (C+(3*a+2)*n+3*a+2) ≤
      atSizeCoefficient a q * X^2 := by
  have hX : 1 ≤ X := by omega
  have hXX : X ≤ X^2 := by nlinarith
  have hwb := atWordBound_le n a q X (by omega)
  have hnwb : n*atWordBound n a q ≤ atWordCoefficient a q * X^2 := by
    calc
      n*atWordBound n a q ≤ X*(atWordCoefficient a q * X) :=
        Nat.mul_le_mul (by omega) hwb
      _ = atWordCoefficient a q * X^2 := by ring
  have hwb2 : atWordBound n a q ≤ atWordCoefficient a q * X^2 :=
    hwb.trans (Nat.mul_le_mul_left _ hXX)
  have hc : (5*a+SourceBooleanEncoding.width a q+8)*1 ≤
      (5*a+SourceBooleanEncoding.width a q+8)*X^2 :=
    Nat.mul_le_mul_left _ (by omega)
  have h3an : (3*a+2)*n ≤ (3*a+2)*X^2 :=
    Nat.mul_le_mul_left _ (by omega)
  unfold atSize atSizeCoefficient
  nlinarith only [hXX,hXd,hnwb,hwb2,hc,h3an]

noncomputable def atLoopCoefficient (a q : Nat) : Nat :=
  (2*atUnitCoefficient a q+a*atGateCoefficient a q)*
    (atSizeCoefficient a q)^4+a+7

/-- Pure arithmetic absorption used for the closed forms. -/
theorem loop_closed_aux (n a K c Z X : Nat) (hXn : n+1 ≤ X)
    (hZ : Z ≤ c*X^2) :
    (n+1)*(2+(K*Z^4+a+3))+2*n+2 ≤ (K*c^4+a+7)*X^9 := by
  have hX : 1 ≤ X := by omega
  have hZ4 : Z^4 ≤ c^4*X^8 := by
    calc
      Z^4 ≤ (c*X^2)^4 := pow_le_pow_left₀ (Nat.zero_le _) hZ 4
      _ = c^4*X^8 := by ring
  have hX8 : 1 ≤ X^8 := Nat.one_le_pow _ _ hX
  have hKZ := Nat.mul_le_mul_left K hZ4
  have hV : 2+(K*Z^4+a+3) ≤ (K*c^4+a+5)*X^8 := by
    have h1 : (a+5)*1 ≤ (a+5)*X^8 := Nat.mul_le_mul_left _ hX8
    have e : (K*c^4+a+5)*X^8 = K*(c^4*X^8)+(a+5)*X^8 := by ring
    omega
  have hprod := Nat.mul_le_mul hXn hV
  have hX9 : X ≤ X^9 := by
    calc
      X = X*1 := by ring
      _ ≤ X*X^8 := Nat.mul_le_mul_left _ hX8
      _ = X^9 := by ring
  have e2 : X*((K*c^4+a+5)*X^8) = (K*c^4+a+5)*X^9 := by ring
  have e3 : (K*c^4+a+7)*X^9 = (K*c^4+a+5)*X^9+2*X^9 := by ring
  omega

theorem atLoopEnvelope_le_closed (n a q S O C X : Nat)
    (hXd : n+S+O+C+1 ≤ X) :
    atLoopEnvelope n a q S O C ≤ atLoopCoefficient a q * X^9 := by
  have hZ := atLoopSize_le n a q S O C X hXd
  have hunf : atLoopEnvelope n a q S O C =
      (n+1)*(2+((2*atUnitCoefficient a q+a*atGateCoefficient a q)*
        (atSize n a q (S+n*atWordBound n a q+atWordBound n a q) O
          (C+(3*a+2)*n+3*a+2))^4+a+3))+2*n+2 := rfl
  rw [hunf]
  unfold atLoopCoefficient
  exact loop_closed_aux n a _ _ _ X (by omega) hZ

/-- Closed-form all-n polynomial clock for the at-least loop. -/
theorem atLeast_loop_cost_le_closed (n a q : Nat)
    (saved output count : List Bool) :
    2*n+2+AtLeastLoop.tailCost n a q saved output count 0 n ≤
      atLoopCoefficient a q *
        (n+saved.length+output.length+count.length+1)^9 :=
  (atLeast_loop_cost_le n a q saved output count).trans
    (atLoopEnvelope_le_closed n a q _ _ _ _ le_rfl)

#print axioms atLeast_loop_word_length_le
#print axioms at_savedAt_length_le
#print axioms at_countAt_length
#print axioms atVertexEnvelope_mono
#print axioms at_tail_cost_le
#print axioms atLeast_loop_cost_le
#print axioms atWordBound_le
#print axioms atLoopSize_le
#print axioms loop_closed_aux
#print axioms atLoopEnvelope_le_closed
#print axioms atLeast_loop_cost_le_closed

end EthInapproximability.CurrentPaper.SourceGenericPrefixClock
