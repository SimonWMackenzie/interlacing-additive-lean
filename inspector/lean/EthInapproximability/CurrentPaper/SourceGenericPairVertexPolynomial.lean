import EthInapproximability.CurrentPaper.SourceGenericPairOnePolynomial

/-! Charged polynomial clock for all ordered pairs at one vertex. This
instantiates the finite-list absorption lemma with the checked physical
one-pair routine, including diagonal pairs and growing bank words. -/

namespace EthInapproximability.CurrentPaper.SourceGenericPairEnumeration

open SourceGenericPrefixMachine
open SourceBooleanPrefix.PairMachineComposition

def publicBase (n a q : Nat) : Nat :=
  4*n+a+ordinalBound n a+SourceBooleanEncoding.width a q+
    wordBound n a q+32

noncomputable def vertexEnvelope (n a q : Nat)
    (saved output count : List Bool) : Nat :=
  (a*a+1)*
    (oneCoefficient a q *
      (publicBase n a q+saved.length+output.length+count.length+
        (a*a)*(wordBound n a q+8)+1)^4+1)

theorem vertex_cost_le_poly {n a q : Nat} (v : Fin n)
    (saved output count : List Bool) :
    vertexCost a q v saved output count ≤
      vertexEnvelope n a q saved output count := by
  have hpayload : ∀ st : Fin a × Fin a,
      (payload q v st).length ≤ wordBound n a q := by
    intro ⟨s,t⟩
    exact pair_word_length_le q v s t
  have hstep : ∀ st : Fin a × Fin a, ∀ saved output count,
      PairOneMachine.cost (q := q) v st.1 st.2 saved output count ≤
        oneCoefficient a q *
          (publicBase n a q+saved.length+output.length+
            count.length+1)^4 := by
    intro ⟨s,t⟩ saved output count
    have hc := one_cost_le_poly (q := q) v s t saved output count
    have hs : oneSize n a q saved output count ≤
        publicBase n a q+saved.length+output.length+count.length+1 := by
      dsimp [oneSize,sourceSize,publicBase]
      omega
    exact hc.trans (Nat.mul_le_mul_left (oneCoefficient a q)
      (pow_le_pow_left₀ (by omega) hs 4))
  have h := listCost_mass_bound
    (fun st : Fin a × Fin a =>
      PairOneMachine.cost (q := q) v st.1 st.2)
    (payload q v) (pairs a) saved output count
    (publicBase n a q) (wordBound n a q)
    (oneCoefficient a q) 4 hpayload hstep
  simpa only [vertexCost,vertexEnvelope,pairs_length] using h

#print axioms vertex_cost_le_poly

end EthInapproximability.CurrentPaper.SourceGenericPairEnumeration
