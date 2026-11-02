import EthInapproximability.CurrentPaper.SourceGenericAtLeastAllVertexPolynomial
import EthInapproximability.CurrentPaper.SourceGenericPairAllVertexPolynomial
import EthInapproximability.CurrentPaper.GenericPrefixCompositeEndpoint

/-! Polynomial clock for the whole fixed-(a,q) generic prefix work program
`PrefixComposite.program a q` (all at-least vertices, then the physical
transfer, then all ordered-pair vertices including diagonals), exactly as
charged by `PrefixComposite.cost`:

* the at-least loop `2*n+2+AtLeastLoop.tailCost ... 0 n`, via the new
  `atLeast_loop_cost_le`;
* the transfer `2*(n+atSaved.length+atCount.length)+8` and its handoff;
* the pair loop `2*n+2+PairVertexLoop.tailCost` at the transferred bank
  `atSaved`/`atCount`, via the privately checked `pair_loop_cost_le`;
* both sequencing handoffs.

The transferred bank is charged at its true length: `atSaved` grows by at
most `atWordBound` per vertex and `atCount` by exactly `3*a+2` per vertex.
Coefficients depend only on the fixed `a,q`. No premise on `a`, `q`, the
bank or the run is added; `output` is arbitrary in the clock theorems and
`[]` only in the endpoint run it is combined with. -/

namespace EthInapproximability.CurrentPaper.SourceGenericPrefixClock

open Turing BitMachineEncoding
open SourceGenericPrefixMachine SourceBooleanPrefix
open SourceClauseEncoding EncodedCNF
set_option maxHeartbeats 2000000

/-! ## The transferred at-least bank -/

theorem atSaved_eq_savedAt (n a q : Nat) (saved : List Bool) :
    PrefixComposite.atSaved n a q saved =
      AtLeastLoop.savedAt n a q saved n := by
  rw [AtLeastLoop.savedAt_eq_prefix,PrefixLoopSource.atLeast_fields]
  rfl

theorem atSaved_length_le (n a q : Nat) (saved : List Bool) :
    (PrefixComposite.atSaved n a q saved).length ≤
      saved.length+n*atWordBound n a q := by
  rw [atSaved_eq_savedAt]
  exact at_savedAt_length_le n a q n saved

theorem atCount_length (n a : Nat) (count : List Bool) :
    (PrefixComposite.atCount n a count).length =
      (3*a+2)*n+count.length := by
  simp [PrefixComposite.atCount]

/-! ## Length form of the checked pair-loop envelope -/

noncomputable def pairLoopEnvelopeLen (n a q S O C : Nat) : Nat :=
  (n+1)*(2+(a*a+1)*
    (SourceGenericPairEnumeration.oneCoefficient a q *
      (SourceGenericPairEnumeration.publicBase n a q+
        (n*SourceGenericPairEnumeration.vertexWordBound n a q+S)+O+
        ((8*(a*a))*n+C)+
        (a*a)*(SourceGenericPairEnumeration.wordBound n a q+8)+1)^4+1))+
    2*n+2

theorem pairLoopEnvelope_eq (n a q : Nat)
    (saved output count : List Bool) :
    SourceGenericPairEnumeration.pairLoopEnvelope n a q saved output count =
      pairLoopEnvelopeLen n a q saved.length output.length count.length := by
  simp only [SourceGenericPairEnumeration.pairLoopEnvelope,
    SourceGenericPairEnumeration.vertexEnvelope,
    SourceGenericPairEnumeration.maxSaved,
    SourceGenericPairEnumeration.maxCount,
    List.length_append,List.length_replicate,pairLoopEnvelopeLen]

theorem pairLoopEnvelopeLen_mono (n a q : Nat) {S O C S' O' C' : Nat}
    (hS : S ≤ S') (hO : O ≤ O') (hC : C ≤ C') :
    pairLoopEnvelopeLen n a q S O C ≤ pairLoopEnvelopeLen n a q S' O' C' := by
  unfold pairLoopEnvelopeLen
  gcongr

/-! ## Explicit composite envelope -/

noncomputable def compositeEnvelope (n a q S O C : Nat) : Nat :=
  atLoopEnvelope n a q S O C +
    (2*(n+(S+n*atWordBound n a q)+((3*a+2)*n+C))+8) + 1 +
    pairLoopEnvelopeLen n a q (S+n*atWordBound n a q) O ((3*a+2)*n+C) + 1

theorem composite_cost_le (n a q : Nat) (saved output count : List Bool) :
    PrefixComposite.cost n a q saved output count ≤
      compositeEnvelope n a q saved.length output.length count.length := by
  have hat := atLeast_loop_cost_le n a q saved output count
  have hpair := SourceGenericPairEnumeration.pair_loop_cost_le n a q
    (PrefixComposite.atSaved n a q saved) output
    (PrefixComposite.atCount n a count)
  rw [pairLoopEnvelope_eq] at hpair
  have hs := atSaved_length_le n a q saved
  have hc := atCount_length n a count
  have hmono := pairLoopEnvelopeLen_mono n a q
    (S := (PrefixComposite.atSaved n a q saved).length)
    (O := output.length)
    (C := (PrefixComposite.atCount n a count).length)
    (S' := saved.length+n*atWordBound n a q) (O' := output.length)
    (C' := (3*a+2)*n+count.length) hs le_rfl (le_of_eq hc)
  unfold PrefixComposite.cost compositeEnvelope
  omega

/-! ## Closed form: pair-loop constants -/

def pairOrdinalCoefficient (a : Nat) : Nat := 2*(a*a)+a+1

theorem ordinalBound_le (n a X : Nat) (hn : n+1 ≤ X) :
    SourceGenericPairEnumeration.ordinalBound n a ≤
      pairOrdinalCoefficient a * X := by
  have hX : 1 ≤ X := by omega
  have h1 : a*a*n ≤ a*a*X := Nat.mul_le_mul_left _ (by omega)
  have h2 : (a*a+a)*1 ≤ (a*a+a)*X := Nat.mul_le_mul_left _ hX
  unfold SourceGenericPairEnumeration.ordinalBound pairOrdinalCoefficient
  nlinarith only [h1,h2,hn]

def pairVariableCoefficient (a q : Nat) : Nat :=
  a+(pairOrdinalCoefficient a+1)*(SourceBooleanEncoding.width a q+1)+4

theorem variableBound_le (n a q X : Nat) (hn : n+1 ≤ X) :
    SourceGenericPairEnumeration.variableBound n a q ≤
      pairVariableCoefficient a q * X := by
  have hX : 1 ≤ X := by omega
  have ho := ordinalBound_le n a X hn
  have h1 : n*a ≤ X*a := Nat.mul_le_mul_right _ (by omega)
  have ho1 : SourceGenericPairEnumeration.ordinalBound n a+1 ≤
      (pairOrdinalCoefficient a+1)*X := by
    have e : (pairOrdinalCoefficient a+1)*X =
        pairOrdinalCoefficient a*X+X := by ring
    omega
  have h2 := Nat.mul_le_mul_right (SourceBooleanEncoding.width a q+1) ho1
  have h3 : 4*1 ≤ 4*X := Nat.mul_le_mul_left _ hX
  unfold SourceGenericPairEnumeration.variableBound pairVariableCoefficient
  nlinarith only [h1,h2,h3]

def pairWordCoefficient (a q : Nat) : Nat :=
  8*(6*pairVariableCoefficient a q+6)

theorem wordBound_le (n a q X : Nat) (hn : n+1 ≤ X) :
    SourceGenericPairEnumeration.wordBound n a q ≤
      pairWordCoefficient a q * X := by
  have hX : 1 ≤ X := by omega
  have hv := variableBound_le n a q X hn
  unfold SourceGenericPairEnumeration.wordBound pairWordCoefficient
  nlinarith only [hv,hX]

def pairBaseCoefficient (a q : Nat) : Nat :=
  4+a+pairOrdinalCoefficient a+SourceBooleanEncoding.width a q+
    pairWordCoefficient a q+32

theorem publicBase_le (n a q X : Nat) (hn : n+1 ≤ X) :
    SourceGenericPairEnumeration.publicBase n a q ≤
      pairBaseCoefficient a q * X := by
  have hX : 1 ≤ X := by omega
  have ho := ordinalBound_le n a X hn
  have hw := wordBound_le n a q X hn
  have h1 : (a+SourceBooleanEncoding.width a q+32)*1 ≤
      (a+SourceBooleanEncoding.width a q+32)*X :=
    Nat.mul_le_mul_left _ hX
  unfold SourceGenericPairEnumeration.publicBase pairBaseCoefficient
  nlinarith only [ho,hw,h1,hn]

def pairInnerCoefficient (a q : Nat) : Nat :=
  pairBaseCoefficient a q+2*(a*a)*pairWordCoefficient a q+
    atWordCoefficient a q+16*(a*a)+3*a+3

theorem pairInner_le (n a q S O C X : Nat) (hXd : n+S+O+C+1 ≤ X) :
    SourceGenericPairEnumeration.publicBase n a q+
        (n*SourceGenericPairEnumeration.vertexWordBound n a q+
          (S+n*atWordBound n a q))+O+
        ((8*(a*a))*n+((3*a+2)*n+C))+
        (a*a)*(SourceGenericPairEnumeration.wordBound n a q+8)+1 ≤
      pairInnerCoefficient a q * X^2 := by
  have hn : n+1 ≤ X := by omega
  have hX : 1 ≤ X := by omega
  have hXX : X ≤ X^2 := by nlinarith
  have hpb := (publicBase_le n a q X hn).trans
    (Nat.mul_le_mul_left (pairBaseCoefficient a q) hXX)
  have hwb := wordBound_le n a q X hn
  have hnv : n*SourceGenericPairEnumeration.vertexWordBound n a q ≤
      (a*a)*pairWordCoefficient a q*X^2 := by
    calc
      n*SourceGenericPairEnumeration.vertexWordBound n a q =
          n*((a*a)*SourceGenericPairEnumeration.wordBound n a q) := rfl
      _ ≤ X*((a*a)*(pairWordCoefficient a q*X)) :=
        Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ hwb)
      _ = (a*a)*pairWordCoefficient a q*X^2 := by ring
  have hnat : n*atWordBound n a q ≤ atWordCoefficient a q*X^2 := by
    calc
      n*atWordBound n a q ≤ X*(atWordCoefficient a q*X) :=
        Nat.mul_le_mul (by omega) (atWordBound_le n a q X hn)
      _ = atWordCoefficient a q*X^2 := by ring
  have h8 : (8*(a*a))*n ≤ (8*(a*a))*X^2 :=
    Nat.mul_le_mul_left _ (by omega)
  have h3 : (3*a+2)*n ≤ (3*a+2)*X^2 :=
    Nat.mul_le_mul_left _ (by omega)
  have haa : (a*a)*(SourceGenericPairEnumeration.wordBound n a q+8) ≤
      (a*a)*(pairWordCoefficient a q+8)*X^2 := by
    calc
      (a*a)*(SourceGenericPairEnumeration.wordBound n a q+8) ≤
          (a*a)*((pairWordCoefficient a q+8)*X^2) := by
        apply Nat.mul_le_mul_left
        have hw2 : SourceGenericPairEnumeration.wordBound n a q ≤
            pairWordCoefficient a q*X^2 :=
          hwb.trans (Nat.mul_le_mul_left _ hXX)
        have e : (pairWordCoefficient a q+8)*X^2 =
            pairWordCoefficient a q*X^2+8*X^2 := by ring
        omega
      _ = (a*a)*(pairWordCoefficient a q+8)*X^2 := by ring
  unfold pairInnerCoefficient
  nlinarith only [hpb,hnv,hnat,h8,h3,haa,hXd,hXX]

noncomputable def pairCoefficient (a q : Nat) : Nat :=
  (a*a+1)*(SourceGenericPairEnumeration.oneCoefficient a q*
    (pairInnerCoefficient a q)^4+1)+4

theorem pair_closed_aux (n A B c I X : Nat) (hXn : n+1 ≤ X)
    (hI : I ≤ c*X^2) :
    (n+1)*(2+A*(B*I^4+1))+2*n+2 ≤ (A*(B*c^4+1)+4)*X^9 := by
  have hX : 1 ≤ X := by omega
  have hI4 : I^4 ≤ c^4*X^8 := by
    calc
      I^4 ≤ (c*X^2)^4 := pow_le_pow_left₀ (Nat.zero_le _) hI 4
      _ = c^4*X^8 := by ring
  have hX8 : 1 ≤ X^8 := Nat.one_le_pow _ _ hX
  have hB := Nat.mul_le_mul_left B hI4
  have hin : B*I^4+1 ≤ (B*c^4+1)*X^8 := by
    have e : (B*c^4+1)*X^8 = B*(c^4*X^8)+X^8 := by ring
    omega
  have hA := Nat.mul_le_mul_left A hin
  have hV : 2+A*(B*I^4+1) ≤ (A*(B*c^4+1)+2)*X^8 := by
    have e : (A*(B*c^4+1)+2)*X^8 = A*((B*c^4+1)*X^8)+2*X^8 := by ring
    omega
  have hprod := Nat.mul_le_mul hXn hV
  have hX9 : X ≤ X^9 := by
    calc
      X = X*1 := by ring
      _ ≤ X*X^8 := Nat.mul_le_mul_left _ hX8
      _ = X^9 := by ring
  have e3 : X*((A*(B*c^4+1)+2)*X^8) = (A*(B*c^4+1)+2)*X^9 := by ring
  have e4 : (A*(B*c^4+1)+4)*X^9 = (A*(B*c^4+1)+2)*X^9+2*X^9 := by ring
  omega

theorem pairLoopEnvelopeLen_le_closed (n a q S O C X : Nat)
    (hXd : n+S+O+C+1 ≤ X) :
    pairLoopEnvelopeLen n a q (S+n*atWordBound n a q) O ((3*a+2)*n+C) ≤
      pairCoefficient a q * X^9 := by
  unfold pairLoopEnvelopeLen pairCoefficient
  exact pair_closed_aux n _ _ _ _ X (by omega)
    (pairInner_le n a q S O C X hXd)

/-! ## Closed form: transfer and the whole composite -/

def transferCoefficient (a q : Nat) : Nat :=
  2*atWordCoefficient a q+6*a+20

theorem transfer_le_closed (n a q S O C X : Nat) (hXd : n+S+O+C+1 ≤ X) :
    2*(n+(S+n*atWordBound n a q)+((3*a+2)*n+C))+8 ≤
      transferCoefficient a q * X^9 := by
  have hn : n+1 ≤ X := by omega
  have hX : 1 ≤ X := by omega
  have hXX : X ≤ X^2 := by nlinarith
  have hX7 : 1 ≤ X^7 := Nat.one_le_pow _ _ hX
  have hX29 : X^2 ≤ X^9 := by
    calc
      X^2 = X^2*1 := by ring
      _ ≤ X^2*X^7 := Nat.mul_le_mul_left _ hX7
      _ = X^9 := by ring
  have hnat : n*atWordBound n a q ≤ atWordCoefficient a q*X^2 := by
    calc
      n*atWordBound n a q ≤ X*(atWordCoefficient a q*X) :=
        Nat.mul_le_mul (by omega) (atWordBound_le n a q X hn)
      _ = atWordCoefficient a q*X^2 := by ring
  have h3 : (3*a+2)*n ≤ (3*a+2)*X^2 :=
    Nat.mul_le_mul_left _ (by omega)
  have hsq : 2*(n+(S+n*atWordBound n a q)+((3*a+2)*n+C))+8 ≤
      transferCoefficient a q * X^2 := by
    unfold transferCoefficient
    nlinarith only [hnat,h3,hXd,hXX]
  exact hsq.trans (Nat.mul_le_mul_left _ hX29)

noncomputable def compositeCoefficient (a q : Nat) : Nat :=
  atLoopCoefficient a q+transferCoefficient a q+pairCoefficient a q+2

theorem compositeEnvelope_le_closed (n a q S O C X : Nat)
    (hXd : n+S+O+C+1 ≤ X) :
    compositeEnvelope n a q S O C ≤ compositeCoefficient a q * X^9 := by
  have h1 := atLoopEnvelope_le_closed n a q S O C X hXd
  have h2 := transfer_le_closed n a q S O C X hXd
  have h3 := pairLoopEnvelopeLen_le_closed n a q S O C X hXd
  have hX9 : 1 ≤ X^9 := Nat.one_le_pow _ _ (by omega)
  have e : compositeCoefficient a q * X^9 =
      atLoopCoefficient a q * X^9+transferCoefficient a q * X^9+
        pairCoefficient a q * X^9+2*X^9 := by
    unfold compositeCoefficient
    ring
  unfold compositeEnvelope
  omega

/-- Closed-form polynomial clock for the whole generic prefix work
program: `PrefixComposite.cost ≤ C(a,q) * (n+|saved|+|output|+|count|+1)^9`. -/
theorem prefix_composite_cost_le_closed (n a q : Nat)
    (saved output count : List Bool) :
    PrefixComposite.cost n a q saved output count ≤
      compositeCoefficient a q *
        (n+saved.length+output.length+count.length+1)^9 :=
  (composite_cost_le n a q saved output count).trans
    (compositeEnvelope_le_closed n a q _ _ _ _ le_rfl)

/-- The checked physical endpoint `PrefixCompositeEndpoint.run_source`
(same program, same start and final banks) with its charged clock replaced
by the closed-form polynomial. -/
theorem run_source_polynomial (n a q : Nat) (saved count : List Bool) :
    ∃ T ≤ compositeCoefficient a q *
        (n+saved.length+count.length+1)^9,
      ((advance (PrefixComposite.program a q))^[T])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel (.inr .copyScan))),
          ((((AtLeastLoopCallback.callback a q).initial,none),
            ((none,none),none)),
            ((PairVertexLoopCallback.routine a q).initial,none)),
          PrefixTransferFrame.framedAt
            (PrefixLoopMachine.blank n 0 saved [] count [])⟩ :
          TM2.Cfg (fun _ : PrefixCopy.Stack => Bool) _ _) =
        ⟨none,
          ((((AtLeastLoopCallback.callback a q).initial,none),
            ((none,none),none)),
            ((PairVertexLoopCallback.routine a q).initial,none)),
          PrefixComposite.finalBank n a q saved [] count⟩ := by
  obtain ⟨T,hT,h⟩ := PrefixCompositeEndpoint.run_source n a q saved count
  refine ⟨T,hT.trans ?_,h⟩
  have hc := prefix_composite_cost_le_closed n a q saved [] count
  simpa only [List.length_nil,Nat.add_zero] using hc

#print axioms atSaved_eq_savedAt
#print axioms atSaved_length_le
#print axioms atCount_length
#print axioms pairLoopEnvelopeLen_mono
#print axioms pairLoopEnvelope_eq
#print axioms composite_cost_le
#print axioms ordinalBound_le
#print axioms variableBound_le
#print axioms wordBound_le
#print axioms publicBase_le
#print axioms pairInner_le
#print axioms pair_closed_aux
#print axioms pairLoopEnvelopeLen_le_closed
#print axioms transfer_le_closed
#print axioms compositeEnvelope_le_closed
#print axioms prefix_composite_cost_le_closed
#print axioms run_source_polynomial

end EthInapproximability.CurrentPaper.SourceGenericPrefixClock
