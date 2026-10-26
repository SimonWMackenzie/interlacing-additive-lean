import CurrentAdditive.GaussBranchSelect
import CurrentAdditive.RationalRouterAllInputJoin
import CurrentAdditive.RationalCanonicalCallback
import CurrentAdditive.GaussForeignSubroutine

set_option maxRecDepth 4096

/-!
The first arithmetic call of a physical Gauss cell.  The branch selector
extracts the correct numerator and the pivot from the full twelve-field cell
packet.  The joined quotient machine then parses the nested pair and performs
signed rational division.  Both parts are fixed TM2 machines and the joined
machine halts in polynomial time on every bitword.
-/

namespace CurrentAdditive.GaussCellQuotient

open EthInapproximability.CurrentPaper
open CurrentAdditive.CodeDCodec
open Turing TM2.Stmt
open BitMachine BitMachineEncoding

noncomputable def machine : BitMachine.Machine :=
  BitMachineComposition.composition
    GaussPhysical.GaussBranchSelect.machine
    RationalRouterQuotientJoin.signedQuotientMachine

def result (input : List Bool) : List Bool :=
  RationalRouterAllInputJoin.quotientResult
    (GaussPhysical.GaussBranchSelect.result input)

theorem polytime : BitMachine.Polytime result := by
  simpa only [result, Function.comp_def] using
    BitMachineComposition.polytime_comp
      GaussPhysical.GaussBranchSelect.polytime
      RationalRouterAllInputJoin.quotient_polytime

theorem exact_cell (flag : Bool)
    (current column row pivot : RawRat) :
    result (GaussPhysical.cellPacket flag current column row pivot) =
      encodeRawRat
        (RationalProductSignedPhysical.quotientRat
          (if flag then row else column) pivot) := by
  simp only [result, GaussPhysical.GaussBranchSelect.result_cellPacket]
  exact RationalRouterAllInputJoin.quotient_result_pair
    (if flag then row else column) pivot

theorem outputs_cell (flag : Bool)
    (current column row pivot : RawRat) :
    ∃ t, machine.OutputsWithin
      (GaussPhysical.cellPacket flag current column row pivot)
      (encodeRawRat
        (RationalProductSignedPhysical.quotientRat
          (if flag then row else column) pivot)) t := by
  have hq := RationalRouterAllInputJoin.quotient_outputs_all
    (GaussPhysical.GaussBranchSelect.result
      (GaussPhysical.cellPacket flag current column row pivot))
  rw [GaussPhysical.GaussBranchSelect.result_cellPacket] at hq
  rw [RationalRouterAllInputJoin.quotient_result_pair] at hq
  have hc :=
    BitMachineComposition.composition_outputsWithin
      GaussPhysical.GaussBranchSelect.machine
      RationalRouterQuotientJoin.signedQuotientMachine
      (GaussPhysical.GaussBranchSelect.outputs_cellPacket
        flag current column row pivot) hq
  exact ⟨_, by simpa only [machine] using hc⟩

noncomputable def canonicalMachine : BitMachine.Machine :=
  BitMachineComposition.composition
    GaussPhysical.GaussBranchSelect.machine
    RationalCanonicalCallback.quotientMachine

noncomputable def canonicalResult (input : List Bool) : List Bool :=
  RationalCanonicalCallback.quotientResult
    (GaussPhysical.GaussBranchSelect.result input)

theorem canonical_polytime : BitMachine.Polytime canonicalResult := by
  simpa only [canonicalResult, Function.comp_def] using
    BitMachineComposition.polytime_comp
      GaussPhysical.GaussBranchSelect.polytime
      RationalCanonicalCallback.quotient_polytime

theorem canonical_exact_cell (flag : Bool)
    (current column row pivot : RawRat)
    (hnum : (if flag then row else column).Valid)
    (hpivot : pivot.Valid)
    (hpivot_num : 0 < EncodedCommunication.bitsValue pivot.numerator) :
    canonicalResult (GaussPhysical.cellPacket flag current column row pivot) =
      encodeRawRat (CodeDCanonicalSource.rawOfRat
        ((if flag then row else column).value / pivot.value)) := by
  simp only [canonicalResult,
    GaussPhysical.GaussBranchSelect.result_cellPacket]
  exact RationalCanonicalCallback.quotient_result_pair
    (if flag then row else column) pivot hnum hpivot hpivot_num

theorem canonical_outputs_cell (flag : Bool)
    (current column row pivot : RawRat)
    (hnum : (if flag then row else column).Valid)
    (hpivot : pivot.Valid)
    (hpivot_num : 0 < EncodedCommunication.bitsValue pivot.numerator) :
    ∃ t, canonicalMachine.OutputsWithin
      (GaussPhysical.cellPacket flag current column row pivot)
      (encodeRawRat (CodeDCanonicalSource.rawOfRat
        ((if flag then row else column).value / pivot.value))) t := by
  obtain ⟨c,hq⟩ := RationalCanonicalCallback.quotient_outputs_pair
    (if flag then row else column) pivot hnum hpivot hpivot_num
  have hc := BitMachineComposition.composition_outputsWithin
    GaussPhysical.GaussBranchSelect.machine
    RationalCanonicalCallback.quotientMachine
    (GaussPhysical.GaussBranchSelect.outputs_cellPacket
      flag current column row pivot) hq
  exact ⟨_, by simpa only [canonicalMachine] using hc⟩

theorem canonical_context_run (flag : Bool)
    (current column row pivot : RawRat)
    (hnum : (if flag then row else column).Valid)
    (hpivot : pivot.Valid)
    (hpivot_num : 0 < EncodedCommunication.bitsValue pivot.numerator)
    (context : Fin 12 → List Bool) :
    ∃ t u, u ≤ t ∧
      let c := ((advance
        (GaussPhysical.GaussForeignSubroutine.program canonicalMachine))^[u])
          (GaussPhysical.GaussForeignSubroutine.startCfg
            canonicalMachine
            (GaussPhysical.cellPacket flag current column row pivot)
            context)
      c.l = some (.inr 0) ∧
      (∀ j : Fin 12, c.stk (.inr j) = context j) ∧
      c.stk (.inl canonicalMachine.output) =
        encodeRawRat (CodeDCanonicalSource.rawOfRat
          ((if flag then row else column).value / pivot.value)) := by
  obtain ⟨t,ht⟩ := canonical_outputs_cell
    flag current column row pivot hnum hpivot hpivot_num
  obtain ⟨u,hu,hc⟩ :=
    GaussPhysical.GaussForeignSubroutine.run_preserves_context
      canonicalMachine
      (GaussPhysical.cellPacket flag current column row pivot)
      (encodeRawRat (CodeDCanonicalSource.rawOfRat
        ((if flag then row else column).value / pivot.value)))
      context t ht
  exact ⟨t,u,hu,hc⟩

#print axioms polytime
#print axioms exact_cell
#print axioms outputs_cell
#print axioms canonical_polytime
#print axioms canonical_exact_cell
#print axioms canonical_outputs_cell
#print axioms canonical_context_run

end CurrentAdditive.GaussCellQuotient
