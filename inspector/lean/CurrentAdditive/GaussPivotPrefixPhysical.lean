import CurrentAdditive.GaussPivotPairEq
import CurrentAdditive.GaussPrefixTrue
import CurrentAdditive.GaussHeaderStrip
import EthInapproximability.CurrentPaper.BankFieldProjection
import EthInapproximability.CurrentPaper.SourceListMachineOuterRun
import EthInapproximability.CurrentPaper.BitMachineComposition

/-! A fixed TM2 pipeline from the Gauss Bank4 state packet to the unary
length of its initial run of diagonal pivot pairs. The semantic identification
of this length with the first free column is proved separately. -/

namespace CurrentAdditive.GaussPivotPrefixPhysical

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication

def pivotWords (ps : List (Nat × Nat)) : List (List Bool) :=
  ps.map fun p => GaussPivotPairEq.pairPacket p.1 p.2

def pivotFlags (ps : List (Nat × Nat)) : List Bool :=
  ps.map fun p => decide (p.1 = p.2)

def pivotListPacket (ps : List (Nat × Nat)) : List Bool :=
  SourceListEncoding.encode (pivotWords ps)

def stateBank (matrix : List Bool) (r c : Nat)
    (ps : List (Nat × Nat)) : BitMachineBankCodec.Bank 4 :=
  ![matrix, List.replicate r true, List.replicate c true,
    pivotListPacket ps]

theorem pair_bound (r c : Nat) :
    5 * ((GaussPivotPairEq.pairPacket r c).length + 1) + 1 +
      (max r c + 2) ≤
    7 * ((GaussPivotPairEq.pairPacket r c).length + 1) + 3 := by
  have hr := BitMachineBankCodec.word_length_le_encode
    (![List.replicate r true, List.replicate c true] :
      BitMachineBankCodec.Bank 2) (0 : Fin 2)
  have hc := BitMachineBankCodec.word_length_le_encode
    (![List.replicate r true, List.replicate c true] :
      BitMachineBankCodec.Bank 2) (1 : Fin 2)
  have hr' : r ≤ (GaussPivotPairEq.pairPacket r c).length := by
    simpa [GaussPivotPairEq.pairPacket] using hr
  have hc' : c ≤ (GaussPivotPairEq.pairPacket r c).length := by
    simpa [GaussPivotPairEq.pairPacket] using hc
  omega

theorem pair_outputs (r c : Nat) :
    GaussPivotPairEq.machine.OutputsWithin
      (GaussPivotPairEq.pairPacket r c) [decide (r = c)]
      (7 * ((GaussPivotPairEq.pairPacket r c).length + 1) + 3) := by
  obtain ⟨t, ht, hh, ho⟩ := GaussPivotPairEq.outputs_pairPacket r c
  exact ⟨t, ht.trans (pair_bound r c), hh, ho⟩

theorem joined_flags (ps : List (Nat × Nat)) :
    SourceListMachineOuter.joined (pivotWords ps) GaussPivotPairEq.result =
      pivotFlags ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      rcases p with ⟨r,c⟩
      simpa [pivotWords, pivotFlags, SourceListMachineOuter.joined_cons,
        GaussPivotPairEq.result_pairPacket] using ih

def pairClock (x : List Bool) : Nat := 7 * (x.length + 1) + 3

theorem outer_outputs (ps : List (Nat × Nat)) :
    (SourceListMachineOuter.machine GaussPivotPairEq.machine).OutputsWithin
      (pivotListPacket ps)
      (natField ps.length ++ pivotFlags ps)
      (SourceListMachineOuter.canonicalBound GaussPivotPairEq.machine
        (pivotWords ps) GaussPivotPairEq.result pairClock) := by
  unfold pivotListPacket
  have h := SourceListMachineOuter.canonical_outputsWithin
    GaussPivotPairEq.machine (pivotWords ps) GaussPivotPairEq.result
    pairClock (by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      rcases p with ⟨r,c⟩
      simpa [pairClock, GaussPivotPairEq.result_pairPacket] using
        pair_outputs r c)
  rw [joined_flags] at h
  simpa only [pivotWords, List.length_map] using h

noncomputable def selector : BitMachine.Machine :=
  BitMachineComposition.composition (BankFieldProjection.machine (3 : Fin 4))
    (SourceListMachineOuter.machine GaussPivotPairEq.machine)

noncomputable def withoutHeader : BitMachine.Machine :=
  BitMachineComposition.composition selector GaussHeaderStrip.machine

noncomputable def machine : BitMachine.Machine :=
  BitMachineComposition.composition withoutHeader GaussPrefixTrue.machine

def stateWord (matrix : List Bool) (r c : Nat)
    (ps : List (Nat × Nat)) : List Bool :=
  BitMachineBankCodec.encode (stateBank matrix r c ps)

theorem state_projection (matrix : List Bool) (r c : Nat)
    (ps : List (Nat × Nat)) :
    (BankFieldProjection.machine (3 : Fin 4)).OutputsWithin
      (stateWord matrix r c ps)
      (pivotListPacket ps)
      (12 * ((stateWord matrix r c ps).length + 1)) := by
  simpa [stateWord, stateBank, BankFieldProjection.result_encode] using
    (BankFieldProjection.outputs (3 : Fin 4) (stateWord matrix r c ps))

theorem selector_outputs (matrix : List Bool) (r c : Nat)
    (ps : List (Nat × Nat)) :
    selector.OutputsWithin (stateWord matrix r c ps)
      (natField ps.length ++ pivotFlags ps)
      (12 * ((stateWord matrix r c ps).length + 1) +
        2 * (pivotListPacket ps).length + 2 +
        SourceListMachineOuter.canonicalBound GaussPivotPairEq.machine
          (pivotWords ps) GaussPivotPairEq.result pairClock) := by
  exact BitMachineComposition.composition_outputsWithin
    (BankFieldProjection.machine (3 : Fin 4))
    (SourceListMachineOuter.machine GaussPivotPairEq.machine)
    (state_projection matrix r c ps) (outer_outputs ps)

theorem withoutHeader_outputs (matrix : List Bool) (r c : Nat)
    (ps : List (Nat × Nat)) :
    withoutHeader.OutputsWithin (stateWord matrix r c ps) (pivotFlags ps)
      (12 * ((stateWord matrix r c ps).length + 1) +
        2 * (pivotListPacket ps).length + 2 +
        SourceListMachineOuter.canonicalBound GaussPivotPairEq.machine
          (pivotWords ps) GaussPivotPairEq.result pairClock +
        2 * (natField ps.length ++ pivotFlags ps).length + 2 +
        (2 * (natField ps.length ++ pivotFlags ps).length + 3)) := by
  exact BitMachineComposition.composition_outputsWithin
    selector GaussHeaderStrip.machine
    (selector_outputs matrix r c ps)
    (GaussHeaderStrip.outputs_valid ps.length (pivotFlags ps))

def prefixCount (ps : List (Nat × Nat)) : Nat :=
  (pivotFlags ps).takeWhile id |>.length

theorem outputs_state (matrix : List Bool) (r c : Nat)
    (ps : List (Nat × Nat)) :
    machine.OutputsWithin (stateWord matrix r c ps)
      (List.replicate (prefixCount ps) true)
      (12 * ((stateWord matrix r c ps).length + 1) +
        2 * (pivotListPacket ps).length + 2 +
        SourceListMachineOuter.canonicalBound GaussPivotPairEq.machine
          (pivotWords ps) GaussPivotPairEq.result pairClock +
        2 * (natField ps.length ++ pivotFlags ps).length + 2 +
        (2 * (natField ps.length ++ pivotFlags ps).length + 3) +
        2 * (pivotFlags ps).length + 2 +
        ((pivotFlags ps).length + 1)) := by
  simpa [machine, prefixCount, GaussPrefixTrue.result] using
    (BitMachineComposition.composition_outputsWithin
      withoutHeader GaussPrefixTrue.machine
      (withoutHeader_outputs matrix r c ps)
      (GaussPrefixTrue.outputs (pivotFlags ps)))

#print axioms outputs_state

end CurrentAdditive.GaussPivotPrefixPhysical
