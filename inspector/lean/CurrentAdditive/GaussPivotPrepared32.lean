import CurrentAdditive.GaussPivotJoin32

/-!
The branch adapter and physical pivot-list join agree on all four prepared
state fields. This theorem starts after the physical pair/header/body workers
have installed their checked outputs on banks 30 and 27. The join itself is
run here, rather than replacing bank 7 by a semantic update.
-/

namespace CurrentAdditive.GaussPivotPrepared32

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open CurrentAdditive.GaussControlTrace
open CurrentAdditive.GaussBranchFields32
open Turing BitMachineEncoding

abbrev Stack := Fin 32

def pivotState {m k : Nat} (s : State m k)
    (B' : Fin m → Fin k → ℚ) (rf : Fin m) (cf : Fin k) : State m k :=
  ⟨B',s.r+1,s.c+1,s.pivots++[(rf,cf)]⟩

def afterCounters (S : Stack → List Bool) : Stack → List Bool :=
  Function.update (Function.update (after3 .pivot S) 5
    (true :: (after3 .pivot S) 5)) 6
    (true :: (after3 .pivot S) 6)

theorem pivot_fields_before_join {m k : Nat}
    (s : State m k) (B' : Fin m → Fin k → ℚ)
    (S : Stack → List Bool)
    (h : ParsedState s S)
    (h22 : S 22 = CurrentAdditive.GaussPhysical.encodeTypedMatrix B') :
    (afterCounters S) 4 =
        CurrentAdditive.GaussPhysical.encodeTypedMatrix B' ∧
      (afterCounters S) 5 = List.replicate (s.r+1) true ∧
      (afterCounters S) 6 = List.replicate (s.c+1) true := by
  have h0 := copied_field .pivot S 0 h.destinations
  have h1 := copied_field .pivot S 1 h.destinations
  have h2 := copied_field .pivot S 2 h.destinations
  constructor
  · simpa [afterCounters,source,dest] using h0.trans h22
  constructor
  · have hr := congrArg (List.cons true) (h1.trans h.row)
    simpa [afterCounters,source,dest,List.replicate_succ] using hr
  · have hc := congrArg (List.cons true) (h2.trans h.column)
    simpa [afterCounters,source,dest,List.replicate_succ] using hc

theorem physical_prepared_pivot {m k : Nat}
    (s : State m k) (B' : Fin m → Fin k → ℚ)
    (rf : Fin m) (cf : Fin k)
    (S : Stack → List Bool)
    (h : ParsedState s S)
    (h22 : S 22 = CurrentAdditive.GaussPhysical.encodeTypedMatrix B')
    (h30 : (afterCounters S) 30 =
      natField (s.pivots++[(rf,cf)]).length)
    (h27 : (afterCounters S) 27 = SourceListEncoding.fields
      ((s.pivots++[(rf,cf)]).map pivotPacket))
    (h24 : (afterCounters S) 24 = [])
    (h31 : (afterCounters S) 31 = []) :
    ∃ t ≤ ((afterCounters S) 7).length+1 +
        (2*(natField (s.pivots++[(rf,cf)]).length).length+3) +
        (4*(natField (s.pivots++[(rf,cf)]).length).length+2*
          (SourceListEncoding.fields
            ((s.pivots++[(rf,cf)]).map pivotPacket)).length+7),
      (GaussPivotJoin32.run t
        ⟨some .clear7,((),none),afterCounters S⟩).l = some .done ∧
      GaussBranchFields32.preparedBank
        (GaussPivotJoin32.run t
          ⟨some .clear7,((),none),afterCounters S⟩).stk =
        stateBank (pivotState s B' rf cf) := by
  let ps := s.pivots++[(rf,cf)]
  obtain ⟨t,ht,hl,hpacket,hpres⟩ :=
    GaussPivotJoin32.physical_join_pivots ps (afterCounters S)
      h30 h27 h24 h31
  obtain ⟨hmatrix,hrow,hcol⟩ :=
    pivot_fields_before_join s B' S h h22
  refine ⟨t,ht,hl,?_⟩
  funext p
  fin_cases p
  · have hp := hpres 0
    simpa [GaussBranchFields32.preparedBank,dest,stateBank,
      pivotState,ps] using hp.trans hmatrix
  · have hp := hpres 1
    simpa [GaussBranchFields32.preparedBank,dest,stateBank,
      pivotState,ps] using hp.trans hrow
  · have hp := hpres 2
    simpa [GaussBranchFields32.preparedBank,dest,stateBank,
      pivotState,ps] using hp.trans hcol
  · simpa [GaussBranchFields32.preparedBank,dest,stateBank,
      pivotState,ps] using hpacket

#print axioms pivot_fields_before_join
#print axioms physical_prepared_pivot

end CurrentAdditive.GaussPivotPrepared32
