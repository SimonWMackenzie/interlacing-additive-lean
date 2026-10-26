import CurrentAdditive.V40LawJobsClock

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

namespace CurrentAdditive.V40LawPairSplit
open EthInapproximability.CurrentPaper
open PhysicalProducer
open V40LawJobsClock
noncomputable section

def projectList (j : Fin 2) : BitMachine.Machine :=
  SourceListMachineOuterFramed.machine (projection j).machine

def projected (j : Fin 2) (xs : List (List Bool)) : List Bool :=
  SourceListEncoding.encode (xs.map (BankFieldProjection.result j))

theorem projectList_realizes (j : Fin 2) :
    Realizes (projectList j) SourceListEncoding.encode (projected j) := by
  let A := projection j
  let f := BankFieldProjection.result j
  let b := fun w : List Bool => A.coefficient*(w.length+1)^A.degree
  have hM (xs : List (List Bool)) : ∀w∈xs,A.machine.OutputsWithin w (f w) (b w) := by
    intro w _
    exact A.outputs w
  obtain ⟨C,d,hC⟩ := RatioMappedListPolynomial.clockCap_poly A.machine A.coefficient A.degree
  refine ⟨C,d,?_⟩
  intro xs
  apply BitMachine.outputsWithin_mono _
    (SourceListMachineOuterFramed.outputsWithin A.machine xs f b (hM xs))
  exact (V40LawListClock.clock_le_on A.machine f b A.coefficient A.degree xs
    (hM xs) (fun _ => le_rfl)).trans (hC _)

def duplicate : Producer := pair identity identity

def machine : BitMachine.Machine :=
  BitMachineComposition.composition
    (BitMachineComposition.composition
      (BitMachineComposition.composition duplicate.machine
        (V40LawBankMap.liftMachine (projectList 0)))
      AppendOrdinaryPrep.swap.machine)
    (V40LawBankMap.liftMachine (projectList 1))

def output (xs : List (List Bool)) : List Bool :=
  V40LawPacket.packet (projected 0 xs) (projected 1 xs)

/-- One actual list is copied once, then its first and second record fields
are mapped in place. Both output lists retain every original position. -/
theorem realizes : Realizes machine SourceListEncoding.encode output := by
  have h0 : Realizes duplicate.machine SourceListEncoding.encode
      (fun xs => V40LawPacket.packet (SourceListEncoding.encode xs)
        (SourceListEncoding.encode xs)) := by
    simpa only [duplicate,pair_result,identity_result,packet_eq] using
      producer (pair identity identity) SourceListEncoding.encode
  have h1 := bank_map (projectList 0) SourceListEncoding.encode
    SourceListEncoding.encode (projected 0) (projectList_realizes 0)
  have h01 := V40LawJobsClock.compose duplicate.machine
    (V40LawBankMap.liftMachine (projectList 0)) _ _ _ h0 h1
  have hs : Realizes AppendOrdinaryPrep.swap.machine
      (fun xs => V40LawPacket.packet (SourceListEncoding.encode xs) (projected 0 xs))
      (fun xs => V40LawPacket.packet (projected 0 xs) (SourceListEncoding.encode xs)) := by
    simpa only [packet_eq,AppendOrdinaryPrep.swap_packet] using
      producer AppendOrdinaryPrep.swap
        (fun xs => V40LawPacket.packet (SourceListEncoding.encode xs) (projected 0 xs))
  have h012 := V40LawJobsClock.compose _ _ _ _ _ h01 hs
  exact V40LawJobsClock.compose _ _ _ _ _ h012
    (bank_map (projectList 1) (projected 0) SourceListEncoding.encode (projected 1)
      (projectList_realizes 1))

theorem projected_pairs (j : Fin 2) (xs : List (List Bool × List Bool)) :
    projected j (xs.map (fun p => V40LawPacket.packet p.1 p.2)) =
      SourceListEncoding.encode (xs.map (fun p => if j=0 then p.1 else p.2)) := by
  simp only [projected,List.map_map,packet_eq,BankFieldProjection.result_encode]
  congr 1
  apply List.map_congr_left
  intro p _
  fin_cases j <;> simp

/-- Concrete decoder companions and exact factor-job lists are extracted
from the same physical record stream, without recomputing either order. -/
theorem outputs_polynomial : ∃ C d : ℕ, ∀ xs : List (List Bool × List Bool),
    machine.OutputsWithin
      (SourceListEncoding.encode (xs.map (fun p => V40LawPacket.packet p.1 p.2)))
      (V40LawPacket.packet (SourceListEncoding.encode (xs.map Prod.fst))
        (SourceListEncoding.encode (xs.map Prod.snd)))
      (C*((SourceListEncoding.encode
        (xs.map (fun p => V40LawPacket.packet p.1 p.2))).length+1)^d) := by
  obtain ⟨C,d,h⟩ := realizes
  refine ⟨C,d,?_⟩
  intro xs
  simpa only [output,projected_pairs,↓reduceIte,show (1 : Fin 2)≠0 by decide] using
    h (xs.map (fun p => V40LawPacket.packet p.1 p.2))

#print axioms projectList_realizes
#print axioms realizes
#print axioms outputs_polynomial
end
end CurrentAdditive.V40LawPairSplit
