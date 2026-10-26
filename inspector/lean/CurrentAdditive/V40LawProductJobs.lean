import CurrentAdditive.V40LawCartesianRows
import CurrentAdditive.V40LawJobOrder
import CurrentAdditive.V40LawJobsRouting
import CurrentAdditive.V40LawPairSplit
import CurrentAdditive.V40LawCodeDPacket

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768

namespace CurrentAdditive.V40LawProductJobs
open EthInapproximability.CurrentPaper
open Paper2 V40LawJobsClock V40LawJobOrder
noncomputable section

structure Data where
  q : ℕ
  m : ℕ
  n : ℕ
  μ : PositiveRationalLaw (Fin m)
  ν : PositiveRationalLaw (Fin n)

def input (a : Data) : List Bool :=
  V40LawJobsRouting.input (List.replicate a.q true) (entries a.μ) (entries a.ν)

def output (a : Data) : List Bool :=
  BitMachineBankCodec.encode (![input a,
    V40LawCodeDPacket.input a.q (V40LawActualProduct.productJobs a.μ a.ν),
    companions a.μ a.ν] : Fin 3 → List Bool)

def rowData (a : Data) : V40LawCartesianRows.Data := (a.n.bits,entries a.μ,entries a.ν)
def saved (a : Data) : List Bool := V40LawPacket.packet (input a) (a.m*a.n).bits
def stage0Word (a : Data) : List Bool :=
  V40LawPacket.packet (saved a) (V40LawCartesianRows.input (rowData a))
def stage1Word (a : Data) : List Bool :=
  V40LawPacket.packet (saved a) (V40LawCartesianRows.output (rowData a))
def stage2Word (a : Data) : List Bool :=
  V40LawPacket.packet (input a) (SourceListEncoding.encode (nestedRecords a.μ a.ν))
def stage3Word (a : Data) : List Bool :=
  V40LawPacket.packet (input a) (V40LawPacket.packet
    (SourceListEncoding.encode (V40LawProductList.inputItems
      (V40LawActualProduct.productJobs a.μ a.ν))) (companions a.μ a.ν))

def first : BitMachine.Machine := BitMachineComposition.composition
  V40LawJobsRouting.prepare.machine (V40LawBankMap.liftMachine V40LawCartesianRows.machine)
def second : BitMachine.Machine := BitMachineComposition.composition first
  V40LawJobsRouting.finishCartesian.machine
def third : BitMachine.Machine := BitMachineComposition.composition second
  (V40LawBankMap.liftMachine V40LawPairSplit.machine)
def machine : BitMachine.Machine := BitMachineComposition.composition third
  V40LawJobsRouting.finish.machine

theorem stage0 : Realizes V40LawJobsRouting.prepare.machine input stage0Word := by
  have hp := producer V40LawJobsRouting.prepare input
  simpa only [input,V40LawJobsRouting.prepare_input,entries,List.length_ofFn,
    stage0Word,saved,rowData,V40LawCartesianRows.input] using hp

theorem stage1 : Realizes (V40LawBankMap.liftMachine V40LawCartesianRows.machine)
    stage0Word stage1Word := by
  have hr : Realizes V40LawCartesianRows.machine
      (fun a => V40LawCartesianRows.input (rowData a))
      (fun a => V40LawCartesianRows.output (rowData a)) := by
    obtain ⟨c,d,h⟩ := V40LawCartesianRows.realizes
    exact ⟨c,d,fun a => h (rowData a)⟩
  exact bank_map _ saved _ _ hr

theorem stage2 : Realizes V40LawJobsRouting.finishCartesian.machine stage1Word stage2Word := by
  have hp := producer V40LawJobsRouting.finishCartesian stage1Word
  have he (a : Data) : V40LawJobsRouting.finishCartesian.result (stage1Word a)=stage2Word a := by
    rw [stage1Word,saved,V40LawJobsRouting.finishCartesian_input]
    simp only [rowData,physical_rows,stage2Word,SourceListEncoding.encode]
    rw [nestedRecords_pairs,List.length_map,positions]
  simpa only [he] using hp

theorem stage3 : Realizes (V40LawBankMap.liftMachine V40LawPairSplit.machine)
    stage2Word stage3Word := by
  have hr : Realizes V40LawPairSplit.machine
      (fun a : Data => SourceListEncoding.encode (nestedRecords a.μ a.ν))
      (fun a => V40LawPacket.packet
        (SourceListEncoding.encode (V40LawProductList.inputItems
          (V40LawActualProduct.productJobs a.μ a.ν))) (companions a.μ a.ν)) := by
    obtain ⟨c,d,h⟩ := V40LawPairSplit.outputs_polynomial
    refine ⟨c,d,?_⟩
    intro a
    simpa only [←nestedRecords_pairs,jobs,companions] using h (pairs a.μ a.ν)
  exact bank_map _ input _ _ hr

theorem stage4 : Realizes V40LawJobsRouting.finish.machine stage3Word output := by
  have hp := producer V40LawJobsRouting.finish stage3Word
  have he (a : Data) : V40LawJobsRouting.finish.result (stage3Word a)=output a := by
    rw [stage3Word,input,V40LawJobsRouting.finish_input]
    rfl
  simpa only [he] using hp

/-- One fixed ordinary-input machine reads both original indexed law
vectors, physically computes every factor job and both original indices,
and returns the exact ordered serializer input with the original packet. -/
theorem realizes : Realizes machine input output :=
  V40LawJobsClock.compose _ _ _ _ _
    (V40LawJobsClock.compose _ _ _ _ _
      (V40LawJobsClock.compose _ _ _ _ _
        (V40LawJobsClock.compose _ _ _ _ _ stage0 stage1) stage2) stage3) stage4

theorem outputs_polynomial : ∃ C d : ℕ, ∀ (q m n : ℕ)
    (μ : PositiveRationalLaw (Fin m)) (ν : PositiveRationalLaw (Fin n)),
    machine.OutputsWithin (input ⟨q,m,n,μ,ν⟩) (output ⟨q,m,n,μ,ν⟩)
      (C*((input ⟨q,m,n,μ,ν⟩).length+1)^d) := by
  obtain ⟨C,d,h⟩ := realizes
  exact ⟨C,d,fun q m n μ ν => h ⟨q,m,n,μ,ν⟩⟩

#print axioms realizes
#print axioms outputs_polynomial
end
end CurrentAdditive.V40LawProductJobs
