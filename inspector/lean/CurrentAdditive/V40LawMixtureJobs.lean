import CurrentAdditive.V40LawMixtureRows
import CurrentAdditive.V40LawMixtureRouting
import CurrentAdditive.V40LawMixtureOrder
import CurrentAdditive.V40LawProductJobs

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768

namespace CurrentAdditive.V40LawMixtureJobs
open EthInapproximability.CurrentPaper
open V40LawJobsClock V40LawMixtureOrder
noncomputable section

abbrev Data := V40LawProductJobs.Data
def input := V40LawProductJobs.input
def leftData (a : Data) : V40LawMixtureRows.Data := ((0 : ℕ).bits,V40LawJobOrder.entries a.μ)
def rightData (a : Data) : V40LawMixtureRows.Data := (a.m.bits,V40LawJobOrder.entries a.ν)
def header0 (a : Data) : List Bool := BitMachineBankCodec.encode
  (![input a,(a.m+a.n).bits,V40LawMixtureRows.input (rightData a)] : Fin 3 → List Bool)
def header1 (a : Data) : List Bool := BitMachineBankCodec.encode
  (![input a,(a.m+a.n).bits,V40LawMixtureRows.output false (leftData a)] : Fin 3 → List Bool)
def word0 (a : Data) := V40LawPacket.packet (header0 a) (V40LawMixtureRows.input (leftData a))
def word1 (a : Data) := V40LawPacket.packet (header0 a) (V40LawMixtureRows.output false (leftData a))
def word2 (a : Data) := V40LawPacket.packet (header1 a) (V40LawMixtureRows.input (rightData a))
def word3 (a : Data) := V40LawPacket.packet (header1 a) (V40LawMixtureRows.output true (rightData a))
def word4 (a : Data) := V40LawPacket.packet (input a)
  (SourceListEncoding.encode (records a.μ a.ν))
def word5 (a : Data) := V40LawPacket.packet (input a)
  (V40LawPacket.packet (SourceListEncoding.encode (V40LawProductList.inputItems
    (V40LawActualProduct.mixtureJobs a.μ a.ν))) (companions a.μ a.ν))
def output (a : Data) := BitMachineBankCodec.encode
  (![input a,V40LawCodeDPacket.input a.q (V40LawActualProduct.mixtureJobs a.μ a.ν),
    companions a.μ a.ν] : Fin 3 → List Bool)

def first := BitMachineComposition.composition V40LawMixtureRouting.prepare.machine
  (V40LawBankMap.liftMachine (V40LawMixtureRows.machine false))
def second := BitMachineComposition.composition first V40LawMixtureRouting.prepareRight.machine
def third := BitMachineComposition.composition second
  (V40LawBankMap.liftMachine (V40LawMixtureRows.machine true))
def fourth := BitMachineComposition.composition third V40LawMixtureRouting.finish.machine
def fifth := BitMachineComposition.composition fourth (V40LawBankMap.liftMachine V40LawPairSplit.machine)
def machine := BitMachineComposition.composition fifth V40LawJobsRouting.finish.machine

theorem stage0 : Realizes V40LawMixtureRouting.prepare.machine input word0 := by
  have h := producer V40LawMixtureRouting.prepare input
  simpa only [input,V40LawProductJobs.input,V40LawMixtureRouting.prepare_input,
    word0,header0,leftData,rightData,V40LawMixtureRows.input,V40LawJobOrder.entries,
    List.length_ofFn] using h

theorem stage1 : Realizes (V40LawBankMap.liftMachine (V40LawMixtureRows.machine false)) word0 word1 := by
  have h : Realizes (V40LawMixtureRows.machine false)
      (fun a => V40LawMixtureRows.input (leftData a))
      (fun a => V40LawMixtureRows.output false (leftData a)) := by
    obtain ⟨C,d,h⟩ := V40LawMixtureRows.realizes false
    exact ⟨C,d,fun a => h (leftData a)⟩
  exact bank_map _ header0 _ _ h

theorem stage2 : Realizes V40LawMixtureRouting.prepareRight.machine word1 word2 := by
  have h := producer V40LawMixtureRouting.prepareRight word1
  simpa only [word1,word2,header0,header1,V40LawMixtureRouting.prepareRight_input] using h

theorem stage3 : Realizes (V40LawBankMap.liftMachine (V40LawMixtureRows.machine true)) word2 word3 := by
  have h : Realizes (V40LawMixtureRows.machine true)
      (fun a => V40LawMixtureRows.input (rightData a))
      (fun a => V40LawMixtureRows.output true (rightData a)) := by
    obtain ⟨C,d,h⟩ := V40LawMixtureRows.realizes true
    exact ⟨C,d,fun a => h (rightData a)⟩
  exact bank_map _ header1 _ _ h

theorem stage4 : Realizes V40LawMixtureRouting.finish.machine word3 word4 := by
  have h := producer V40LawMixtureRouting.finish word3
  have he (a : Data) : V40LawMixtureRouting.finish.result (word3 a)=word4 a := by
    rw [word3,header1,V40LawMixtureRouting.finish_input]
    rw [leftData,rightData,left_rows,right_rows a.μ a.ν,word4,
      SourceListEncoding.encode,records_length,records,AppendEntryPhysical.fields_append]
  simpa only [he] using h

theorem stage5 : Realizes (V40LawBankMap.liftMachine V40LawPairSplit.machine) word4 word5 := by
  have h : Realizes V40LawPairSplit.machine
      (fun a : Data => SourceListEncoding.encode (records a.μ a.ν))
      (fun a => V40LawPacket.packet (SourceListEncoding.encode (V40LawProductList.inputItems
        (V40LawActualProduct.mixtureJobs a.μ a.ν))) (companions a.μ a.ν)) := by
    obtain ⟨C,d,h⟩ := V40LawPairSplit.outputs_polynomial
    refine ⟨C,d,?_⟩
    intro a
    simpa only [←records_pairs,jobs,companions] using h (pairs a.μ a.ν)
  exact bank_map _ input _ _ h

theorem stage6 : Realizes V40LawJobsRouting.finish.machine word5 output := by
  have h := producer V40LawJobsRouting.finish word5
  have he (a : Data) : V40LawJobsRouting.finish.result (word5 a)=output a := by
    rw [word5,input,V40LawProductJobs.input,V40LawJobsRouting.finish_input]
    rfl
  simpa only [he] using h

/-- Both fixed branch maps run on their original ordered law packets.
The two exact streams are joined left first, with physically computed total
count and offsets. The actual mixture factors and tags are not inputs. -/
theorem realizes : Realizes machine input output :=
  V40LawJobsClock.compose _ _ _ _ _
    (V40LawJobsClock.compose _ _ _ _ _
      (V40LawJobsClock.compose _ _ _ _ _
        (V40LawJobsClock.compose _ _ _ _ _
          (V40LawJobsClock.compose _ _ _ _ _
            (V40LawJobsClock.compose _ _ _ _ _ stage0 stage1) stage2) stage3) stage4) stage5) stage6

#print axioms realizes
end
end CurrentAdditive.V40LawMixtureJobs
