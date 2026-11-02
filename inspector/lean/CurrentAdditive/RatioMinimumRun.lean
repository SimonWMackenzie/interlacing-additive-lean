import CurrentAdditive.RatioListPolynomial
import CurrentAdditive.RatioScanPolynomial
import EthInapproximability.CurrentPaper.MultiMove

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 100
noncomputable section
namespace CurrentAdditive.RatioMinimumRun
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open MinimumRatioCallbackLayout CurrentAdditive.GaussListContext
open MinimumRatioContext RatioListClockCaps EntryClockPoly

def jobs : List (MultiMove.Job Stack) := [⟨low 9,[]⟩]
def clearProgram := MultiMove.program jobs (low 31)
abbrev PrepLabel := BitMachineRawSequence.Label RatioListPreparation.Label (MultiMove.Label 1)
def prepProgram := BitMachineRawSequence.program RatioListPreparation.program clearProgram
  (MultiMove.startLabel jobs) RatioListPreparation.control MultiMove.initial
def prepStart : PrepLabel := BitMachineRawSequence.leftLabel RatioListPreparation.start
def prepControl := (RatioListPreparation.control,MultiMove.initial)
def scanControl := StatefulListScheduler.getterControl MinimumRatioCallbackPhysical.control
  (CylinderContextScanStep.copyControl ((),none))
abbrev Label := BitMachineRawSequence.Label PrepLabel
  (StatefulListScheduler.Label (BitMachineRawSequence.Label
    MinimumRatioCallbackPhysical.ItemLabel MinimumRatioExtraClear.Label))
def program := BitMachineRawSequence.program prepProgram RatioPhysicalFold.program
  (.inr (.inr .check)) prepControl scanControl
def start : Label := BitMachineRawSequence.leftLabel prepStart
def control := (prepControl,scanControl)

theorem empty_scalar (source output context : List Bool) (index fuel : Nat) :
    RatioRequestFrame.boundary source output context [] index fuel =
      RatioPhysicalFold.boundary source output context index fuel := by
  unfold RatioRequestFrame.boundary
  apply Function.update_eq_self_iff.mpr
  simp [RatioPhysicalFold.boundary,StatefulListScheduler.initialBank,
    RatioPhysicalFold.blank,Function.update_apply,low,Fin.ext_iff,Fin.ofNat]

theorem prep (xs : List (List Bool)) (context : List Bool) :
    ∃ t ≤ RatioListPreparation.clock xs+
      (2*(EncodedCommunication.natField xs.length).length+3)+1,
      ((advance prepProgram)^[t])
        (⟨some prepStart,prepControl,RatioPhysicalFold.boundary
          (SourceListEncoding.encode xs) [] context 0 0⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,prepControl,RatioPhysicalFold.boundary (SourceListEncoding.encode xs) []
          context 0 xs.length⟩ := by
  have hne : low 9 ≠ low 31 := by simp [low,Fin.ext_iff]
  obtain ⟨a,ha,hrA⟩ := RatioListFullRun.prepare xs context []
  simp only [empty_scalar] at hrA
  let S := RatioPhysicalFold.boundary (SourceListEncoding.encode xs)
    (EncodedCommunication.natField xs.length) context 0 xs.length
  have hvalid : MultiMove.Valid (low 31) jobs := by
    intro j hj
    simp only [jobs,List.mem_singleton] at hj
    subst j
    exact ⟨hne,by simp,by simp⟩
  have h31 : S (low 31) = [] := by
    simp [S,RatioPhysicalFold.boundary,StatefulListScheduler.initialBank,
      RatioPhysicalFold.blank,Function.update_apply,low,Fin.ext_iff,Fin.ofNat]
  have hrB := MultiMove.run jobs (low 31) hvalid S h31
  have hcost : MultiMove.cost jobs S+1=2*(EncodedCommunication.natField xs.length).length+3 := by
    simp [MultiMove.cost,jobs,S,RatioPhysicalFold.boundary,StatefulListScheduler.initialBank,
      Function.update_apply,low,Fin.ext_iff,Fin.ofNat]
  rw [hcost] at hrB
  have hout : MultiMove.apply jobs S =
      RatioPhysicalFold.boundary (SourceListEncoding.encode xs) [] context 0 xs.length := by
    funext j
    simp [MultiMove.apply,MultiMove.step,jobs,BitMachineBroadcast.prepend,S,
      RatioPhysicalFold.boundary,StatefulListScheduler.initialBank,Function.update_apply,
      low,Fin.ext_iff,Fin.ofNat]
    split_ifs <;> simp_all
  rw [hout] at hrB
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs RatioListPreparation.program clearProgram
    RatioListPreparation.start (MultiMove.startLabel jobs)
    RatioListPreparation.control RatioListPreparation.control MultiMove.initial MultiMove.initial
    _ S _ a _ hrA hrB
  exact ⟨t,by omega,by simpa only [prepProgram,prepStart,prepControl] using hr⟩

theorem prep_clock_le (xs : List (List Bool)) :
    RatioListPreparation.clock xs ≤ RatioListPolynomial.prepCap
      (SourceListEncoding.encode xs).length := by
  let L := (SourceListEncoding.encode xs).length
  have hn : xs.length ≤ L := GaussRowCount.rows_le_input xs
  have hc := invoke_le GaussRowCount.machine (SourceListEncoding.encode xs)
    (GaussRowCount.polynomialClock L) L (GaussRowCount.polynomialClock L) (by rfl) (by rfl)
  have hh := invoke_le SourceFieldWriter.unaryFieldMachine (List.replicate xs.length true)
    ((UnaryBinaryEncoding.coefficient+10)*(xs.length+1)^2) L
    ((UnaryBinaryEncoding.coefficient+10)*(L+1)^2) (by simpa using hn) (by gcongr)
  change _ ≤ RatioListPolynomial.prepCap L
  unfold RatioListPreparation.clock RatioListPolynomial.prepCap
  dsimp only [L] at *
  omega

/-- The scanner starts from the pair packet alone and computes its own
loop fuel. The canonical count header is parsed by an actual list counter;
all preparation, clearing, comparisons and final checks are charged. -/
theorem uniform_run : ∃ C d : Nat, ∀ (xs : List (List Bool)) (context : List Bool),
    ∃ t ≤ C*((SourceListEncoding.encode xs).length+1)^d, ∃ v,
      ((advance program)^[t])
        (⟨some start,control,RatioPhysicalFold.boundary (SourceListEncoding.encode xs)
          [] context 0 0⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,v,RatioPhysicalFold.boundary (SourceListEncoding.encode xs)
          (xs.foldl MinimumRatioStepSpec.step []) context xs.length 0⟩ := by
  classical
  obtain ⟨Q,dQ,hQ⟩ := RatioScanPolynomial.uniform_scan_polynomial
  have hp : PolyIn (fun n : Nat => n)
      (fun n => RatioListPolynomial.prepCap n+4*n+5+Q*(n+1)^dQ+2) := by
    unfold RatioListPolynomial.prepCap GaussRowCount.polynomialClock GaussRowCount.itemEnvelope invokeCap
    solve_list_poly
  obtain ⟨C,d,hC⟩ := hp
  refine ⟨C,d,?_⟩
  intro xs context
  obtain ⟨a,ha,hrA⟩ := prep xs context
  obtain ⟨b,hb,v,hrB⟩ := hQ xs context
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs prepProgram RatioPhysicalFold.program
    prepStart (.inr (.inr .check)) prepControl prepControl scanControl v _ _ _ a b hrA hrB
  have hpclock := prep_clock_le xs
  have hn := GaussRowCount.rows_le_input xs
  have hheader := EncodedGraph.natField_length_upper xs.length
  refine ⟨t,?_,_,by simpa only [program,start,control] using hr⟩
  exact (show t ≤ RatioListPolynomial.prepCap (SourceListEncoding.encode xs).length+
    4*(SourceListEncoding.encode xs).length+5+Q*((SourceListEncoding.encode xs).length+1)^dQ+2
      by omega).trans (hC _)

#print axioms uniform_run
end CurrentAdditive.RatioMinimumRun
