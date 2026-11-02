import EthInapproximability.CurrentPaper.ColumnInputStaging
import EthInapproximability.CurrentPaper.ETHParameterBinsActual
import EthInapproximability.CurrentPaper.BitMachineStackRun
import EthInapproximability.CurrentPaper.BitMachineRawSequence
import Mathlib.Data.Fin.VecNotation

/-! The checked ETH scale/bin machine physically installs its bin count in
weighted-writer cell 28 before the checked scalar staging+join. -/

namespace EthInapproximability.CurrentPaper.BinsWriterAssembly

open Turing BitMachineEncoding BitMachineStackEmbedding

noncomputable section

abbrev ParameterStack := ETHBinsJoinedScratch.Stack
abbrev WriterStack := Fin 64
abbrev Stack := ParameterStack ⊕ WriterStack

def paramSlots : ParameterStack ↪ Stack :=
  ⟨Sum.inl, by intro a b h; exact Sum.inl_injective h⟩
def writerSlots : WriterStack ↪ Stack :=
  ⟨Sum.inr, by intro a b h; exact Sum.inr_injective h⟩

def copySlots : Fin 3 ↪ Stack :=
  ⟨![.inl (.inr ETHBinsSourcePreservingScratch.outputKey),
      .inr 28, .inr 61], by decide⟩

def binProgram := fun l => stackStmt paramSlots (ETHBinsJoinedScratch.program l)
def copyProgram := MatrixStage4ScalarPreparationOps.copyProgram copySlots
def writerProgram := fun l => stackStmt writerSlots (ColumnInputStaging.program l)

def binStart : ETHBinsJoinedScratch.Label :=
  BitMachineRawSequence.leftLabel ETHBinsJoinedScratch.scaleStart
def binControl : ETHBinsJoinedScratch.Control :=
  (ETHBinsJoinedScratch.scaleControl, ETHBinsJoinedScratch.binsControl)

noncomputable def writerPreBank
    (d : MatrixWeightedEntryController.Input) (a q L : ℕ) :
    WriterStack → List Bool :=
  Function.update (ColumnInputStaging.partialBank d a q L) 28 []

noncomputable def initialBank (i : Parameters.Input)
    (d : MatrixWeightedEntryController.Input) (a q L : ℕ) :
    Stack → List Bool :=
  bank paramSlots (Sum.elim (fun _ => []) (writerPreBank d a q L))
    (ETHBinsJoinedScratch.initialBank i)

theorem writerPre_blank (d : MatrixWeightedEntryController.Input) (a q L : ℕ) :
    writerPreBank d a q L 28 = [] ∧ writerPreBank d a q L 61 = [] := by
  constructor
  · simp [writerPreBank]
  · simpa [writerPreBank] using
      (ColumnInputStaging.partial_blank d a q L).2.2.2.1

theorem restore_writer (d : MatrixWeightedEntryController.Input)
    (a q L : ℕ) :
    Function.update (writerPreBank d a q L) 28
      (List.replicate d.s true) = ColumnInputStaging.partialBank d a q L := by
  funext k
  by_cases hk : k = (28 : WriterStack)
  · subst k
    simp [writerPreBank, (ColumnInputStaging.partial_live d a q L).1]
  · simp [writerPreBank,hk]

theorem bins_run (i : Parameters.Input)
    (d : MatrixWeightedEntryController.Input) (a q L : ℕ) :
    ∃ t ≤ ETHBinsJoinedScratch.totalBound i,
      ∃ v : Fin ETHBinsStandaloneScratch.machine.controlCount,
      ∃ F : ParameterStack → List Bool,
      ((advance binProgram)^[t])
        ⟨some binStart,binControl,initialBank i d a q L⟩ =
        ⟨none,(ETHBinsJoinedScratch.scaleControl,(none,v)),
          bank paramSlots (Sum.elim (fun _ => []) (writerPreBank d a q L)) F⟩ ∧
      F (.inr ETHBinsSourcePreservingScratch.outputKey) =
        List.replicate (Parameters.bins i) true := by
  obtain ⟨t,ht,v,F,hr,hbins,_hscale,_hraw⟩ :=
    ETHBinsJoinedScratch.actual_bins_run i
  let foreign : Stack → List Bool :=
    Sum.elim (fun _ => []) (writerPreBank d a q L)
  have he := BitMachineStackRun.run paramSlots foreign
    ETHBinsJoinedScratch.program
    (⟨some binStart,binControl,ETHBinsJoinedScratch.initialBank i⟩ :
      TM2.Cfg (fun _ : ParameterStack => Bool)
        ETHBinsJoinedScratch.Label ETHBinsJoinedScratch.Control) t
  have hr' : ((advance ETHBinsJoinedScratch.program)^[t])
      (⟨some binStart,binControl,ETHBinsJoinedScratch.initialBank i⟩ :
        TM2.Cfg (fun _ : ParameterStack => Bool)
          ETHBinsJoinedScratch.Label ETHBinsJoinedScratch.Control) =
      ⟨none,(ETHBinsJoinedScratch.scaleControl,(none,v)),F⟩ := by
    simpa only [binStart,binControl] using hr
  rw [hr'] at he
  refine ⟨t,ht,v,F,?_,hbins⟩
  simpa only [binProgram,initialBank,binStart,binControl,
    stackCfg,foreign] using he

theorem bin_output_at (d : MatrixWeightedEntryController.Input)
    (a q L : ℕ) (F : ParameterStack → List Bool) :
    (bank paramSlots (Sum.elim (fun _ => []) (writerPreBank d a q L)) F)
      (copySlots 0) = F (.inr ETHBinsSourcePreservingScratch.outputKey) := by
  exact bank_at paramSlots _ F (.inr ETHBinsSourcePreservingScratch.outputKey)

theorem bin_writer_blank (d : MatrixWeightedEntryController.Input)
    (a q L : ℕ) (F : ParameterStack → List Bool) :
    (bank paramSlots (Sum.elim (fun _ => []) (writerPreBank d a q L)) F)
      (copySlots 1) = [] ∧
    (bank paramSlots (Sum.elim (fun _ => []) (writerPreBank d a q L)) F)
      (copySlots 2) = [] := by
  have h28 : ¬ ∃ k : ParameterStack, paramSlots k = (copySlots 1) := by
    rintro ⟨k,h⟩; cases h
  have h61 : ¬ ∃ k : ParameterStack, paramSlots k = (copySlots 2) := by
    rintro ⟨k,h⟩; cases h
  constructor
  · rw [bank_outside paramSlots _ F _ h28]
    exact (writerPre_blank d a q L).1
  · rw [bank_outside paramSlots _ F _ h61]
    exact (writerPre_blank d a q L).2

theorem bin_copy_run (i : Parameters.Input)
    (d : MatrixWeightedEntryController.Input) (a q L : ℕ)
    (hd : d.s = Parameters.bins i)
    (F : ParameterStack → List Bool)
    (hF : F (.inr ETHBinsSourcePreservingScratch.outputKey) =
      List.replicate (Parameters.bins i) true) :
    let S := bank paramSlots (Sum.elim (fun _ => []) (writerPreBank d a q L)) F
    ((advance copyProgram)^[2*d.s+2])
      ⟨some BitMachineCopy.Label.scan,none,S⟩ =
      ⟨none,none,bank writerSlots S (ColumnInputStaging.partialBank d a q L)⟩ := by
  let S := bank paramSlots (Sum.elim (fun _ => []) (writerPreBank d a q L)) F
  have hb := bin_writer_blank d a q L F
  have hs : S (copySlots 0) = List.replicate d.s true := by
    change (bank paramSlots (Sum.elim (fun _ => []) (writerPreBank d a q L)) F)
      (copySlots 0) = _
    rw [bin_output_at]
    simpa only [hd] using hF
  have hc := MatrixStage4ScalarPreparationOps.copy_run copySlots S hb.2
  have hcopy : ((advance copyProgram)^[2*d.s+2])
      ⟨some BitMachineCopy.Label.scan,none,S⟩ =
      ⟨none,none,Function.update S (.inr (28 : WriterStack))
        (List.replicate d.s true)⟩ := by
    have hb1 : S (copySlots 1) = [] := hb.1
    rw [hs, hb1] at hc
    simpa only [copyProgram, List.length_replicate, List.append_nil]
      using hc
  change ((advance copyProgram)^[2*d.s+2])
      ⟨some BitMachineCopy.Label.scan,none,S⟩ = _
  rw [hcopy]
  congr 1
  have hself : bank writerSlots S (writerPreBank d a q L) = S := by
    apply bank_eq_self
    intro k
    have hout : ¬ ∃ x : ParameterStack, paramSlots x = writerSlots k := by
      rintro ⟨x,hx⟩; cases hx
    have hbo := bank_outside paramSlots
      (Sum.elim (fun _ => []) (writerPreBank d a q L))
      F (writerSlots k) hout
    simpa only [writerSlots] using hbo.symm
  calc
    Function.update S (.inr (28 : WriterStack)) (List.replicate d.s true) =
        Function.update (bank writerSlots S (writerPreBank d a q L))
          (writerSlots 28) (List.replicate d.s true) := by
            simpa only [writerSlots] using
              congrArg (fun T => Function.update T (writerSlots 28)
                (List.replicate d.s true)) hself.symm
    _ = bank writerSlots S (Function.update (writerPreBank d a q L) 28
          (List.replicate d.s true)) :=
      (bank_update writerSlots S (writerPreBank d a q L) 28 _).symm
    _ = bank writerSlots S (ColumnInputStaging.partialBank d a q L) := by
      rw [restore_writer]

def P12 := BitMachineRawSequence.program binProgram copyProgram
  BitMachineCopy.Label.scan binControl (none : Option Bool)
def program := BitMachineRawSequence.program P12 writerProgram
  ColumnInputStaging.start (binControl,none) ColumnInputStaging.initial
def start : BitMachineRawSequence.Label
    (BitMachineRawSequence.Label ETHBinsJoinedScratch.Label BitMachineCopy.Label)
    (ColumnInputStaging.Raw.Label
      (ColumnInputStaging.Raw.Label
        (ColumnInputStaging.Raw.Label BitMachineCopy.Label BitMachineCopy.Label)
        BitMachineCopy.Label) ColumnWriterJoin.Label) := by
  exact BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel binStart)

def initialControl : (ETHBinsJoinedScratch.Control × Option Bool) ×
    (((Option Bool × Option Bool) × Option Bool) × ColumnWriterJoin.Control) :=
  ((binControl,none),ColumnInputStaging.initial)

def totalCost (i : Parameters.Input) (a q L rx cy : ℕ) : ℕ :=
  ETHBinsJoinedScratch.totalBound i +
    (2 * Parameters.bins i + 2) +
    (ColumnInputStaging.stageCost (Parameters.bins i) rx cy +
      ColumnWriterJoin.joinCost a (Parameters.bins i) q L rx cy + 1) + 2

theorem initial_writer_bin_blank (i : Parameters.Input)
    (d : MatrixWeightedEntryController.Input) (a q L : ℕ) :
    initialBank i d a q L (writerSlots 28) = [] := by
  have hout : ¬ ∃ k : ParameterStack, paramSlots k = writerSlots 28 := by
    rintro ⟨k,h⟩; cases h
  rw [initialBank, bank_outside paramSlots _ _ _ hout]
  exact (writerPre_blank d a q L).1

theorem actual_bins_writer_run {rx cy : ℕ} (i : Parameters.Input)
    (R : Fin rx → Fin cy → Bool) (a q L nv nb : ℕ)
    (hs : 0 < Parameters.bins i)
    (family : Construction.SecondFamily a q L (Fin rx))
    (order : Construction.ItemOrder nv nb)
    (vectors : Fin (nv+nb) → Fin q → Bool)
    (cap : ∀ α, (Construction.activeItems vectors α).card ≤ Parameters.bins i) :
    let d := MatrixWeightedEntrySemantic.actualInput R a (Parameters.bins i)
      q L nv nb hs family order vectors cap
    ∃ t ≤ totalCost i a q L rx cy,
      ∃ F : ParameterStack → List Bool,
      ((advance program)^[t])
        ⟨some start,initialControl,initialBank i d a q L⟩ =
        ⟨none,initialControl,
          bank writerSlots
            (bank paramSlots
              (Sum.elim (fun _ => []) (writerPreBank d a q L)) F)
            (MatrixWeightedEntryController.persistentBank d)⟩ ∧
      F (.inr ETHBinsSourcePreservingScratch.outputKey) =
        List.replicate (Parameters.bins i) true := by
  let d := MatrixWeightedEntrySemantic.actualInput R a (Parameters.bins i)
    q L nv nb hs family order vectors cap
  obtain ⟨tb,htb,v,F,hbins,hF⟩ := bins_run i d a q L
  let S := bank paramSlots
    (Sum.elim (fun _ => []) (writerPreBank d a q L)) F
  let T := bank writerSlots S (ColumnInputStaging.partialBank d a q L)
  let U := bank writerSlots S (MatrixWeightedEntryController.persistentBank d)
  have hd : d.s = Parameters.bins i := rfl
  have hcopy := bin_copy_run i d a q L hd F hF
  have hcopy' : ((advance copyProgram)^[2*Parameters.bins i+2])
      (⟨some BitMachineCopy.Label.scan,none,S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none,none,T⟩ := by
    simpa only [S,T,hd] using hcopy
  obtain ⟨tw,htw,hstage⟩ := ColumnInputStaging.staged_actual_run
    R a (Parameters.bins i) q L nv nb hs family order vectors cap
  have hw := BitMachineStackRun.run writerSlots S
    ColumnInputStaging.program
    (⟨some ColumnInputStaging.start,ColumnInputStaging.initial,
      ColumnInputStaging.partialBank d a q L⟩ :
      TM2.Cfg (fun _ : WriterStack => Bool)
        (ColumnInputStaging.Raw.Label
          (ColumnInputStaging.Raw.Label
            (ColumnInputStaging.Raw.Label BitMachineCopy.Label BitMachineCopy.Label)
            BitMachineCopy.Label) ColumnWriterJoin.Label)
        (((Option Bool × Option Bool) × Option Bool) × ColumnWriterJoin.Control)) tw
  have hstage' : ((advance ColumnInputStaging.program)^[tw])
      ⟨some ColumnInputStaging.start,ColumnInputStaging.initial,
        ColumnInputStaging.partialBank d a q L⟩ =
      ⟨none,ColumnInputStaging.initial,
        MatrixWeightedEntryController.persistentBank d⟩ := by
    simpa only [d] using hstage
  rw [hstage'] at hw
  have hw' : ((advance writerProgram)^[tw])
      (⟨some ColumnInputStaging.start,ColumnInputStaging.initial,T⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none,ColumnInputStaging.initial,U⟩ := by
    simpa only [writerProgram,T,U,stackCfg] using hw
  obtain ⟨tbc,htbc,hbc⟩ := BitMachineRawSequence.runs
    binProgram copyProgram binStart BitMachineCopy.Label.scan
    binControl (ETHBinsJoinedScratch.scaleControl,(none,v))
    (none : Option Bool) none
    (initialBank i d a q L) S T tb (2*Parameters.bins i+2)
    (by simpa only [S] using hbins) hcopy'
  obtain ⟨t,ht,hall⟩ := BitMachineRawSequence.runs
    P12 writerProgram
    (BitMachineRawSequence.leftLabel binStart)
    ColumnInputStaging.start
    (binControl,none) (binControl,none)
    ColumnInputStaging.initial ColumnInputStaging.initial
    (initialBank i d a q L) T U tbc tw
    (by simpa only [P12] using hbc) hw'
  refine ⟨t, ?_, F, ?_, hF⟩
  · dsimp [totalCost] at *
    omega
  · simpa only [program,start,initialControl,S,U] using hall

#print axioms writerPre_blank
#print axioms restore_writer
#print axioms bins_run
#print axioms bin_copy_run
#print axioms initial_writer_bin_blank
#print axioms actual_bins_writer_run

end
end EthInapproximability.CurrentPaper.BinsWriterAssembly
