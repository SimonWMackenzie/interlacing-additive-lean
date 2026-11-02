import EthInapproximability.CurrentPaper.ColumnWriterJoin
import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps
import EthInapproximability.CurrentPaper.BitMachineRawSequence
import Mathlib.Data.Fin.VecNotation

/-! Three physical source-preserving writer-bank copies followed by the
checked Stage--4 column-scalar writer join. -/

namespace EthInapproximability.CurrentPaper.ColumnInputStaging

open Turing BitMachineEncoding BitMachineStackEmbedding

abbrev Stack := Fin 64
namespace Raw
abbrev Label := BitMachineRawSequence.Label
abbrev leftLabel := @BitMachineRawSequence.leftLabel
abbrev program := @BitMachineRawSequence.program
abbrev runs := @BitMachineRawSequence.runs
end Raw

/-- Source, destination, and physically empty temporary stack. -/
def sSlots : Fin 3 ↪ Stack := ⟨![28,55,61], by decide⟩
def rxSlots : Fin 3 ↪ Stack := ⟨![17,58,62], by decide⟩
def cySlots : Fin 3 ↪ Stack := ⟨![27,59,63], by decide⟩

def sProgram := MatrixStage4ScalarPreparationOps.copyProgram sSlots
def rxProgram := MatrixStage4ScalarPreparationOps.copyProgram rxSlots
def cyProgram := MatrixStage4ScalarPreparationOps.copyProgram cySlots

/-- Only a,q,L are initially staged; s,rx,cy are copied from live writer
cells rather than supplied a second time. -/
def partialLocalBank (a q L : ℕ) : Fin 40 → List Bool :=
  fun i => if i = 0 then List.replicate a true
    else if i = 2 then List.replicate q true
    else if i = 3 then List.replicate L true else []

noncomputable def partialBank (d : MatrixWeightedEntryController.Input)
    (a q L : ℕ) : Stack → List Bool :=
  bank ColumnWriterJoin.slots (ColumnWriterJoin.strippedBank d)
    (partialLocalBank a q L)

def afterS (S : Stack → List Bool) (s : ℕ) : Stack → List Bool :=
  Function.update S 55 (List.replicate s true)
def afterRx (S : Stack → List Bool) (rx : ℕ) : Stack → List Bool :=
  Function.update S 58 (List.replicate rx true)
def afterCy (S : Stack → List Bool) (cy : ℕ) : Stack → List Bool :=
  Function.update S 59 (List.replicate cy true)

theorem partial_live (d : MatrixWeightedEntryController.Input)
    (a q L : ℕ) :
    partialBank d a q L 28 = List.replicate d.s true ∧
    partialBank d a q L 17 = List.replicate d.rx true ∧
    partialBank d a q L 27 = List.replicate d.cy true := by
  have h28 : ¬ ∃ i : Fin 40, ColumnWriterJoin.slots i = (28 : Stack) := by decide
  have h17 : ¬ ∃ i : Fin 40, ColumnWriterJoin.slots i = (17 : Stack) := by decide
  have h27 : ¬ ∃ i : Fin 40, ColumnWriterJoin.slots i = (27 : Stack) := by decide
  simp [partialBank, bank_outside _ _ _ _ h28,
    bank_outside _ _ _ _ h17, bank_outside _ _ _ _ h27,
    ColumnWriterJoin.strippedBank,
    MatrixWeightedEntryController.persistentBank]

theorem partial_blank (d : MatrixWeightedEntryController.Input)
    (a q L : ℕ) :
    partialBank d a q L 55 = [] ∧
    partialBank d a q L 58 = [] ∧
    partialBank d a q L 59 = [] ∧
    partialBank d a q L 61 = [] ∧
    partialBank d a q L 62 = [] ∧
    partialBank d a q L 63 = [] := by
  have h61 : ¬ ∃ i : Fin 40, ColumnWriterJoin.slots i = (61 : Stack) := by decide
  have h62 : ¬ ∃ i : Fin 40, ColumnWriterJoin.slots i = (62 : Stack) := by decide
  have h63 : ¬ ∃ i : Fin 40, ColumnWriterJoin.slots i = (63 : Stack) := by decide
  simp [partialBank, show (55 : Stack) = ColumnWriterJoin.slots 1 from rfl,
    show (58 : Stack) = ColumnWriterJoin.slots 4 from rfl,
    show (59 : Stack) = ColumnWriterJoin.slots 5 from rfl,
    bank_at, partialLocalBank, bank_outside _ _ _ _ h61,
    bank_outside _ _ _ _ h62, bank_outside _ _ _ _ h63,
    ColumnWriterJoin.strippedBank,
    MatrixWeightedEntryController.persistentBank]

theorem s_run (d : MatrixWeightedEntryController.Input) (a q L : ℕ) :
    ((advance sProgram)^[2*d.s+2])
      (⟨some .scan, none, partialBank d a q L⟩ :
        TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, afterS (partialBank d a q L) d.s⟩ := by
  have h := MatrixStage4ScalarPreparationOps.copy_run sSlots
    (partialBank d a q L) (partial_blank d a q L).2.2.2.1
  have hs := (partial_live d a q L).1
  have he := (partial_blank d a q L).1
  simpa [sProgram, sSlots, hs, he, afterS] using h

theorem rx_run (d : MatrixWeightedEntryController.Input) (a q L : ℕ) :
    ((advance rxProgram)^[2*d.rx+2])
      (⟨some .scan, none, afterS (partialBank d a q L) d.s⟩ :
        TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, afterRx (afterS (partialBank d a q L) d.s) d.rx⟩ := by
  let S := afterS (partialBank d a q L) d.s
  have he : S (rxSlots 2) = [] := by
    simp [S,afterS,rxSlots,(partial_blank d a q L).2.2.2.2.1]
  have hs : S (rxSlots 0) = List.replicate d.rx true := by
    simp [S,afterS,rxSlots,(partial_live d a q L).2.1]
  have ht : S (rxSlots 1) = [] := by
    simp [S,afterS,rxSlots,(partial_blank d a q L).2.1]
  have h := MatrixStage4ScalarPreparationOps.copy_run rxSlots S he
  simpa only [rxProgram, hs, ht, List.length_replicate,
    List.append_nil, afterRx, S] using h

theorem cy_run (d : MatrixWeightedEntryController.Input) (a q L : ℕ) :
    ((advance cyProgram)^[2*d.cy+2])
      (⟨some .scan, none,
        afterRx (afterS (partialBank d a q L) d.s) d.rx⟩ :
        TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none,
        afterCy (afterRx (afterS (partialBank d a q L) d.s) d.rx) d.cy⟩ := by
  let S := afterRx (afterS (partialBank d a q L) d.s) d.rx
  have he : S (cySlots 2) = [] := by
    simp [S,afterS,afterRx,cySlots,(partial_blank d a q L).2.2.2.2.2]
  have hs : S (cySlots 0) = List.replicate d.cy true := by
    simp [S,afterS,afterRx,cySlots,(partial_live d a q L).2.2]
  have ht : S (cySlots 1) = [] := by
    simp [S,afterS,afterRx,cySlots,(partial_blank d a q L).2.2.1]
  have h := MatrixStage4ScalarPreparationOps.copy_run cySlots S he
  simpa only [cyProgram, hs, ht, List.length_replicate,
    List.append_nil, afterCy, S] using h

theorem after_three_eq_full (d : MatrixWeightedEntryController.Input)
    (a q L : ℕ) :
    afterCy (afterRx (afterS (partialBank d a q L) d.s) d.rx) d.cy =
      ColumnWriterJoin.sourceBank (ColumnWriterJoin.strippedBank d)
        a d.s q L d.rx d.cy := by
  simp only [afterCy, afterRx, afterS, partialBank,
    ColumnWriterJoin.sourceBank,
    show (55 : Stack) = ColumnWriterJoin.slots 1 from rfl,
    show (58 : Stack) = ColumnWriterJoin.slots 4 from rfl,
    show (59 : Stack) = ColumnWriterJoin.slots 5 from rfl,
    ← bank_update]
  congr 1
  funext i
  fin_cases i <;> simp [partialLocalBank, ColumnScalarPrefix.inputBank]

def P12 := Raw.program sProgram rxProgram .scan (none : Option Bool) none
def P123 := Raw.program P12 cyProgram .scan
  ((none,none) : Option Bool × Option Bool) none
def program := Raw.program P123 ColumnWriterJoin.program
  ColumnWriterJoin.start (((none,none),none) :
    (Option Bool × Option Bool) × Option Bool) ColumnWriterJoin.initial

def start : Raw.Label
    (Raw.Label (Raw.Label BitMachineCopy.Label BitMachineCopy.Label)
      BitMachineCopy.Label) ColumnWriterJoin.Label :=
  Raw.leftLabel (Raw.leftLabel (Raw.leftLabel BitMachineCopy.Label.scan))
def initial := ((((none,none),none),ColumnWriterJoin.initial) :
  ((Option Bool × Option Bool) × Option Bool) × ColumnWriterJoin.Control)

def stageCost (s rx cy : ℕ) : ℕ :=
  (2*s+2)+(2*rx+2)+(2*cy+2)+3

theorem three_run (d : MatrixWeightedEntryController.Input) (a q L : ℕ) :
    ∃ t ≤ stageCost d.s d.rx d.cy,
      ((advance P123)^[t])
        ⟨some (Raw.leftLabel (Raw.leftLabel BitMachineCopy.Label.scan)),
          ((none,none),none),partialBank d a q L⟩ =
      ⟨none,((none,none),none),
        ColumnWriterJoin.sourceBank (ColumnWriterJoin.strippedBank d)
          a d.s q L d.rx d.cy⟩ := by
  have h1 := s_run d a q L
  have h2 := rx_run d a q L
  have h3 := cy_run d a q L
  obtain ⟨u,hu,h12⟩ := Raw.runs sProgram rxProgram
    BitMachineCopy.Label.scan BitMachineCopy.Label.scan
    none none none none
    (partialBank d a q L)
    (afterS (partialBank d a q L) d.s)
    (afterRx (afterS (partialBank d a q L) d.s) d.rx)
    (2*d.s+2) (2*d.rx+2) h1 h2
  obtain ⟨v,hv,h123⟩ := Raw.runs P12 cyProgram
    (Raw.leftLabel BitMachineCopy.Label.scan) BitMachineCopy.Label.scan
    (none,none) (none,none) none none
    (partialBank d a q L)
    (afterRx (afterS (partialBank d a q L) d.s) d.rx)
    (afterCy (afterRx (afterS (partialBank d a q L) d.s) d.rx) d.cy)
    u (2*d.cy+2) (by simpa only [P12] using h12) h3
  refine ⟨v, ?_, ?_⟩
  · dsimp [stageCost]; omega
  · rw [after_three_eq_full] at h123
    simpa only [P123] using h123

theorem staged_actual_run {rx cy : ℕ}
    (R : Fin rx → Fin cy → Bool) (a s q L nv nb : ℕ) (hs : 0 < s)
    (family : Construction.SecondFamily a q L (Fin rx))
    (order : Construction.ItemOrder nv nb)
    (vectors : Fin (nv+nb) → Fin q → Bool)
    (cap : ∀ α, (Construction.activeItems vectors α).card ≤ s) :
    let d := MatrixWeightedEntrySemantic.actualInput
      R a s q L nv nb hs family order vectors cap
    ∃ t ≤ stageCost s rx cy + ColumnWriterJoin.joinCost a s q L rx cy + 1,
      ((advance program)^[t])
        ⟨some start, initial, partialBank d a q L⟩ =
      ⟨none, initial, MatrixWeightedEntryController.persistentBank d⟩ := by
  let d := MatrixWeightedEntrySemantic.actualInput
    R a s q L nv nb hs family order vectors cap
  obtain ⟨u,hu,hstage⟩ := three_run d a q L
  obtain ⟨v,hv,hjoin⟩ := ColumnWriterJoin.actual_run_joinCost
    R a s q L nv nb hs family order vectors cap
  have hd : d.s = s ∧ d.rx = rx ∧ d.cy = cy := by
    simp [d,MatrixWeightedEntrySemantic.actualInput]
  have hbank : ColumnWriterJoin.sourceBank (ColumnWriterJoin.strippedBank d)
      a d.s q L d.rx d.cy =
      ColumnWriterJoin.actualSource R a s q L nv nb hs family order vectors cap := by
    rcases hd with ⟨hs',hrx,hcy⟩
    simp only [hs',hrx,hcy]
    rfl
  rw [hbank] at hstage
  obtain ⟨t,ht,hr⟩ := Raw.runs P123 ColumnWriterJoin.program
    (Raw.leftLabel (Raw.leftLabel BitMachineCopy.Label.scan))
    ColumnWriterJoin.start
    ((none,none),none) ((none,none),none)
    ColumnWriterJoin.initial ColumnWriterJoin.initial
    (partialBank d a q L)
    (ColumnWriterJoin.actualSource R a s q L nv nb hs family order vectors cap)
    (MatrixWeightedEntryController.persistentBank d)
    u v (by simpa only [P123] using hstage)
    (by simpa only [ColumnWriterJoin.run,ColumnWriterJoin.cfg] using hjoin)
  refine ⟨t, ?_, ?_⟩
  · rw [hd.1, hd.2.1, hd.2.2] at hu
    omega
  · simpa only [program,start,initial] using hr

#print axioms partial_live
#print axioms partial_blank
#print axioms s_run
#print axioms rx_run
#print axioms cy_run
#print axioms after_three_eq_full
#print axioms three_run
#print axioms staged_actual_run

end EthInapproximability.CurrentPaper.ColumnInputStaging
