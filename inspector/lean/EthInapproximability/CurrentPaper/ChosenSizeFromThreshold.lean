import EthInapproximability.CurrentPaper.ChosenSizeSuffix
import EthInapproximability.CurrentPaper.BitMachineStackRun

/-! Prime search and physical unary size power on one framed writer bank. -/

namespace EthInapproximability.CurrentPaper.ChosenSizeFromThreshold

open Turing BitMachineEncoding BitMachineStackEmbedding

noncomputable section

abbrev Stack := ChosenSizeSuffix.Stack

def searchSlots : ChosenPrimeRaw.Stack ↪ Stack :=
  ⟨Sum.inl, by intro a b h; exact Sum.inl_injective h⟩

def foreignBank (d : MatrixWeightedEntryController.Input)
    (a q t : ℕ) : Stack → List Bool
  | .inl _ => []
  | .inr (.inl k) => ColumnInputStaging.partialBank d a q 0 k
  | .inr (.inr k) => if k = 0 then List.replicate t true else []

def X (d : MatrixWeightedEntryController.Input) (a q t : ℕ) : ℕ :=
  PrimeSampler.threshold q t (Construction.qOne a * d.rx)

def L (d : MatrixWeightedEntryController.Input) (a q t : ℕ) : ℕ :=
  PrimeSampler.size q t (Construction.qOne a * d.rx)

def initialBank (d : MatrixWeightedEntryController.Input) (a q t : ℕ) :
    Stack → List Bool :=
  bank searchSlots (foreignBank d a q t) (ChosenPrimeRaw.initial (X d a q t)).stk

def searchProgram := fun l => stackStmt searchSlots (ChosenPrimeRaw.program l)
def program := BitMachineRawSequence.program searchProgram ChosenSizeSuffix.program
  ChosenSizeSuffix.start (ChosenPrimeRaw.initial 2).var ChosenSizeSuffix.initialControl

abbrev Label := BitMachineRawSequence.Label ChosenPrimeRaw.Label ChosenSizeSuffix.Label
abbrev Control := ChosenPrimeRaw.Control × ChosenSizeSuffix.Control

def start : Label := BitMachineRawSequence.leftLabel (.inr .initialize)
def initialControl : Control := ((ChosenPrimeRaw.initial 2).var,
  ChosenSizeSuffix.initialControl)

def bound (d : MatrixWeightedEntryController.Input) (a q t : ℕ) : ℕ :=
  ChosenPrimeRaw.bound (X d a q t) +
    ChosenSizeSuffix.bound (PrimeSampler.prime q t (Construction.qOne a * d.rx)) t + 1

private theorem partialL_zero (d : MatrixWeightedEntryController.Input)
    (a q : ℕ) : ColumnInputStaging.partialBank d a q 0 57 = [] := by
  simp [ColumnInputStaging.partialBank, ColumnInputStaging.partialLocalBank,
    show (57 : Fin 64) = ColumnWriterJoin.slots 3 from rfl, bank_at]

private theorem partialL_update (d : MatrixWeightedEntryController.Input)
    (a q L : ℕ) :
    ColumnInputStaging.partialBank d a q L =
      Function.update (ColumnInputStaging.partialBank d a q 0) 57
        (List.replicate L true) := by
  have hlocal : ColumnInputStaging.partialLocalBank a q L =
      Function.update (ColumnInputStaging.partialLocalBank a q 0) 3
        (List.replicate L true) := by
    funext k
    fin_cases k <;> simp [ColumnInputStaging.partialLocalBank]
  rw [ColumnInputStaging.partialBank, hlocal, bank_update,
    ColumnInputStaging.partialBank]
  rfl

private theorem writer_projection (d : MatrixWeightedEntryController.Input)
    (a q t L : ℕ) (F : ChosenPrimeRaw.Stack → List Bool) :
    (fun k : Fin 64 =>
      (Function.update (bank searchSlots (foreignBank d a q t) F)
        ChosenSizeSuffix.writerL (List.replicate L true)) (.inr (.inl k))) =
      ColumnInputStaging.partialBank d a q L := by
  rw [partialL_update]
  funext k
  by_cases hk : k = 57
  · subst k; simp [ChosenSizeSuffix.writerL]
  · have hout : ¬ ∃ j : ChosenPrimeRaw.Stack,
        searchSlots j = (.inr (.inl k) : Stack) := by
      rintro ⟨j,h⟩; cases h
    simp [Function.update_of_ne, hk, ChosenSizeSuffix.writerL,
      bank_outside searchSlots (foreignBank d a q t) F _ hout,
      foreignBank]

/-- Conditional only on the *initial unary threshold word* being physically
present. The least prime and L are produced by one fixed program; neither is
an input. The source t word and the writer's a,q fields are retained. -/
theorem size_from_threshold (d : MatrixWeightedEntryController.Input)
    (a q t : ℕ) :
    ∃ u ≤ bound d a q t,
      ∃ F : ChosenPrimeRaw.Stack → List Bool,
        ((advance program)^[u])
          (⟨some start,initialControl,initialBank d a q t⟩ :
            TM2.Cfg (fun _ : Stack => Bool) Label Control) =
          ⟨none,initialControl,
            Function.update (bank searchSlots (foreignBank d a q t) F)
              ChosenSizeSuffix.writerL (List.replicate (L d a q t) true)⟩ ∧
        F (.inr 3) =
          List.replicate (PrimeSampler.prime q t (Construction.qOne a * d.rx)) true ∧
        (fun k : Fin 64 =>
          (Function.update (bank searchSlots (foreignBank d a q t) F)
            ChosenSizeSuffix.writerL (List.replicate (L d a q t) true))
              (.inr (.inl k))) =
          ColumnInputStaging.partialBank d a q (L d a q t) := by
  let m := Construction.qOne a * d.rx
  let p := PrimeSampler.prime q t m
  obtain ⟨up,hup,v,F,hsearch,hprime⟩ := ChosenPrimeRaw.chosen_run q t m
  let S := bank searchSlots (foreignBank d a q t) F
  have hs : ((advance searchProgram)^[up])
      (⟨some (.inr .initialize),(ChosenPrimeRaw.initial (X d a q t)).var,
        initialBank d a q t⟩ :
        TM2.Cfg (fun _ : Stack => Bool) ChosenPrimeRaw.Label ChosenPrimeRaw.Control) =
      ⟨none,v,S⟩ := by
    have he := BitMachineStackRun.run searchSlots (foreignBank d a q t)
      ChosenPrimeRaw.program (ChosenPrimeRaw.initial (X d a q t)) up
    have he0 : ((advance ChosenPrimeRaw.program)^[up])
        (ChosenPrimeRaw.initial (X d a q t)) = ⟨none,v,F⟩ := by
      simpa only [X, m] using hsearch
    rw [he0] at he
    simpa only [searchProgram, initialBank, S, stackCfg,
      ChosenPrimeRaw.initial] using he
  have hP : S ChosenSizeSuffix.primeCell = List.replicate p true := by
    change (bank searchSlots (foreignBank d a q t) F)
      (searchSlots (.inr 3)) = _
    rw [bank_at]
    exact hprime
  have hT : S ChosenSizeSuffix.tCell = List.replicate t true := by
    simp [S, ChosenSizeSuffix.tCell, bank_outside,
      searchSlots, foreignBank]
  have hL : S ChosenSizeSuffix.writerL = [] := by
    simp [S, ChosenSizeSuffix.writerL, bank_outside,
      searchSlots, foreignBank, partialL_zero]
  have hf : S ChosenSizeSuffix.fuelCell = [] := by
    simp [S, ChosenSizeSuffix.fuelCell, bank_outside,
      searchSlots, foreignBank]
  have hc : S (.inr (.inr 2)) = [] := by
    simp [S, bank_outside, searchSlots, foreignBank]
  have h3 : S (.inr (.inr 3)) = [] := by
    simp [S, bank_outside, searchSlots, foreignBank]
  have h4 : S (.inr (.inr 4)) = [] := by
    simp [S, bank_outside, searchSlots, foreignBank]
  have h5 : S (.inr (.inr 5)) = [] := by
    simp [S, bank_outside, searchSlots, foreignBank]
  have h6 : S (.inr (.inr 6)) = [] := by
    simp [S, bank_outside, searchSlots, foreignBank]
  obtain ⟨uz,huz,hz⟩ := ChosenSizeSuffix.size_suffix_run S p t
    hP hT hL hf hc h3 h4 h5 h6
  have hz0 : ((advance ChosenSizeSuffix.program)^[uz])
      (⟨some ChosenSizeSuffix.start,ChosenSizeSuffix.initialControl,S⟩ :
        TM2.Cfg (fun _ : Stack => Bool)
          ChosenSizeSuffix.Label ChosenSizeSuffix.Control) =
      ⟨none,ChosenSizeSuffix.initialControl,
        Function.update S ChosenSizeSuffix.writerL (List.replicate (L d a q t) true)⟩ := by
    simpa only [L, PrimeSampler.size_exact, m, p] using hz
  obtain ⟨u,hu,hr⟩ := BitMachineRawSequence.runs
    searchProgram ChosenSizeSuffix.program (.inr .initialize)
    ChosenSizeSuffix.start
    (ChosenPrimeRaw.initial (X d a q t)).var v
    ChosenSizeSuffix.initialControl ChosenSizeSuffix.initialControl
    (initialBank d a q t) S
    (Function.update S ChosenSizeSuffix.writerL (List.replicate (L d a q t) true))
    up uz hs hz0
  refine ⟨u, ?_, F, ?_, hprime, ?_⟩
  · have hpu : up ≤ ChosenPrimeRaw.bound (X d a q t) := by
      simpa only [X, m] using hup
    have hzu : uz ≤ ChosenSizeSuffix.bound
        (PrimeSampler.prime q t (Construction.qOne a * d.rx)) t := by
      simpa only [p, m] using huz
    unfold bound
    omega
  · simpa only [program, start, initialControl, S] using hr
  · exact writer_projection d a q t (L d a q t) F

#print axioms size_from_threshold

end
end EthInapproximability.CurrentPaper.ChosenSizeFromThreshold
