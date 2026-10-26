import EthInapproximability.CurrentPaper.ChosenSizeFromThreshold
import EthInapproximability.CurrentPaper.BitMachineStackRun

/-! The frozen physical prime-search/power program framed over an arbitrary
weighted writer, requiring only its output cell57 initially blank. -/

namespace EthInapproximability.CurrentPaper.ChosenSizeArbitraryWriter

open Turing BitMachineEncoding BitMachineStackEmbedding
noncomputable section

abbrev Stack := ChosenSizeSuffix.Stack
def searchSlots : ChosenPrimeRaw.Stack ↪ Stack :=
  ⟨Sum.inl,by intro a b h; exact Sum.inl_injective h⟩
def writer (k : Fin 64) : Stack := .inr (.inl k)
def foreignBank (W : Fin 64 → List Bool) (t : ℕ) : Stack → List Bool
  | .inl _ => []
  | .inr (.inl k) => W k
  | .inr (.inr k) => if k = 0 then List.replicate t true else []

def initialBank (W : Fin 64 → List Bool) (q t m : ℕ) : Stack → List Bool :=
  bank searchSlots (foreignBank W t)
    (ChosenPrimeRaw.initial (PrimeSampler.threshold q t m)).stk
def searchProgram := fun l => stackStmt searchSlots (ChosenPrimeRaw.program l)
def program := BitMachineRawSequence.program searchProgram ChosenSizeSuffix.program
  ChosenSizeSuffix.start (ChosenPrimeRaw.initial 2).var
    ChosenSizeSuffix.initialControl
def start : ChosenSizeFromThreshold.Label :=
  BitMachineRawSequence.leftLabel (.inr .initialize)
def initialControl : ChosenSizeFromThreshold.Control := ((ChosenPrimeRaw.initial 2).var,
  ChosenSizeSuffix.initialControl)
def bound (q t m : ℕ) := ChosenPrimeRaw.bound (PrimeSampler.threshold q t m) +
  ChosenSizeSuffix.bound (PrimeSampler.prime q t m) t + 1

theorem run (W : Fin 64 → List Bool) (q t m : ℕ) (h57 : W 57 = []) :
    ∃ u ≤ bound q t m,
      ∃ F : ChosenPrimeRaw.Stack → List Bool,
        ((advance program)^[u])
          (⟨some start,initialControl,initialBank W q t m⟩ :
            TM2.Cfg (fun _ : Stack => Bool) _ _) =
          ⟨none,initialControl,
            Function.update (bank searchSlots (foreignBank W t) F)
              ChosenSizeSuffix.writerL
              (List.replicate (PrimeSampler.size q t m) true)⟩ ∧
        F (.inr 3) = List.replicate (PrimeSampler.prime q t m) true ∧
        (fun k : Fin 64 =>
          (Function.update (bank searchSlots (foreignBank W t) F)
            ChosenSizeSuffix.writerL
            (List.replicate (PrimeSampler.size q t m) true)) (writer k)) =
          Function.update W 57 (List.replicate (PrimeSampler.size q t m) true) := by
  let p := PrimeSampler.prime q t m
  obtain ⟨up,hup,v,F,hsearch,hprime⟩ := ChosenPrimeRaw.chosen_run q t m
  let S := bank searchSlots (foreignBank W t) F
  have hs : ((advance searchProgram)^[up])
      (⟨some (.inr .initialize),(ChosenPrimeRaw.initial (PrimeSampler.threshold q t m)).var,
        initialBank W q t m⟩ :
        TM2.Cfg (fun _ : Stack => Bool) ChosenPrimeRaw.Label ChosenPrimeRaw.Control) =
      ⟨none,v,S⟩ := by
    have he := BitMachineStackRun.run searchSlots (foreignBank W t)
      ChosenPrimeRaw.program
      (ChosenPrimeRaw.initial (PrimeSampler.threshold q t m)) up
    rw [hsearch] at he
    simpa only [searchProgram,initialBank,S,stackCfg,
      ChosenPrimeRaw.initial] using he
  have hP : S ChosenSizeSuffix.primeCell = List.replicate p true := by
    change (bank searchSlots (foreignBank W t) F) (searchSlots (.inr 3)) = _
    rw [bank_at]
    exact hprime
  have hT : S ChosenSizeSuffix.tCell = List.replicate t true := by
    simp [S,ChosenSizeSuffix.tCell,bank_outside,searchSlots,foreignBank]
  have hL : S ChosenSizeSuffix.writerL = [] := by
    simpa [S,ChosenSizeSuffix.writerL,bank_outside,searchSlots,foreignBank] using h57
  have hf : S ChosenSizeSuffix.fuelCell = [] := by
    simp [S,ChosenSizeSuffix.fuelCell,bank_outside,searchSlots,foreignBank]
  have hc : S (.inr (.inr 2)) = [] := by
    simp [S,bank_outside,searchSlots,foreignBank]
  have h3 : S (.inr (.inr 3)) = [] := by
    simp [S,bank_outside,searchSlots,foreignBank]
  have h4 : S (.inr (.inr 4)) = [] := by
    simp [S,bank_outside,searchSlots,foreignBank]
  have h5 : S (.inr (.inr 5)) = [] := by
    simp [S,bank_outside,searchSlots,foreignBank]
  have h6 : S (.inr (.inr 6)) = [] := by
    simp [S,bank_outside,searchSlots,foreignBank]
  obtain ⟨uz,huz,hz⟩ := ChosenSizeSuffix.size_suffix_run S p t
    hP hT hL hf hc h3 h4 h5 h6
  have hz0 : ((advance ChosenSizeSuffix.program)^[uz])
      (⟨some ChosenSizeSuffix.start,ChosenSizeSuffix.initialControl,S⟩ :
        TM2.Cfg (fun _ : Stack => Bool)
          ChosenSizeSuffix.Label ChosenSizeSuffix.Control) =
      ⟨none,ChosenSizeSuffix.initialControl,
        Function.update S ChosenSizeSuffix.writerL
          (List.replicate (PrimeSampler.size q t m) true)⟩ := by
    simpa only [p,PrimeSampler.size_exact] using hz
  obtain ⟨u,hu,hr⟩ := BitMachineRawSequence.runs
    searchProgram ChosenSizeSuffix.program (.inr .initialize)
    ChosenSizeSuffix.start
    (ChosenPrimeRaw.initial (PrimeSampler.threshold q t m)).var v
    ChosenSizeSuffix.initialControl ChosenSizeSuffix.initialControl
    (initialBank W q t m) S
    (Function.update S ChosenSizeSuffix.writerL
      (List.replicate (PrimeSampler.size q t m) true))
    up uz hs hz0
  refine ⟨u,?_,F,?_,hprime,?_⟩
  · have huz' : uz ≤ ChosenSizeSuffix.bound (PrimeSampler.prime q t m) t := by
      simpa only [p] using huz
    dsimp [bound]
    omega
  · simpa only [program,start,initialControl,S] using hr
  · funext k
    by_cases hk : k = 57
    · subst k
      simp [writer,ChosenSizeSuffix.writerL]
    · have hout : ¬ ∃ j : ChosenPrimeRaw.Stack,
          searchSlots j = (writer k : Stack) := by
        rintro ⟨j,h⟩; cases h
      have hne : writer k ≠ ChosenSizeSuffix.writerL := by
        simpa [writer,ChosenSizeSuffix.writerL] using hk
      rw [Function.update_of_ne hne]
      rw [bank_outside searchSlots (foreignBank W t) F _ hout]
      simp [foreignBank,writer,Function.update_of_ne hk]

#print axioms run

end
end EthInapproximability.CurrentPaper.ChosenSizeArbitraryWriter
