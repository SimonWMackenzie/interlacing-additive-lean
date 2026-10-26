import EthInapproximability.CurrentPaper.ChosenPrimeRaw
import EthInapproximability.CurrentPaper.BitMachineStackGrowth
import EthInapproximability.CurrentPaper.BitMachineClearBank
import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps
import EthInapproximability.CurrentPaper.BitMachineRawSequence
import EthInapproximability.CurrentPaper.BitMachineStackRun

/-!
# The chosen prime as a unary word with an EXACT exit bank

Lane owner:b-stage4-entry-program, segment 1 (prime operand word).

The admitted `ChosenPrimeRaw.chosen_run` runs the production prime search from
the unary threshold and exposes only its output stack; its other stacks are
existential. This fixed three-phase controller (search; charged copy of the
output stack into a target cell; charged pop-clear of EVERY search stack)
ends at an exact bank: target = `unary (PrimeSampler.prime q t m)`, every
other cell blank. The clear is charged with the `BitMachineStackGrowth`
majorant of the search run, so the clock is a public function of the
threshold.
-/

namespace EthInapproximability.CurrentPaper.PrimeWordExact

open Turing BitMachineEncoding BitMachineStackEmbedding
open MatrixStage4ScalarPreparationOps

noncomputable section

abbrev SStack := ChosenPrimeRaw.Stack
abbrev Stack := SStack ⊕ Fin 2

def searchSlots : SStack ↪ Stack := ⟨Sum.inl, Sum.inl_injective⟩

def target : Stack := .inr 0

def nCells : ℕ := ChosenPrimeRaw.Tester.stackCount + 4

def clearCells : Fin nCells ↪ Stack :=
  ⟨fun i => .inl (finSumFinEquiv.symm i),
    fun _ _ h => finSumFinEquiv.symm.injective (Sum.inl_injective h)⟩

inductive ClearLabel where
  | clear (i : Fin (nCells + 1))
  | done

def clearProgram : ClearLabel →
    TM2.Stmt (fun _ : Stack => Bool) ClearLabel (Unit × Option Bool)
  | .clear i => if h : i.val < nCells then
      BitMachineClearBank.clearStep (clearCells ⟨i.val, h⟩)
        (.clear i) (.clear ⟨i.val + 1, by omega⟩)
    else BitMachineClearBank.finishStep (fun _ => ()) .done
  | .done => .halt

def clearCost (S : Stack → List Bool) : ℕ :=
  (∑ i : Fin nCells, (S (clearCells i)).length) + nCells + 2

theorem clear_run (S : Stack → List Bool) :
    ((advance clearProgram)^[clearCost S])
      (⟨some (.clear 0), ((), none), S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) ClearLabel (Unit × Option Bool)) =
      ⟨none, ((), none), BitMachineClearBank.cleared clearCells S⟩ := by
  have hs (i : Fin nCells) : clearProgram (.clear i.castSucc) =
      BitMachineClearBank.clearStep (clearCells i)
        (.clear i.castSucc) (.clear i.succ) := by
    simp only [clearProgram, Fin.val_castSucc, dif_pos i.isLt]
    rfl
  have hf : clearProgram (.clear (Fin.last nCells)) =
      BitMachineClearBank.finishStep (fun _ => ()) .done := by
    simp only [clearProgram, Fin.val_last, lt_self_iff_false, ↓reduceDIte]
  have hr := BitMachineClearBank.clear_bank_run clearProgram
    (fun _ => ()) ClearLabel.done nCells clearCells clearCells.injective
    ClearLabel.clear hs hf () S
  have hd : advance clearProgram
      (⟨some .done, ((), none), BitMachineClearBank.cleared clearCells S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) ClearLabel (Unit × Option Bool)) =
      ⟨none, ((), none), BitMachineClearBank.cleared clearCells S⟩ := rfl
  rw [clearCost, show (∑ i : Fin nCells, (S (clearCells i)).length) + nCells + 2 =
      1 + ((∑ i : Fin nCells, (S (clearCells i)).length) + nCells + 1) by omega,
    Function.iterate_add_apply, hr]
  exact hd

def copySlots : Fin 3 ↪ Stack :=
  ⟨![.inl (.inr 3), .inr 0, .inr 1], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all⟩

def searchProgram (l : ChosenPrimeRaw.Label) :
    TM2.Stmt (fun _ : Stack => Bool) ChosenPrimeRaw.Label ChosenPrimeRaw.Control :=
  stackStmt searchSlots (ChosenPrimeRaw.program l)

def searchStart : ChosenPrimeRaw.Label := .inr .initialize
def searchControl : ChosenPrimeRaw.Control := (ChosenPrimeRaw.Tester.initial, none)

abbrev TailLabel := BitMachineRawSequence.Label BitMachineCopy.Label ClearLabel
abbrev TailControl := BitMachineRawSequence.Control (Option Bool) (Unit × Option Bool)
abbrev Label := BitMachineRawSequence.Label ChosenPrimeRaw.Label TailLabel
abbrev Control := BitMachineRawSequence.Control ChosenPrimeRaw.Control TailControl

def tailProgram : TailLabel → TM2.Stmt (fun _ : Stack => Bool) TailLabel TailControl :=
  BitMachineRawSequence.program (copyProgram copySlots) clearProgram (.clear 0)
    (none : Option Bool) ((), none)

def tailStart : TailLabel := BitMachineRawSequence.leftLabel .scan
def tailControl : TailControl := (none, ((), none))

/-- The single fixed controller. -/
def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  BitMachineRawSequence.program searchProgram tailProgram tailStart searchControl tailControl

def start : Label := BitMachineRawSequence.leftLabel searchStart
def initControl : Control := (searchControl, tailControl)

/-- Start bank: the production search's own initial bank (unary threshold
in its candidate stack, everything else blank) and two blank cells. -/
def startBank (X : ℕ) : Stack → List Bool :=
  Sum.elim (ChosenPrimeRaw.initial X).stk (fun _ => [])

/-- Exact exit bank: only the prime word survives. -/
def exitBank (p : ℕ) : Stack → List Bool :=
  Sum.elim (fun _ => []) ![List.replicate p true, []]

def wordBound (X : ℕ) : ℕ :=
  ChosenPrimeRaw.bound X + (2 * (2 * X) + 2) +
    (nCells * (X + BitMachineStackGrowth.perStep ChosenPrimeRaw.program *
      ChosenPrimeRaw.bound X) + nCells + 2) + 2

theorem bank_search (S : SStack → List Bool) :
    bank searchSlots (fun _ => []) S = Sum.elim S (fun _ => []) := by
  funext k
  rcases k with k | k
  · exact bank_at searchSlots (fun _ => []) S k
  · apply bank_outside
    rintro ⟨j, hj⟩
    cases hj

theorem initial_length_le (X : ℕ) (k : SStack) :
    ((ChosenPrimeRaw.initial X).stk k).length ≤ X := by
  rcases k with k | k
  · simp [ChosenPrimeRaw.initial, PrimeSamplerSearch.adminCfg, PrimeSamplerSearch.cfg]
  · fin_cases k <;>
      simp [ChosenPrimeRaw.initial, PrimeSamplerSearch.adminCfg, PrimeSamplerSearch.cfg,
        PrimeSamplerSearch.foreign]

theorem prime_word (q t m : ℕ) :
    ∃ u ≤ wordBound (PrimeSampler.threshold q t m),
      ((advance program)^[u])
        (⟨some start, initControl, startBank (PrimeSampler.threshold q t m)⟩ :
          TM2.Cfg (fun _ : Stack => Bool) Label Control) =
        ⟨none, initControl, exitBank (PrimeSampler.prime q t m)⟩ := by
  obtain ⟨u, hu, v, F, hrun, hout⟩ := ChosenPrimeRaw.chosen_run q t m
  have hp2 : PrimeSampler.prime q t m < 2 * PrimeSampler.threshold q t m :=
    (PrimeSampler.prime_window q t m).2
  set X := PrimeSampler.threshold q t m with hX
  set p := PrimeSampler.prime q t m with hp
  -- phase A: search, lifted
  have hinit : ChosenPrimeRaw.initial X =
      (⟨some searchStart, searchControl, (ChosenPrimeRaw.initial X).stk⟩ :
        ChosenPrimeRaw.Config) := rfl
  have hA0 := BitMachineStackRun.run searchSlots (fun _ => []) ChosenPrimeRaw.program
    (ChosenPrimeRaw.initial X) u
  change ((advance ChosenPrimeRaw.program)^[u]) (ChosenPrimeRaw.initial X) = _ at hrun
  rw [hrun] at hA0
  have hA : ((advance searchProgram)^[u])
      (⟨some searchStart, searchControl, startBank X⟩ :
        TM2.Cfg (fun _ : Stack => Bool) ChosenPrimeRaw.Label ChosenPrimeRaw.Control) =
      ⟨none, v, Sum.elim F (fun _ => [])⟩ := by
    have h1 : stackCfg searchSlots (fun _ => []) (ChosenPrimeRaw.initial X) =
        (⟨some searchStart, searchControl, startBank X⟩ :
          TM2.Cfg (fun _ : Stack => Bool) ChosenPrimeRaw.Label ChosenPrimeRaw.Control) := by
      rw [hinit]
      simp only [stackCfg, bank_search]
      rfl
    have h2 : stackCfg searchSlots (fun _ => [])
        (⟨none, v, F⟩ : ChosenPrimeRaw.Config) =
        (⟨none, v, Sum.elim F (fun _ => [])⟩ :
          TM2.Cfg (fun _ : Stack => Bool) ChosenPrimeRaw.Label ChosenPrimeRaw.Control) := by
      simp only [stackCfg, bank_search]
    rw [← h1, ← h2]
    exact hA0
  -- growth of every search stack
  have hgrow : ∀ k : SStack, (F k).length ≤ X +
      BitMachineStackGrowth.perStep ChosenPrimeRaw.program * ChosenPrimeRaw.bound X := by
    intro k
    have hg := BitMachineStackGrowth.run_growth ChosenPrimeRaw.program
      (ChosenPrimeRaw.initial X) u k
    change ((advance ChosenPrimeRaw.program)^[u]) (ChosenPrimeRaw.initial X) = _ at hrun
    rw [hrun] at hg
    have hi := initial_length_le X k
    have hm := Nat.mul_le_mul_left (BitMachineStackGrowth.perStep ChosenPrimeRaw.program) hu
    simp only at hg
    omega
  -- phase B: copy the prime word out
  let T : Stack → List Bool := Sum.elim F (fun _ => [])
  have hB0 := copy_run copySlots T rfl
  have hsrc : T (copySlots 0) = List.replicate p true := hout
  have htgt : T (copySlots 1) = [] := rfl
  rw [htgt, List.append_nil, hsrc, List.length_replicate] at hB0
  let U : Stack → List Bool := Function.update T target (List.replicate p true)
  have hB : ((advance (copyProgram copySlots))^[2 * p + 2])
      (⟨some .scan, none, T⟩ : TM2.Cfg (fun _ : Stack => Bool)
        BitMachineCopy.Label (Option Bool)) = ⟨none, none, U⟩ := hB0
  -- phase C: clear every search stack
  have hC := clear_run U
  have hcleared : BitMachineClearBank.cleared clearCells U = exitBank p := by
    funext k
    rcases k with k | k
    · have hk : ∃ i, clearCells i = Sum.inl k := ⟨finSumFinEquiv k, by
        simp [clearCells]⟩
      simp [BitMachineClearBank.cleared, hk, exitBank]
    · have hk : ¬ ∃ i, clearCells i = Sum.inr k := by
        rintro ⟨i, hi⟩
        simp [clearCells] at hi
      simp only [BitMachineClearBank.cleared, hk, if_false]
      fin_cases k
      · simp [U, target, exitBank]
      · show Function.update T target (List.replicate p true) (Sum.inr 1) =
          exitBank p (Sum.inr 1)
        rw [Function.update_of_ne (by simp [target])]
        rfl
  rw [hcleared] at hC
  have hcost : clearCost U ≤ nCells * (X +
      BitMachineStackGrowth.perStep ChosenPrimeRaw.program * ChosenPrimeRaw.bound X) +
      nCells + 2 := by
    unfold clearCost
    have hsum : (∑ i : Fin nCells, (U (clearCells i)).length) ≤
        ∑ _i : Fin nCells, (X + BitMachineStackGrowth.perStep ChosenPrimeRaw.program *
          ChosenPrimeRaw.bound X) := by
      apply Finset.sum_le_sum
      intro i _
      have hne : clearCells i ≠ target := by simp [clearCells, target]
      simp only [U, Function.update_of_ne hne]
      exact hgrow _
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
    omega
  -- sequencing
  obtain ⟨w, hw, hBC⟩ := BitMachineRawSequence.runs (copyProgram copySlots) clearProgram
    BitMachineCopy.Label.scan (.clear 0) (none : Option Bool) none ((), none) ((), none)
    T U (exitBank p) (2 * p + 2) (clearCost U) hB hC
  obtain ⟨z, hz, hall⟩ := BitMachineRawSequence.runs searchProgram tailProgram
    searchStart tailStart searchControl v tailControl tailControl
    (startBank X) T (exitBank p) u w hA hBC
  refine ⟨z, ?_, hall⟩
  unfold wordBound
  omega

#print axioms clear_run
#print axioms prime_word

end

end EthInapproximability.CurrentPaper.PrimeWordExact
