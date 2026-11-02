import CurrentAdditive.QuarticEllPhysical

/-! A single fixed program from unary vertex count to unary quartic width:
the old L producer, a physical copy of its ell output, then the checked
quartic-width machine. -/

namespace Paper2.CurrentAdditive.QuarticNumericFront.WidthFromN

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open BitMachineRawSequence (leftLabel)
open CurrentAdditive.RandomizedSchedule

abbrev Stack := LProducer.LK ⊕ (WidthMachine.Stack ⊕ Fin 1)

instance : DecidableEq Stack := inferInstance

def lSlots : LProducer.LK ↪ Stack := ⟨Sum.inl, Sum.inl_injective⟩
def wSlots : WidthMachine.Stack ↪ Stack :=
  ⟨fun x => .inr (.inl x), by intro x y h; cases h; rfl⟩
def source : Stack := .inl (LProducer.outR 1)
def target : Stack := .inr (.inl 0)
def scratch : Stack := .inr (.inr 0)
def copySlots : Fin 3 ↪ Stack := ⟨![source, target, scratch], by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [source, target, scratch]⟩

def initial (n : ℕ) : Stack → List Bool :=
  Sum.elim (LProducer.L0 n) (fun _ => [])

def lProgram := fun l => stackStmt lSlots (LProducer.lProg l)
def copyProgram := MatrixStage4ScalarPreparationOps.copyProgram copySlots
def wProgram := fun l => stackStmt wSlots (WidthMachine.program l)
def first := BitMachineRawSequence.program lProgram copyProgram .scan LProducer.lCtl
  (none : Option Bool)
def firstControl := (LProducer.lCtl, (none : Option Bool))
def program := BitMachineRawSequence.program first wProgram WidthMachine.startLabel
  firstControl WidthMachine.initialControl
def initialControl := (firstControl, WidthMachine.initialControl)
def startLabel := FullFront.labelOfP program
  (leftLabel (leftLabel LProducer.lStart))

def clock (n : ℕ) : ℕ :=
  LProducer.lBd n +
    (2 * RestorationWidthScheduleScratch.ell (Nat.clog 2 n) + 2) +
    WidthMachine.clock (RestorationWidthScheduleScratch.ell (Nat.clog 2 n)) + 2

theorem run (n : ℕ) :
    let e := RestorationWidthScheduleScratch.ell (Nat.clog 2 n)
    ∃ T ≤ clock n, ∃ F : LProducer.LK → List Bool,
      ((advance program)^[T])
        (⟨some startLabel, initialControl, initial n⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, initialControl,
          Sum.elim F (Sum.elim
            (Function.update (Function.update (Function.update (WidthMachine.initial e) 1
              (List.replicate 4 true)) 5 (List.replicate (4 * e) true))
              9 (List.replicate (width27 (Nat.clog 2 n)) true))
            (fun _ => []))⟩ ∧ CountFront.LFacts n F := by
  intro e
  obtain ⟨tL, htL, vcL, F, hrL, hEll, hFacts⟩ := l_program_writes_ell n
  let S1 : Stack → List Bool := Sum.elim F (fun _ => [])
  have hL : ((advance lProgram)^[tL])
      (⟨some LProducer.lStart, LProducer.lCtl, initial n⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, vcL, S1⟩ := by
    have h := BitMachineStackRun.run lSlots (initial n) LProducer.lProg
      (⟨some LProducer.lStart, LProducer.lCtl, LProducer.L0 n⟩ :
        TM2.Cfg (fun _ : LProducer.LK => Bool) _ _) tL
    rw [hrL] at h
    have hstart : bank lSlots (initial n) (LProducer.L0 n) = initial n := by
      apply bank_eq_self
      intro x
      rfl
    have hfinish : bank lSlots (initial n) F = S1 := by
      funext x
      rcases x with x | x
      · exact bank_at lSlots (initial n) F x
      · exact bank_outside lSlots (initial n) F (.inr x) (by rintro ⟨y, hy⟩; cases hy)
    simpa only [lProgram, stackCfg, hstart, hfinish] using h
  let S2 : Stack → List Bool := Sum.elim F
    (Sum.elim (WidthMachine.initial e) (fun _ => []))
  have hCopy : ((advance copyProgram)^[2 * e + 2])
      (⟨some .scan, (none : Option Bool), S1⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, none, S2⟩ := by
    have hc := MatrixStage4ScalarPreparationOps.copy_run copySlots S1
      (by rfl)
    have hsrc : (S1 (copySlots 0)).length = e := by
      change (F (LProducer.outR 1)).length = e
      rw [hEll, List.length_replicate]
    rw [hsrc] at hc
    have hfinish : Function.update S1 (copySlots 1)
        (S1 (copySlots 0) ++ S1 (copySlots 1)) = S2 := by
      funext x
      by_cases hx : x = target
      · subst x
        rw [show copySlots 1 = target from rfl, Function.update_self]
        change F (LProducer.outR 1) ++ [] = WidthMachine.initial e 0
        rw [hEll, List.append_nil]
        rfl
      · rw [Function.update_of_ne (by simpa only [copySlots] using hx)]
        rcases x with x | x | x
        · rfl
        · have hx0 : x ≠ 0 := by
            intro h0
            apply hx
            simp [target, h0]
          change [] = WidthMachine.initial e x
          simp [WidthMachine.initial, Function.update_of_ne hx0]
        · fin_cases x
          rfl
    rw [hfinish] at hc
    exact hc
  obtain ⟨tW, htW, hrW⟩ := WidthMachine.run e
  let FW := Function.update (Function.update (Function.update (WidthMachine.initial e) 1
    (List.replicate 4 true)) 5 (List.replicate (4 * e) true))
    9 (List.replicate (2 ^ (4 * e)) true)
  have hW : ((advance wProgram)^[tW])
      (⟨some WidthMachine.startLabel, WidthMachine.initialControl, S2⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, WidthMachine.initialControl, Sum.elim F (Sum.elim FW (fun _ => []))⟩ := by
    have h := BitMachineStackRun.run wSlots S2 WidthMachine.program
      (⟨some WidthMachine.startLabel, WidthMachine.initialControl,
        WidthMachine.initial e⟩ :
        TM2.Cfg (fun _ : WidthMachine.Stack => Bool) _ _) tW
    rw [hrW] at h
    have hstart : bank wSlots S2 (WidthMachine.initial e) = S2 := by
      apply bank_eq_self
      intro x
      rfl
    have hfinish : bank wSlots S2 FW = Sum.elim F (Sum.elim FW (fun _ => [])) := by
      funext x
      rcases x with x | x | x
      · exact bank_outside wSlots S2 FW (.inl x) (by rintro ⟨y, hy⟩; cases hy)
      · exact bank_at wSlots S2 FW x
      · exact bank_outside wSlots S2 FW (.inr (.inr x)) (by rintro ⟨y, hy⟩; cases hy)
    change ((advance wProgram)^[tW])
      (⟨some WidthMachine.startLabel, WidthMachine.initialControl,
        bank wSlots S2 (WidthMachine.initial e)⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, WidthMachine.initialControl, bank wSlots S2 FW⟩ at h
    rw [hstart, hfinish] at h
    exact h
  obtain ⟨tLC, htLC, hrLC⟩ := BitMachineRawSequence.runs lProgram copyProgram
    LProducer.lStart .scan LProducer.lCtl vcL none none
    (initial n) S1 S2 tL (2 * e + 2) hL hCopy
  obtain ⟨T, hT, hr⟩ := BitMachineRawSequence.runs first wProgram
    (leftLabel LProducer.lStart) WidthMachine.startLabel firstControl firstControl
    WidthMachine.initialControl WidthMachine.initialControl
    (initial n) S2 (Sum.elim F (Sum.elim FW (fun _ => [])))
    tLC tW hrLC hW
  refine ⟨T, ?_, F, ?_, hFacts⟩
  · change T ≤ LProducer.lBd n + (2 * e + 2) + WidthMachine.clock e + 2
    omega
  · simpa only [program, startLabel, initialControl, FW, e, width27,
      Nat.mul_comm] using hr

end
end Paper2.CurrentAdditive.QuarticNumericFront.WidthFromN

#print axioms Paper2.CurrentAdditive.QuarticNumericFront.WidthFromN.run
