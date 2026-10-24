import CurrentAdditive.QuarticWidthFromNClock
import CurrentAdditive.QuarticQPhysical
import Paper2.CopyAll

/-! A fixed count-front carrier for the quartic schedule.  The first stage is
the physical unary-n to quartic-width program; the four copies and Q program
below are independent of the old restoration-width source. -/

namespace Paper2.CurrentAdditive.QuarticNumericFront.LQ27

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open BitMachineRawSequence (leftLabel)
open CurrentAdditive.RandomizedSchedule

abbrev WK := WidthFromN.Stack
abbrev QK := QProducer.QK
abbrev Stack := WK ⊕ (QK ⊕ Fin 1)

instance : DecidableEq Stack := inferInstance

def wc (x : WK) : Stack := .inl x
def qc (x : QK) : Stack := .inr (.inl x)
def scratch : Stack := .inr (.inr 0)
def wSlots : WK ↪ Stack := ⟨Sum.inl, Sum.inl_injective⟩
def qSlots : QK ↪ Stack :=
  ⟨fun x => .inr (.inl x), by intro x y h; cases h; rfl⟩

def source (i : Fin 4) : Stack :=
  ![wc (.inl LProducer.nC), wc (.inl (LProducer.outR 0)),
    wc (.inl LProducer.sC), wc (.inr (.inl 9))] i
def target (i : Fin 4) : Stack :=
  ![qc (.inl 0), qc (.inl 2), qc (.inl 3), qc (.inl 4)] i
def copySlots (i : Fin 4) : Fin 3 ↪ Stack :=
  ⟨![source i, target i, scratch], by
    intro x y h
    fin_cases i <;> fin_cases x <;> fin_cases y <;>
      simp_all [source, target, wc, qc, scratch]⟩

theorem src_ne_dst (i j : Fin 4) : copySlots i 0 ≠ copySlots j 1 := by
  fin_cases i <;> fin_cases j <;> simp [copySlots, source, target, wc, qc]

theorem scratch_ne_dst (i j : Fin 4) : copySlots i 2 ≠ copySlots j 1 := by
  fin_cases i <;> fin_cases j <;> simp [copySlots, scratch, target, qc]

theorem dst_injective (i j : Fin 4)
    (h : copySlots i 1 = copySlots j 1) : i = j := by
  fin_cases i <;> fin_cases j <;> simp_all [copySlots, target, qc]

def initial (n m : ℕ) : Stack → List Bool :=
  Sum.elim (WidthFromN.initial n)
    (Sum.elim (Function.update (fun _ => []) (.inl 1) (List.replicate m true))
      (fun _ => []))

def widthProgram := fun l => stackStmt wSlots (WidthFromN.program l)
def copyProgram := CopyAll.prog copySlots
def qProgram (Δ : ℕ) (γ : ℚ) :=
  fun l => stackStmt qSlots (QProducer.qProg γ.num.toNat γ.den Δ l)

def first := BitMachineRawSequence.program widthProgram copyProgram
  (.inl ⟨0, by omega⟩) WidthFromN.initialControl none
def firstControl := (WidthFromN.initialControl, (none : Option Bool))
def program (Δ : ℕ) (γ : ℚ) :=
  BitMachineRawSequence.program first (qProgram Δ γ)
    (QProducer.qStart γ.num.toNat γ.den Δ) firstControl QProducer.qCtl
def initialControl := (firstControl, QProducer.qCtl)
def startLabel (Δ : ℕ) (γ : ℚ) := FullFront.labelOfP (program Δ γ)
  (leftLabel (leftLabel WidthFromN.startLabel))

def widthBank (n m : ℕ) (F : LProducer.LK → List Bool) : Stack → List Bool :=
  Sum.elim
    (Sum.elim F (Sum.elim
      (Function.update (Function.update (Function.update
        (WidthMachine.initial (RestorationWidthScheduleScratch.ell (Nat.clog 2 n))) 1
        (List.replicate 4 true)) 5
        (List.replicate (4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 n)) true))
        9 (List.replicate (width27 (Nat.clog 2 n)) true)) (fun _ => [])))
    (Sum.elim (Function.update (fun _ => []) (.inl 1) (List.replicate m true))
      (fun _ => []))

theorem width_stage (n m : ℕ) :
    ∃ t ≤ WidthFromN.clock n, ∃ F : LProducer.LK → List Bool,
      ((advance widthProgram)^[t])
        (⟨some WidthFromN.startLabel, WidthFromN.initialControl, initial n m⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, WidthFromN.initialControl, widthBank n m F⟩ ∧
      CountFront.LFacts n F := by
  obtain ⟨t, ht, F, hr, hFacts⟩ := WidthFromN.run n
  let FW : WK → List Bool :=
    Sum.elim F (Sum.elim
      (Function.update (Function.update (Function.update
        (WidthMachine.initial (RestorationWidthScheduleScratch.ell (Nat.clog 2 n))) 1
        (List.replicate 4 true)) 5
        (List.replicate (4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 n)) true))
        9 (List.replicate (width27 (Nat.clog 2 n)) true)) (fun _ => []))
  have h := BitMachineStackRun.run wSlots (initial n m) WidthFromN.program
    (⟨some WidthFromN.startLabel, WidthFromN.initialControl, WidthFromN.initial n⟩ :
      TM2.Cfg (fun _ : WK => Bool) _ _) t
  rw [hr] at h
  have hstart : bank wSlots (initial n m) (WidthFromN.initial n) = initial n m := by
    apply bank_eq_self
    intro x
    rfl
  have hfinish : bank wSlots (initial n m) FW = widthBank n m F := by
    funext x
    rcases x with x | x | x
    · exact bank_at wSlots (initial n m) FW x
    · exact bank_outside wSlots (initial n m) FW (.inr (.inl x))
        (by rintro ⟨y, hy⟩; cases hy)
    · exact bank_outside wSlots (initial n m) FW (.inr (.inr x))
        (by rintro ⟨y, hy⟩; cases hy)
  refine ⟨t, ht, F, ?_, hFacts⟩
  simpa only [widthProgram, stackCfg, hstart, hfinish, widthBank, FW]
    using h

def sourceValue (n : ℕ) : Fin 4 → ℕ :=
  ![n, Nat.clog 2 n, SourceProfileParameters.width (Nat.clog 2 n),
    width27 (Nat.clog 2 n)]

def copyBound (n : ℕ) : ℕ :=
  n + Nat.clog 2 n + SourceProfileParameters.width (Nat.clog 2 n) +
    width27 (Nat.clog 2 n)

theorem widthBank_source (n m : ℕ) (F : LProducer.LK → List Bool)
    (hFacts : CountFront.LFacts n F) (i : Fin 4) :
    widthBank n m F (copySlots i 0) =
      List.replicate (sourceValue n i) true := by
  obtain ⟨hn, -, -, -, -, -, -, -, hs, -, -, -, -, -, -, -, g0, g1,
    hr0, -, hout0, -⟩ := hFacts
  have hL : F (LProducer.outR 0) = List.replicate (Nat.clog 2 n) true :=
    (hr0 _).trans hout0
  fin_cases i
  · change F LProducer.nC = List.replicate n true
    simpa only [LProducer.u] using hn
  · change F (LProducer.outR 0) = List.replicate (Nat.clog 2 n) true
    exact hL
  · change F LProducer.sC =
      List.replicate (SourceProfileParameters.width (Nat.clog 2 n)) true
    rw [LProducer.s_eq]
    exact hs
  · change (Function.update (Function.update (Function.update
        (WidthMachine.initial (RestorationWidthScheduleScratch.ell (Nat.clog 2 n))) 1
        (List.replicate 4 true)) 5
        (List.replicate (4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 n)) true))
        9 (List.replicate (width27 (Nat.clog 2 n)) true)) 9 =
        List.replicate (width27 (Nat.clog 2 n)) true
    exact Function.update_self _ _ _

theorem copies_stage (n m : ℕ) (F : LProducer.LK → List Bool)
    (hFacts : CountFront.LFacts n F) :
    ∃ t ≤ 4 * (2 * copyBound n + 3) + 1, ∃ vc,
      ((advance copyProgram)^[t])
        (⟨some (.inl ⟨0, by omega⟩), none, widthBank n m F⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, vc, CopyAll.done copySlots 4 (widthBank n m F)⟩ := by
  apply CopyAll.all_run copySlots src_ne_dst scratch_ne_dst dst_injective
    (widthBank n m F)
  · intro i
    change ([] : List Bool) = []
    rfl
  · intro i
    rw [widthBank_source n m F hFacts i, List.length_replicate]
    fin_cases i <;> simp [sourceValue, copyBound] <;> omega

theorem copied_q_input (n m : ℕ) (F : LProducer.LK → List Bool)
    (hFacts : CountFront.LFacts n F) (i : Fin 4) :
    CopyAll.done copySlots 4 (widthBank n m F) (target i) =
      List.replicate (sourceValue n i) true := by
  have h := CopyAll.done_dst copySlots dst_injective (widthBank n m F) i
  rw [show copySlots i 1 = target i from rfl] at h
  rw [h, widthBank_source n m F hFacts i]
  have hblank : widthBank n m F (copySlots i 1) = [] := by
    fin_cases i <;> change ([] : List Bool) = [] <;> rfl
  have hblank' : widthBank n m F (target i) = [] := by
    simpa only [show copySlots i 1 = target i from rfl] using hblank
  rw [hblank', List.append_nil]

theorem copied_q_bank (n m : ℕ) (F : LProducer.LK → List Bool)
    (hFacts : CountFront.LFacts n F) :
    bank qSlots (CopyAll.done copySlots 4 (widthBank n m F))
      (QProducer.Q0 n m (Nat.clog 2 n)
        (SourceProfileParameters.width (Nat.clog 2 n))
        (width27 (Nat.clog 2 n))) =
      CopyAll.done copySlots 4 (widthBank n m F) := by
  apply bank_eq_self
  intro x
  change QProducer.Q0 n m (Nat.clog 2 n)
      (SourceProfileParameters.width (Nat.clog 2 n))
      (width27 (Nat.clog 2 n)) x =
    CopyAll.done copySlots 4 (widthBank n m F) (qc x)
  have h0 := copied_q_input n m F hFacts 0
  have h2 := copied_q_input n m F hFacts 1
  have h3 := copied_q_input n m F hFacts 2
  have h4 := copied_q_input n m F hFacts 3
  have hother (x : QK)
      (hx : ∀ j : Fin 4, target j ≠ qc x) :
      CopyAll.done copySlots 4 (widthBank n m F) (qc x) =
        widthBank n m F (qc x) := by
    apply CopyAll.done_off
    intro j
    exact hx j
  by_cases hx0 : x = .inl 0
  · subst x
    change QProducer.Q0 n m (Nat.clog 2 n)
      (SourceProfileParameters.width (Nat.clog 2 n))
      (width27 (Nat.clog 2 n)) (.inl 0) =
      CopyAll.done copySlots 4 (widthBank n m F) (target 0)
    rw [h0]
    rfl
  by_cases hx1 : x = .inl 1
  · subst x
    have h := hother (.inl 1) (by intro j; fin_cases j <;> simp [target, qc])
    rw [h]
    rfl
  by_cases hx2 : x = .inl 2
  · subst x
    change QProducer.Q0 n m (Nat.clog 2 n)
      (SourceProfileParameters.width (Nat.clog 2 n))
      (width27 (Nat.clog 2 n)) (.inl 2) =
      CopyAll.done copySlots 4 (widthBank n m F) (target 1)
    rw [h2]
    rfl
  by_cases hx3 : x = .inl 3
  · subst x
    have h3' : CopyAll.done copySlots 4 (widthBank n m F) (target 2) =
        List.replicate (SourceProfileParameters.width (Nat.clog 2 n)) true := by
      simpa only [sourceValue] using h3
    change QProducer.Q0 n m (Nat.clog 2 n)
      (SourceProfileParameters.width (Nat.clog 2 n))
      (width27 (Nat.clog 2 n)) (.inl 3) =
      CopyAll.done copySlots 4 (widthBank n m F) (target 2)
    rw [h3']
    simp only [QProducer.Q0, QProducer.u, Function.update_self,
      Function.update_of_ne (by decide : (Sum.inl (3 : Fin 29) : QK) ≠ .inl 4)]
  by_cases hx4 : x = .inl 4
  · subst x
    change QProducer.Q0 n m (Nat.clog 2 n)
      (SourceProfileParameters.width (Nat.clog 2 n))
      (width27 (Nat.clog 2 n)) (.inl 4) =
      CopyAll.done copySlots 4 (widthBank n m F) (target 3)
    rw [h4]
    rfl
  have hkeep := hother x (by
    intro j
    fin_cases j <;> simp [target, qc, Ne.symm hx0, Ne.symm hx2,
      Ne.symm hx3, Ne.symm hx4])
  rw [hkeep]
  have hbase : widthBank n m F (qc x) = [] := by
    change (Function.update (fun _ : QK => []) (.inl 1)
      (List.replicate m true)) x = []
    simp only [Function.update_of_ne hx1]
  have hQ : QProducer.Q0 n m (Nat.clog 2 n)
      (SourceProfileParameters.width (Nat.clog 2 n))
      (width27 (Nat.clog 2 n)) x = [] := by
    simp only [QProducer.Q0,
      Function.update_of_ne hx0, Function.update_of_ne hx1,
      Function.update_of_ne hx2, Function.update_of_ne hx3,
      Function.update_of_ne hx4]
  rw [hbase, hQ]

theorem q_stage (n m Δ : ℕ) (γ : ℚ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hn : 0 < n) (hm : 0 < m)
    (F : LProducer.LK → List Bool) (hFacts : CountFront.LFacts n F) :
    let B := CopyAll.done copySlots 4 (widthBank n m F)
    ∃ t ≤ QProducer.qBd γ.num.toNat γ.den Δ n m (Nat.clog 2 n)
      (SourceProfileParameters.width (Nat.clog 2 n)) (width27 (Nat.clog 2 n)),
      ∃ vc, ∃ FQ : QK → List Bool,
        ((advance (qProgram Δ γ))^[t])
          (⟨some (QProducer.qStart γ.num.toNat γ.den Δ), QProducer.qCtl, B⟩ :
            TM2.Cfg (fun _ : Stack => Bool) _ _) =
          ⟨none, vc, bank qSlots B FQ⟩ ∧
        FQ (.inl 1) = List.replicate m true ∧
        FQ (.inl 24) = List.replicate
          (Q27 (V := Fin n) (E := Fin m) (Nat.clog 2 n) γ Δ) true := by
  intro B
  obtain ⟨t, ht, vc, FQ, hr, hm, hQ⟩ := q_program_writes_Q27 n m (Nat.clog 2 n) Δ γ
    hγ hΔ hn hm
  have h := BitMachineStackRun.run qSlots B (QProducer.qProg γ.num.toNat γ.den Δ)
    (⟨some (QProducer.qStart γ.num.toNat γ.den Δ), QProducer.qCtl,
      QProducer.Q0 n m (Nat.clog 2 n)
        (SourceProfileParameters.width (Nat.clog 2 n))
        (width27 (Nat.clog 2 n))⟩ :
      TM2.Cfg (fun _ : QK => Bool) _ _) t
  rw [hr] at h
  have hstart := copied_q_bank n m F hFacts
  change bank qSlots B (QProducer.Q0 n m (Nat.clog 2 n)
    (SourceProfileParameters.width (Nat.clog 2 n))
    (width27 (Nat.clog 2 n))) = B at hstart
  refine ⟨t, ht, vc, FQ, ?_, hm, hQ⟩
  simpa only [qProgram, stackCfg, hstart] using h

def clock (n m Δ : ℕ) (γ : ℚ) : ℕ :=
  WidthFromN.clock n + (4 * (2 * copyBound n + 3) + 1) +
    QProducer.qBd γ.num.toNat γ.den Δ n m (Nat.clog 2 n)
      (SourceProfileParameters.width (Nat.clog 2 n)) (width27 (Nat.clog 2 n)) + 2

/-- A single fixed L, quartic-width, Q program; the packet supplies only unary
vertex/edge counts. Its output keeps the old public L facts and has exact
quartic Q in the Q-machine region. -/
theorem run (n m Δ : ℕ) (γ : ℚ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hn : 0 < n) (hm : 0 < m) :
    ∃ t ≤ clock n m Δ γ, ∃ F : LProducer.LK → List Bool,
      ∃ FQ : QK → List Bool, ∃ vc,
      ((advance (program Δ γ))^[t])
        (⟨some (startLabel Δ γ), initialControl, initial n m⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, vc,
          bank qSlots (CopyAll.done copySlots 4 (widthBank n m F)) FQ⟩ ∧
      CountFront.LFacts n F ∧
      FQ (.inl 1) = List.replicate m true ∧
      FQ (.inl 24) = List.replicate
        (Q27 (V := Fin n) (E := Fin m) (Nat.clog 2 n) γ Δ) true := by
  obtain ⟨tW, htW, F, hW, hFacts⟩ := width_stage n m
  obtain ⟨tC, htC, vcC, hC⟩ := copies_stage n m F hFacts
  obtain ⟨tQ, htQ, vcQ, FQ, hQ, hMval, hQval⟩ := q_stage n m Δ γ hγ hΔ hn hm F hFacts
  obtain ⟨tWC, htWC, hWC⟩ := BitMachineRawSequence.runs widthProgram copyProgram
    WidthFromN.startLabel (.inl ⟨0, by omega⟩)
    WidthFromN.initialControl WidthFromN.initialControl none vcC
    (initial n m) (widthBank n m F)
    (CopyAll.done copySlots 4 (widthBank n m F))
    tW tC hW hC
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs first (qProgram Δ γ)
    (leftLabel WidthFromN.startLabel)
    (QProducer.qStart γ.num.toNat γ.den Δ)
    firstControl (WidthFromN.initialControl, vcC) QProducer.qCtl vcQ
    (initial n m) (CopyAll.done copySlots 4 (widthBank n m F))
    (bank qSlots (CopyAll.done copySlots 4 (widthBank n m F)) FQ)
    tWC tQ hWC hQ
  refine ⟨t, ?_, F, FQ, (firstControl, vcQ), ?_, hFacts, hMval, hQval⟩
  · unfold clock
    omega
  · simpa only [program, startLabel, initialControl] using hr

end
end Paper2.CurrentAdditive.QuarticNumericFront.LQ27

#print axioms Paper2.CurrentAdditive.QuarticNumericFront.LQ27.width_stage
#print axioms Paper2.CurrentAdditive.QuarticNumericFront.LQ27.copies_stage
#print axioms Paper2.CurrentAdditive.QuarticNumericFront.LQ27.copied_q_bank
#print axioms Paper2.CurrentAdditive.QuarticNumericFront.LQ27.run
