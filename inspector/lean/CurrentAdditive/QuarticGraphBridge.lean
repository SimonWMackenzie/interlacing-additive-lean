import CurrentAdditive.QuarticLQFront
import Paper2.GFront

/-! Reuse the old fixed graph-byte parser as a physical first stage. Its old
numeric work is redundant, but its parser provides genuine unary vertex and
edge counts. Two physical copies feed the frozen quartic L/Q front. -/

namespace Paper2.CurrentAdditive.QuarticNumericFront.Graph27

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open BitMachineRawSequence (leftLabel)

abbrev Old := CountFront.J2
abbrev New := LQ27.Stack
abbrev Stack := Old ⊕ (New ⊕ Fin 1)
instance : DecidableEq Stack := inferInstance

def old (x : Old) : Stack := .inl x
def new (x : New) : Stack := .inr (.inl x)
def scratch : Stack := .inr (.inr 0)
def oldSlots : Old ↪ Stack := ⟨Sum.inl, Sum.inl_injective⟩
def newSlots : New ↪ Stack :=
  ⟨fun x => .inr (.inl x), by intro x y h; cases h; rfl⟩

def nSource : Stack := old (CountFront.jc (CountFront.lc LProducer.nC))
def mSource : Stack := old (CountFront.jc (CountFront.qc (.inl 1)))
def nTarget : Stack := new (LQ27.wc (.inl LProducer.nC))
def mTarget : Stack := new (LQ27.qc (.inl 1))
def copies (i : Fin 2) : Fin 3 ↪ Stack :=
  ⟨![![nSource, mSource] i, ![nTarget, mTarget] i, scratch], by
    intro x y h
    fin_cases i <;> fin_cases x <;> fin_cases y <;>
      simp_all [nSource, mSource, nTarget, mTarget, old, new, scratch]⟩

theorem src_ne_dst (i j : Fin 2) : copies i 0 ≠ copies j 1 := by
  fin_cases i <;> fin_cases j <;>
    simp [copies, nSource, mSource, nTarget, mTarget, old, new]
theorem scratch_ne_dst (i j : Fin 2) : copies i 2 ≠ copies j 1 := by
  fin_cases i <;> fin_cases j <;> simp [copies, scratch, nTarget, mTarget, new]
theorem dst_injective (i j : Fin 2) (h : copies i 1 = copies j 1) : i = j := by
  fin_cases i <;> fin_cases j <;>
    simp_all [copies, nTarget, mTarget, new, LQ27.wc, LQ27.qc]

def initial (g : EncodedGraph.Graph) : Stack → List Bool :=
  Sum.elim (CountFront.G0 g) (fun _ => [])

def oldProgram (Δ : ℕ) (γ : ℚ) :=
  fun l => stackStmt oldSlots
    (CountFront.gfront γ.num.toNat γ.den Δ l)
def copyProgram := CopyAll.prog copies
def newProgram (Δ : ℕ) (γ : ℚ) :=
  fun l => stackStmt newSlots (LQ27.program Δ γ l)

def f1 (Δ : ℕ) (γ : ℚ) :=
  BitMachineRawSequence.program (oldProgram Δ γ) copyProgram
    (.inl ⟨0, by omega⟩) (CountFront.gfrontCtl) none
def v1 := (CountFront.gfrontCtl, (none : Option Bool))
def program (Δ : ℕ) (γ : ℚ) :=
  BitMachineRawSequence.program (f1 Δ γ) (newProgram Δ γ)
    (LQ27.startLabel Δ γ) v1 LQ27.initialControl
def initialControl := (v1, LQ27.initialControl)
def startLabel (Δ : ℕ) (γ : ℚ) := FullFront.labelOfP (program Δ γ)
  (leftLabel (leftLabel (CountFront.gStart γ.num.toNat γ.den Δ)))

def oldBank (g : EncodedGraph.Graph) (hg : g.Valid)
    (FL : LProducer.LK → List Bool) (FQ : QProducer.QK → List Bool) :
    Stack → List Bool :=
  Sum.elim (Sum.elim (Sum.elim FL (Sum.elim FQ (fun _ => [])))
    (Sum.elim (PublicGraphEndpointMachine.resultBank g hg)
      (fun _ => EncodedGraph.encode g))) (fun _ => [])

theorem old_stage (Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph) (hg : g.Valid) :
    ∃ t ≤ (2 * (EncodedGraph.encode g).length + 2) +
      103 * ((EncodedGraph.encode g).length + 1) ^ 3 +
      (2 * g.vertices + 2) + (2 * g.edges.length + 2) +
      CountFront.lqBd γ.num.toNat γ.den Δ g.vertices g.edges.length + 4,
      ∃ vc, ∃ FL : LProducer.LK → List Bool,
      ∃ FQ : QProducer.QK → List Bool,
      ((advance (oldProgram Δ γ))^[t])
        (⟨some (CountFront.gStart γ.num.toNat γ.den Δ),
          CountFront.gfrontCtl, initial g⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, vc, oldBank g hg FL FQ⟩ ∧
      CountFront.LFacts g.vertices FL ∧
      CountFront.QFacts γ.num.toNat γ.den Δ g.vertices g.edges.length
        (Nat.clog 2 g.vertices)
        (2 ^ (16 + Nat.clog 2 (Nat.clog 2 g.vertices + 1)))
        (2 ^ (Nat.clog 2 (Nat.clog 2 g.vertices + 1) *
          Nat.clog 2 (Nat.clog 2 g.vertices + 1))) FQ := by
  obtain ⟨t, ht, vc, FL, FQ, hr, hLF, hQF⟩ :=
    CountFront.g_run γ.num.toNat γ.den Δ g hg
  let O : Old → List Bool :=
    Sum.elim (Sum.elim FL (Sum.elim FQ (fun _ => [])))
      (Sum.elim (PublicGraphEndpointMachine.resultBank g hg)
        (fun _ => EncodedGraph.encode g))
  have h := BitMachineStackRun.run oldSlots (initial g)
    (CountFront.gfront γ.num.toNat γ.den Δ)
    (⟨some (CountFront.gStart γ.num.toNat γ.den Δ),
      CountFront.gfrontCtl, CountFront.G0 g⟩ :
      TM2.Cfg (fun _ : Old => Bool) _ _) t
  rw [hr] at h
  have hstart : bank oldSlots (initial g) (CountFront.G0 g) = initial g := by
    apply bank_eq_self
    intro x
    rfl
  have hfinish : bank oldSlots (initial g) O = oldBank g hg FL FQ := by
    funext x
    rcases x with x | x | x
    · exact bank_at oldSlots (initial g) O x
    · exact bank_outside oldSlots (initial g) O (.inr (.inl x))
        (by rintro ⟨y, hy⟩; cases hy)
    · exact bank_outside oldSlots (initial g) O (.inr (.inr x))
        (by rintro ⟨y, hy⟩; cases hy)
  refine ⟨t, ht, vc, FL, FQ, ?_, hLF, hQF⟩
  simpa only [oldProgram, stackCfg, hstart, hfinish, O] using h

theorem oldBank_source (g : EncodedGraph.Graph) (hg : g.Valid)
    (FL : LProducer.LK → List Bool) (FQ : QProducer.QK → List Bool)
    (hLF : CountFront.LFacts g.vertices FL)
    (hm : FQ (.inl 1) = List.replicate g.edges.length true)
    (i : Fin 2) :
    oldBank g hg FL FQ (copies i 0) =
      List.replicate (![g.vertices, g.edges.length] i) true := by
  obtain ⟨hn, -⟩ := hLF
  fin_cases i
  · change FL LProducer.nC = List.replicate g.vertices true
    simpa only [LProducer.u] using hn
  · change FQ (.inl 1) = List.replicate g.edges.length true
    simpa only [QProducer.u] using hm

theorem copies_stage (g : EncodedGraph.Graph) (hg : g.Valid)
    (FL : LProducer.LK → List Bool) (FQ : QProducer.QK → List Bool)
    (hLF : CountFront.LFacts g.vertices FL)
    (hm : FQ (.inl 1) = List.replicate g.edges.length true) :
    ∃ t ≤ 2 * (2 * (g.vertices + g.edges.length) + 3) + 1, ∃ vc,
      ((advance copyProgram)^[t])
        (⟨some (.inl ⟨0, by omega⟩), none, oldBank g hg FL FQ⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, vc, CopyAll.done copies 2 (oldBank g hg FL FQ)⟩ := by
  apply CopyAll.all_run copies src_ne_dst scratch_ne_dst dst_injective
    (oldBank g hg FL FQ)
  · intro i
    change ([] : List Bool) = []
    rfl
  · intro i
    rw [oldBank_source g hg FL FQ hLF hm i, List.length_replicate]
    fin_cases i <;> simp

theorem copied_new_input (g : EncodedGraph.Graph) (hg : g.Valid)
    (FL : LProducer.LK → List Bool) (FQ : QProducer.QK → List Bool)
    (hLF : CountFront.LFacts g.vertices FL)
    (hm : FQ (.inl 1) = List.replicate g.edges.length true) :
    let B := CopyAll.done copies 2 (oldBank g hg FL FQ)
    bank newSlots B (LQ27.initial g.vertices g.edges.length) = B := by
  intro B
  apply bank_eq_self
  intro x
  by_cases hx0 : x = LQ27.wc (.inl LProducer.nC)
  · subst x
    have h := CopyAll.done_dst copies dst_injective (oldBank g hg FL FQ) 0
    change B nTarget = oldBank g hg FL FQ nSource ++ oldBank g hg FL FQ nTarget at h
    have hv := oldBank_source g hg FL FQ hLF hm 0
    change oldBank g hg FL FQ nSource = List.replicate g.vertices true at hv
    change LQ27.initial g.vertices g.edges.length
      (LQ27.wc (.inl LProducer.nC)) = B nTarget
    rw [h, hv]
    rw [show oldBank g hg FL FQ nTarget = [] from rfl, List.append_nil]
    rfl
  by_cases hx1 : x = LQ27.qc (.inl 1)
  · subst x
    have h := CopyAll.done_dst copies dst_injective (oldBank g hg FL FQ) 1
    change B mTarget = oldBank g hg FL FQ mSource ++ oldBank g hg FL FQ mTarget at h
    have hv := oldBank_source g hg FL FQ hLF hm 1
    change oldBank g hg FL FQ mSource = List.replicate g.edges.length true at hv
    change LQ27.initial g.vertices g.edges.length
      (LQ27.qc (.inl 1)) = B mTarget
    rw [h, hv]
    rw [show oldBank g hg FL FQ mTarget = [] from rfl, List.append_nil]
    rfl
  have hkeep : B (new x) = oldBank g hg FL FQ (new x) := by
    apply CopyAll.done_off
    intro i
    fin_cases i
    · exact fun h => hx0 (by simpa [copies, nTarget, new] using h.symm)
    · exact fun h => hx1 (by simpa [copies, mTarget, new] using h.symm)
  have hblank : B (new x) = [] := by rw [hkeep]; rfl
  change LQ27.initial g.vertices g.edges.length x = B (new x)
  rw [hblank]
  rcases x with w | q | s
  · rcases w with l | z
    · change LProducer.L0 g.vertices l = []
      rw [LProducer.L0, Function.update_of_ne]
      intro h
      exact hx0 (by simp [LQ27.wc, LProducer.nC, h])
    · rfl
  · change (Function.update (fun _ : QProducer.QK => []) (.inl 1)
      (List.replicate g.edges.length true)) q = []
    rw [Function.update_of_ne]
    intro h
    exact hx1 (by simp [LQ27.qc, h])
  · rfl

def clock (g : EncodedGraph.Graph) (Δ : ℕ) (γ : ℚ) : ℕ :=
  ((2 * (EncodedGraph.encode g).length + 2) +
    103 * ((EncodedGraph.encode g).length + 1) ^ 3 +
    (2 * g.vertices + 2) + (2 * g.edges.length + 2) +
    CountFront.lqBd γ.num.toNat γ.den Δ g.vertices g.edges.length + 4) +
  (2 * (2 * (g.vertices + g.edges.length) + 3) + 1) +
    LQ27.clock g.vertices g.edges.length Δ γ + 2

/-- One fixed machine starting with literal graph bytes and producing the
quartic width/Q numeric region. The old graph parser supplies actual unary
vertex and edge counts; every handoff is a physical copy. -/
theorem run (g : EncodedGraph.Graph) (hg : g.Valid)
    (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hn : 0 < g.vertices) (hm : 0 < g.edges.length) :
    ∃ t ≤ clock g Δ γ,
      ∃ FLold : LProducer.LK → List Bool,
      ∃ FQold : QProducer.QK → List Bool,
      ∃ FLnew : LProducer.LK → List Bool,
      ∃ FQnew : QProducer.QK → List Bool,
      ∃ vc,
      let B := CopyAll.done copies 2 (oldBank g hg FLold FQold)
      let N := bank LQ27.qSlots
        (CopyAll.done LQ27.copySlots 4
          (LQ27.widthBank g.vertices g.edges.length FLnew)) FQnew
      ((advance (program Δ γ))^[t])
        (⟨some (startLabel Δ γ), initialControl, initial g⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, vc, bank newSlots B N⟩ ∧
      CountFront.LFacts g.vertices FLnew ∧
      FQnew (.inl 1) = List.replicate g.edges.length true ∧
      FQnew (.inl 24) = List.replicate
        (CurrentAdditive.RandomizedSchedule.Q27
          (V := Fin g.vertices) (E := Fin g.edges.length)
          (Nat.clog 2 g.vertices) γ Δ) true := by
  obtain ⟨tOld, htOld, vcOld, FLold, FQold, hOld, hLF, hQF⟩ :=
    old_stage Δ γ g hg
  obtain ⟨c, _, hmOld, -⟩ := hQF
  have hmOld' : FQold (.inl 1) = List.replicate g.edges.length true := by
    simpa only [QProducer.u] using hmOld
  obtain ⟨tCopy, htCopy, vcCopy, hCopy⟩ :=
    copies_stage g hg FLold FQold hLF hmOld'
  obtain ⟨tNew, htNew, FLnew, FQnew, vcNew, hNew, hFacts, hmNew, hQNew⟩ :=
    LQ27.run g.vertices g.edges.length Δ γ hγ hΔ hn hm
  let B := CopyAll.done copies 2 (oldBank g hg FLold FQold)
  let N := bank LQ27.qSlots
    (CopyAll.done LQ27.copySlots 4
      (LQ27.widthBank g.vertices g.edges.length FLnew)) FQnew
  have hLift := BitMachineStackRun.run newSlots B (LQ27.program Δ γ)
    (⟨some (LQ27.startLabel Δ γ), LQ27.initialControl,
      LQ27.initial g.vertices g.edges.length⟩ :
      TM2.Cfg (fun _ : New => Bool) _ _) tNew
  rw [hNew] at hLift
  have hstart : bank newSlots B (LQ27.initial g.vertices g.edges.length) = B :=
    copied_new_input g hg FLold FQold hLF hmOld'
  have hNew' : ((advance (newProgram Δ γ))^[tNew])
      (⟨some (LQ27.startLabel Δ γ), LQ27.initialControl, B⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, vcNew, bank newSlots B N⟩ := by
    simpa only [newProgram, stackCfg, hstart, N] using hLift
  obtain ⟨tFirst, htFirst, hFirst⟩ :=
    BitMachineRawSequence.runs (oldProgram Δ γ) copyProgram
      (CountFront.gStart γ.num.toNat γ.den Δ) (.inl ⟨0, by omega⟩)
      CountFront.gfrontCtl vcOld none vcCopy
      (initial g) (oldBank g hg FLold FQold) B
      tOld tCopy hOld hCopy
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs (f1 Δ γ) (newProgram Δ γ)
    (leftLabel (CountFront.gStart γ.num.toNat γ.den Δ))
    (LQ27.startLabel Δ γ)
    v1 (CountFront.gfrontCtl, vcCopy) LQ27.initialControl vcNew
    (initial g) B (bank newSlots B N)
    tFirst tNew hFirst hNew'
  refine ⟨t, ?_, FLold, FQold, FLnew, FQnew,
    (v1, vcNew), ?_, hFacts, hmNew, hQNew⟩
  · unfold clock
    omega
  · simpa only [program, startLabel, initialControl, B, N] using hr

end
end Paper2.CurrentAdditive.QuarticNumericFront.Graph27

#print axioms Paper2.CurrentAdditive.QuarticNumericFront.Graph27.old_stage
#print axioms Paper2.CurrentAdditive.QuarticNumericFront.Graph27.copied_new_input
#print axioms Paper2.CurrentAdditive.QuarticNumericFront.Graph27.run
