import CurrentAdditive.QuarticGraphBridge

/-! Put the physical quartic graph/count program behind the actual three-cell
input packet. The two non-graph packet cells remain available for the later
threshold and start-bank installation. -/

namespace Paper2.CurrentAdditive.QuarticNumericFront.Packet27

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open BitMachineRawSequence (leftLabel)

abbrev GS := Graph27.Stack
abbrev JM := TMFront.JM
abbrev SO := SuccessOrient.Stack
abbrev Stack := GS ⊕ (JM ⊕ (SO ⊕ (Fin 3 ⊕ Fin 1)))
instance : DecidableEq Stack := inferInstance

def graph (x : GS) : Stack := .inl x
def tm (x : JM) : Stack := .inr (.inl x)
def so (x : SO) : Stack := .inr (.inr (.inl x))
def packet (i : Fin 3) : Stack := .inr (.inr (.inr (.inl i)))
def scratch : Stack := .inr (.inr (.inr (.inr 0)))
def graphSlots : GS ↪ Stack := ⟨Sum.inl, Sum.inl_injective⟩
def tmSlots : JM ↪ Stack :=
  ⟨fun x => .inr (.inl x), by intro x y h; cases h; rfl⟩

def graphInput : GS := Graph27.old CountFront.gB
def graphCopy : Fin 3 ↪ Stack :=
  ⟨![packet 0, graph graphInput, scratch], by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [packet, graph, scratch]⟩

def initial (X : Fin 3 → List Bool) : Stack → List Bool :=
  Sum.elim (fun _ => []) (Sum.elim (fun _ => [])
    (Sum.elim (fun _ => []) (Sum.elim X (fun _ => []))))

def graphProgram (Δ : ℕ) (γ : ℚ) :=
  fun l => stackStmt graphSlots (Graph27.program Δ γ l)
def copyProgram := MatrixStage4ScalarPreparationOps.copyProgram graphCopy
def program (Δ : ℕ) (γ : ℚ) :=
  BitMachineRawSequence.program copyProgram (graphProgram Δ γ)
    (Graph27.startLabel Δ γ) none Graph27.initialControl
def initialControl := ((none : Option Bool), Graph27.initialControl)
def startLabel (Δ : ℕ) (γ : ℚ) := FullFront.labelOfP (program Δ γ)
  (leftLabel BitMachineCopy.Label.scan)

def graphExit (g : EncodedGraph.Graph) (hg : g.Valid)
    (FLold : LProducer.LK → List Bool) (FQold : QProducer.QK → List Bool)
    (FLnew : LProducer.LK → List Bool) (FQnew : QProducer.QK → List Bool) :
    GS → List Bool :=
  let B := CopyAll.done Graph27.copies 2 (Graph27.oldBank g hg FLold FQold)
  let N := bank LQ27.qSlots
    (CopyAll.done LQ27.copySlots 4
      (LQ27.widthBank g.vertices g.edges.length FLnew)) FQnew
  bank Graph27.newSlots B N

def exitBank (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ)
    (word : List Bool)
    (FLold : LProducer.LK → List Bool) (FQold : QProducer.QK → List Bool)
    (FLnew : LProducer.LK → List Bool) (FQnew : QProducer.QK → List Bool) :
    Stack → List Bool :=
  Sum.elim (graphExit g hg FLold FQold FLnew FQnew)
    (Sum.elim (fun _ => []) (Sum.elim (fun _ => [])
      (Sum.elim (FullFront.X0 g k word) (fun _ => []))))

theorem graph_copy_run (g : EncodedGraph.Graph) (k : ℕ) (word : List Bool) :
    ((advance copyProgram)^[(2 * (EncodedGraph.encode g).length + 2)])
      (⟨some BitMachineCopy.Label.scan, none,
        initial (FullFront.X0 g k word)⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, none,
        Function.update (initial (FullFront.X0 g k word))
          (graph graphInput) (EncodedGraph.encode g)⟩ := by
  have h := MatrixStage4ScalarPreparationOps.copy_run graphCopy
    (initial (FullFront.X0 g k word)) (by rfl)
  have hl : (initial (FullFront.X0 g k word) (graphCopy 0)).length =
      (EncodedGraph.encode g).length := rfl
  rw [hl] at h
  have hsrc : initial (FullFront.X0 g k word) (graphCopy 0) =
      EncodedGraph.encode g := rfl
  have hdst : initial (FullFront.X0 g k word) (graphCopy 1) = [] := rfl
  rw [hsrc, hdst, List.append_nil] at h
  simpa only [copyProgram] using h

theorem graph_input_bank (g : EncodedGraph.Graph) (k : ℕ)
    (word : List Bool) :
    let S := Function.update (initial (FullFront.X0 g k word))
      (graph graphInput) (EncodedGraph.encode g)
    bank graphSlots S (Graph27.initial g) = S := by
  intro S
  apply bank_eq_self
  intro x
  by_cases hx : x = graphInput
  · subst x
    change EncodedGraph.encode g = S (graph graphInput)
    simp [S]
  · have hG : Graph27.initial g x = [] := by
      rcases x with y | z | w
      · change CountFront.G0 g y = []
        rw [CountFront.G0, Function.update_of_ne]
        intro h
        exact hx (by cases h; rfl)
      · rfl
      · rfl
    rw [hG]
    change ([] : List Bool) = S (graph x)
    have hne : graph x ≠ graph graphInput := by
      intro h
      exact hx (by cases h; rfl)
    dsimp only [S]
    rw [Function.update_of_ne hne]
    rfl

theorem graph_exit_bank (g : EncodedGraph.Graph) (hg : g.Valid)
    (k : ℕ) (word : List Bool)
    (FLold : LProducer.LK → List Bool) (FQold : QProducer.QK → List Bool)
    (FLnew : LProducer.LK → List Bool) (FQnew : QProducer.QK → List Bool) :
    let S := Function.update (initial (FullFront.X0 g k word))
      (graph graphInput) (EncodedGraph.encode g)
    bank graphSlots S (graphExit g hg FLold FQold FLnew FQnew) =
      exitBank g hg k word FLold FQold FLnew FQnew := by
  intro S
  funext x
  rcases x with x | x | x | x | x
  · exact bank_at graphSlots S _ x
  · rw [bank_outside graphSlots S _ (.inr (.inl x))
      (by rintro ⟨y, hy⟩; cases hy)]
    change S (.inr (.inl x)) = ([] : List Bool)
    dsimp only [S]
    rw [Function.update_of_ne (by simp [graph] :
      (.inr (.inl x) : Stack) ≠ graph graphInput)]
    rfl
  · rw [bank_outside graphSlots S _ (.inr (.inr (.inl x)))
      (by rintro ⟨y, hy⟩; cases hy)]
    change S (.inr (.inr (.inl x))) = ([] : List Bool)
    dsimp only [S]
    rw [Function.update_of_ne (by simp [graph] :
      (.inr (.inr (.inl x)) : Stack) ≠ graph graphInput)]
    rfl
  · rw [bank_outside graphSlots S _ (.inr (.inr (.inr (.inl x))))
      (by rintro ⟨y, hy⟩; cases hy)]
    change S (packet x) = FullFront.X0 g k word x
    dsimp only [S]
    rw [Function.update_of_ne (by simp [graph, packet] :
      packet x ≠ graph graphInput)]
    rfl
  · rw [bank_outside graphSlots S _ (.inr (.inr (.inr (.inr x))))
      (by rintro ⟨y, hy⟩; cases hy)]
    fin_cases x
    change S scratch = ([] : List Bool)
    dsimp only [S]
    rw [Function.update_of_ne (by simp [graph, scratch] :
      scratch ≠ graph graphInput)]
    rfl

def clock (g : EncodedGraph.Graph) (Δ : ℕ) (γ : ℚ) : ℕ :=
  (2 * (EncodedGraph.encode g).length + 2) + Graph27.clock g Δ γ + 1

theorem run (g : EncodedGraph.Graph) (hg : g.Valid)
    (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hn : 0 < g.vertices) (hm : 0 < g.edges.length)
    (k : ℕ) (word : List Bool) :
    ∃ t ≤ clock g Δ γ,
      ∃ FLold : LProducer.LK → List Bool,
      ∃ FQold : QProducer.QK → List Bool,
      ∃ FLnew : LProducer.LK → List Bool,
      ∃ FQnew : QProducer.QK → List Bool,
      ∃ vc,
      ((advance (program Δ γ))^[t])
        (⟨some (startLabel Δ γ), initialControl,
          initial (FullFront.X0 g k word)⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, vc, exitBank g hg k word FLold FQold FLnew FQnew⟩ ∧
      CountFront.LFacts g.vertices FLnew ∧
      FQnew (.inl 1) = List.replicate g.edges.length true ∧
      FQnew (.inl 24) = List.replicate
        (CurrentAdditive.RandomizedSchedule.Q27
          (V := Fin g.vertices) (E := Fin g.edges.length)
          (Nat.clog 2 g.vertices) γ Δ) true := by
  let S := Function.update (initial (FullFront.X0 g k word))
    (graph graphInput) (EncodedGraph.encode g)
  have hCopy := graph_copy_run g k word
  obtain ⟨tG, htG, FLold, FQold, FLnew, FQnew, vcG, hG,
    hFacts, hmNew, hQNew⟩ := Graph27.run g hg Δ γ hγ hΔ hn hm
  have hLift := BitMachineStackRun.run graphSlots S (Graph27.program Δ γ)
    (⟨some (Graph27.startLabel Δ γ), Graph27.initialControl,
      Graph27.initial g⟩ : TM2.Cfg (fun _ : GS => Bool) _ _) tG
  rw [hG] at hLift
  have hstart : bank graphSlots S (Graph27.initial g) = S :=
    graph_input_bank g k word
  have hfinish := graph_exit_bank g hg k word FLold FQold FLnew FQnew
  have hG' : ((advance (graphProgram Δ γ))^[tG])
      (⟨some (Graph27.startLabel Δ γ), Graph27.initialControl, S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, vcG, exitBank g hg k word FLold FQold FLnew FQnew⟩ := by
    simp only [stackCfg, hstart] at hLift
    change ((advance (graphProgram Δ γ))^[tG])
      (⟨some (Graph27.startLabel Δ γ), Graph27.initialControl, S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, vcG, bank graphSlots S
        (graphExit g hg FLold FQold FLnew FQnew)⟩ at hLift
    rw [hfinish] at hLift
    exact hLift
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs copyProgram (graphProgram Δ γ)
    BitMachineCopy.Label.scan (Graph27.startLabel Δ γ)
    none none Graph27.initialControl vcG
    (initial (FullFront.X0 g k word)) S
    (exitBank g hg k word FLold FQold FLnew FQnew)
    (2 * (EncodedGraph.encode g).length + 2) tG hCopy hG'
  refine ⟨t, ?_, FLold, FQold, FLnew, FQnew,
    (none, vcG), ?_, hFacts, hmNew, hQNew⟩
  · unfold clock
    omega
  · simpa only [program, startLabel, initialControl, S] using hr

end
end Paper2.CurrentAdditive.QuarticNumericFront.Packet27

#print axioms Paper2.CurrentAdditive.QuarticNumericFront.Packet27.graph_copy_run
#print axioms Paper2.CurrentAdditive.QuarticNumericFront.Packet27.graph_input_bank
#print axioms Paper2.CurrentAdditive.QuarticNumericFront.Packet27.graph_exit_bank
#print axioms Paper2.CurrentAdditive.QuarticNumericFront.Packet27.run
