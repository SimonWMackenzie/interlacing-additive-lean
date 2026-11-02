import CurrentAdditive.V22PublicRepeatBase

namespace V22PublicRepeat
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
open Turing EthInapproximability.CurrentPaper BitMachineEncoding BitMachineStackEmbedding
variable {Raw : Type*} [DecidableEq Raw]
local instance : DecidableEq (Stack Raw) := Classical.decEq _

def edgeProgram (graphPort : Raw) := CurrentAdditive.GenericParameterBranch.framedProgram
  V22EdgeCountMachine.machine (.inl graphPort) edgePort edgeSlots
def pairProgram (sPort : Raw) := CurrentAdditive.GenericParameterPair.framedProgram (.inl sPort) edgePort pairPort pairSlots
def powProgram : CurrentAdditive.GenericParameterBranch.Label q0Machine → TM2.Stmt (fun _ : Stack Raw => Bool)
    (CurrentAdditive.GenericParameterBranch.Label q0Machine) (CurrentAdditive.GenericParameterBranch.Control q0Machine) :=
  CurrentAdditive.GenericParameterBranch.framedProgram q0Machine pairPort q0Port powSlots
def divProgram (q₂Port : Raw) := V22ParameterDivide.framedProgram (.inl q₂Port) q0Port repetitionPort divSlots
def edgeControl := CurrentAdditive.GenericParameterBranch.startControl V22EdgeCountMachine.machine
def pairControl := CurrentAdditive.GenericParameterPair.startControl
def powControl := CurrentAdditive.GenericParameterBranch.startControl q0Machine
def divControl := V22ParameterDivide.startControl
def pre₁ (graphPort sPort : Raw) := BitMachineRawSequence.program
  (edgeProgram graphPort) (pairProgram sPort) CurrentAdditive.GenericParameterPair.startLabel edgeControl pairControl
def pre₂ (graphPort sPort : Raw) := BitMachineRawSequence.program
  (pre₁ graphPort sPort) (powProgram (Raw:=Raw)) (CurrentAdditive.GenericParameterBranch.startLabel q0Machine)
    (edgeControl,pairControl) powControl
def program (graphPort sPort q₂Port : Raw) := BitMachineRawSequence.program
  (pre₂ graphPort sPort) (divProgram q₂Port) V22ParameterDivide.startLabel
    ((edgeControl,pairControl),powControl) divControl
abbrev Label := BitMachineRawSequence.Label
  (BitMachineRawSequence.Label
    (BitMachineRawSequence.Label (CurrentAdditive.GenericParameterBranch.Label V22EdgeCountMachine.machine) CurrentAdditive.GenericParameterPair.Label)
    (CurrentAdditive.GenericParameterBranch.Label q0Machine)) V22ParameterDivide.Label
def start : Label := .inl (.inl (.inl (CurrentAdditive.GenericParameterBranch.startLabel V22EdgeCountMachine.machine)))
def control := (((edgeControl,pairControl),powControl),divControl)
def edgeClock (g : EncodedGraph.Graph) := 2*(EncodedGraph.encode g).length+
  100*((EncodedGraph.encode g).length+1)^3+2*g.edges.length+6
def pairClock (s m : ℕ) := (2*s+2)+(2*m+2)+(s+m+3)+
  (2*(MatrixUnaryArithmetic.encodeInput s m).length+2)+3
def powClock (s m : ℕ) := 2*(MatrixUnaryArithmetic.encodeInput s m).length+
  q0Clock s m+2*(V22RepeatArithmetic.q0 s m)+6
def clock (g : EncodedGraph.Graph) (s q₂ : ℕ) :=
  edgeClock g+pairClock s g.edges.length+powClock s g.edges.length+
  V22ParameterDivide.clock q₂ (V22RepeatArithmetic.q0 s g.edges.length)+3

theorem edge_work (S : Raw → List Bool) (graphPort : Raw) (g : EncodedGraph.Graph)
    (w : Work) (he : ¬∃j,edgeWork j=w) :
    afterEdge S graphPort g (.inr (.inr w))=[] := by
  rw [afterEdge,edgeSlots,bank_other_work _ _ _ _ he]
  rfl
theorem pair_work (S : Raw → List Bool) (graphPort : Raw) (g : EncodedGraph.Graph) (s : ℕ)
    (w : Work) (he : ¬∃j,edgeWork j=w) (hp : ¬∃j,pairWork j=w) :
    afterPair S graphPort g s (.inr (.inr w))=[] := by
  rw [afterPair,pairSlots,bank_other_work _ _ _ _ hp]
  exact edge_work S graphPort g w he
theorem pow_work (S : Raw → List Bool) (graphPort : Raw) (g : EncodedGraph.Graph) (s : ℕ)
    (w : Work) (he : ¬∃j,edgeWork j=w) (hp : ¬∃j,pairWork j=w) (hq : ¬∃j,powWork j=w) :
    afterQ0 S graphPort g s (.inr (.inr w))=[] := by
  rw [afterQ0,powSlots,bank_other_work _ _ _ _ hq]
  exact pair_work S graphPort g s w he hp

theorem edge_run (S : Raw → List Bool) (graphPort : Raw) (g : EncodedGraph.Graph) (hg : g.Valid)
    (hgraph : S graphPort=EncodedGraph.encode g) :
    ∃ t ≤ edgeClock g, ((advance (edgeProgram graphPort))^[t])
      (⟨some (CurrentAdditive.GenericParameterBranch.startLabel V22EdgeCountMachine.machine),edgeControl,initial S⟩ :
        TM2.Cfg (fun _ : Stack Raw => Bool) _ _) = ⟨none,edgeControl,afterEdge S graphPort g⟩ := by
  simpa only [edgeClock,List.length_replicate] using CurrentAdditive.GenericParameterBranch.run_install_framed_from_ambient V22EdgeCountMachine.machine
    (.inl graphPort) edgePort (EncodedGraph.encode g) (List.replicate g.edges.length true)
    (100*((EncodedGraph.encode g).length+1)^3) edgeSlots (initial S)
    hgraph rfl (by intro j; rfl) (V22EdgeCountMachine.outputs g hg)

theorem pair_run (S : Raw → List Bool) (graphPort sPort : Raw) (g : EncodedGraph.Graph) (s : ℕ)
    (hs : S sPort=List.replicate s true) :
    ∃ t ≤ pairClock s g.edges.length, ((advance (pairProgram sPort))^[t])
      (⟨some CurrentAdditive.GenericParameterPair.startLabel,pairControl,afterEdge S graphPort g⟩ :
        TM2.Cfg (fun _ : Stack Raw => Bool) _ _) = ⟨none,pairControl,afterPair S graphPort g s⟩ := by
  apply CurrentAdditive.GenericParameterPair.run_install_framed_from_ambient (.inl sPort) edgePort pairPort
    s g.edges.length pairSlots (afterEdge S graphPort g)
  · change afterEdge S graphPort g (basePort (.inl sPort))=_
    rw [edge_base]
    exact hs
  · change afterEdge S graphPort g (basePort edgePort)=_
    rw [edge_base]
    rfl
  · change afterEdge S graphPort g (basePort pairPort)=_
    rw [edge_base]
    rfl
  · intro j
    change afterEdge S graphPort g (.inr (.inr (pairWork j)))=[]
    exact edge_work S graphPort g _ (by rintro ⟨x,hx⟩; cases hx)

theorem pow_run (S : Raw → List Bool) (graphPort : Raw) (g : EncodedGraph.Graph) (s : ℕ) :
    ∃ t ≤ powClock s g.edges.length, ((advance (powProgram (Raw:=Raw)))^[t])
      (⟨some (CurrentAdditive.GenericParameterBranch.startLabel q0Machine),powControl,afterPair S graphPort g s⟩ :
        TM2.Cfg (fun _ : Stack Raw => Bool) _ _) = ⟨none,powControl,afterQ0 S graphPort g s⟩ := by
  have hsource : afterPair S graphPort g s (powSlots (.inl pairPort))=
      MatrixUnaryArithmetic.encodeInput s g.edges.length := by
    change afterPair S graphPort g s (basePort pairPort)=_
    rw [pair_base]
    rfl
  have hdest : afterPair S graphPort g s (powSlots (.inl q0Port))=[] := by
    change afterPair S graphPort g s (basePort q0Port)=_
    rw [pair_base,edge_base]
    rfl
  have hfresh : ∀j : PowWork,afterPair S graphPort g s (powSlots (.inr j))=[] := by
    intro j
    change afterPair S graphPort g s (.inr (.inr (powWork j)))=[]
    exact pair_work S graphPort g s _ (by rintro ⟨x,hx⟩; cases hx)
      (by rintro ⟨x,hx⟩; cases hx)
  simpa only [powClock,List.length_replicate] using
    CurrentAdditive.GenericParameterBranch.run_install_framed_from_ambient q0Machine pairPort q0Port
      (MatrixUnaryArithmetic.encodeInput s g.edges.length)
      (List.replicate (V22RepeatArithmetic.q0 s g.edges.length) true)
      (q0Clock s g.edges.length) powSlots (afterPair S graphPort g s)
      hsource hdest hfresh (q0_outputs s g.edges.length)

theorem div_run (S : Raw → List Bool) (graphPort q₂Port : Raw) (g : EncodedGraph.Graph) (s q₂ : ℕ)
    (hq : S q₂Port=List.replicate q₂ true) :
    ∃ t ≤ V22ParameterDivide.clock q₂ (V22RepeatArithmetic.q0 s g.edges.length),
      ((advance (divProgram q₂Port))^[t])
      (⟨some V22ParameterDivide.startLabel,divControl,afterQ0 S graphPort g s⟩ :
        TM2.Cfg (fun _ : Stack Raw => Bool) _ _) = ⟨none,divControl,final S graphPort g s q₂⟩ := by
  apply V22ParameterDivide.run_install_framed_from_ambient (.inl q₂Port) q0Port repetitionPort
    q₂ (V22RepeatArithmetic.q0 s g.edges.length) divSlots (afterQ0 S graphPort g s)
  · change afterQ0 S graphPort g s (basePort (.inl q₂Port))=_
    rw [q0_base,pair_base,edge_base]
    exact hq
  · change afterQ0 S graphPort g s (basePort q0Port)=_
    rw [q0_base]
    rfl
  · change afterQ0 S graphPort g s (basePort repetitionPort)=_
    rw [q0_base,pair_base,edge_base]
    rfl
  · intro j
    change afterQ0 S graphPort g s (.inr (.inr (divWork j)))=[]
    exact pow_work S graphPort g s _ (by rintro ⟨x,hx⟩; cases hx)
      (by rintro ⟨x,hx⟩; cases hx) (by rintro ⟨x,hx⟩; cases hx)

theorem run (S : Raw → List Bool) (graphPort sPort q₂Port : Raw) (g : EncodedGraph.Graph)
    (hg : g.Valid) (s q₂ : ℕ) (hgraph : S graphPort=EncodedGraph.encode g)
    (hs : S sPort=List.replicate s true) (hq : S q₂Port=List.replicate q₂ true) :
    ∃ t ≤ clock g s q₂, ((advance (program graphPort sPort q₂Port))^[t])
      (⟨some start,control,initial S⟩ : TM2.Cfg (fun _ : Stack Raw => Bool) Label _) =
      ⟨none,control,final S graphPort g s q₂⟩ := by
  obtain ⟨a,ha,ea⟩ := edge_run S graphPort g hg hgraph
  obtain ⟨b,hb,eb⟩ := pair_run S graphPort sPort g s hs
  obtain ⟨u,hu,eu⟩ := BitMachineRawSequence.runs (edgeProgram graphPort) (pairProgram sPort)
    (CurrentAdditive.GenericParameterBranch.startLabel V22EdgeCountMachine.machine) CurrentAdditive.GenericParameterPair.startLabel
    edgeControl edgeControl pairControl pairControl (initial S) (afterEdge S graphPort g)
    (afterPair S graphPort g s) a b ea eb
  obtain ⟨c,hc,ec⟩ := pow_run S graphPort g s
  obtain ⟨v,hv,ev⟩ := BitMachineRawSequence.runs (pre₁ graphPort sPort) (powProgram (Raw:=Raw))
    (.inl (CurrentAdditive.GenericParameterBranch.startLabel V22EdgeCountMachine.machine)) (CurrentAdditive.GenericParameterBranch.startLabel q0Machine)
    (edgeControl,pairControl) (edgeControl,pairControl) powControl powControl
    (initial S) (afterPair S graphPort g s) (afterQ0 S graphPort g s) u c eu ec
  obtain ⟨d,hd,ed⟩ := div_run S graphPort q₂Port g s q₂ hq
  obtain ⟨t,ht,et⟩ := BitMachineRawSequence.runs (pre₂ graphPort sPort) (divProgram q₂Port)
    (.inl (.inl (CurrentAdditive.GenericParameterBranch.startLabel V22EdgeCountMachine.machine))) V22ParameterDivide.startLabel
    ((edgeControl,pairControl),powControl) ((edgeControl,pairControl),powControl) divControl divControl
    (initial S) (afterQ0 S graphPort g s) (final S graphPort g s q₂) v d ev ed
  exact ⟨t,by unfold clock; omega,et⟩

end
end V22PublicRepeat
