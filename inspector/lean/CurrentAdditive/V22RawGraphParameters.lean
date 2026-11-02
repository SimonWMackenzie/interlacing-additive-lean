import CurrentAdditive.V22FullScheduleBatch
import CurrentAdditive.V22GraphVertexMachine
import CurrentAdditive.GenericParameterPair

/-! One fixed physical full-product parameter compiler. Its initial bank has
only the literal canonical graph encoding and the supplied delimiter-free
unary k. It parses the graph, constructs the (n,k) arithmetic input, computes
the literal public schedule, and installs the exact sample constructor bank.
The graph-copy source reduction is a separate preceding computation. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
namespace V22RawGraphParameters
noncomputable section
open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open V22FullScheduleBatch
abbrev VertexWork := Fin V22GraphVertexMachine.machine.stackCount ⊕ Fin 3
abbrev Stack := V22FullScheduleBatch.Stack ⊕ (VertexWork ⊕ Fin 6)
def vertexSlots : CurrentAdditive.GenericParameterBranch.Stack V22GraphVertexMachine.machine Base ↪ Stack where
  toFun | .inl b => .inl (.inl b) | .inr w => .inr (.inl w)
  inj' := by intro a b h; cases a <;> cases b <;> simp_all
def pairSlots : CurrentAdditive.GenericParameterPair.Stack Base ↪ Stack where
  toFun | .inl b => .inl (.inl b) | .inr w => .inr (.inr w)
  inj' := by intro a b h; cases a <;> cases b <;> simp_all
def batchSlots : V22FullScheduleBatch.Stack ↪ Stack := ⟨Sum.inl,Sum.inl_injective⟩
def vertexProgram := CurrentAdditive.GenericParameterBranch.framedProgram V22GraphVertexMachine.machine
  graphPort nPort vertexSlots
def pairProgram := CurrentAdditive.GenericParameterPair.framedProgram nPort kPort sourcePort pairSlots
def batchProgram := fun l => stackStmt batchSlots (V22FullScheduleBatch.program l)
def vertexControl := CurrentAdditive.GenericParameterBranch.startControl V22GraphVertexMachine.machine
def pairControl := CurrentAdditive.GenericParameterPair.startControl
def frontProgram := BitMachineRawSequence.program vertexProgram pairProgram
  CurrentAdditive.GenericParameterPair.startLabel vertexControl pairControl
def program := BitMachineRawSequence.program frontProgram batchProgram
  V22FullScheduleBatch.start (vertexControl,pairControl) V22FullScheduleBatch.control
abbrev FrontLabel := BitMachineRawSequence.Label
  (CurrentAdditive.GenericParameterBranch.Label V22GraphVertexMachine.machine) CurrentAdditive.GenericParameterPair.Label
abbrev Label := BitMachineRawSequence.Label FrontLabel (V22ParameterBatch.Label machines)
def start : Label := .inl (.inl (CurrentAdditive.GenericParameterBranch.startLabel V22GraphVertexMachine.machine))
def control := ((vertexControl,pairControl),V22FullScheduleBatch.control)
def rawBase (bits : List Bool) (k : ℕ) : Base → List Bool
  | .inl _ => []
  | .inr i => if i=0 then bits else if i=1 then List.replicate k true else []
def initial (bits : List Bool) (k : ℕ) : Stack → List Bool :=
  Sum.elim (Sum.elim (rawBase bits k) (fun _ => [])) (fun _ => [])
def afterVertex (bits : List Bool) (n k : ℕ) : Stack → List Bool :=
  bank vertexSlots (initial bits k)
    (CurrentAdditive.GenericParameterBranch.terminal V22GraphVertexMachine.machine (rawBase bits k)
      nPort bits (List.replicate n true) (100*(bits.length+1)^3))
def afterPair (bits : List Bool) (n k : ℕ) : Stack → List Bool :=
  bank pairSlots (afterVertex bits n k)
    (CurrentAdditive.GenericParameterPair.terminal (fun b => afterVertex bits n k (.inl (.inl b)))
      sourcePort n k)
def final (bits : List Bool) (n k : ℕ) : Stack → List Bool :=
  bank batchSlots (afterPair bits n k) (V22FullScheduleBatch.final bits n k)
def vertexClock (bits : List Bool) (n : ℕ) :=
  2*bits.length+100*(bits.length+1)^3+2*n+6
def pairClock (n k : ℕ) :=
  (2*n+2)+(2*k+2)+(n+k+3)+
    (2*(MatrixUnaryArithmetic.encodeInput n k).length+2)+3
def clock (bits : List Bool) (n k : ℕ) :=
  vertexClock bits n+pairClock n k+V22FullScheduleBatch.clock n k+2

theorem initial_raw (bits : List Bool) (k : ℕ) (j : Stack) :
    initial bits k j = if j=.inl (.inl graphPort) then bits
      else if j=.inl (.inl kPort) then List.replicate k true else [] := by
  cases j with
  | inl j =>
      cases j with
      | inl b => cases b with
        | inl b => simp [initial,rawBase,graphPort,kPort]
        | inr i => simp [initial,rawBase,graphPort,kPort]
      | inr w => simp [initial,graphPort,kPort]
  | inr w => simp [initial,graphPort,kPort]

theorem vertex_base (bits : List Bool) (n k : ℕ) (b : Base) :
    afterVertex bits n k (.inl (.inl b))=
      if b=nPort then List.replicate n true else rawBase bits k b := by
  by_cases h : b=nPort
  · subst b
    exact (CurrentAdditive.GenericParameterBranch.ambient_target V22GraphVertexMachine.machine nPort
      (rawBase bits k) bits (List.replicate n true) _ vertexSlots (initial bits k)).trans (by simp)
  · rw [if_neg h]
    exact CurrentAdditive.GenericParameterBranch.ambient_base_other V22GraphVertexMachine.machine nPort b h
      (rawBase bits k) bits (List.replicate n true) _ vertexSlots (initial bits k)
theorem pair_base (bits : List Bool) (n k : ℕ) (b : Base) :
    afterPair bits n k (.inl (.inl b))=
      if b=sourcePort then MatrixUnaryArithmetic.encodeInput n k
      else afterVertex bits n k (.inl (.inl b)) := by
  by_cases h : b=sourcePort
  · subst b
    exact (CurrentAdditive.GenericParameterPair.ambient_target _ sourcePort n k pairSlots
      (afterVertex bits n k)).trans (by simp)
  · rw [if_neg h]
    exact CurrentAdditive.GenericParameterPair.ambient_base_other _ sourcePort b h n k pairSlots (afterVertex bits n k)

theorem afterPair_projection (bits : List Bool) (n k : ℕ) :
    (fun j => afterPair bits n k (.inl j))=prepared bits n k := by
  funext j
  cases j with
  | inl b =>
      rw [pair_base,vertex_base]
      cases b with
      | inl j => rfl
      | inr j => fin_cases j <;> rfl
  | inr w =>
      change bank pairSlots _ _ (.inl (.inr w))=[]
      rw [bank_outside]
      · change bank vertexSlots _ _ (.inl (.inr w))=[]
        rw [bank_outside]
        · rfl
        · rintro ⟨x,hx⟩; cases x <;> simp [vertexSlots] at hx
      · rintro ⟨x,hx⟩; cases x <;> simp [pairSlots] at hx

theorem vertex_run (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) :
    ∃ t ≤ vertexClock (EncodedGraph.encode g) g.vertices,
      ((advance vertexProgram)^[t])
        (⟨some (CurrentAdditive.GenericParameterBranch.startLabel V22GraphVertexMachine.machine),vertexControl,
          initial (EncodedGraph.encode g) k⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,vertexControl,afterVertex (EncodedGraph.encode g) g.vertices k⟩ := by
  simpa only [vertexClock,List.length_replicate] using
    CurrentAdditive.GenericParameterBranch.run_install_framed_from_ambient V22GraphVertexMachine.machine
    graphPort nPort (EncodedGraph.encode g) (List.replicate g.vertices true)
    (100*((EncodedGraph.encode g).length+1)^3) vertexSlots
    (initial (EncodedGraph.encode g) k) rfl rfl (fun _ => rfl) (V22GraphVertexMachine.outputs g hg)
theorem pair_run (bits : List Bool) (n k : ℕ) :
    ∃ t ≤ pairClock n k, ((advance pairProgram)^[t])
      (⟨some CurrentAdditive.GenericParameterPair.startLabel,pairControl,afterVertex bits n k⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none,pairControl,afterPair bits n k⟩ := by
  apply CurrentAdditive.GenericParameterPair.run_install_framed_from_ambient nPort kPort sourcePort n k pairSlots
    (afterVertex bits n k)
  · simpa [vertexSlots] using vertex_base bits n k nPort
  · simpa [vertexSlots,rawBase,nPort,kPort] using vertex_base bits n k kPort
  · simpa [vertexSlots,rawBase,nPort,sourcePort] using vertex_base bits n k sourcePort
  · intro w
    change bank vertexSlots _ _ (.inr (.inr w))=[]
    rw [bank_outside]
    · rfl
    · rintro ⟨x,hx⟩; cases x <;> simp [vertexSlots] at hx

theorem batch_run (bits : List Bool) (n k : ℕ) :
    ∃ t ≤ V22FullScheduleBatch.clock n k,
      ((advance batchProgram)^[t])
        (⟨some V22FullScheduleBatch.start,V22FullScheduleBatch.control,afterPair bits n k⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,V22FullScheduleBatch.control,final bits n k⟩ := by
  obtain ⟨t,ht,hr⟩ := V22FullScheduleBatch.run bits n k
  have h := BitMachineStackRun.run batchSlots (afterPair bits n k)
    V22FullScheduleBatch.program
    (⟨some V22FullScheduleBatch.start,V22FullScheduleBatch.control,prepared bits n k⟩ :
      TM2.Cfg (fun _ : V22FullScheduleBatch.Stack => Bool) _ _) t
  rw [hr] at h
  have hb : bank batchSlots (afterPair bits n k) (prepared bits n k)=afterPair bits n k :=
    bank_eq_self batchSlots _ _ (fun j => (congrFun (afterPair_projection bits n k) j).symm)
  exact ⟨t,ht,by simpa only [batchProgram,stackCfg,hb,final] using h⟩

/-- A full-bank computation from only canonical raw graph bytes and supplied
unary k. No schedule bank, seed, precision, or successful tape is supplied. -/
theorem run (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) :
    ∃ t ≤ clock (EncodedGraph.encode g) g.vertices k,
      ((advance program)^[t])
        (⟨some start,control,initial (EncodedGraph.encode g) k⟩ :
          TM2.Cfg (fun _ : Stack => Bool) Label _) =
        ⟨none,control,final (EncodedGraph.encode g) g.vertices k⟩ := by
  obtain ⟨a,ha,hra⟩ := vertex_run g hg k
  obtain ⟨b,hb,hrb⟩ := pair_run (EncodedGraph.encode g) g.vertices k
  obtain ⟨c,hc,hrc⟩ := batch_run (EncodedGraph.encode g) g.vertices k
  obtain ⟨u,hu,hru⟩ := BitMachineRawSequence.runs vertexProgram pairProgram
    (CurrentAdditive.GenericParameterBranch.startLabel V22GraphVertexMachine.machine) CurrentAdditive.GenericParameterPair.startLabel
    vertexControl vertexControl pairControl pairControl
    (initial (EncodedGraph.encode g) k) (afterVertex (EncodedGraph.encode g) g.vertices k)
    (afterPair (EncodedGraph.encode g) g.vertices k) a b hra hrb
  obtain ⟨t,ht,hrt⟩ := BitMachineRawSequence.runs frontProgram batchProgram
    (BitMachineRawSequence.leftLabel (CurrentAdditive.GenericParameterBranch.startLabel V22GraphVertexMachine.machine))
    V22FullScheduleBatch.start (vertexControl,pairControl) (vertexControl,pairControl)
    V22FullScheduleBatch.control V22FullScheduleBatch.control
    (initial (EncodedGraph.encode g) k) (afterPair (EncodedGraph.encode g) g.vertices k)
    (final (EncodedGraph.encode g) g.vertices k) u c
    (by simpa only [frontProgram] using hru) hrc
  exact ⟨t,by unfold clock; omega,by simpa only [program,start,control] using hrt⟩

theorem constructor_projection (bits : List Bool) (n k : ℕ) :
    (fun j : Constructor => final bits n k (.inl (.inl (.inl j))))=constructorInput n k := by
  funext j
  exact (bank_at batchSlots _ _ (.inl (.inl j))).trans
    (congrFun (V22FullScheduleBatch.constructor_projection bits n k) j)
theorem graph_preserved (bits : List Bool) (n k : ℕ) :
    final bits n k (.inl (.inl graphPort))=bits :=
  (bank_at batchSlots _ _ (.inl graphPort)).trans (V22FullScheduleBatch.graph_preserved bits n k)
theorem k_preserved (bits : List Bool) (n k : ℕ) :
    final bits n k (.inl (.inl kPort))=List.replicate k true :=
  (bank_at batchSlots _ _ (.inl kPort)).trans (V22FullScheduleBatch.k_preserved bits n k)
theorem precision_exact (bits : List Bool) (n k : ℕ) :
    final bits n k (.inl (.inl precisionPort))=List.replicate
      (CurrentAdditive.V38OneStep.publicBits (V39FullSampleResources.fullAlphabet n (Nat.clog 2 n))
        (2^V39FullSampleResources.fullDrawExponent (Nat.clog 2 n) k)) true :=
  (bank_at batchSlots _ _ (.inl precisionPort)).trans (V22FullScheduleBatch.precision_exact bits n k)

#print axioms run
#print axioms constructor_projection
#print axioms graph_preserved
#print axioms k_preserved
#print axioms precision_exact
end
end V22RawGraphParameters
