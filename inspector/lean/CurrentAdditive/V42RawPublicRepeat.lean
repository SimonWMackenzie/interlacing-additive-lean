import CurrentAdditive.V22PublicRepeatClock
import CurrentAdditive.V42RawSamplerJoin

/-! Literal raw graph+k+tape execution through the actual sampler and the
new physical edge-count/padded-width/repetition computation. -/
namespace V42RawPublicRepeat
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option synthInstance.maxSize 16384
open Turing EthInapproximability.CurrentPaper BitMachineEncoding BitMachineStackEmbedding
open V42RuntimeSchedule
open CurrentAdditive

abbrev Raw := V42RawSamplerJoin.Stack
abbrev Stack := V22PublicRepeat.Stack Raw
noncomputable def rawDecEq : DecidableEq Raw := inferInstance
local instance : DecidableEq Raw := rawDecEq
local instance : DecidableEq Stack := Classical.decEq _
def graphPort : Raw := .inl (.inl (.inl V42FullScheduleBatch.graphPort))
def corePort (j : Fin 65) : Raw := .inl (.inl (.inl (.inl (.inl j))))
def sPort : Raw := corePort 17
def q₂Port : Raw := corePort 12
def rawSlots : Raw ↪ Stack := Function.Embedding.inl
def samplerProgram := fun l => stackStmt rawSlots (V42RawSamplerJoin.program l)
def repeatProgram := V22PublicRepeat.program graphPort sPort q₂Port
def program := BitMachineRawSequence.program samplerProgram repeatProgram V22PublicRepeat.start
  V42RawSamplerJoin.control V22PublicRepeat.control
abbrev Label := BitMachineRawSequence.Label V42RawSamplerJoin.Label V22PublicRepeat.Label
def start : Label := .inl V42RawSamplerJoin.start
def control := (V42RawSamplerJoin.control,V22PublicRepeat.control)
def clock (g : EncodedGraph.Graph) (k : ℕ) :=
  V42RawSamplerJoin.clock (EncodedGraph.encode g) g.vertices k+
  V22PublicRepeat.clock g (fullS (Nat.clog 2 g.vertices)) (fullQ₂ (Nat.clog 2 g.vertices))+1

theorem lift_raw_bank (A B : Raw → List Bool) :
    bank rawSlots (V22PublicRepeat.initial A) B=V22PublicRepeat.initial B := by
  funext j
  cases j with
  | inl j => exact bank_at rawSlots _ _ j
  | inr j =>
      rw [bank_outside]
      · rfl
      · rintro ⟨x,hx⟩; cases hx

theorem sampler_graph (g : EncodedGraph.Graph) (k : ℕ) [NeZero g.vertices]
    (cc δv ζ : ℚ) (ht : FullTests cc (Nat.clog 2 g.vertices) g.edges.length δv ζ)
    (bits : RoundedDraw.BitBlocks (V42RawSamplerJoin.precision g.vertices k) (V42RawSamplerJoin.reservation g.vertices k))
    (suffix : List Bool) :
    V42RawSamplerJoin.final (EncodedGraph.encode g) g.vertices k g.edges.length cc δv ζ ht bits suffix graphPort=
      EncodedGraph.encode g := by
  rw [graphPort,V42RawSamplerJoin.final_raw_preserved]
  exact V42RawGraphParameters.graph_preserved _ _ _

theorem sampler_core (g : EncodedGraph.Graph) (k : ℕ) [NeZero g.vertices]
    (cc δv ζ : ℚ) (ht : FullTests cc (Nat.clog 2 g.vertices) g.edges.length δv ζ)
    (bits : RoundedDraw.BitBlocks (V42RawSamplerJoin.precision g.vertices k) (V42RawSamplerJoin.reservation g.vertices k))
    (suffix : List Bool) (j : Fin 65) :
    V42RawSamplerJoin.final (EncodedGraph.encode g) g.vertices k g.edges.length cc δv ζ ht bits suffix (corePort j)=
      Paper2.CodeRecursiveSeedPrep.publicBase g.vertices (fullS (Nat.clog 2 g.vertices))
        (fullQ₁ (Nat.clog 2 g.vertices)) (fullQ₂ (Nat.clog 2 g.vertices))
        (fullW (Nat.clog 2 g.vertices)) (fullQ (Nat.clog 2 g.vertices))
        (seedWidth (Nat.clog 2 g.vertices)) (List.replicate k true) j := by
  rw [corePort,V42RawSamplerJoin.final_raw_preserved]
  exact (congrFun (V42RawGraphParameters.constructor_projection (EncodedGraph.encode g) g.vertices k) (.inl j)).trans
    (V42FullScheduleBatch.constructor_core g.vertices k j)

theorem run (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) [NeZero g.vertices]
    (cc δv ζ : ℚ) (ht : FullTests cc (Nat.clog 2 g.vertices) g.edges.length δv ζ)
    (bits : RoundedDraw.BitBlocks (V42RawSamplerJoin.precision g.vertices k) (V42RawSamplerJoin.reservation g.vertices k))
    (suffix : List Bool) :
    let tape := RoundedCodeLoop.tapeWord (V42RawSamplerJoin.precision g.vertices k)
      (V42RawSamplerJoin.reservation g.vertices k) bits ++ suffix
    let S := V42RawSamplerJoin.final (EncodedGraph.encode g) g.vertices k g.edges.length cc δv ζ ht bits suffix
    let s := fullS (Nat.clog 2 g.vertices)
    let q₂ := fullQ₂ (Nat.clog 2 g.vertices)
    ∃ t ≤ clock g k, ((advance program)^[t])
      (⟨some start,control,V22PublicRepeat.initial (V42RawSamplerJoin.initial (EncodedGraph.encode g) k tape)⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Label _) =
      ⟨none,control,V22PublicRepeat.final S graphPort g s q₂⟩ := by
  intro tape S s q₂
  obtain ⟨a,ha,ea⟩ := V42RawSamplerJoin.run g hg k cc δv ζ ht bits suffix
  have ea' : ((advance V42RawSamplerJoin.program)^[a])
      (⟨some V42RawSamplerJoin.start,V42RawSamplerJoin.control,
        V42RawSamplerJoin.initial (EncodedGraph.encode g) k tape⟩ :
        TM2.Cfg (fun _ : Raw => Bool) V42RawSamplerJoin.Label _) =
      ⟨none,V42RawSamplerJoin.control,S⟩ := by
    convert ea using 1 <;> congr 3 <;> exact Subsingleton.elim _ _
  have elift := BitMachineStackRun.run rawSlots
    (V22PublicRepeat.initial (V42RawSamplerJoin.initial (EncodedGraph.encode g) k tape))
    V42RawSamplerJoin.program
    (⟨some V42RawSamplerJoin.start,V42RawSamplerJoin.control,V42RawSamplerJoin.initial (EncodedGraph.encode g) k tape⟩ :
      TM2.Cfg (fun _ : Raw => Bool) V42RawSamplerJoin.Label _) a
  rw [ea'] at elift
  have efirst : ((advance samplerProgram)^[a])
      (⟨some V42RawSamplerJoin.start,V42RawSamplerJoin.control,
        V22PublicRepeat.initial (V42RawSamplerJoin.initial (EncodedGraph.encode g) k tape)⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none,V42RawSamplerJoin.control,V22PublicRepeat.initial S⟩ := by
    simpa only [samplerProgram,stackCfg,lift_raw_bank] using elift
  have hgraph : S graphPort=EncodedGraph.encode g := sampler_graph g k cc δv ζ ht bits suffix
  have hs : S sPort=List.replicate s true := by
    simpa only [Paper2.CodeRecursiveSeedPrep.publicBase,↓reduceIte] using sampler_core g k cc δv ζ ht bits suffix 17
  have hq : S q₂Port=List.replicate q₂ true := by
    simpa only [Paper2.CodeRecursiveSeedPrep.publicBase,↓reduceIte] using sampler_core g k cc δv ζ ht bits suffix 12
  obtain ⟨b,hb,eb⟩ := V22PublicRepeat.run S graphPort sPort q₂Port g hg s q₂ hgraph hs hq
  obtain ⟨t,hclock,e⟩ := BitMachineRawSequence.runs samplerProgram repeatProgram
    V42RawSamplerJoin.start V22PublicRepeat.start V42RawSamplerJoin.control V42RawSamplerJoin.control
    V22PublicRepeat.control V22PublicRepeat.control
    (V22PublicRepeat.initial (V42RawSamplerJoin.initial (EncodedGraph.encode g) k tape))
    (V22PublicRepeat.initial S) (V22PublicRepeat.final S graphPort g s q₂) a b efirst eb
  refine ⟨t,?_,e⟩
  change t ≤ V42RawSamplerJoin.clock (EncodedGraph.encode g) g.vertices k+
    V22PublicRepeat.clock g s q₂+1
  omega

end
end V42RawPublicRepeat

