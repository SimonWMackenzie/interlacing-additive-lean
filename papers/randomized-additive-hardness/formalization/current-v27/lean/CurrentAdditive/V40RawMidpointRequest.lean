import CurrentAdditive.V40MidpointAmbient
import CurrentAdditive.V39WRawRun

namespace CurrentAdditive.V40RawMidpointRequest
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 16384
open Paper2 Turing EthInapproximability.CurrentPaper
open BitMachineEncoding BitMachineStackEmbedding EncodedCommunication
open V38Schedule V39PublicSchedule V39FullSampleResources
abbrev Raw := V39WRaw.Stack
abbrev Stack := V40MidpointAmbient.Ambient Raw
local instance : DecidableEq Raw := Classical.decEq _


def bPort : Raw := V39WRaw.printerSlots V39WEncodedTable.thresholdPort
def kPort : Raw := V39WRaw.printerSlots (.inl 8)
def printedPort : Raw := V39WRaw.outputPort

theorem b_ne_k : bPort ≠ kPort := by
  intro h
  have h' := V39WRaw.printerSlots.injective h
  cases h'
theorem b_ne_printed : bPort ≠ printedPort := by
  intro h
  have h' := V39WRaw.printerSlots.injective h
  have h'' := V39WEncodedTable.headerSlots.injective h'
  change HeaderJoin.thrM = HeaderJoin.wOut at h''
  cases h''
theorem k_ne_printed : kPort ≠ printedPort := by
  intro h
  have h' := V39WRaw.printerSlots.injective h
  cases h'

def rawSlots : Raw ↪ Stack := Function.Embedding.inl
def rawProgram := fun l => stackStmt rawSlots (V39WRaw.program l)
def requestProgram := V40MidpointAmbient.program bPort kPort printedPort
  b_ne_k b_ne_printed k_ne_printed

def program := BitMachineRawSequence.program rawProgram requestProgram
  V40MidpointRequest.start V39WRaw.control V40MidpointRequest.control
def start := FetchIndexed.labelOf program
  (BitMachineRawSequence.leftLabel V39WRaw.start)
def control := (V39WRaw.control,V40MidpointRequest.control)
def initial := V40MidpointAmbient.initial (J := Raw)
def outputPort : Stack := .inr (V40MidpointRequest.low 7)

def clock (g : EncodedGraph.Graph) (K : Nat) :=
  V39WRaw.clock g K + V40MidpointRequest.cap
    (sampleSide (Nat.clog 2 g.vertices) K ^ 2) + 1

theorem lift_raw_bank (A B : Raw → List Bool) :
    bank rawSlots (initial A) B = initial B := by
  funext j
  cases j with
  | inl j => exact bank_at rawSlots _ _ j
  | inr j =>
      rw [bank_outside rawSlots _ _ _ (by rintro ⟨x,h⟩; cases h)]
      rfl

theorem physical_request_raw (g : EncodedGraph.Graph) (hg : g.Valid) (K : Nat)
    [NeZero g.vertices] (cc δv ζ : ℚ)
    (ht : FullTests cc (Nat.clog 2 g.vertices) g.edges.length δv ζ)
    (bits : RoundedDraw.BitBlocks (V22RawSamplerJoin.precision g.vertices K)
      (V22RawSamplerJoin.reservation g.vertices K)) (suffix : List Bool) :
    let tape := RoundedCodeLoop.tapeWord (V22RawSamplerJoin.precision g.vertices K)
      (V22RawSamplerJoin.reservation g.vertices K) bits ++ suffix
    let hq := V22RawPublicRepeat.width_eq g cc δv ζ ht
    let z := V39WRaw.labels g K cc δv ζ ht bits
    let m := sampleSide (Nat.clog 2 g.vertices) K
    let f : Fin m → Fin m → Bool := fun i j =>
      V39RecursiveTable.matrix (V39EdgeSourceFront.edgeActivity g hg (by
        have h := fullS_ge_256 (Nat.clog 2 g.vertices); omega)
        (V22RawPublicRepeat.repetitions g) hq) K (z.1 i) (z.2 j)
    let WB := (MatrixTableWriter.ready
      (V39WEntry.bankW g (V22RawPublicRepeat.repetitions g) K m m z.1 z.2)
      m m 0 0 0 0 [] (MatrixMaterialization.rowMajor f)).contents
    let W := V39WRaw.finished (V39WRaw.afterRaw g K cc δv ζ ht bits suffix)
      (V39WRaw.sources g K cc δv ζ ht bits) WB m (B (Nat.clog 2 g.vertices) K)
      (MatrixMaterialization.rowMajor f)
    ∃ t ≤ clock g K, ∃ v,
      ((advance program)^[t])
        (⟨some start,control,initial (V39WRaw.initial (V22PublicRepeat.initial
          (V22RawSamplerJoin.initial (EncodedGraph.encode g) K tape)))⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,v,V40MidpointAmbient.final W (B (Nat.clog 2 g.vertices) K) K
          (encodeInstance ⟨m,m,B (Nat.clog 2 g.vertices) K,MatrixMaterialization.rowMajor f⟩)⟩ := by
  intro tape hq z m f WB W
  let word := encodeInstance ⟨m,m,B (Nat.clog 2 g.vertices) K,MatrixMaterialization.rowMajor f⟩
  obtain ⟨a,ha,va,ea⟩ := V39WRaw.physical_encoded_raw g hg K cc δv ζ ht bits suffix
  have ea' : ((advance V39WRaw.program)^[a])
      (⟨some V39WRaw.start,V39WRaw.control,V39WRaw.initial (V22PublicRepeat.initial
        (V22RawSamplerJoin.initial (EncodedGraph.encode g) K tape))⟩ :
        TM2.Cfg (fun _ : Raw => Bool) _ _) = ⟨none,va,W⟩ := ea
  have eraw := HeaderJoin.liftG rawSlots V39WRaw.program
    (initial (V39WRaw.initial (V22PublicRepeat.initial
      (V22RawSamplerJoin.initial (EncodedGraph.encode g) K tape)))) _ W
    (by intro j; rfl) _ _ _ _ ea'
  rw [lift_raw_bank] at eraw
  have hb : W bPort = List.replicate (B (Nat.clog 2 g.vertices) K) true :=
    V39WRaw.finished_threshold _ _ _ _ _ _
  have hk : W kPort = List.replicate K true := by
    change W (V39WRaw.sourceSlots 8) = _
    dsimp only [W]
    rw [V39WRaw.finished_source]
    rfl
  have hp : W printedPort = word := V39WRaw.finished_word _ _ _ _ _ _
  obtain ⟨b,hbtime,eb⟩ := V40MidpointAmbient.outputs bPort kPort printedPort
    b_ne_k b_ne_printed k_ne_printed W _ K word hb hk hp
  have hbPublic := V40MidpointRequest.public_clock_le (Nat.clog 2 g.vertices) K f
  change V40MidpointRequest.clock (B (Nat.clog 2 g.vertices) K) K word ≤
    V40MidpointRequest.cap (m^2) at hbPublic
  obtain ⟨t,htime,hr⟩ := BitMachineRawSequence.runs rawProgram requestProgram
    V39WRaw.start V40MidpointRequest.start V39WRaw.control va
    V40MidpointRequest.control V40MidpointRequest.control _ _ _ a b eraw eb
  exact ⟨t,by unfold clock; dsimp only [word,m] at hbtime hbPublic; omega,
    (V39WRaw.control,V40MidpointRequest.control),by
      simpa only [program,start,control,FetchIndexed.labelOf] using hr⟩

#print axioms physical_request_raw
end
end CurrentAdditive.V40RawMidpointRequest
