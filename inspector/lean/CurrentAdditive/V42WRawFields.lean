import CurrentAdditive.V39WEncodedTransport
import CurrentAdditive.V39WTableSample
import CurrentAdditive.V42RawPublicRepeatFields
import CurrentAdditive.V42RawSamplerOutput

/-! Literal placement of the retained raw sampler/repetition fields into the
fixed encoded table printer. Every writer/header work cell is fresh. -/
namespace CurrentAdditive.V42WRaw
noncomputable section
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 16384
open Paper2 Turing EthInapproximability.CurrentPaper
open BitMachineEncoding BitMachineStackEmbedding
open V42RuntimeSchedule
open V39WEntry
open V39WTablePrepare (WriterStack)

abbrev Raw := V42RawPublicRepeat.Stack
abbrev Stack := Raw ⊕ (WriterStack ⊕ (HeaderA.HB ⊕ Fin 3))
local instance : DecidableEq Raw := Classical.decEq _
local instance : DecidableEq Stack := Classical.decEq _
local instance : DecidableEq V39WEncodedTable.Stack := Classical.decEq _

def old (j : V42RawSamplerJoin.Stack) : Raw := .inl j
def core (j : Fin 65) : Raw := old (V42RawSamplerJoin.originalConstructor (.inl j))
def shapeCell (j : Fin 65) : Raw := old (V42RawSamplerJoin.shapeSlots (.inr (.inl j)))
def rawThreshold : Raw := old (.inl (.inl (.inl (.inr (10:Fin 13)))))
def blank : Stack := .inr (.inr (.inr 0))
def headerScratch : Stack := .inr (.inr (.inr 1))
def prepareScratch : Stack := .inr (.inr (.inr 2))

def sourceSlots : Fin 14 → Stack :=
  ![.inl (old V42RawSamplerJoin.graphPort),.inl (.inr (.inl 3)),.inl (.inr (.inl 0)),
    .inl (core 63),.inl (core 16),.inl (core 17),.inl (core 31),.inl (core 32),
    .inl (old V42RawSamplerJoin.kPort),
    .inl (old (V42RawSamplerJoin.originalConstructor CodeGeneratorSampleTransfer.countX)),
    .inl (shapeCell 2),.inl (shapeCell 33),.inl (old V42RawSamplerJoin.outputPort),blank]

theorem sourceSlots_injective : Function.Injective sourceSlots := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl |
    simp [sourceSlots,old,core,shapeCell,blank,V42RawSamplerJoin.graphPort,V42RawSamplerJoin.kPort,
      V42RawSamplerJoin.originalConstructor,V42RawSamplerJoin.outputPort,V42RawSamplerJoin.shapeSlots,
      V39PhysicalShapeSample.sampleSlots,V39PhysicalSample.source,CodeGeneratorSampleTransfer.countX,
      V42FullScheduleBatch.graphPort,V42FullScheduleBatch.kPort,
        V39PhysicalShapeSample.sampleSlots,V39PhysicalSample.source] at h

def printerMap : V39WEncodedTable.Stack → Stack
  | .inl i => sourceSlots i
  | .inr (.inl (.inl w)) => .inr (.inl w)
  | .inr (.inl (.inr (.inl h))) => .inr (.inr (.inl h))
  | .inr (.inl (.inr (.inr f))) => (![.inl rawThreshold,headerScratch] : Fin 2 → Stack) f
  | .inr (.inr _) => prepareScratch

theorem printerMap_injective : Function.Injective printerMap := by
  intro a b h
  rcases a with a | ((a | (a | a)) | a) <;>
    rcases b with b | ((b | (b | b)) | b)
  · exact congrArg Sum.inl (sourceSlots_injective h)
  · fin_cases a <;> simp [printerMap,sourceSlots,blank] at h
  · fin_cases a <;> simp [printerMap,sourceSlots,blank] at h
  · fin_cases a <;> fin_cases b <;>
      simp [printerMap,sourceSlots,old,core,shapeCell,blank,headerScratch,rawThreshold,
        V42RawSamplerJoin.graphPort,V42RawSamplerJoin.kPort,V42RawSamplerJoin.outputPort,
        V42RawSamplerJoin.originalConstructor,V42RawSamplerJoin.shapeSlots,
        V42FullScheduleBatch.graphPort,V42FullScheduleBatch.kPort,
        V39PhysicalShapeSample.sampleSlots,V39PhysicalSample.source] at h
  · fin_cases a <;> fin_cases b <;> simp [printerMap,sourceSlots,blank,prepareScratch] at h
  · fin_cases b <;> simp [printerMap,sourceSlots,blank] at h
  · simpa [printerMap] using h
  · simp [printerMap] at h
  · fin_cases b <;> simp [printerMap,rawThreshold,headerScratch] at h
  · simp [printerMap,prepareScratch] at h
  · fin_cases b <;> simp [printerMap,sourceSlots,blank] at h
  · simp [printerMap] at h
  · simpa [printerMap] using h
  · fin_cases b <;> simp [printerMap,rawThreshold,headerScratch] at h
  · simp [printerMap,prepareScratch] at h
  · fin_cases a <;> fin_cases b <;>
      simp [printerMap,sourceSlots,old,core,shapeCell,blank,headerScratch,rawThreshold,
        V42RawSamplerJoin.graphPort,V42RawSamplerJoin.kPort,V42RawSamplerJoin.outputPort,
        V42RawSamplerJoin.originalConstructor,V42RawSamplerJoin.shapeSlots,
        V42FullScheduleBatch.graphPort,V42FullScheduleBatch.kPort,
        V39PhysicalShapeSample.sampleSlots,V39PhysicalSample.source] at h
  · fin_cases a <;> simp [printerMap,rawThreshold,headerScratch] at h
  · fin_cases a <;> simp [printerMap,rawThreshold,headerScratch] at h
  · fin_cases a <;> fin_cases b <;> first | rfl | simp [printerMap,rawThreshold,headerScratch] at h
  · fin_cases a <;> fin_cases b <;> simp [printerMap,rawThreshold,headerScratch,prepareScratch] at h
  · fin_cases a <;> fin_cases b <;> simp [printerMap,sourceSlots,blank,prepareScratch] at h
  · simp [printerMap,prepareScratch] at h
  · simp [printerMap,prepareScratch] at h
  · fin_cases a <;> fin_cases b <;> simp [printerMap,rawThreshold,headerScratch,prepareScratch] at h
  · fin_cases a; fin_cases b; rfl

def printerSlots : V39WEncodedTable.Stack ↪ Stack := ⟨printerMap,printerMap_injective⟩
def rawSlots : Raw ↪ Stack := Function.Embedding.inl
def outputPort : Stack := printerSlots V39WEncodedTable.outputPort
def initial (S : Raw → List Bool) : Stack → List Bool := Sum.elim S (fun _ => [])

#print axioms sourceSlots_injective
#print axioms printerMap_injective
end
end CurrentAdditive.V42WRaw

