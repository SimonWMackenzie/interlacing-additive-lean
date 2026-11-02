import CurrentAdditive.V42RawSamplerJoin

set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 16384
namespace V42RawSamplerJoin
noncomputable section
open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open V42FullScheduleBatch
open V42RuntimeSchedule
open CurrentAdditive.V38OneStep CurrentAdditive.V39RecursiveGenerator

def graphPort : Stack := .inl (.inl (.inl V42FullScheduleBatch.graphPort))
def kPort : Stack := .inl (.inl (.inl V42FullScheduleBatch.kPort))
def originalConstructor (j : Constructor) : Stack := .inl (.inl (.inl (.inl j)))
def outputPort : Stack := shapeSlots
  (CurrentAdditive.V39PhysicalShapeSample.sampleSlots (.inl CurrentAdditive.V39PhysicalSample.source))

/-- The entire initial bank contains only the literal graph, supplied unary k,
and random input tape. In particular no precision or constructor is preloaded. -/
theorem initial_only_inputs (graph : List Bool) (k : ℕ) (tape : List Bool) (j : Stack) :
    initial graph k tape j = if j=graphPort then graph
      else if j=kPort then List.replicate k true else if j=tapePort then tape else [] := by
  cases j with
  | inl r => simpa [initial,graphPort,kPort,tapePort] using V42RawGraphParameters.initial_raw graph k r
  | inr j =>
    rcases j with j|(j|j)
    · simp [initial,extra,graphPort,kPort,tapePort]
    · by_cases h : j.val=RoundedCodeOutput.tapePort
      · have he : j=freshTape := Subtype.ext h
        subst j
        simp [initial,extra,graphPort,kPort,tapePort,freshTape]
      · have he : j≠freshTape := by intro he; apply h; exact congrArg Subtype.val he
        simp [initial,extra,graphPort,kPort,tapePort,h,he]
    · simp [initial,extra,graphPort,kPort,tapePort]

section Output
variable (graph : List Bool) (n k edgeCount : ℕ) [NeZero n] (cc δv ζ : ℚ)
variable (ht : FullTests cc (Nat.clog 2 n) edgeCount δv ζ)
variable (bits : CurrentAdditive.RoundedDraw.BitBlocks (precision n k) (reservation n k))
variable (suffix : List Bool)

theorem final_constructor (j : Constructor) :
    final graph n k edgeCount cc δv ζ ht bits suffix (originalConstructor j)=constructorInput n k j :=
  (final_raw_preserved graph n k edgeCount cc δv ζ ht bits suffix _).trans
    (congrFun (V42RawGraphParameters.constructor_projection graph n k) j)

theorem final_graph : final graph n k edgeCount cc δv ζ ht bits suffix graphPort=graph :=
  (final_raw_preserved graph n k edgeCount cc δv ζ ht bits suffix _).trans
    (V42RawGraphParameters.graph_preserved graph n k)

theorem final_k : final graph n k edgeCount cc δv ζ ht bits suffix kPort=List.replicate k true :=
  (final_raw_preserved graph n k edgeCount cc δv ζ ht bits suffix _).trans
    (V42RawGraphParameters.k_preserved graph n k)

theorem final_precision : final graph n k edgeCount cc δv ζ ht bits suffix precisionPort=
    List.replicate (precision n k) true :=
  (final_raw_preserved graph n k edgeCount cc δv ζ ht bits suffix _).trans
    (V42RawGraphParameters.precision_exact graph n k)

theorem final_public_extra (i : Fin 13) :
    final graph n k edgeCount cc δv ζ ht bits suffix (.inl (.inl (.inl (.inr i))))=
      V42FullScheduleBatch.expected graph n k (.inr i) := by
  rw [final_raw_preserved]
  exact (bank_at V42RawGraphParameters.batchSlots _ _ (.inl (.inr i))).trans
    (V42FullScheduleBatch.final_base graph n k (.inr i))

theorem final_threshold :
    final graph n k edgeCount cc δv ζ ht bits suffix (.inl (.inl (.inl (.inr (10 : Fin 13)))))=
      List.replicate (V42RuntimeSchedule.B (Nat.clog 2 n) k) true := by
  simpa [V42FullScheduleBatch.expected] using final_public_extra graph n k edgeCount cc δv ζ ht bits suffix 10

theorem final_output : final graph n k edgeCount cc δv ζ ht bits suffix outputPort=
    CurrentAdditive.V39GeneratorCode.sampleWord n (seedWidth (Nat.clog 2 n))
      (fullQ₁ (Nat.clog 2 n)) (fullQ₂ (Nat.clog 2 n)) (fullS (Nat.clog 2 n))
      (fullW (Nat.clog 2 n)) (fullQ (Nat.clog 2 n)) k (sampleSide (Nat.clog 2 n) k)
      (CurrentAdditive.V39PhysicalSample.sampleAtBudget n (seedWidth (Nat.clog 2 n))
        (fullQ₁ (Nat.clog 2 n)) (fullQ₂ (Nat.clog 2 n)) (fullS (Nat.clog 2 n))
        (fullW (Nat.clog 2 n)) (fullQ (Nat.clog 2 n))
        (by have h := fullS_ge_256 (Nat.clog 2 n); omega) rfl k (sampleSide (Nat.clog 2 n) k)
        (reservation n k) (fullDrawCap_le cc (Nat.clog 2 n) edgeCount k δv ζ ht) bits) := by
  exact CurrentAdditive.V39PhysicalShapeSample.physical_output _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem final_output_event_error (E : List Bool → Prop) :
    |(CurrentAdditive.RoundedDraw.bitBlocksLaw (precision n k) (reservation n k)).prob
      (fun bits => E (final graph n k edgeCount cc δv ζ ht bits suffix outputPort)) -
      (sampleLaw n (seedWidth (Nat.clog 2 n)) (fullQ₁ (Nat.clog 2 n)) (fullQ₂ (Nat.clog 2 n))
        (fullS (Nat.clog 2 n)) (fullW (Nat.clog 2 n)) (fullQ (Nat.clog 2 n))
        k (sampleSide (Nat.clog 2 n) k)).toFiniteLaw.prob
      (fun z => E (CurrentAdditive.V39GeneratorCode.sampleWord n (seedWidth (Nat.clog 2 n))
        (fullQ₁ (Nat.clog 2 n)) (fullQ₂ (Nat.clog 2 n)) (fullS (Nat.clog 2 n))
        (fullW (Nat.clog 2 n)) (fullQ (Nat.clog 2 n)) k (sampleSide (Nat.clog 2 n) k) z))| ≤ (1:ℝ)/200 := by
  simp_rw [final,outputPort,bank_at]
  exact CurrentAdditive.V39PhysicalShapeSample.output_event_error_200 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
end Output

#print axioms initial_only_inputs
#print axioms final_constructor
#print axioms final_output
#print axioms final_output_event_error
end
end V42RawSamplerJoin


