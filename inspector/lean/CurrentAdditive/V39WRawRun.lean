import CurrentAdditive.V39WRawInput
import CurrentAdditive.V39WRawFinal
import CurrentAdditive.V39WTablePublicClock
import Paper2.RecursiveDefaults

/-! The actual raw graph/parameter/tape computation followed by the complete
current encoded table printer. The two fixed programs share literal retained
input fields; every printer work cell starts blank. -/
namespace CurrentAdditive.V39WRaw
noncomputable section
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 16384
open Paper2 Turing EthInapproximability.CurrentPaper
open BitMachineEncoding BitMachineStackEmbedding
open V38Schedule V39PublicSchedule V39FullSampleResources
local instance : DecidableEq Raw := Classical.decEq _
local instance : DecidableEq Stack := Classical.decEq _

def rawProgram := fun l => stackStmt rawSlots (V22RawPublicRepeat.program l)
def printProgram := fun l => stackStmt printerSlots (V39WEncodedTable.program l)
def program := BitMachineRawSequence.program rawProgram printProgram V39WEncodedTable.start
  V22RawPublicRepeat.control V39WEncodedTable.control
def start := FetchIndexed.labelOf program
  (BitMachineRawSequence.leftLabel V22RawPublicRepeat.start)
def control := (V22RawPublicRepeat.control,V39WEncodedTable.control)

def clock (g : EncodedGraph.Graph) (K : Nat) :=
  V22RawPublicRepeat.clock g K+
    V39WTablePublicClock.wholeClock g (seedWidth (Nat.clog 2 g.vertices))
      (fullS (Nat.clog 2 g.vertices)) (fullQ₁ (Nat.clog 2 g.vertices))
      (fullQ₂ (Nat.clog 2 g.vertices)) (fullW (Nat.clog 2 g.vertices))
      (fullQ (Nat.clog 2 g.vertices)) (V22RawPublicRepeat.repetitions g) K
      (sampleSide (Nat.clog 2 g.vertices) K) (B (Nat.clog 2 g.vertices) K)+1

theorem lift_raw_bank (A B : Raw → List Bool) :
    bank rawSlots (initial A) B=initial B := by
  funext j
  cases j with
  | inl j => exact bank_at rawSlots _ _ j
  | inr j =>
      rw [bank_outside rawSlots _ _ _ (by rintro ⟨x,h⟩; cases h)]
      rfl

def tails (n : Nat) [NeZero n] :=
  Paper2.RecursiveEntries.defaultTails
    (s := fullS (Nat.clog 2 n)) (q₁ := fullQ₁ (Nat.clog 2 n))
    (q₂ := fullQ₂ (Nat.clog 2 n)) (w := fullW (Nat.clog 2 n)) (Q := fullQ (Nat.clog 2 n))
    (fun _ : Fin (seedWidth (Nat.clog 2 n)) => false)
    (0 : Fin (seedWidth (Nat.clog 2 n)))
    ((0 : Fin (4*fullS (Nat.clog 2 n))), (Sum.inl (0 : Fin n) : Fin n ⊕ Fin (fullS (Nat.clog 2 n)-3)))
    (full_positive_widths (Nat.clog 2 n)).2.2.1
    (full_positive_widths (Nat.clog 2 n)).2.2.2.2.2.2.1
    (full_positive_widths (Nat.clog 2 n)).2.2.2.2.2.2.2

theorem physical_encoded_raw (g : EncodedGraph.Graph) (hg : g.Valid) (K : Nat)
    [NeZero g.vertices] (cc δv ζ : ℚ)
    (ht : FullTests cc (Nat.clog 2 g.vertices) g.edges.length δv ζ)
    (bits : RoundedDraw.BitBlocks (V22RawSamplerJoin.precision g.vertices K)
      (V22RawSamplerJoin.reservation g.vertices K)) (suffix : List Bool) :
    let tape := RoundedCodeLoop.tapeWord (V22RawSamplerJoin.precision g.vertices K)
      (V22RawSamplerJoin.reservation g.vertices K) bits ++ suffix
    let hq := V22RawPublicRepeat.width_eq g cc δv ζ ht
    let hs : 4 ≤ fullS (Nat.clog 2 g.vertices) := by
      have h := fullS_ge_256 (Nat.clog 2 g.vertices); omega
    let z := labels g K cc δv ζ ht bits
    let m := sampleSide (Nat.clog 2 g.vertices) K
    let f : Fin m → Fin m → Bool := fun i j =>
      V39RecursiveTable.matrix (V39EdgeSourceFront.edgeActivity g hg (by omega)
        (V22RawPublicRepeat.repetitions g) hq) K (z.1 i) (z.2 j)
    let WB := (MatrixTableWriter.ready
      (V39WEntry.bankW g (V22RawPublicRepeat.repetitions g) K m m z.1 z.2)
      m m 0 0 0 0 [] (MatrixMaterialization.rowMajor f)).contents
    ∃ t ≤ clock g K, ∃ v,
      ((advance program)^[t])
        (⟨some start,control,initial (V22PublicRepeat.initial
          (V22RawSamplerJoin.initial (EncodedGraph.encode g) K tape))⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,v,bank printerSlots (afterRaw g K cc δv ζ ht bits suffix)
          (V39WEncodedTable.final (sources g K cc δv ζ ht bits) WB m m
            (B (Nat.clog 2 g.vertices) K) (MatrixMaterialization.rowMajor f))⟩ := by
  intro tape hq hs z m f WB
  obtain ⟨a,ha,ea⟩ := V22RawPublicRepeat.run_final g hg K cc δv ζ ht bits suffix
  have ea' : ((advance V22RawPublicRepeat.program)^[a])
      (⟨some V22RawPublicRepeat.start,V22RawPublicRepeat.control,
        V22PublicRepeat.initial (V22RawSamplerJoin.initial (EncodedGraph.encode g) K tape)⟩ :
        TM2.Cfg (fun _ : Raw => Bool) _ _) =
      ⟨none,V22RawPublicRepeat.control,V22RawPublicRepeat.final g K cc δv ζ ht bits suffix⟩ := by
    convert ea using 1 <;> congr 3 <;> exact Subsingleton.elim _ _
  have eraw := HeaderJoin.liftG rawSlots V22RawPublicRepeat.program
    (initial (V22PublicRepeat.initial (V22RawSamplerJoin.initial (EncodedGraph.encode g) K tape)))
    (V22PublicRepeat.initial (V22RawSamplerJoin.initial (EncodedGraph.encode g) K tape))
    (V22RawPublicRepeat.final g K cc δv ζ ht bits suffix) (by intro j; rfl)
    _ _ _ _ ea'
  rw [lift_raw_bank] at eraw
  obtain ⟨b,hb,vb,eprint⟩ := V39WEncodedTable.physical_from_bank printerSlots
    (afterRaw g K cc δv ζ ht bits suffix) g hg
    (full_positive_widths (Nat.clog 2 g.vertices)).1 hs
    (V22RawPublicRepeat.repetitions g) hq (tails g.vertices) K m
    (B (Nat.clog 2 g.vertices) K) z.1 z.2 (printer_ready g K cc δv ζ ht bits suffix)
  have hbPublic := V39WTablePublicClock.charge_public g hg hs
    (V22RawPublicRepeat.repetitions g) hq (tails g.vertices) K m
    (B (Nat.clog 2 g.vertices) K) z.1 z.2
  obtain ⟨t,htime,hr⟩ := BitMachineRawSequence.runs rawProgram printProgram
    V22RawPublicRepeat.start V39WEncodedTable.start V22RawPublicRepeat.control
    V22RawPublicRepeat.control V39WEncodedTable.control vb _ _ _ a b eraw eprint
  exact ⟨t,by unfold clock; dsimp only [m] at hb hbPublic; omega,(V22RawPublicRepeat.control,vb),by
    simpa only [program,start,control,sources,afterRaw,FetchIndexed.labelOf] using hr⟩

#print axioms lift_raw_bank
#print axioms physical_encoded_raw
end
end CurrentAdditive.V39WRaw
