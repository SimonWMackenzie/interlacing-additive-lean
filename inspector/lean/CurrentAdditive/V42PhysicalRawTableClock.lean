import CurrentAdditive.V42RawTableClock
import CurrentAdditive.V42WRawRun

set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 16384
namespace V42FullTableClock
noncomputable section
open Paper2 Turing EthInapproximability.CurrentPaper CurrentAdditive
open BitMachineEncoding BitMachineStackEmbedding
open V42RuntimeSchedule
open V42WRaw
local instance : DecidableEq V42WRaw.Raw := Classical.decEq _
local instance : DecidableEq V42WRaw.Stack := Classical.decEq _

theorem physical_clock_eq (g : EncodedGraph.Graph) (k : ℕ) :
    V42WRaw.clock g k=rawTableClock g k := rfl

/-- The fixed physical raw graph+k+tape constructor, with its entire actual
encoded-table exit bank and one uniform bound for every supplied random tape. -/
theorem physical_encoded_raw_full (g : EncodedGraph.Graph) (hg : g.Valid) (K : Nat)
    [NeZero g.vertices] (cc δv ζ : ℚ) (hK : 1 ≤ K)
    (ht : FullTests cc (Nat.clog 2 g.vertices) g.edges.length δv ζ)
    (bits : RoundedDraw.BitBlocks (V42RawSamplerJoin.precision g.vertices K)
      (V42RawSamplerJoin.reservation g.vertices K)) (suffix : List Bool) :
    let tape := RoundedCodeLoop.tapeWord (V42RawSamplerJoin.precision g.vertices K)
      (V42RawSamplerJoin.reservation g.vertices K) bits ++ suffix
    let hq := V42RawPublicRepeat.width_eq g cc δv ζ ht
    let hs : 4 ≤ fullS (Nat.clog 2 g.vertices) := by
      have h := fullS_ge_256 (Nat.clog 2 g.vertices); omega
    let z := labels g K cc δv ζ ht bits
    let m := sampleSide (Nat.clog 2 g.vertices) K
    let f : Fin m → Fin m → Bool := fun i j =>
      V39RecursiveTable.matrix (V39EdgeSourceFront.edgeActivity g hg (by omega)
        (V42RawPublicRepeat.repetitions g) hq) K (z.1 i) (z.2 j)
    let WB := (MatrixTableWriter.ready
      (V39WEntry.bankW g (V42RawPublicRepeat.repetitions g) K m m z.1 z.2)
      m m 0 0 0 0 [] (MatrixMaterialization.rowMajor f)).contents
    ∃ t ≤ (graphSize g)^11*2^(rawTableExponent*T (Nat.clog 2 g.vertices) K), ∃ v,
      ((advance V42WRaw.program)^[t])
        (⟨some V42WRaw.start,V42WRaw.control,V42WRaw.initial (V22PublicRepeat.initial
          (V42RawSamplerJoin.initial (EncodedGraph.encode g) K tape))⟩ :
          TM2.Cfg (fun _ : V42WRaw.Stack => Bool) _ _) =
        ⟨none,v,bank printerSlots (afterRaw g K cc δv ζ ht bits suffix)
          (V39WEncodedTable.final (sources g K cc δv ζ ht bits) WB m m
            (B (Nat.clog 2 g.vertices) K) (MatrixMaterialization.rowMajor f))⟩ := by
  intro tape hq hs z m f WB
  obtain ⟨t,htime,v,hr⟩ := V42WRaw.physical_encoded_raw g hg K cc δv ζ ht bits suffix
  refine ⟨t,htime.trans ?_,v,hr⟩
  rw [physical_clock_eq]
  exact raw_table_full g K cc δv ζ hK ht

/-- Fixed polynomial parser/serializer overhead remains within one fixed
exponential after the actual public input and run bounds are substituted. -/
theorem polynomial_from_two_exponentials (C d a b D x : ℕ) (hD : 1 ≤ D)
    (hx : x ≤ 2^(a*D)+2^(b*D)+1) :
    C*(x+1)^d ≤ 2^((C+d*(a+b+2))*D) := by
  let Z := 2^((a+b)*D)
  have ha : 2^(a*D) ≤ Z := Nat.pow_le_pow_right (by decide) (by nlinarith)
  have hb : 2^(b*D) ≤ Z := Nat.pow_le_pow_right (by decide) (by nlinarith)
  have hZ : 1 ≤ Z := Nat.one_le_two_pow
  have hx4 : x+1 ≤ 4*Z := by omega
  have hxpow : x+1 ≤ 2^((a+b+2)*D) := by
    calc
      _ ≤ 4*Z := hx4
      _=2^((a+b)*D+2) := by dsimp [Z]; rw [pow_add]; norm_num; ring
      _ ≤ 2^((a+b+2)*D) := Nat.pow_le_pow_right (by decide) (by nlinarith)
  have hC : C ≤ 2^(C*D) := Nat.lt_two_pow_self.le.trans
    (Nat.pow_le_pow_right (by decide) (by nlinarith))
  calc
    _ ≤ 2^(C*D)*(2^((a+b+2)*D))^d := Nat.mul_le_mul hC (Nat.pow_le_pow_left hxpow d)
    _=2^((C+d*(a+b+2))*D) := by rw [←pow_mul,←pow_add]; congr 1; ring

#print axioms physical_clock_eq
#print axioms physical_encoded_raw_full
#print axioms polynomial_from_two_exponentials
end
end V42FullTableClock

