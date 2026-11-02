import CurrentAdditive.V42ZeroSamplerClock
import CurrentAdditive.V42PacketClock

/-! The actual new raw sampler/entry-evaluator/printer clock for every
natural iteration count, including its zero-round seed case. -/
namespace CurrentAdditive.V42ZeroAccess
noncomputable section
open Paper2 EthInapproximability.CurrentPaper
open V42RuntimeSchedule V42FullTableClock V39WTablePublicClock
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 32768

def rawTableExponentAll : ℕ := samplerExponent+repeatExponent+tableExponent+8
attribute [local irreducible] coreExponent tableCoefficient tableExponent repeatExponent
  rawTableExponentAll samplerExponent V42RawSamplerJoin.joinExponent

theorem raw_table_full_all (g : EncodedGraph.Graph) (k : ℕ) (c δv ζ : ℚ)
    (ht : FullTests c (Nat.clog 2 g.vertices) g.edges.length δv ζ) :
    rawTableClock g k ≤ (graphSize g)^11*2^(rawTableExponentAll*T (Nat.clog 2 g.vertices) k) := by
  let L := Nat.clog 2 g.vertices
  let D := samplerExponent+repeatExponent+tableExponent
  let Z := 2^(D*T L k)
  let A := (graphSize g)^11*Z
  have hL : 16 ≤ L := ht.1.2.2.1
  have hT : 1 ≤ T L k := by unfold T; nlinarith
  have hn : g.vertices ≤ 2^L := Nat.le_pow_clog (by decide) _
  have hn2 : 2 ≤ g.vertices := by
    by_contra h
    have he : g.vertices=0 ∨ g.vertices=1 := by omega
    rcases he with he|he <;> norm_num [L,he] at hL
  have hraw := sampler_clock_all (EncodedGraph.encode g) g.vertices k g.edges.length c δv ζ hn2 ht
  change V42RawSamplerJoin.clock (EncodedGraph.encode g) g.vertices k ≤
    102*(graphSize g)^3+2^(samplerExponent*T L k) at hraw
  have hr := repeat_clock_full g c δv ζ L k hn ht
  have hw := whole_full g c δv ζ L k hn ht
  have hrawZ : 2^(samplerExponent*T L k) ≤ Z := Nat.pow_le_pow_right (by decide) (by dsimp [D]; nlinarith)
  have hrZ : 2^(repeatExponent*T L k) ≤ Z := Nat.pow_le_pow_right (by decide) (by dsimp [D]; nlinarith)
  have hwZ : 2^(tableExponent*T L k) ≤ Z := Nat.pow_le_pow_right (by decide) (by dsimp [D]; nlinarith)
  have hG : 1 ≤ graphSize g := by unfold graphSize; omega
  have hG3 : (graphSize g)^3 ≤ (graphSize g)^11 := Nat.pow_le_pow_right hG (by decide)
  have hZ : 1 ≤ Z := Nat.one_le_two_pow
  have hGA : (graphSize g)^11 ≤ A := Nat.le_mul_of_pos_right _ (by omega)
  have hZA : Z ≤ A := Nat.le_mul_of_pos_left _ (by have h : 1 ≤ (graphSize g)^11 := one_le_pow₀ hG; omega)
  have hA : 1 ≤ A := hZ.trans hZA
  have hrawA : V42RawSamplerJoin.clock (EncodedGraph.encode g) g.vertices k ≤ 103*A := by
    have hG3A := hG3.trans hGA
    omega
  have hrA : V22PublicRepeat.clock g (fullS L) (fullQ₂ L) ≤ A :=
    hr.trans (Nat.mul_le_mul hG3 hrZ)
  have hwA := hw.trans (Nat.mul_le_mul_left ((graphSize g)^11) hwZ)
  have hbound : rawTableClock g k ≤ 128*A := by
    unfold rawTableClock V42RawPublicRepeat.clock
    change V42RawSamplerJoin.clock (EncodedGraph.encode g) g.vertices k+
      V22PublicRepeat.clock g (fullS L) (fullQ₂ L)+1+
      wholeClock g (seedWidth L) (fullS L) (fullQ₁ L) (fullQ₂ L) (fullW L) (fullQ L)
        (fullRepeat L g.edges.length) k (sampleSide L k) (V42RuntimeSchedule.B L k)+1 ≤ _
    omega
  apply hbound.trans
  calc
    128*A=(graphSize g)^11*2^(D*T L k+7) := by dsimp [A,Z]; rw [pow_add]; norm_num; ring
    _ ≤ (graphSize g)^11*2^(rawTableExponentAll*T (Nat.clog 2 g.vertices) k) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by
        unfold rawTableExponentAll
        dsimp only [D,L] at *
        nlinarith))


theorem raw_table_pure_all (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) (c δv ζ : ℚ)
    (ht : FullTests c (Nat.clog 2 g.vertices) g.edges.length δv ζ) :
    rawTableClock g k ≤ 2^((rawTableExponentAll+440)*T (Nat.clog 2 g.vertices) k) := by
  let L := Nat.clog 2 g.vertices
  have hgsize := graph_size_full g hg c δv ζ L (Nat.le_pow_clog (by decide) _) ht
  have hLT : L ≤ T L k := by unfold T; nlinarith
  apply (raw_table_full_all g k c δv ζ ht).trans
  calc
    _ ≤ (2^(40*L))^11*2^(rawTableExponentAll*T L k) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hgsize 11)
    _=2^(440*L+rawTableExponentAll*T L k) := by rw [←pow_mul,←pow_add]; congr 1; ring
    _ ≤ 2^((rawTableExponentAll+440)*T L k) := Nat.pow_le_pow_right (by decide) (by
      rw [Nat.add_mul]
      have h := Nat.mul_le_mul_left 440 hLT
      omega)


#print axioms raw_table_full_all
#print axioms raw_table_pure_all
end
end CurrentAdditive.V42ZeroAccess
