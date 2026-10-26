import CurrentAdditive.V42FullTableWriter
import CurrentAdditive.V42RawPublicRepeat
import CurrentAdditive.V42RawSamplerClock

set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 16384
namespace V42FullTableClock
noncomputable section
open Paper2 EthInapproximability.CurrentPaper
open CurrentAdditive V42RuntimeSchedule
open V39WTablePublicClock
attribute [local irreducible] V22PublicRepeat.clockCoefficient

def repeatExponent : ℕ := V22PublicRepeat.clockCoefficient+3078
def rawTableExponent : ℕ := V42RawSamplerJoin.joinExponent+repeatExponent+tableExponent+8
attribute [local irreducible] coreExponent tableCoefficient tableExponent repeatExponent rawTableExponent
  V42RawSamplerJoin.joinExponent

theorem repeat_clock_full (g : EncodedGraph.Graph) (c δv ζ : ℚ) (L k : ℕ)
    (hn : g.vertices ≤ 2^L) (ht : FullTests c L g.edges.length δv ζ) :
    V22PublicRepeat.clock g (fullS L) (fullQ₂ L) ≤ (graphSize g)^3*2^(repeatExponent*T L k) := by
  let Z := 2^(1024*T L k)
  have hT : 1 ≤ T L k := by have hL := ht.1.2.2.1; unfold T; nlinarith
  obtain ⟨_,_,_,hq,hs,_,_⟩ := full_widths_le_pow g.vertices L hn ht.2
  have he := (full_edge_repeat_le c δv ζ L g.edges.length ht).1.trans hq
  have hEZ : 2^fullWidthExponent L ≤ Z := Nat.pow_le_pow_right (by decide) (by
    unfold fullWidthExponent T; nlinarith)
  have hsZ := hs.trans hEZ
  have hqZ := hq.trans hEZ
  have heZ := he.trans hEZ
  have hG : 1 ≤ graphSize g := by unfold graphSize; omega
  have hZ : 1 ≤ Z := Nat.one_le_two_pow
  have hGZ : graphSize g ≤ graphSize g*Z := Nat.le_mul_of_pos_right _ (by omega)
  have hZG : Z ≤ graphSize g*Z := Nat.le_mul_of_pos_left _ (by omega)
  have hsum : (EncodedGraph.encode g).length+fullS L+g.edges.length+fullQ₂ L+1 ≤ 4*graphSize g*Z := by
    calc
      _=graphSize g+fullS L+g.edges.length+fullQ₂ L := by unfold graphSize; omega
      _ ≤ 4*(graphSize g*Z) := by omega
      _=4*graphSize g*Z := by ring
  have hpoly := V22PublicRepeat.clock_polynomial g (fullS L) (fullQ₂ L) (by simpa only [fullQ₂_eq_old] using ht.1.1.2.2.1)
  have hcoef : V22PublicRepeat.clockCoefficient ≤ 2^(V22PublicRepeat.clockCoefficient*T L k) :=
    Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by decide) (by nlinarith))
  have h64 : (64 : ℕ) ≤ 2^(6*T L k) := by
    change 2^6 ≤ _
    exact Nat.pow_le_pow_right (by decide) (by nlinarith)
  calc
    _ ≤ V22PublicRepeat.clockCoefficient*(4*graphSize g*Z)^3 :=
      hpoly.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsum 3))
    _=64*V22PublicRepeat.clockCoefficient*(graphSize g)^3*Z^3 := by ring
    _ ≤ 2^(6*T L k)*2^(V22PublicRepeat.clockCoefficient*T L k)*(graphSize g)^3*Z^3 := by gcongr
    _=(graphSize g)^3*2^(repeatExponent*T L k) := by
      dsimp only [Z]
      unfold repeatExponent
      rw [←pow_mul,←pow_add]
      rw [Nat.mul_comm (2^(6*T L k+V22PublicRepeat.clockCoefficient*T L k)) ((graphSize g)^3),
        Nat.mul_assoc,←pow_add]
      congr 2
      ring

/-- The exact serial clock agreed with the physical bank-join owner: raw
parameters/current sampler/repetition supplier, then prepared writer/header,
with one final bank-preserving finite-control handoff. -/
def rawTableClock (g : EncodedGraph.Graph) (k : ℕ) : ℕ :=
  let L := Nat.clog 2 g.vertices
  V42RawPublicRepeat.clock g k+
    wholeClock g (seedWidth L) (fullS L) (fullQ₁ L) (fullQ₂ L) (fullW L) (fullQ L)
      (fullRepeat L g.edges.length) k (sampleSide L k) (V42RuntimeSchedule.B L k)+1

theorem raw_table_full (g : EncodedGraph.Graph) (k : ℕ) (c δv ζ : ℚ) (hk : 1 ≤ k)
    (ht : FullTests c (Nat.clog 2 g.vertices) g.edges.length δv ζ) :
    rawTableClock g k ≤ (graphSize g)^11*2^(rawTableExponent*T (Nat.clog 2 g.vertices) k) := by
  let L := Nat.clog 2 g.vertices
  let D := V42RawSamplerJoin.joinExponent+repeatExponent+tableExponent
  let Z := 2^(D*T L k)
  let A := (graphSize g)^11*Z
  have hL : 16 ≤ L := ht.1.2.2.1
  have hT : 1 ≤ T L k := by unfold T; nlinarith
  have hn : g.vertices ≤ 2^L := Nat.le_pow_clog (by decide) _
  have hn2 : 2 ≤ g.vertices := by
    by_contra h
    have he : g.vertices=0 ∨ g.vertices=1 := by omega
    rcases he with he|he <;> norm_num [L,he] at hL
  have hraw := V42RawSamplerJoin.clock_le_exp (EncodedGraph.encode g) g.vertices k g.edges.length c δv ζ hn2 hk ht
  change V42RawSamplerJoin.clock (EncodedGraph.encode g) g.vertices k ≤
    102*(graphSize g)^3+2^(V42RawSamplerJoin.joinExponent*T L k) at hraw
  have hr := repeat_clock_full g c δv ζ L k hn ht
  have hw := whole_full g c δv ζ L k hn ht
  have hrawZ : 2^(V42RawSamplerJoin.joinExponent*T L k) ≤ Z := Nat.pow_le_pow_right (by decide) (by dsimp [D]; nlinarith)
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
    _ ≤ (graphSize g)^11*2^(rawTableExponent*T (Nat.clog 2 g.vertices) k) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by
        unfold rawTableExponent
        dsimp only [D,L] at *
        nlinarith))

/-- The explicit byte factor can also be discharged using the actual
canonical encoding of the unchanged valid input graph. -/
theorem graph_size_full (g : EncodedGraph.Graph) (hg : g.Valid) (c δv ζ : ℚ) (L : ℕ)
    (hn : g.vertices ≤ 2^L) (ht : FullTests c L g.edges.length δv ζ) :
    graphSize g ≤ 2^(40*L) := by
  let M := 2^fullWidthExponent L
  have hL := ht.1.2.2.1
  obtain ⟨hnM,_,_,hq,_,_,_⟩ := full_widths_le_pow g.vertices L hn ht.2
  have heM := (full_edge_repeat_le c δv ζ L g.edges.length ht).1.trans hq
  have hM : 1 ≤ M := Nat.one_le_two_pow
  have hglen := EncodedGraph.encode_length_upper g hg
  have hb : graphSize g ≤ 16*M^2 := by
    have hpoly : g.vertices+3+g.edges.length*(4*g.vertices+4) ≤ M+3+M*(4*M+4) := by
      gcongr
    unfold graphSize
    change g.vertices ≤ M at hnM
    change g.edges.length ≤ M at heM
    nlinarith only [hglen,hpoly,hM]
  calc
    _ ≤ 16*M^2 := hb
    _=2^(2*fullWidthExponent L+4) := by dsimp [M]; rw [←pow_mul,pow_add]; norm_num; ring
    _ ≤ 2^(40*L) := Nat.pow_le_pow_right (by decide) (by unfold fullWidthExponent; omega)

theorem raw_table_pure (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) (c δv ζ : ℚ) (hk : 1 ≤ k)
    (ht : FullTests c (Nat.clog 2 g.vertices) g.edges.length δv ζ) :
    rawTableClock g k ≤ 2^((rawTableExponent+440)*T (Nat.clog 2 g.vertices) k) := by
  let L := Nat.clog 2 g.vertices
  have hgsize := graph_size_full g hg c δv ζ L (Nat.le_pow_clog (by decide) _) ht
  have hLT : L ≤ T L k := by unfold T; nlinarith
  apply (raw_table_full g k c δv ζ hk ht).trans
  calc
    _ ≤ (2^(40*L))^11*2^(rawTableExponent*T L k) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hgsize 11)
    _=2^(440*L+rawTableExponent*T L k) := by rw [←pow_mul,←pow_add]; congr 1; ring
    _ ≤ 2^((rawTableExponent+440)*T L k) := Nat.pow_le_pow_right (by decide) (by
      rw [Nat.add_mul]
      have h := Nat.mul_le_mul_left 440 hLT
      omega)

theorem actual_random_tape_length (g : EncodedGraph.Graph) (k : ℕ) (c δv ζ : ℚ)
    (ht : FullTests c (Nat.clog 2 g.vertices) g.edges.length δv ζ)
    (bits : RoundedDraw.BitBlocks (V42RawSamplerJoin.precision g.vertices k)
      (V42RawSamplerJoin.reservation g.vertices k)) (suffix : List Bool) :
    (RoundedCodeLoop.tapeWord (V42RawSamplerJoin.precision g.vertices k)
      (V42RawSamplerJoin.reservation g.vertices k) bits ++ suffix).length ≤
        2^(272*T (Nat.clog 2 g.vertices) k)+suffix.length := by
  rw [List.length_append,RoundedCodeLoop.tapeWord_length]
  simpa only [T,Nat.mul_assoc] using Nat.add_le_add_right (V42RuntimeSchedule.reserved_bits_le g.vertices
    (Nat.clog 2 g.vertices) k (Nat.le_pow_clog (by decide) _) ht.2) _

def rawInputSize (g : EncodedGraph.Graph) (k : ℕ)
    (bits : RoundedDraw.BitBlocks (V42RawSamplerJoin.precision g.vertices k)
      (V42RawSamplerJoin.reservation g.vertices k)) (suffix : List Bool) :=
  (EncodedGraph.encode g).length+k+
    (RoundedCodeLoop.tapeWord (V42RawSamplerJoin.precision g.vertices k)
      (V42RawSamplerJoin.reservation g.vertices k) bits ++ suffix).length

theorem raw_input_size_full (g : EncodedGraph.Graph) (k : ℕ) (c δv ζ : ℚ)
    (ht : FullTests c (Nat.clog 2 g.vertices) g.edges.length δv ζ)
    (bits : RoundedDraw.BitBlocks (V42RawSamplerJoin.precision g.vertices k)
      (V42RawSamplerJoin.reservation g.vertices k)) (suffix : List Bool) :
    rawInputSize g k bits suffix ≤ graphSize g+suffix.length+2^(273*T (Nat.clog 2 g.vertices) k) := by
  let D := T (Nat.clog 2 g.vertices) k
  let Z := 2^(272*D)
  have hL := ht.1.2.2.1
  have hD : 1 ≤ D := by dsimp [D,T]; nlinarith
  have hkD : k ≤ D := by dsimp [D,T]; nlinarith
  have hkZ : k ≤ Z := (hkD.trans Nat.lt_two_pow_self.le).trans
    (Nat.pow_le_pow_right (by decide) (by omega))
  have htape := actual_random_tape_length g k c δv ζ ht bits suffix
  have htwice : 2*Z ≤ 2^(273*D) := by
    calc
      2*Z=2^(272*D+1) := by dsimp [Z]; rw [pow_add]; norm_num; ring
      _ ≤ 2^(273*D) := Nat.pow_le_pow_right (by decide) (by omega)
  change _ ≤ graphSize g+suffix.length+2^(273*D)
  change _ ≤ Z+suffix.length at htape
  unfold rawInputSize graphSize
  omega

theorem raw_input_size_pure (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) (c δv ζ : ℚ)
    (ht : FullTests c (Nat.clog 2 g.vertices) g.edges.length δv ζ)
    (bits : RoundedDraw.BitBlocks (V42RawSamplerJoin.precision g.vertices k)
      (V42RawSamplerJoin.reservation g.vertices k)) :
    rawInputSize g k bits [] ≤ 2^(275*T (Nat.clog 2 g.vertices) k) := by
  let L := Nat.clog 2 g.vertices
  have hL := ht.1.2.2.1
  have hT : 1 ≤ T L k := by unfold T; nlinarith
  have hLT : L ≤ T L k := by unfold T; nlinarith
  have hgsize := (graph_size_full g hg c δv ζ L (Nat.le_pow_clog (by decide) _) ht).trans
    (Nat.pow_le_pow_right (by decide) (show 40*L ≤ 273*T L k by omega))
  have hsize := raw_input_size_full g k c δv ζ ht bits []
  simp only [List.length_nil,Nat.add_zero] at hsize
  change rawInputSize g k bits [] ≤ graphSize g+2^(273*T L k) at hsize
  calc
    _ ≤ 2*2^(273*T L k) := by omega
    _=2^(273*T L k+1) := by rw [pow_add]; norm_num; ring
    _ ≤ 2^(275*T L k) := Nat.pow_le_pow_right (by decide) (by omega)

#print axioms repeat_clock_full
#print axioms raw_table_full

#print axioms graph_size_full
#print axioms raw_table_pure

#print axioms actual_random_tape_length
#print axioms raw_input_size_full
#print axioms raw_input_size_pure
end
end V42FullTableClock



