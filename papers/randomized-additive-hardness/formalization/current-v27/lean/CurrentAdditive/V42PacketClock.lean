import CurrentAdditive.V42WRawPacket
import CurrentAdditive.V42PhysicalRawTableClock
import CurrentAdditive.V39PacketClock

/-! Uniform bound for the actual packed raw-graph machine, including its
physical input decoding and output serialization. -/
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 32768
namespace CurrentAdditive.V42WRaw
noncomputable section
open Paper2 EthInapproximability.CurrentPaper
open V42RuntimeSchedule V42FullTableClock
local instance : DecidableEq Stack := Classical.decEq _

def packedInput (g : EncodedGraph.Graph) (K : ℕ)
    (bits : RoundedDraw.BitBlocks (V42RawSamplerJoin.precision g.vertices K)
      (V42RawSamplerJoin.reservation g.vertices K)) : List Bool :=
  BitMachineBankCodec.encode ![EncodedGraph.encode g,List.replicate K true,
    RoundedCodeLoop.tapeWord (V42RawSamplerJoin.precision g.vertices K)
      (V42RawSamplerJoin.reservation g.vertices K) bits]

def packetCoefficient : ℕ := V39TypedPacket.clockCoefficient
  graphPort kPort tapePort graph_ne_k graph_ne_tape k_ne_tape program

def packetExponent : ℕ := packetCoefficient+278+(rawTableExponent+440)+2

theorem packedInput_length (g : EncodedGraph.Graph) (K : ℕ)
    (bits : RoundedDraw.BitBlocks (V42RawSamplerJoin.precision g.vertices K)
      (V42RawSamplerJoin.reservation g.vertices K)) :
    (packedInput g K bits).length=2*rawInputSize g K bits []+3 := by
  simp only [packedInput,BitMachineBankCodec.encode_length,Fin.sum_univ_succ,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero,Nat.add_zero,
    List.length_replicate,rawInputSize,List.append_nil]
  ring

theorem packet_clock_exponential (g : EncodedGraph.Graph) (hg : g.Valid) (K : ℕ)
    (cc δv ζ : ℚ) (hK : 1≤K)
    (ht : FullTests cc (Nat.clog 2 g.vertices) g.edges.length δv ζ)
    (bits : RoundedDraw.BitBlocks (V42RawSamplerJoin.precision g.vertices K)
      (V42RawSamplerJoin.reservation g.vertices K)) :
    packetClock (packedInput g K bits).length (clock g K) ≤
      2^(packetExponent*T (Nat.clog 2 g.vertices) K) := by
  let D := T (Nat.clog 2 g.vertices) K
  let b := rawTableExponent+440
  let Z := 2^((278+b)*D)
  have hD : 1≤D := by
    have hL := ht.1.2.2.1
    dsimp [D,T]
    nlinarith
  have hinput : (packedInput g K bits).length ≤ 2^(278*D) := by
    rw [packedInput_length]
    have hi := raw_input_size_pure g hg K cc δv ζ ht bits
    change rawInputSize g K bits [] ≤ 2^(275*D) at hi
    have hp : 1≤2^(275*D) := Nat.one_le_two_pow
    calc
      2*rawInputSize g K bits []+3 ≤ 8*2^(275*D) := by omega
      _ = 2^(275*D+3) := by rw [pow_add]; norm_num; ring
      _ ≤ 2^(278*D) := Nat.pow_le_pow_right (by decide) (by omega)
  have htime : clock g K ≤ 2^(b*D) := by
    rw [physical_clock_eq]
    exact raw_table_pure g hg K cc δv ζ hK ht
  have hiZ : 2^(278*D) ≤ Z := Nat.pow_le_pow_right (by decide) (by nlinarith)
  have htZ : 2^(b*D) ≤ Z := Nat.pow_le_pow_right (by decide) (by nlinarith)
  have hZ : 1≤Z := Nat.one_le_two_pow
  have hsum : (packedInput g K bits).length+clock g K+1 ≤ 4*Z := by omega
  have hsumExp : (packedInput g K bits).length+clock g K+1 ≤ 2^((278+b+2)*D) := by
    calc
      _ ≤ 4*Z := hsum
      _ = 2^((278+b)*D+2) := by dsimp [Z]; rw [pow_add]; norm_num; ring
      _ ≤ 2^((278+b+2)*D) := Nat.pow_le_pow_right (by decide) (by nlinarith)
  have hc : packetCoefficient ≤ 2^(packetCoefficient*D) := Nat.lt_two_pow_self.le.trans
    (Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_right _ hD))
  have hclock := V39TypedPacket.clock_linear (L := PacketLabel) (V := PacketControl) graphPort kPort tapePort
    graph_ne_k graph_ne_tape k_ne_tape program (packedInput g K bits).length (clock g K)
  calc
    packetClock (packedInput g K bits).length (clock g K) ≤
      packetCoefficient*((packedInput g K bits).length+clock g K+1) := hclock
    _ ≤ 2^(packetCoefficient*D)*2^((278+b+2)*D) := Nat.mul_le_mul hc hsumExp
    _ = 2^(packetExponent*D) := by rw [←pow_add]; congr 1; unfold packetExponent; dsimp [b]; ring

theorem packed_outputs_exponential (g : EncodedGraph.Graph) (hg : g.Valid) (K : ℕ)
    [NeZero g.vertices] (cc δv ζ : ℚ) (hK : 1≤K)
    (ht : FullTests cc (Nat.clog 2 g.vertices) g.edges.length δv ζ)
    (bits : RoundedDraw.BitBlocks (V42RawSamplerJoin.precision g.vertices K)
      (V42RawSamplerJoin.reservation g.vertices K)) :
    finiteMachine.OutputsWithin (packedInput g K bits) (outputWord g hg K cc δv ζ ht bits)
      (2^(packetExponent*T (Nat.clog 2 g.vertices) K)) := by
  have ho := packet_outputs g hg K cc δv ζ ht bits []
  simp only [List.append_nil] at ho
  exact BitMachine.outputsWithin_mono _ ho (packet_clock_exponential g hg K cc δv ζ hK ht bits)

#print axioms packet_clock_exponential
#print axioms packed_outputs_exponential

/-- The promised graph supplies every runtime premise. The program and its
absolute exponent are independent of the source constants and input graph. -/
theorem promised_packed_outputs (g : EncodedGraph.Graph) (hg : g.Valid) (K Δ : ℕ)
    [NeZero g.vertices] (γ : ℚ) (hK : 1≤K) (hγ : 0<γ) (hΔ : 0<Δ)
    (hnm : g.vertices≤2*g.edges.length) (hdeg : 2*g.edges.length≤Δ*g.vertices)
    (hlarge : V42RuntimeSchedule.sourceCutoff γ Δ≤g.vertices)
    (bits : RoundedDraw.BitBlocks (V42RawSamplerJoin.precision g.vertices K)
      (V42RawSamplerJoin.reservation g.vertices K)) :
    let cc := V38Schedule.fullConstant γ Δ g.vertices g.edges.length
    let δv := V38Schedule.sourceDeltaV γ Δ g.vertices g.edges.length
    let ζ := V38Schedule.sourceZeta γ
    let ht := V42RuntimeSchedule.tests_all_large γ Δ g.vertices g.edges.length
      hγ hΔ (NeZero.pos g.vertices) hnm hdeg hlarge
    finiteMachine.OutputsWithin (packedInput g K bits) (outputWord g hg K cc δv ζ ht bits)
      (2^(packetExponent*T (Nat.clog 2 g.vertices) K)) := by
  intro cc δv ζ ht
  exact packed_outputs_exponential g hg K cc δv ζ hK ht bits

#print axioms promised_packed_outputs
end
end CurrentAdditive.V42WRaw


