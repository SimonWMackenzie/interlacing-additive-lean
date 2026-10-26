import EthInapproximability.CurrentPaper.WeightedRawWordsLevel0K

/-! # Segment 1: the public polynomial clock of the level-0 raw-word program

Lane `owner:b-raw-words-clock` (Paper B, unit 2). The frozen predecessor
`b-weighted-raw-words-owner` proved the fixed program `rawWordsKProgram M c`
halts within the explicit clock `rawWordsKBound`. Here every clock summand is
majorized by an explicit coefficient times a fixed power:

* `level0Bound n ≤ level0C * (n+1)^128` (the only super-cubic summand is the
  unary row count `2^(2^e)`, `2^e = IndexSeed.width b < 128(b+1)`,
  `b = sourceDepth n`, `2^b ≤ 2(n+1)`);
* `edgesBound g ≤ 120 * (|encode g|+1)^3` for every valid graph;
* `kBound M n ≤ kPolyC M * (n+1)^3 + fuelBound (kValue M n)` and
  `fuelBound k ≤ 4k + 4|Nat.bits k| + 4 ≤ 8n + 4`;
* `rawWordsKBound M n c |encode g| g ≤ rawC M c * (n + |encode g| + 1)^128`.

No machine is changed; these are arithmetic facts about the frozen clocks. -/

namespace EthInapproximability.CurrentPaper.WeightedRawWordsClock

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.CurrentPaper.WeightedRawWords

noncomputable section

/-- The fixed numeral `2^255` (kept as a name so that arithmetic tactics do
not expand it). -/
def rowC : ℕ := 2 ^ 255

/-! ## Elementary facts about the depth and the row exponent -/

theorem sourceDepth_le_succ (n : ℕ) : EffectiveIteration.sourceDepth n ≤ n + 1 := by
  unfold EffectiveIteration.sourceDepth
  apply Nat.clog_le_of_le_pow
  have h : n + 1 < 2 ^ (n + 1) := Nat.lt_two_pow_self
  omega

theorem two_pow_sourceDepth_le (n : ℕ) :
    2 ^ EffectiveIteration.sourceDepth n ≤ 2 * (n + 1) := by
  unfold EffectiveIteration.sourceDepth
  have hpos : 0 < Nat.clog 2 (n + 2) := Nat.clog_pos (by norm_num) (by omega)
  have h := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (x := n + 2) (by omega)
  obtain ⟨k, hk⟩ : ∃ k, Nat.clog 2 (n + 2) = k + 1 := ⟨Nat.clog 2 (n + 2) - 1, by omega⟩
  rw [hk] at h ⊢
  simp only [Nat.pred_eq_sub_one, Nat.add_sub_cancel] at h
  rw [pow_succ]
  omega

theorem two_pow_costExp_lt (b : ℕ) : 2 ^ costExp b < 128 * (b + 1) := by
  rw [costExp_eq]
  exact IndexSeed.width_lt b

theorem costExp_lt (b : ℕ) : costExp b < 128 * (b + 1) :=
  lt_trans Nat.lt_two_pow_self (two_pow_costExp_lt b)

/-- The unary row count `2^(2^e)` of level 0 is polynomial of degree 128. -/
theorem double_pow_le (n : ℕ) :
    2 ^ 2 ^ costExp (EffectiveIteration.sourceDepth n) ≤ rowC * (n + 1) ^ 128 := by
  set b := EffectiveIteration.sourceDepth n with hb
  have h1 : 2 ^ costExp b ≤ b * 128 + 127 := by
    have := two_pow_costExp_lt b
    omega
  have h2 : 2 ^ 2 ^ costExp b ≤ 2 ^ (b * 128 + 127) := Nat.pow_le_pow_right (by norm_num) h1
  have h3 : 2 ^ (b * 128 + 127) = 2 ^ 127 * (2 ^ b) ^ 128 := by
    rw [pow_add, pow_mul]
    ring
  have h4 : (2 ^ b) ^ 128 ≤ (2 * (n + 1)) ^ 128 :=
    Nat.pow_le_pow_left (two_pow_sourceDepth_le n) 128
  have h5 : (2 * (n + 1)) ^ 128 = 2 ^ 128 * (n + 1) ^ 128 := by rw [mul_pow]
  rw [h3] at h2
  rw [h5] at h4
  calc 2 ^ 2 ^ costExp b ≤ 2 ^ 127 * (2 ^ b) ^ 128 := h2
    _ ≤ 2 ^ 127 * (2 ^ 128 * (n + 1) ^ 128) := Nat.mul_le_mul_left _ h4
    _ = rowC * (n + 1) ^ 128 := by unfold rowC; ring

theorem one_le_succ_pow (n k : ℕ) : 1 ≤ (n + 1) ^ k := Nat.one_le_pow _ _ (by omega)

theorem succ_le_succ_pow (n k : ℕ) (hk : 1 ≤ k) : n + 1 ≤ (n + 1) ^ k := by
  calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
    _ ≤ (n + 1) ^ k := Nat.pow_le_pow_right (by omega) hk

/-! ## S2: the level-0 numeric words -/

def edgeBoundC : ℕ := 9 * UnaryBinaryEncoding.coefficient + 75

theorem edgeBound_le (n : ℕ) : edgeBound n ≤ edgeBoundC * (n + 1) ^ 2 := by
  have hb : Nat.clog 2 (n + 2) ≤ n + 1 := sourceDepth_le_succ n
  have hsq : (n + 2 + 1) ^ 2 ≤ 9 * (n + 1) ^ 2 := by nlinarith
  have hU := Nat.mul_le_mul_left (UnaryBinaryEncoding.coefficient + 6) hsq
  have hX1 := one_le_succ_pow n 2
  have hxX := succ_le_succ_pow n 2 (by norm_num)
  unfold edgeBound ETHScaleColumnCandidate.logCost edgeBoundC
  generalize (n + 2 + 1) ^ 2 = Q at *
  generalize (n + 1) ^ 2 = X at *
  generalize Nat.clog 2 (n + 2) = B at *
  generalize UnaryBinaryEncoding.coefficient = U at *
  nlinarith

def depthBoundC : ℕ := edgeBoundC + 13 + 2 * edgeCard + edgeCard * edgePer * edgeBoundC

theorem depthBound_le (n : ℕ) : depthBound n ≤ depthBoundC * (n + 1) ^ 2 := by
  have hE := edgeBound_le n
  have hb := sourceDepth_le_succ n
  have hX1 := one_le_succ_pow n 2
  have hxX := succ_le_succ_pow n 2 (by norm_num)
  have h1 := Nat.mul_le_mul_left edgePer hE
  have hnX : n ≤ (n + 1) ^ 2 := by omega
  have h2 := Nat.mul_le_mul_left edgeCard (Nat.add_le_add hnX h1)
  have h3 := Nat.mul_le_mul_left edgeCard hX1
  unfold depthBound depthBoundC
  generalize (n + 1) ^ 2 = X at *
  generalize edgeBound n = D at *
  generalize EffectiveIteration.sourceDepth n = B at *
  generalize edgeCard = eC at *
  generalize edgePer = eP at *
  generalize edgeBoundC = EB at *
  nlinarith

def logBoundC : ℕ := 258 + 16641 * (UnaryBinaryEncoding.coefficient + 6)

theorem logBound_le (n : ℕ) :
    logBound (64 * (1 + EffectiveIteration.sourceDepth n)) ≤ logBoundC * (n + 1) ^ 2 := by
  have hb := sourceDepth_le_succ n
  have hm : 64 * (1 + EffectiveIteration.sourceDepth n) + 1 ≤ 129 * (n + 1) := by omega
  have hsq := Nat.pow_le_pow_left hm 2
  have hsq' : (129 * (n + 1)) ^ 2 = 16641 * (n + 1) ^ 2 := by ring
  rw [hsq'] at hsq
  have hU := Nat.mul_le_mul_left (UnaryBinaryEncoding.coefficient + 6) hsq
  have hX1 := one_le_succ_pow n 2
  have hxX := succ_le_succ_pow n 2 (by norm_num)
  unfold logBound logBoundC
  generalize (64 * (1 + EffectiveIteration.sourceDepth n) + 1) ^ 2 = Q at *
  generalize (n + 1) ^ 2 = X at *
  generalize EffectiveIteration.sourceDepth n = B at *
  generalize UnaryBinaryEncoding.coefficient = U at *
  nlinarith

def logStageC : ℕ := logBoundC + 518 + 129 * logCard + logCard * logPer * logBoundC

theorem logStageBound_le (n : ℕ) :
    logStageBound (64 * (1 + EffectiveIteration.sourceDepth n)) ≤ logStageC * (n + 1) ^ 2 := by
  have hL := logBound_le n
  have hb := sourceDepth_le_succ n
  have he := costExp_lt (EffectiveIteration.sourceDepth n)
  have hX1 := one_le_succ_pow n 2
  have hxX := succ_le_succ_pow n 2 (by norm_num)
  have hm : 64 * (1 + EffectiveIteration.sourceDepth n) ≤ 128 * (n + 1) ^ 2 := by omega
  have h1 := Nat.mul_le_mul_left logPer hL
  have h2 := Nat.mul_le_mul_left logCard (Nat.add_le_add hm h1)
  have h3 := Nat.mul_le_mul_left logCard hX1
  unfold logStageBound logStageC
  unfold costExp at he
  generalize (n + 1) ^ 2 = X at *
  generalize logBound (64 * (1 + EffectiveIteration.sourceDepth n)) = D at *
  generalize Nat.clog 2 (64 * (1 + EffectiveIteration.sourceDepth n)) = e at *
  generalize EffectiveIteration.sourceDepth n = B at *
  generalize logCard = lC at *
  generalize logPer = lP at *
  generalize logBoundC = LB at *
  nlinarith

def costC : ℕ := logStageC + 6000

theorem costBound_le (n : ℕ) :
    costBound (EffectiveIteration.sourceDepth n) ≤
      costC * (n + 1) ^ 2 + 4 * rowC * (n + 1) ^ 128 := by
  have hS := logStageBound_le n
  have hb := sourceDepth_le_succ n
  have hw := two_pow_costExp_lt (EffectiveIteration.sourceDepth n)
  have he := costExp_lt (EffectiveIteration.sourceDepth n)
  have hD := double_pow_le n
  have hX1 := one_le_succ_pow n 2
  have hxX := succ_le_succ_pow n 2 (by norm_num)
  unfold costBound MatrixAddressMachine.exactTime costC
  generalize (n + 1) ^ 128 = Y at *
  generalize (n + 1) ^ 2 = X at *
  generalize logStageBound (64 * (1 + EffectiveIteration.sourceDepth n)) = S at *
  generalize 2 ^ 2 ^ costExp (EffectiveIteration.sourceDepth n) = D at *
  generalize 2 ^ costExp (EffectiveIteration.sourceDepth n) = W at *
  generalize costExp (EffectiveIteration.sourceDepth n) = e at *
  generalize EffectiveIteration.sourceDepth n = B at *
  generalize logStageC = LS at *
  generalize rowC = R at *
  nlinarith

/-- Explicit level-0 coefficient; exponent 128. -/
def level0C : ℕ := depthBoundC + costC + 1 + 4 * rowC

theorem level0Bound_le (n : ℕ) : level0Bound n ≤ level0C * (n + 1) ^ 128 := by
  have hD := depthBound_le n
  have hC := costBound_le n
  have hXY : (n + 1) ^ 2 ≤ (n + 1) ^ 128 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hY1 := one_le_succ_pow n 128
  have h1 := Nat.mul_le_mul_left depthBoundC hXY
  have h2 := Nat.mul_le_mul_left costC hXY
  unfold level0Bound level0C
  generalize (n + 1) ^ 128 = Y at *
  generalize (n + 1) ^ 2 = X at *
  generalize depthBound n = A at *
  generalize costBound (EffectiveIteration.sourceDepth n) = C at *
  generalize depthBoundC = a at *
  generalize costC = b at *
  generalize rowC = R at *
  nlinarith

#print axioms level0Bound_le

/-! ## S3: the edge word -/

theorem endpointStream_le (g : EncodedGraph.Graph) (hg : g.Valid) :
    (SourceNormalizationMachineDecode.endpointStream g).length ≤
      g.edges.length * (2 * g.vertices + 2) := by
  have he : ∀ p ∈ g.edges, p.1 ≤ g.vertices ∧ p.2 ≤ g.vertices := by
    intro p hp
    obtain ⟨h₁, h₂, _⟩ := hg p hp
    exact ⟨by omega, by omega⟩
  simpa only [SourceNormalizationMachineDecode.endpointStream,
    SourceNormalizationMachineDecode.edgeStream] using
    SourceNormalizationMachineDecode.edgeStream_length_bound g.vertices g.edges he

theorem edgesBound_le (g : EncodedGraph.Graph) (hg : g.Valid) :
    edgesBound g ≤ 120 * ((EncodedGraph.encode g).length + 1) ^ 3 := by
  have hs := endpointStream_le g hg
  have hn := EncodedGraph.encode_length_lower g
  set N := (EncodedGraph.encode g).length with hN
  have hv : g.vertices ≤ N := by omega
  have hm : g.edges.length ≤ N := by omega
  have hmul : g.edges.length * (2 * g.vertices + 2) ≤ N * (2 * N + 2) :=
    Nat.mul_le_mul hm (by omega)
  have hZ : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hZ1 := one_le_succ_pow N 3
  have hxZ := succ_le_succ_pow N 3 (by norm_num)
  have hsq : N * (2 * N + 2) ≤ 2 * (N + 1) ^ 2 := by nlinarith
  unfold edgesBound
  rw [← hN]
  generalize (N + 1) ^ 3 = Z at *
  generalize (N + 1) ^ 2 = X at *
  generalize (SourceNormalizationMachineDecode.endpointStream g).length = S at *
  generalize g.edges.length = E at *
  generalize g.vertices = V at *
  generalize N * (2 * N + 2) = P at *
  omega

theorem edgesBound_serialize_le {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : ParameterizedNP.GuardedSourceGraph.EndpointGraph V E) :
    edgesBound (EncodedETHSource.serializeGraph G) ≤
      120 * ((EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length + 1) ^ 3 :=
  edgesBound_le _ (EncodedETHSource.serializeGraph_valid G)

#print axioms edgesBound_le
#print axioms edgesBound_serialize_le

/-! ## S5: the k fuel -/

theorem bits_length_le (k : ℕ) : (Nat.bits k).length ≤ k := by
  rw [Nat.size_eq_bits_len, Nat.size_le]
  exact Nat.lt_two_pow_self

/-- The fuel clock is `O(k + |Nat.bits k|)`, exactly. -/
theorem fuelBound_eq (k : ℕ) :
    fuelBound k = 4 * k + 4 * (Nat.bits k).length + 4 := by
  unfold fuelBound
  omega

theorem fuelBound_le (k : ℕ) : fuelBound k ≤ 8 * k + 4 := by
  have := bits_length_le k
  rw [fuelBound_eq]
  omega

theorem kValue_le (M : BitMachine.Machine) (n : ℕ) : kValue M n ≤ n :=
  SlowClock.repetitions_le _ n

theorem output_length_le (M : BitMachine.Machine) (n : ℕ) :
    (ClockRuntime.output M (List.replicate n true)).length ≤
      4 * n + ClockStepEncoded.width M + 2 := by
  have h := ClockRuntime.packetAt_length M (List.replicate n true) n (by simp)
  simpa [ClockRuntime.output, ClockRuntime.lengthBound] using h

/-- Explicit coefficient of the cubic part of the k clock. -/
def kPolyC (M : BitMachine.Machine) : ℕ :=
  ClockRuntime.timeCoefficient M +
    (Drv M).stackCount * BitMachineStackGrowth.perStep (Drv M).program *
      ClockRuntime.timeCoefficient M +
    2 * (Drv M).stackCount + 3 * ClockStepEncoded.width M ^ 2 +
    30 * ClockStepEncoded.width M + 60

theorem kArith (n w s p T P t F Z : ℕ) (hP : P ≤ 4 * n + w + 2) (hT : t ≤ T * Z)
    (hZ1 : 1 ≤ Z) (hnZ : n + 1 ≤ Z) :
    (2 * n + 2) + (t + ((2 * P + 2) + ((s * (n + p * t) + s + 2) +
      (((2 * w + 3) * (P + 1) + 1) + ((w * P + w + 2) + F + 1) + 1) + 1) + 1) + 1) + 1 ≤
      (T + s * p * T + 2 * s + 3 * w ^ 2 + 30 * w + 60) * Z + F := by
  have hn : n ≤ Z := by omega
  have a1 := Nat.mul_le_mul_left w hP
  have a2 := Nat.mul_le_mul_left (2 * w + 3) (Nat.add_le_add_right hP 1)
  have a3 := Nat.mul_le_mul_left s (Nat.add_le_add hn (Nat.mul_le_mul_left p hT))
  have a4 := Nat.mul_le_mul_left w hn
  have a5 := Nat.mul_le_mul_left (w * w) hZ1
  have a6 := Nat.mul_le_mul_left s hZ1
  have a7 := Nat.mul_le_mul_left w hZ1
  nlinarith

theorem kBound_le_fuel (M : BitMachine.Machine) (n : ℕ) :
    kBound M n ≤ kPolyC M * (n + 1) ^ 3 + fuelBound (kValue M n) := by
  have h := kArith n (ClockStepEncoded.width M) (Drv M).stackCount
    (BitMachineStackGrowth.perStep (Drv M).program) (ClockRuntime.timeCoefficient M)
    (ClockRuntime.output M (List.replicate n true)).length (ClockRuntime.time M n)
    (fuelBound (kValue M n)) ((n + 1) ^ 3) (output_length_le M n)
    (ClockRuntime.time_polynomial M n) (one_le_succ_pow n 3) (succ_le_succ_pow n 3 (by norm_num))
  unfold kBound kPolyC
  exact h

theorem kBound_le (M : BitMachine.Machine) (n : ℕ) :
    kBound M n ≤ kPolyC M * (n + 1) ^ 3 + (8 * n + 4) := by
  have h1 := kBound_le_fuel M n
  have h2 := fuelBound_le (kValue M n)
  have h3 := kValue_le M n
  omega

#print axioms fuelBound_eq
#print axioms kBound_le_fuel
#print axioms kBound_le

/-! ## The whole clock -/

/-- Explicit coefficient of the whole level-0 clock; exponent 128. -/
def rawC (M : BitMachine.Machine) (c : ℕ) : ℕ := level0C + kPolyC M + 3 * c + 200

theorem rawWordsKBound_le (M : BitMachine.Machine) (n c : ℕ) (g : EncodedGraph.Graph)
    (hg : g.Valid) :
    rawWordsKBound M n c (EncodedGraph.encode g).length g ≤
      rawC M c * (n + (EncodedGraph.encode g).length + 1) ^ 128 := by
  set N := (EncodedGraph.encode g).length with hN
  have hL := level0Bound_le n
  have hE := edgesBound_le g hg
  have hK := kBound_le M n
  have hpk := SourceOriginalBranchPackets.packet_length n (EncodedGraph.encode g)
  rw [← hN] at hE hpk
  have hY1 : 1 ≤ (n + N + 1) ^ 128 := Nat.one_le_pow _ _ (by omega)
  have hxY : n + N + 1 ≤ (n + N + 1) ^ 128 := by
    calc n + N + 1 = (n + N + 1) ^ 1 := (pow_one _).symm
      _ ≤ (n + N + 1) ^ 128 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hA : (n + 1) ^ 128 ≤ (n + N + 1) ^ 128 := Nat.pow_le_pow_left (by omega) 128
  have hB : (N + 1) ^ 3 ≤ (n + N + 1) ^ 128 :=
    le_trans (Nat.pow_le_pow_left (by omega) 3) (Nat.pow_le_pow_right (by omega) (by norm_num))
  have hC : (n + 1) ^ 3 ≤ (n + N + 1) ^ 128 :=
    le_trans (Nat.pow_le_pow_left (by omega) 3) (Nat.pow_le_pow_right (by omega) (by norm_num))
  have b1 := Nat.mul_le_mul_left level0C hA
  have b2 := Nat.mul_le_mul_left 120 hB
  have b3 := Nat.mul_le_mul_left (kPolyC M) hC
  have b4 := Nat.mul_le_mul_left c hY1
  unfold rawWordsKBound rawC
  rw [hpk]
  generalize (n + N + 1) ^ 128 = Y at *
  generalize (n + 1) ^ 128 = Y1 at *
  generalize (N + 1) ^ 3 = Z at *
  generalize (n + 1) ^ 3 = Z1 at *
  generalize level0Bound n = L at *
  generalize edgesBound g = Ed at *
  generalize kBound M n = K at *
  generalize level0C = l at *
  generalize kPolyC M = k at *
  nlinarith

theorem rawWordsKBound_serialize_le (M : BitMachine.Machine) (n c : ℕ) {V E : Type*}
    [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : ParameterizedNP.GuardedSourceGraph.EndpointGraph V E) :
    rawWordsKBound M n c (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length
        (EncodedETHSource.serializeGraph G) ≤
      rawC M c * (n + (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length + 1) ^ 128 :=
  rawWordsKBound_le M n c _ (EncodedETHSource.serializeGraph_valid G)

#print axioms rawWordsKBound_le

/-! ## The headline with the public polynomial clock -/

/-- The frozen headline `level0_handoff_k`, with the clock replaced by the
explicit polynomial `rawC M c * (n + |encode (serializeGraph G)| + 1)^128`. -/
theorem level0_handoff_k_poly (M : BitMachine.Machine) {V E : Type} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (G : ParameterizedNP.GuardedSourceGraph.EndpointGraph V E) (n c : ℕ) :
    ∃ t ≤ rawC M c * (n + (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length + 1) ^ 128,
      ((advance (rawWordsKProgram M c))^[t])
        (unpackStart c (SourceOriginalBranchPackets.packet n
          (EncodedGraph.encode (EncodedETHSource.serializeGraph G)))
          ((level0Ctrl, (edgesCtrl, tailCtrl)), kCtrl M)) =
        ⟨none, (none, ((), ((level0Ctrl, (edgesCtrl, tailCtrl)), kCtrl M))),
          Sum.elim
            (WeightedRawRowsSource.initialBank
              (EffectiveIteration.runParameters G c (EffectiveIteration.sourceDepth n)
                (Iteration.seedState (EffectiveIteration.sourceDepth n)) 0)
              (EncodedETHSource.serializeGraph G) noW)
            (Function.update
              (masterBank n (EncodedGraph.encode (EncodedETHSource.serializeGraph G)) c
                (EffectiveIteration.sourceDepth n)
                (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget
                (Fintype.card E))
              Aux.K (List.replicate (kValue M n) true))⟩ := by
  obtain ⟨t, ht, h⟩ := level0_handoff_k M G n c
  exact ⟨t, le_trans ht (rawWordsKBound_serialize_le M n c G), h⟩

/-- The same clock in the input length: the input is the packet, of length
`2(n + |encode (serializeGraph G)|) + 2`. -/
theorem level0_handoff_k_input_poly (M : BitMachine.Machine) {V E : Type} [Fintype V]
    [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : ParameterizedNP.GuardedSourceGraph.EndpointGraph V E) (n c : ℕ) :
    ∃ t ≤ rawC M c * ((SourceOriginalBranchPackets.packet n
          (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ 128,
      ((advance (rawWordsKProgram M c))^[t])
        (unpackStart c (SourceOriginalBranchPackets.packet n
          (EncodedGraph.encode (EncodedETHSource.serializeGraph G)))
          ((level0Ctrl, (edgesCtrl, tailCtrl)), kCtrl M)) =
        ⟨none, (none, ((), ((level0Ctrl, (edgesCtrl, tailCtrl)), kCtrl M))),
          Sum.elim
            (WeightedRawRowsSource.initialBank
              (EffectiveIteration.runParameters G c (EffectiveIteration.sourceDepth n)
                (Iteration.seedState (EffectiveIteration.sourceDepth n)) 0)
              (EncodedETHSource.serializeGraph G) noW)
            (Function.update
              (masterBank n (EncodedGraph.encode (EncodedETHSource.serializeGraph G)) c
                (EffectiveIteration.sourceDepth n)
                (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget
                (Fintype.card E))
              Aux.K (List.replicate (kValue M n) true))⟩ := by
  obtain ⟨t, ht, h⟩ := level0_handoff_k_poly M G n c
  refine ⟨t, le_trans ht (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ 128)), h⟩
  rw [SourceOriginalBranchPackets.packet_length]
  omega

/-- The paper's source machine: for `M = CutoffBitMachine.actualMachine c A d`
the same fixed program halts within `rawC M c * (n + |enc G| + 1)^128`;
`k = SlowClock.repetitions (actualClock c A d) n`. -/
theorem level0_handoff_actual_poly (c A d : ℕ) {V E : Type} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (G : ParameterizedNP.GuardedSourceGraph.EndpointGraph V E) (n : ℕ) :
    ∃ t ≤ rawC (CutoffBitMachine.actualMachine c A d) c *
        (n + (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length + 1) ^ 128,
      ((advance (rawWordsKProgram (CutoffBitMachine.actualMachine c A d) c))^[t])
        (unpackStart c (SourceOriginalBranchPackets.packet n
          (EncodedGraph.encode (EncodedETHSource.serializeGraph G)))
          ((level0Ctrl, (edgesCtrl, tailCtrl)), kCtrl (CutoffBitMachine.actualMachine c A d))) =
        ⟨none, (none, ((), ((level0Ctrl, (edgesCtrl, tailCtrl)),
            kCtrl (CutoffBitMachine.actualMachine c A d)))),
          Sum.elim
            (WeightedRawRowsSource.initialBank
              (EffectiveIteration.runParameters G c (EffectiveIteration.sourceDepth n)
                (Iteration.seedState (EffectiveIteration.sourceDepth n)) 0)
              (EncodedETHSource.serializeGraph G) noW)
            (Function.update
              (masterBank n (EncodedGraph.encode (EncodedETHSource.serializeGraph G)) c
                (EffectiveIteration.sourceDepth n)
                (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget
                (Fintype.card E))
              Aux.K (List.replicate
                (SlowClock.repetitions (CutoffBitMachine.actualClock c A d) n) true))⟩ :=
  level0_handoff_k_poly (CutoffBitMachine.actualMachine c A d) G n c

#print axioms level0_handoff_k_poly
#print axioms level0_handoff_k_input_poly
#print axioms level0_handoff_actual_poly
#print axioms double_pow_le
#print axioms edgeBound_le
#print axioms depthBound_le
#print axioms logBound_le
#print axioms logStageBound_le
#print axioms costBound_le
#print axioms fuelBound_le
#print axioms kArith
#print axioms output_length_le
#print axioms kValue_le

end
end EthInapproximability.CurrentPaper.WeightedRawWordsClock
