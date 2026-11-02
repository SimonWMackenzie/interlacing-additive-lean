import EthInapproximability.CurrentPaper.EntryClockPolyVec

/-!
# Segment 3: ONE public clock for the level-0 writer-22 program

Lane owner:b-entry-clock-2 (Paper B, unit 2, CP-EFFECTIVE). Pure arithmetic; no machine.

`writer22_clock_le`: there is an absolute `C` such that for every graph `G`, every `n c`,
every naming bound `p` with `EffectiveIteration.oneLevelBound (P0 G n c) ≤ p`, and every
`Family4Spec` clock `T`, the literal clock of the admitted
`EntryPrepVec.level0_writer22_of_family4` is at most
`(n + |enc G| + 1)^C + 2^(C * p) + T`, where `|enc G|` is the literal length of
`EncodedGraph.encode (EncodedETHSource.serializeGraph G)`.

`level0_writer22_clock`: the admitted `OuterLevel0Full.Writer22Spec` of the SAME program
(literally the one of `level0_writer22_of_family4`) holds with the clock
`(n + |enc G| + 1)^C + 2^(C p) + T`; and `level0_writer22_clock_poly` with
`(n+|enc G|+1)^C' + 2^(C' p)` under the stated polynomial premise
`T ≤ (n+|enc G|+1)^C0 + 2^(C0 p)` (`C' = max C C0 + 1`).
-/

namespace EthInapproximability.CurrentPaper.EntryClockPoly

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open EthInapproximability.ParameterizedNP.GuardedSourceSlab
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Ready OuterLevel0Prep
open EntryPrepBudget EntryTailEmbed EntryTailClear EntryPrepCopy EntryPrepVec
open Construction MatrixStage4Codes MatrixStage4Digits MatrixMaterialization

/-! ## Absorbing a uniform polynomial into `X^C + 2^(C p)` -/

theorem mul_le_sq_add (x y : ℕ) : x * y ≤ x ^ 2 + y ^ 2 := by
  rcases le_total x y with h | h
  · have := Nat.mul_le_mul_right y h
    nlinarith
  · have := Nat.mul_le_mul_left x h
    nlinarith

theorem absorb (K D a b X p Y : ℕ) (hX : 2 ≤ X) (hp : 1 ≤ p)
    (hY : Y ≤ 2 ^ (a * p) * X ^ b) :
    K * (Y + 1) ^ D ≤ X ^ (K + 2 * b * D) + 2 ^ ((K + 2 * (a + 1) * D) * p) := by
  have hZ : 1 ≤ 2 ^ (a * p) * X ^ b :=
    Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by omega))
  have h2p : 2 ≤ 2 ^ p := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by decide) hp
  have hA : Y + 1 ≤ 2 ^ ((a + 1) * p) * X ^ b := by
    have e : 2 ^ ((a + 1) * p) * X ^ b = 2 ^ p * (2 ^ (a * p) * X ^ b) := by
      rw [show (a + 1) * p = a * p + p by ring, pow_add]; ring
    rw [e]
    nlinarith
  have hpow : (Y + 1) ^ D ≤ (2 ^ ((a + 1) * p)) ^ D * (X ^ b) ^ D := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left hA _
  have hsq := mul_le_sq_add ((2 ^ ((a + 1) * p)) ^ D) ((X ^ b) ^ D)
  have hK1 : K ≤ 2 ^ (K * p) :=
    (Nat.le_of_lt Nat.lt_two_pow_self).trans (Nat.pow_le_pow_right (by decide) (by nlinarith))
  have hK2 : K ≤ X ^ K :=
    (Nat.le_of_lt Nat.lt_two_pow_self).trans (Nat.pow_le_pow_left hX _)
  have e1 : ((2 ^ ((a + 1) * p)) ^ D) ^ 2 = 2 ^ (2 * (a + 1) * D * p) := by
    rw [← pow_mul, ← pow_mul]; congr 1; ring
  have e2 : ((X ^ b) ^ D) ^ 2 = X ^ (2 * b * D) := by
    rw [← pow_mul, ← pow_mul]; congr 1; ring
  rw [e1, e2] at hsq
  have f1 : K * 2 ^ (2 * (a + 1) * D * p) ≤ 2 ^ ((K + 2 * (a + 1) * D) * p) := by
    calc K * 2 ^ (2 * (a + 1) * D * p) ≤ 2 ^ (K * p) * 2 ^ (2 * (a + 1) * D * p) :=
          Nat.mul_le_mul_right _ hK1
      _ = 2 ^ ((K + 2 * (a + 1) * D) * p) := by rw [← pow_add]; congr 1; ring
  have f2 : K * X ^ (2 * b * D) ≤ X ^ (K + 2 * b * D) := by
    calc K * X ^ (2 * b * D) ≤ X ^ K * X ^ (2 * b * D) := Nat.mul_le_mul_right _ hK2
      _ = X ^ (K + 2 * b * D) := by rw [← pow_add]
  calc K * (Y + 1) ^ D ≤ K * (2 ^ (2 * (a + 1) * D * p) + X ^ (2 * b * D)) :=
        Nat.mul_le_mul_left _ (hpow.trans hsq)
    _ = K * 2 ^ (2 * (a + 1) * D * p) + K * X ^ (2 * b * D) := by ring
    _ ≤ _ := by omega

/-! ## Level-0 smallness in the naming bound -/

section level

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem level0_small (G : EndpointGraph V E) (n c p : ℕ)
    (hname : EffectiveIteration.oneLevelBound (P0 G n c) ≤ p) :
    128 ≤ p ∧ (inst0 G n c).s ≤ p ∧ (inst0 G n c).q ≤ 2 ^ p := by
  rw [oneLevel_eq] at hname
  obtain ⟨h128, _, _, hs, _, hq2, _⟩ := EffectiveIteration.parameter_size_bounds (P0 G n c)
  generalize hT : Parameters.balanceOrder (P0 G n c) = T at hname h128 hs hq2
  have hT1 : 1 ≤ T := by omega
  have hT14 : T ≤ T ^ 4 := by
    calc T = T ^ 1 := (pow_one T).symm
      _ ≤ T ^ 4 := Nat.pow_le_pow_right hT1 (by decide)
  refine ⟨by omega, by rw [inst0_s]; omega, ?_⟩
  rw [inst0_q]
  exact Nat.pow_le_pow_right (by decide) (by omega)

theorem ell_two (G : EndpointGraph V E) : 2 ≤ ellG G := by
  have := card_le_ell G; omega

/-- The instance size in the product shape `2^(6p) * X`. -/
theorem U_prod (G : EndpointGraph V E) (n c p : ℕ)
    (hname : EffectiveIteration.oneLevelBound (P0 G n c) ≤ p) :
    (inst0 G n c).U ≤ 2 ^ (6 * p) * (n + ellG G + 1) := by
  have hU := U_inst0_le G n c p hname
  obtain ⟨hp, _, _⟩ := level0_small G n c p hname
  have hV : Fintype.card V ≤ n + ellG G + 1 := by have := card_le_ell G; omega
  have hpp : p ≤ 2 ^ p := Nat.le_of_lt Nat.lt_two_pow_self
  have hp2 : p ^ 2 ≤ 2 ^ (2 * p) := by
    rw [pow_mul', sq]; nlinarith
  have hpX : p * Fintype.card V ≤ 2 ^ p * (n + ellG G + 1) := Nat.mul_le_mul hpp hV
  have e2 : 2 ^ (2 * p) = 2 ^ p * 2 ^ p := by rw [two_mul, pow_add]
  have e6 : 2 ^ (6 * p) = 2 ^ (2 * p) * 2 ^ (4 * p) := by rw [← pow_add]; congr 1; ring
  have h16 : 16 ≤ 2 ^ (4 * p) := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (4 * p) := Nat.pow_le_pow_right (by decide) (by omega)
  have h1p : 1 ≤ 2 ^ p := Nat.one_le_two_pow
  have hX : 1 ≤ n + ellG G + 1 := by omega
  -- 3*2^p + 2p + 4p^2 + 4 p |V| ≤ 13 * 2^(2p) * X ≤ 2^(6p) * X
  have hsum : 3 * 2 ^ p + 2 * p + 4 * p ^ 2 + 4 * p * Fintype.card V ≤
      13 * (2 ^ (2 * p) * (n + ellG G + 1)) := by
    have a1 : 2 ^ p ≤ 2 ^ (2 * p) * (n + ellG G + 1) := by
      rw [e2]; nlinarith
    have a2 : p ^ 2 ≤ 2 ^ (2 * p) * (n + ellG G + 1) :=
      hp2.trans (Nat.le_mul_of_pos_right _ hX)
    have a3 : 2 ^ p * (n + ellG G + 1) ≤ 2 ^ (2 * p) * (n + ellG G + 1) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by omega))
    have a4 : 4 * p * Fintype.card V = 4 * (p * Fintype.card V) := by ring
    omega
  calc (inst0 G n c).U ≤ 13 * (2 ^ (2 * p) * (n + ellG G + 1)) := hU.trans hsum
    _ ≤ 2 ^ (4 * p) * (2 ^ (2 * p) * (n + ellG G + 1)) := Nat.mul_le_mul_right _ (by omega)
    _ = 2 ^ (6 * p) * (n + ellG G + 1) := by rw [e6]; ring

/-- The graph-piece size in the product shape `2^(4p) * X^2`. -/
theorem UG_prod (G : EndpointGraph V E) (n c p : ℕ)
    (hname : EffectiveIteration.oneLevelBound (P0 G n c) ≤ p) :
    UG ⟨V, E, G, EntryPrepVec.sv G n c⟩ ≤ 2 ^ (4 * p) * (n + ellG G + 1) ^ 2 := by
  obtain ⟨hp, hs, hq⟩ := level0_small G n c p hname
  have hstr := stream_le G
  have hX : 2 ≤ n + ellG G + 1 := by have := ell_two G; omega
  have hpp : p ≤ 2 ^ p := Nat.le_of_lt Nat.lt_two_pow_self
  have h16 : 16 ≤ 2 ^ (3 * p) := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (3 * p) := Nat.pow_le_pow_right (by decide) (by omega)
  have e4 : 2 ^ (4 * p) = 2 ^ p * 2 ^ (3 * p) := by rw [← pow_add]; congr 1; ring
  have h1 : 1 ≤ 2 ^ p := Nat.one_le_two_pow
  unfold UG
  dsimp only
  have hs' : EntryPrepVec.sv G n c ≤ p := hs
  have hq' : q2 G (EntryPrepVec.sv G n c) ≤ 2 ^ p := hq
  generalize hXd : n + ellG G + 1 = X at hX ⊢
  have hℓ : ellG G ≤ X := by omega
  have hstr' : strG G ≤ X * (2 * X + 2) :=
    hstr.trans (Nat.mul_le_mul hℓ (by omega))
  have hX2 : X * (2 * X + 2) ≤ 3 * X ^ 2 := by nlinarith
  have hXX : X ≤ X ^ 2 := by nlinarith
  have hsum : EntryPrepVec.sv G n c + ellG G + q2 G (EntryPrepVec.sv G n c) + strG G ≤
      6 * (2 ^ p * X ^ 2) := by
    have b1 : 2 ^ p ≤ 2 ^ p * X ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
    have b2 : X ^ 2 ≤ 2 ^ p * X ^ 2 := Nat.le_mul_of_pos_left _ (by positivity)
    omega
  calc _ ≤ 6 * (2 ^ p * X ^ 2) := hsum
    _ ≤ 2 ^ (3 * p) * (2 ^ p * X ^ 2) := Nat.mul_le_mul_right _ (by omega)
    _ = 2 ^ (4 * p) * X ^ 2 := by rw [e4]; ring

/-- The seed-table clock (admitted `EntryPrepPoly.seed_bound_poly'`) in the shape `X^1027`. -/
theorem seed_le (n ℓ : ℕ) (hX : 2 ≤ n + ℓ + 1) :
    SeedTable.bound (IndexSeed.width (EffectiveIteration.sourceDepth n)) ≤ (n + ℓ + 1) ^ 1027 := by
  refine (EntryPrepPoly.seed_bound_poly' n ℓ).trans ?_
  generalize n + ℓ + 1 = X at hX ⊢
  have h4 : 4 * X ≤ X ^ 3 := by
    have h4' : 4 ≤ X * X := Nat.mul_le_mul hX hX
    calc 4 * X ≤ X * X * X := Nat.mul_le_mul_right _ h4'
      _ = X ^ 3 := by ring
  have h2 : 2 ^ 128 ≤ X ^ 128 := Nat.pow_le_pow_left hX _
  have h7 : 7 ≤ X ^ 3 := by omega
  calc 7 * ((4 * X) ^ 128 * 2 ^ 128) ^ 2 ≤ X ^ 3 * ((X ^ 3) ^ 128 * X ^ 128) ^ 2 :=
        Nat.mul_le_mul h7 (Nat.pow_le_pow_left (Nat.mul_le_mul (Nat.pow_le_pow_left h4 _) h2) _)
    _ = X ^ 1027 := by rw [← pow_mul, ← pow_add, ← pow_mul, ← pow_add]

/-- The literal level-0 writer-22 clock splits into the seed clock, the instance pieces,
the vectors clock and `T`. -/
theorem clock_split (G : EndpointGraph V E) (n c T : ℕ) :
    SeedTable.bound (IndexSeed.width (EffectiveIteration.sourceDepth n)) +
        (EntryPrepVec.prepBound G n c (EntryPrepVec.labBound G n c T) +
          (EntryTailClear.tailBound G n c + EntryTailClear.clearBound G n c + 1) + 1) + 1 =
      SeedTable.bound (IndexSeed.width (EffectiveIteration.sourceDepth n)) +
        restI (inst0 G n c) + EntryPrepVec.boundV G n c + T + 7 := by
  have h1 := boundA_eq G n c
  have h2 := labBound_eq G n c T
  have h3 := wordB_eq G n c
  have h4 := clearBound_eq G n c
  have h5 : EntryTailClear.tailBound G n c = writerI (inst0 G n c) := tailBound_eq G n c
  unfold EntryPrepVec.prepBound restI
  omega

end level

/-! ## Segment 3 -/

/-- ONE public clock: absolute `C`, uniform over graphs, `n`, `c`, `p` and `T`. -/
theorem writer22_clock_le : ∃ C : ℕ, ∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : EndpointGraph V E) (n c p T : ℕ),
    EffectiveIteration.oneLevelBound (P0 G n c) ≤ p →
    SeedTable.bound (IndexSeed.width (EffectiveIteration.sourceDepth n)) +
        (EntryPrepVec.prepBound G n c (EntryPrepVec.labBound G n c T) +
          (EntryTailClear.tailBound G n c + EntryTailClear.clearBound G n c + 1) + 1) + 1 ≤
      (n + ellG G + 1) ^ C + 2 ^ (C * p) + T := by
  obtain ⟨K1, D1, h1⟩ := restI_poly
  obtain ⟨K2, D2, h2⟩ := bvG_poly
  let C1 := K1 + 2 * 1 * D1
  let C1' := K1 + 2 * (6 + 1) * D1
  let C2 := K2 + 2 * 2 * D2
  let C2' := K2 + 2 * (4 + 1) * D2
  let M := C1 + C1' + C2 + C2' + 1027
  refine ⟨M + 4, ?_⟩
  intro V E _ _ _ _ G n c p T hname
  obtain ⟨hp, _, _⟩ := level0_small G n c p hname
  have hX : 2 ≤ n + ellG G + 1 := by have := ell_two G; omega
  have hp1 : 1 ≤ p := by omega
  rw [clock_split]
  -- the three pieces
  have hr : restI (inst0 G n c) ≤ (n + ellG G + 1) ^ C1 + 2 ^ (C1' * p) := by
    refine (h1 ⟨inst0 G n c, inst0_pos G n c⟩).trans ?_
    have := absorb K1 D1 6 1 (n + ellG G + 1) p (inst0 G n c).U hX hp1
      (by simpa using U_prod G n c p hname)
    simpa using this
  have hv : EntryPrepVec.boundV G n c ≤ (n + ellG G + 1) ^ C2 + 2 ^ (C2' * p) := by
    refine (boundV_le G n c).trans ((h2 _).trans ?_)
    exact absorb K2 D2 4 2 (n + ellG G + 1) p _ hX hp1 (UG_prod G n c p hname)
  have hs := seed_le n (ellG G) hX
  generalize n + ellG G + 1 = X at hX hr hv hs ⊢
  -- collect
  have hX1 : 1 ≤ X := by omega
  have m1 : X ^ C1 ≤ X ^ M := Nat.pow_le_pow_right hX1 (by omega)
  have m2 : X ^ C2 ≤ X ^ M := Nat.pow_le_pow_right hX1 (by omega)
  have m3 : X ^ 1027 ≤ X ^ M := Nat.pow_le_pow_right hX1 (by omega)
  have q1 : 2 ^ (C1' * p) ≤ 2 ^ (M * p) :=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega))
  have q2' : 2 ^ (C2' * p) ≤ 2 ^ (M * p) :=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega))
  have x16 : 16 ≤ X ^ 4 := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ X ^ 4 := Nat.pow_le_pow_left hX _
  have eX : X ^ (M + 4) = X ^ M * X ^ 4 := pow_add _ _ _
  have e2 : 2 ^ ((M + 4) * p) = 2 ^ (M * p) * 2 ^ (4 * p) := by
    rw [← pow_add]; congr 1; ring
  have t16 : 16 ≤ 2 ^ (4 * p) := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (4 * p) := Nat.pow_le_pow_right (by decide) (by omega)
  have hXM : 1 ≤ X ^ M := Nat.one_le_pow _ _ (by omega)
  have g1 : 16 * X ^ M ≤ X ^ M * X ^ 4 := by rw [mul_comm]; exact Nat.mul_le_mul_left _ x16
  have g2 : 16 * 2 ^ (M * p) ≤ 2 ^ (M * p) * 2 ^ (4 * p) := by
    rw [mul_comm]; exact Nat.mul_le_mul_left _ t16
  rw [eX, e2]
  omega

variable (Mm : BitMachine.Machine)

theorem writer22Spec_mono {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    {LW VW : Type} (W : LW → TM2.Stmt (fun _ : HStack => Bool) LW VW) (w₀ : LW) (v₀ : VW)
    {T T' : ℕ} (G : EndpointGraph V E) (n c : ℕ) (hle : T ≤ T')
    (h : OuterLevel0Full.Writer22Spec Mm W w₀ v₀ T G n c) :
    OuterLevel0Full.Writer22Spec Mm W w₀ v₀ T' G n c := by
  intro F Q P hf
  obtain ⟨t, ht, v₁, hrun⟩ := h F Q P hf
  exact ⟨t, ht.trans hle, v₁, hrun⟩

/-- The admitted level-0 writer-22 program, with ONE public clock. -/
theorem level0_writer22_clock : ∃ C : ℕ, ∀ {V E : Type} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : EndpointGraph V E) (n c p : ℕ) {LW VW : Type}
    (W : LW → TM2.Stmt (fun _ : HStack => Bool) LW VW) (w₀ : LW) (v₀ : VW) (T : ℕ),
    EffectiveIteration.oneLevelBound (P0 G n c) ≤ p →
    Family4Spec Mm W w₀ v₀ T G n c →
    OuterLevel0Full.Writer22Spec Mm
      (BitMachineRawSequence.program EntrySeedSpec.seedProgram
        (BitMachineRawSequence.program (prepProg4 W w₀ v₀) tailClear
          (BitMachineRawSequence.leftLabel RawTableTail.startLabel)
          (prepInit ((MultiMove.initial, false), v₀))
          (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool))))
        (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel (MultiMove.startLabel (copyJobs.map CopyFill.toJob)))))
        ((none : Option Bool), (none : Option Bool))
        (prepInit ((MultiMove.initial, false), v₀),
          (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool)))))
      (BitMachineRawSequence.leftLabel SeedTable.startLabel)
      (((none : Option Bool), (none : Option Bool)),
        (prepInit ((MultiMove.initial, false), v₀),
          (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool)))))
      ((n + ellG G + 1) ^ C + 2 ^ (C * p) + T) G n c := by
  obtain ⟨C, hC⟩ := writer22_clock_le
  refine ⟨C, ?_⟩
  intro V E _ _ _ _ G n c p LW VW W w₀ v₀ T hname hF
  exact writer22Spec_mono Mm _ _ _ G n c (hC G n c p T hname)
    (level0_writer22_of_family4 Mm G n c W w₀ v₀ T hF)

/-- The same under the stated polynomial premise on the `Family4Spec` clock. -/
theorem level0_writer22_clock_poly (C0 : ℕ) : ∃ C : ℕ, ∀ {V E : Type} [Fintype V]
    [DecidableEq V] [Fintype E] [DecidableEq E] (G : EndpointGraph V E) (n c p : ℕ)
    {LW VW : Type} (W : LW → TM2.Stmt (fun _ : HStack => Bool) LW VW) (w₀ : LW) (v₀ : VW)
    (T : ℕ),
    EffectiveIteration.oneLevelBound (P0 G n c) ≤ p →
    T ≤ (n + ellG G + 1) ^ C0 + 2 ^ (C0 * p) →
    Family4Spec Mm W w₀ v₀ T G n c →
    OuterLevel0Full.Writer22Spec Mm
      (BitMachineRawSequence.program EntrySeedSpec.seedProgram
        (BitMachineRawSequence.program (prepProg4 W w₀ v₀) tailClear
          (BitMachineRawSequence.leftLabel RawTableTail.startLabel)
          (prepInit ((MultiMove.initial, false), v₀))
          (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool))))
        (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel (MultiMove.startLabel (copyJobs.map CopyFill.toJob)))))
        ((none : Option Bool), (none : Option Bool))
        (prepInit ((MultiMove.initial, false), v₀),
          (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool)))))
      (BitMachineRawSequence.leftLabel SeedTable.startLabel)
      (((none : Option Bool), (none : Option Bool)),
        (prepInit ((MultiMove.initial, false), v₀),
          (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool)))))
      ((n + ellG G + 1) ^ C + 2 ^ (C * p)) G n c := by
  obtain ⟨C, hC⟩ := level0_writer22_clock Mm
  refine ⟨max C C0 + 1, ?_⟩
  intro V E _ _ _ _ G n c p LW VW W w₀ v₀ T hname hT hF
  refine writer22Spec_mono Mm _ _ _ G n c ?_ (hC G n c p W w₀ v₀ T hname hF)
  obtain ⟨hp, _, _⟩ := level0_small G n c p hname
  have hX : 2 ≤ n + ellG G + 1 := by have := ell_two G; omega
  generalize n + ellG G + 1 = X at hX hT ⊢
  have hX1 : 1 ≤ X := by omega
  have a1 : X ^ C ≤ X ^ max C C0 := Nat.pow_le_pow_right hX1 (le_max_left _ _)
  have a2 : X ^ C0 ≤ X ^ max C C0 := Nat.pow_le_pow_right hX1 (le_max_right _ _)
  have b1 : 2 ^ (C * p) ≤ 2 ^ (max C C0 * p) :=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (le_max_left _ _))
  have b2 : 2 ^ (C0 * p) ≤ 2 ^ (max C C0 * p) :=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (le_max_right _ _))
  have eX : X ^ (max C C0 + 1) = X ^ max C C0 * X := pow_succ _ _
  have e2 : 2 ^ ((max C C0 + 1) * p) = 2 ^ (max C C0 * p) * 2 ^ p := by
    rw [← pow_add]; congr 1; ring
  have t2 : 2 ≤ 2 ^ p := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by decide) (by omega)
  have g1 : 2 * X ^ max C C0 ≤ X ^ max C C0 * X := by rw [mul_comm]; exact Nat.mul_le_mul_left _ hX
  have g2 : 2 * 2 ^ (max C C0 * p) ≤ 2 ^ (max C C0 * p) * 2 ^ p := by
    rw [mul_comm]; exact Nat.mul_le_mul_left _ t2
  rw [eX, e2]
  omega

#print axioms absorb
#print axioms U_prod
#print axioms UG_prod
#print axioms seed_le
#print axioms clock_split
#print axioms writer22_clock_le
#print axioms level0_writer22_clock
#print axioms level0_writer22_clock_poly

end EthInapproximability.CurrentPaper.EntryClockPoly
