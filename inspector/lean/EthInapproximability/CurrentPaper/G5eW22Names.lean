import EthInapproximability.CurrentPaper.G5dLevel0

/-!
# The level-0 writer-22 clock from the level-0 source names (private lane owner:b-g5-5, segment 1)

The admitted `EntryClockPoly3.T22_0_le` bounds the literal level-0 writer-22 clock
`ClockO.T22zero G n c` under the premise `oneLevelBound (EntryClockPoly.P0 G n c) ≤ p`, a bound on
the parameter VALUE `2 ^ nextScale (scale P0) = 128 * balanceOrder ^ 4` (read-back finding K3).
Here the same literal clock is bounded by `(n + |enc G| + 1)^C + 2^(C p)` for ONE absolute `C`
under the level-0 SOURCE NAMES only (`ActualOrderFromCarrier.SourceNames` at the level-0 record
`EntryClockPoly3.φ ⟨V, E, G, n, c⟩`, i.e. the naming-length / description / auxiliary-width /
restriction-depth clauses of the lock) and `clog(n+2) ≤ p`.

Proof: the literal split `EntryClockPoly.clock_split` (admitted); the three pieces are bounded by the
admitted uniform polynomials `EntryClockPoly.restI_poly`, `EntryClockPoly.bvG_poly`,
`EntryClockPoly.seed_le`, whose size arguments (`Inst.U` of the admitted level-0 instance `inst0`,
and `UG`) are bounded HERE by the admitted actual-count envelope
`ActualCountClock.A ≤ 800 * 2^p * (|enc G| + 1)` (`ActualSourceNames.actual_counts_source_bound`)
instead of `oneLevelBound`; the family clock `TF` by the frozen b-g5-owner-2
`ActualOrderFromCarrier.TF0_clock_from_source_names`.
-/

noncomputable section

namespace EthInapproximability.CurrentPaper.G5eW22Names

open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open Construction MatrixStage4Codes MatrixStage4Digits MatrixMaterialization

set_option maxHeartbeats 3000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

section level

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The level-0 record of `(G, n, c)` (the admitted `EntryClockPoly3.φ`). -/
abbrev r0 (G : EndpointGraph V E) (n c : ℕ) : EntryClockPoly3.LI :=
  EntryClockPoly3.φ ⟨V, E, G, n, c⟩

theorem ell_eq (G : EndpointGraph V E) (n c : ℕ) :
    EntryClockPoly3.ell3 (r0 G n c).G = EntryClockPoly.ellG G := rfl

/-- The actual-count envelope of the level-0 record in the product shape `2^(11p) * X`. -/
theorem A_le (G : EndpointGraph V E) (n c p : ℕ) (hp : 1 ≤ p)
    (h : ActualOrderFromCarrier.SourceNames (r0 G n c) p) :
    ActualCountClock.A (r0 G n c) ≤ 2 ^ (11 * p) * (n + EntryClockPoly.ellG G + 1) := by
  have h1 := ActualSourceNames.actual_counts_source_bound (r0 G n c) p h.toNames
  rw [ell_eq] at h1
  have h800 : 800 ≤ 2 ^ (10 * p) := by
    calc 800 ≤ 2 ^ 10 := by norm_num
      _ ≤ 2 ^ (10 * p) := Nat.pow_le_pow_right (by decide) (by omega)
  have e : 2 ^ (11 * p) = 2 ^ (10 * p) * 2 ^ p := by
    rw [← pow_add]; congr 1; ring
  calc ActualCountClock.A (r0 G n c) ≤ 800 * 2 ^ p * (EntryClockPoly.ellG G + 1) := h1
    _ ≤ 2 ^ (10 * p) * 2 ^ p * (n + EntryClockPoly.ellG G + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ h800) (by omega)
    _ = 2 ^ (11 * p) * (n + EntryClockPoly.ellG G + 1) := by rw [e]

/-- The size `Inst.U` of the admitted level-0 instance is quadratic in the actual counts. -/
theorem U_le_A (G : EndpointGraph V E) (n c : ℕ) :
    (EntryClockPoly.inst0 G n c).U ≤ 13 * (ActualCountClock.A (r0 G n c) + 1) ^ 2 := by
  obtain ⟨-, -, -, -, hs, -, hfl, -, hrx, -, hL, -, -, -, -, hbs, hcy, -, -, -, -, -, -, hv, -⟩ :=
    ActualCountClock.actual_atom_bounds (r0 G n c)
  generalize hA : ActualCountClock.A (r0 G n c) = A at hs hfl hrx hL hbs hcy hv
  have hs' : (EntryClockPoly.inst0 G n c).s ≤ A := hs
  have hL' : (EntryClockPoly.inst0 G n c).L ≤ A := hL
  have hrx' : (EntryClockPoly.inst0 G n c).rx ≤ A := hrx
  have hfl' : firstLength (EntryClockPoly.inst0 G n c).a (EntryClockPoly.inst0 G n c).s ≤ A := hfl
  have hV : Fintype.card V ≤ A := hv
  have hcy' : (EntryClockPoly.inst0 G n c).cy ^ ((EntryClockPoly.inst0 G n c).s + 1) ≤ A := hcy
  have hbs' : binBase (EntryClockPoly.inst0 G n c).a (EntryClockPoly.inst0 G n c).s
      (EntryClockPoly.inst0 G n c).q (EntryClockPoly.inst0 G n c).cy ^
        (EntryClockPoly.inst0 G n c).s ≤ A := hbs
  have hcols : cols (EntryClockPoly.inst0 G n c).a (EntryClockPoly.inst0 G n c).s
      (EntryClockPoly.inst0 G n c).q (EntryClockPoly.inst0 G n c).cy ≤ A * A := by
    rw [EntryClockPoly.cols_eq]; exact Nat.mul_le_mul hcy' hbs'
  have e1 : (EntryClockPoly.inst0 G n c).s * Fintype.card V ≤ A * A := Nat.mul_le_mul hs' hV
  have e2 : (EntryClockPoly.inst0 G n c).s * ((EntryClockPoly.inst0 G n c).s - 3) ≤ A * A :=
    Nat.mul_le_mul hs' ((Nat.sub_le _ _).trans hs')
  have hitems : (EntryClockPoly.inst0 G n c).nv + (EntryClockPoly.inst0 G n c).nb ≤ 8 * (A * A) := by
    show 4 * (EntryClockPoly.inst0 G n c).s * Fintype.card V +
      4 * (EntryClockPoly.inst0 G n c).s * ((EntryClockPoly.inst0 G n c).s - 3) ≤ _
    rw [Nat.mul_assoc, Nat.mul_assoc]
    omega
  unfold EntryClockPoly.Inst.U
  have hsq : (A + 1) ^ 2 = A * A + 2 * A + 1 := by ring
  rw [hsq]
  omega

/-- `Inst.U` of the level-0 instance in the product shape `2^(28p) * X^2`. -/
theorem U_prod_names (G : EndpointGraph V E) (n c p : ℕ) (hp : 1 ≤ p)
    (h : ActualOrderFromCarrier.SourceNames (r0 G n c) p) :
    (EntryClockPoly.inst0 G n c).U ≤ 2 ^ (28 * p) * (n + EntryClockPoly.ellG G + 1) ^ 2 := by
  have hU := U_le_A G n c
  have hA := A_le G n c p hp h
  generalize ActualCountClock.A (r0 G n c) = A at hU hA
  have hXpos : 1 ≤ n + EntryClockPoly.ellG G + 1 := by omega
  generalize n + EntryClockPoly.ellG G + 1 = X at hA hXpos ⊢
  -- A + 1 ≤ 2^(12p) X
  have hA1 : A + 1 ≤ 2 ^ (12 * p) * X := by
    have e : 2 ^ (12 * p) = 2 ^ p * 2 ^ (11 * p) := by rw [← pow_add]; congr 1; ring
    have h2p : 2 ≤ 2 ^ p := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ p := Nat.pow_le_pow_right (by decide) hp
    have hZ : 1 ≤ 2 ^ (11 * p) * X := Nat.mul_pos Nat.one_le_two_pow hXpos
    rw [e, Nat.mul_assoc]
    nlinarith
  have h16 : 16 ≤ 2 ^ (4 * p) := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (4 * p) := Nat.pow_le_pow_right (by decide) (by omega)
  have e28 : 2 ^ (28 * p) = 2 ^ (4 * p) * (2 ^ (12 * p)) ^ 2 := by
    rw [← pow_mul, ← pow_add]; congr 1; ring
  calc (EntryClockPoly.inst0 G n c).U ≤ 13 * (A + 1) ^ 2 := hU
    _ ≤ 13 * (2 ^ (12 * p) * X) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hA1 _)
    _ ≤ 2 ^ (4 * p) * (2 ^ (12 * p) * X) ^ 2 := Nat.mul_le_mul_right _ (by omega)
    _ = 2 ^ (28 * p) * X ^ 2 := by rw [e28, mul_pow]; ring

/-- The graph-piece size `UG` in the product shape `2^(14p) * X^2`. -/
theorem UG_prod_names (G : EndpointGraph V E) (n c p : ℕ) (hp : 1 ≤ p)
    (h : ActualOrderFromCarrier.SourceNames (r0 G n c) p) :
    EntryClockPoly.UG ⟨V, E, G, EntryPrepVec.sv G n c⟩ ≤
      2 ^ (14 * p) * (n + EntryClockPoly.ellG G + 1) ^ 2 := by
  obtain ⟨-, -, -, -, hs, -, -, hq, -⟩ := ActualCountClock.actual_atom_bounds (r0 G n c)
  have hA := A_le G n c p hp h
  have hstr := EntryClockPoly.stream_le G
  have hX : 2 ≤ n + EntryClockPoly.ellG G + 1 := by have := EntryClockPoly.ell_two G; omega
  have hs' : EntryPrepVec.sv G n c ≤ ActualCountClock.A (r0 G n c) := hs
  have hq' : ActualCountClock.A (r0 G n c) ≥
      EthInapproximability.ParameterizedNP.GuardedSourceSlab.q2 G (EntryPrepVec.sv G n c) := hq
  unfold EntryClockPoly.UG
  dsimp only
  generalize ActualCountClock.A (r0 G n c) = A at hA hs' hq'
  generalize EthInapproximability.ParameterizedNP.GuardedSourceSlab.q2 G (EntryPrepVec.sv G n c) = q
    at hq' ⊢
  generalize EntryPrepVec.sv G n c = s at hs' ⊢
  have hℓ : EntryClockPoly.ellG G ≤ n + EntryClockPoly.ellG G + 1 := by omega
  generalize hXd : n + EntryClockPoly.ellG G + 1 = X at hX hA hℓ ⊢
  have hstr' : EntryClockPoly.strG G ≤ X * (2 * X + 2) :=
    hstr.trans (Nat.mul_le_mul hℓ (by omega))
  have hP1 : 1 ≤ 2 ^ (11 * p) := Nat.one_le_two_pow
  have hX2 : X ≤ X ^ 2 := by nlinarith
  have hAX : A ≤ 2 ^ (11 * p) * X ^ 2 := hA.trans (Nat.mul_le_mul_left _ hX2)
  have hXX : X * (2 * X + 2) + X ≤ 4 * X ^ 2 := by nlinarith
  have hX2' : X ^ 2 ≤ 2 ^ (11 * p) * X ^ 2 := Nat.le_mul_of_pos_left _ (by omega)
  have h8 : 8 ≤ 2 ^ (3 * p) := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (3 * p) := Nat.pow_le_pow_right (by decide) (by omega)
  have e14 : 2 ^ (14 * p) = 2 ^ (3 * p) * 2 ^ (11 * p) := by rw [← pow_add]; congr 1; ring
  calc s + EntryClockPoly.ellG G + q + EntryClockPoly.strG G ≤ 6 * (2 ^ (11 * p) * X ^ 2) := by
        omega
    _ ≤ 2 ^ (3 * p) * (2 ^ (11 * p) * X ^ 2) := Nat.mul_le_mul_right _ (by omega)
    _ = 2 ^ (14 * p) * X ^ 2 := by rw [e14, Nat.mul_assoc]

end level

/-- **Segment 1 (writer piece).** The literal clock of the admitted level-0 writer 22 with a free
family clock `T`, from the level-0 source names: ONE absolute `C`. Same statement shape as the
admitted `EntryClockPoly.writer22_clock_le`, with `oneLevelBound (P0 G n c) ≤ p` replaced by
`clog(n+2) ≤ p` and the level-0 `SourceNames`. -/
theorem writer22_clock_names : ∃ C : ℕ, ∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : EndpointGraph V E) (n c p T : ℕ),
    Nat.clog 2 (n + 2) ≤ p → ActualOrderFromCarrier.SourceNames (r0 G n c) p →
    SeedTable.bound (IndexSeed.width (EffectiveIteration.sourceDepth n)) +
        (EntryPrepVec.prepBound G n c (EntryPrepVec.labBound G n c T) +
          (EntryTailClear.tailBound G n c + EntryTailClear.clearBound G n c + 1) + 1) + 1 ≤
      (n + EntryClockPoly.ellG G + 1) ^ C + 2 ^ (C * p) + T := by
  obtain ⟨K1, D1, h1⟩ := EntryClockPoly.restI_poly
  obtain ⟨K2, D2, h2⟩ := EntryClockPoly.bvG_poly
  let C1 := K1 + 2 * 2 * D1
  let C1' := K1 + 2 * (28 + 1) * D1
  let C2 := K2 + 2 * 2 * D2
  let C2' := K2 + 2 * (14 + 1) * D2
  let M := C1 + C1' + C2 + C2' + 1027
  refine ⟨M + 4, ?_⟩
  intro V E _ _ _ _ G n c p T hfloor hnames
  have hp1 : 1 ≤ p := by
    have := Nat.clog_pos (by decide : 1 < 2) (by omega : 1 < n + 2)
    omega
  have hX : 2 ≤ n + EntryClockPoly.ellG G + 1 := by have := EntryClockPoly.ell_two G; omega
  rw [EntryClockPoly.clock_split]
  have hr : EntryClockPoly.restI (EntryClockPoly.inst0 G n c) ≤
      (n + EntryClockPoly.ellG G + 1) ^ C1 + 2 ^ (C1' * p) :=
    (h1 ⟨EntryClockPoly.inst0 G n c, EntryClockPoly.inst0_pos G n c⟩).trans
      (EntryClockPoly.absorb K1 D1 28 2 (n + EntryClockPoly.ellG G + 1) p
        (EntryClockPoly.inst0 G n c).U hX hp1 (U_prod_names G n c p hp1 hnames))
  have hv : EntryPrepVec.boundV G n c ≤ (n + EntryClockPoly.ellG G + 1) ^ C2 + 2 ^ (C2' * p) :=
    (EntryClockPoly.boundV_le G n c).trans ((h2 _).trans
      (EntryClockPoly.absorb K2 D2 14 2 (n + EntryClockPoly.ellG G + 1) p _ hX hp1
        (UG_prod_names G n c p hp1 hnames)))
  have hs := EntryClockPoly.seed_le n (EntryClockPoly.ellG G) hX
  generalize n + EntryClockPoly.ellG G + 1 = X at hX hr hv hs ⊢
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

/-- **Segment 1.** The literal level-0 writer-22 clock `ClockO.T22zero` (the clock of the admitted
`EntryPrepFamily.level0_writer22`) from the level-0 source names: ONE absolute `C`, no
`oneLevelBound` premise. -/
theorem T22zero_names : ∃ C : ℕ, ∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : EndpointGraph V E) (n c p : ℕ),
    Nat.clog 2 (n + 2) ≤ p → ActualOrderFromCarrier.SourceNames (r0 G n c) p →
    ClockO.T22zero G n c ≤
      (n + (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length + 1) ^ C + 2 ^ (C * p) := by
  obtain ⟨Cw, hw⟩ := writer22_clock_names
  obtain ⟨Ct, ht⟩ := ActualOrderFromCarrier.TF0_clock_from_source_names
  refine ⟨Cw + 2 * Ct + 1, fun {V E} _ _ _ _ G n c p hfloor hnames => ?_⟩
  have hp1 : 1 ≤ p := by
    have := Nat.clog_pos (by decide : 1 < 2) (by omega : 1 < n + 2)
    omega
  have hW := hw G n c p (EntryPrepFamily.TF G n c) hfloor hnames
  have hT : EntryPrepFamily.TF G n c ≤ (n + EntryClockPoly3.ell3 G + 2) ^ Ct + 2 ^ (Ct * p) :=
    ht ⟨V, E, G, n, c⟩ p hfloor hnames
  have hell : EntryClockPoly3.ell3 G = EntryClockPoly.ellG G := rfl
  have hell' : (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length =
      EntryClockPoly.ellG G := rfl
  rw [hell] at hT
  rw [hell']
  have hX : 2 ≤ n + EntryClockPoly.ellG G + 1 := by have := EntryClockPoly.ell_two G; omega
  have e : n + EntryClockPoly.ellG G + 2 = (n + EntryClockPoly.ellG G + 1) + 1 := by omega
  rw [e] at hT
  generalize n + EntryClockPoly.ellG G + 1 = X at hX hW hT ⊢
  have hX1 : X + 1 ≤ X ^ 2 := by nlinarith
  have hTX : (X + 1) ^ Ct ≤ X ^ (2 * Ct) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left hX1 _
  have hm := EntryClockPoly3.merge2 X p Cw (2 * Ct) hX hp1
  have hmax : max Cw (2 * Ct) + 1 ≤ Cw + 2 * Ct + 1 := by
    have := max_le (Nat.le_add_right Cw (2 * Ct)) (Nat.le_add_left (2 * Ct) Cw); omega
  have hX1' : 1 ≤ X := by omega
  have m1 : X ^ (max Cw (2 * Ct) + 1) ≤ X ^ (Cw + 2 * Ct + 1) := Nat.pow_le_pow_right hX1' hmax
  have m2 : 2 ^ ((max Cw (2 * Ct) + 1) * p) ≤ 2 ^ ((Cw + 2 * Ct + 1) * p) :=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ hmax)
  have e2 : 2 ^ (Ct * p) ≤ 2 ^ (2 * Ct * p) :=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega))
  have hW' : ClockO.T22zero G n c ≤ X ^ Cw + 2 ^ (Cw * p) + EntryPrepFamily.TF G n c := hW
  omega

#print axioms A_le
#print axioms U_le_A
#print axioms U_prod_names
#print axioms UG_prod_names
#print axioms writer22_clock_names
#print axioms T22zero_names

end EthInapproximability.CurrentPaper.G5eW22Names
