import EthInapproximability.CurrentPaper.EntryFamilyLevel
import EthInapproximability.CurrentPaper.EffectiveIteration
import EthInapproximability.CurrentPaper.BalanceOrderWriterFrame
import EthInapproximability.CurrentPaper.ETHParameterBinsPolynomial
import EthInapproximability.CurrentPaper.MatrixWeightedPreparedPolynomial

/-!
# Lane owner:b-entry-clock-3, segment 1 core: the level-generic family clock is polynomial

Pure arithmetic about ADMITTED clock definitions; no machine.

For every level `(G, c, b, y, lv, M)` let `T := balanceOrder (stepParameters G c b y lv M)`,
`ℓ := |enc G|` and `U := 2^(128 T^4) * (ℓ + 1)` (`128 T^4 = oneLevelBound`, admitted
`nextScale_identity`). The admitted family clock of the level controller
(`WeightedLevelFields15.publicBound15 … + EntryFamilyLevel.copyBound … +
EntryFamilyAssembly.assemblyBound … + 6`, the clock of the admitted
`EntryFamilyLevel.level_family_tables`, with the level arguments of the admitted consumer) is
`≤ K * (U + 1)^D` for ONE pair of absolute constants `K D` over ALL levels.

`PolyIn` and its closure lemmas are a verbatim copy of the admitted
`EntryClockPoly.PolyIn` (production `EntryClockPolyFrame`), and `iterate_le_aux`/`powerBound_le`
of its leaf lemmas, re-declared in this lane's namespace because the production module
`EntryClockPolyFrame` imports `EntryRunsRaw`, whose production closure clashes with the frozen
private twins (owner-4 `CopyFill`, …) imported by the owner-8 chain.
-/

namespace EthInapproximability.CurrentPaper.EntryClockPoly3

open EthInapproximability.ParameterizedNP.GuardedSourceGraph

/-! ## The uniform-polynomial framework (copy of the admitted `EntryClockPolyFrame`) -/

def PolyIn {ι : Type*} (U : ι → ℕ) (f : ι → ℕ) : Prop :=
  ∃ K D : ℕ, ∀ i, f i ≤ K * (U i + 1) ^ D

namespace PolyIn

variable {ι : Type*} {U : ι → ℕ}

theorem mono {f g : ι → ℕ} (h : ∀ i, f i ≤ g i) (hg : PolyIn U g) : PolyIn U f := by
  obtain ⟨K, D, hK⟩ := hg
  exact ⟨K, D, fun i => (h i).trans (hK i)⟩

theorem const (c : ℕ) : PolyIn U (fun _ => c) := ⟨c, 0, fun i => by simp⟩

theorem self : PolyIn U U := ⟨1, 1, fun i => by simp⟩

theorem of_le {f : ι → ℕ} (h : ∀ i, f i ≤ U i) : PolyIn U f := mono h self

theorem add {f g : ι → ℕ} (hf : PolyIn U f) (hg : PolyIn U g) :
    PolyIn U (fun i => f i + g i) := by
  obtain ⟨K1, D1, h1⟩ := hf
  obtain ⟨K2, D2, h2⟩ := hg
  refine ⟨K1 + K2, D1 + D2, fun i => ?_⟩
  have hX : 1 ≤ U i + 1 := Nat.le_add_left 1 (U i)
  have e1 : (U i + 1) ^ D1 ≤ (U i + 1) ^ (D1 + D2) :=
    Nat.pow_le_pow_right hX (Nat.le_add_right _ _)
  have e2 : (U i + 1) ^ D2 ≤ (U i + 1) ^ (D1 + D2) :=
    Nat.pow_le_pow_right hX (Nat.le_add_left _ _)
  calc f i + g i ≤ K1 * (U i + 1) ^ D1 + K2 * (U i + 1) ^ D2 := Nat.add_le_add (h1 i) (h2 i)
    _ ≤ K1 * (U i + 1) ^ (D1 + D2) + K2 * (U i + 1) ^ (D1 + D2) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ e1) (Nat.mul_le_mul_left _ e2)
    _ = (K1 + K2) * (U i + 1) ^ (D1 + D2) := by ring

theorem mul {f g : ι → ℕ} (hf : PolyIn U f) (hg : PolyIn U g) :
    PolyIn U (fun i => f i * g i) := by
  obtain ⟨K1, D1, h1⟩ := hf
  obtain ⟨K2, D2, h2⟩ := hg
  refine ⟨K1 * K2, D1 + D2, fun i => ?_⟩
  calc f i * g i ≤ (K1 * (U i + 1) ^ D1) * (K2 * (U i + 1) ^ D2) := Nat.mul_le_mul (h1 i) (h2 i)
    _ = K1 * K2 * (U i + 1) ^ (D1 + D2) := by ring

theorem pow {f : ι → ℕ} (hf : PolyIn U f) (k : ℕ) : PolyIn U (fun i => f i ^ k) := by
  induction k with
  | zero => simpa using (const 1 : PolyIn U (fun _ => 1))
  | succ k ih =>
    simp only [pow_succ]
    exact mul ih hf

theorem max {f g : ι → ℕ} (hf : PolyIn U f) (hg : PolyIn U g) :
    PolyIn U (fun i => Max.max (f i) (g i)) :=
  mono (fun _ => max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)) (add hf hg)

theorem sub {f : ι → ℕ} (g : ι → ℕ) (hf : PolyIn U f) : PolyIn U (fun i => f i - g i) :=
  mono (fun _ => Nat.sub_le _ _) hf

theorem comap {κ : Type*} {V : κ → ℕ} {f : ι → ℕ} (φ : κ → ι) (hU : ∀ k, U (φ k) ≤ V k)
    (hf : PolyIn U f) : PolyIn V (fun k => f (φ k)) := by
  obtain ⟨K, D, h⟩ := hf
  refine ⟨K, D, fun k => (h (φ k)).trans (Nat.mul_le_mul_left _ ?_)⟩
  exact Nat.pow_le_pow_left (Nat.add_le_add_right (hU k) 1) _

end PolyIn

/-- Close a `PolyIn` goal built from `+ * ^k - max`, constants and hypotheses. -/
macro "pc" : tactic => `(tactic| repeat' (first
  | assumption
  | exact PolyIn.const _
  | apply PolyIn.add
  | apply PolyIn.mul
  | apply PolyIn.pow
  | apply PolyIn.sub
  | apply PolyIn.max))

/-! ## Leaf: the weighted power clock (copy of the admitted leaf lemmas) -/

theorem iterate_le_aux (acc base B : ℕ) :
    ∀ m k, (∀ j, j ≤ m + k → base ^ j ≤ B) →
      MatrixWeightedPower.iterateBound (acc * base ^ k) base m ≤ m * (9 * (acc * B) + 7) := by
  intro m
  induction m with
  | zero => intro k _; simp [MatrixWeightedPower.iterateBound]
  | succ m ih =>
    intro k hB
    have hk : acc * base ^ k * base = acc * base ^ (k + 1) := by ring
    have ih' := ih (k + 1) (fun j hj => hB j (by omega))
    have b1 : base ^ k ≤ B := hB k (by omega)
    have b2 : base ^ (k + 1) ≤ B := hB (k + 1) (by omega)
    have c1 : acc * base ^ k ≤ acc * B := Nat.mul_le_mul_left _ b1
    have c2 : acc * base ^ (k + 1) ≤ acc * B := Nat.mul_le_mul_left _ b2
    have hr : MatrixWeightedPower.roundBound (acc * base ^ k) base =
        3 * (acc * base ^ (k + 1)) + 5 * (acc * base ^ k) + 7 := by
      unfold MatrixWeightedPower.roundBound MatrixAddressMachine.exactTime
      ring
    simp only [MatrixWeightedPower.iterateBound]
    rw [hk, hr]
    have e : (m + 1) * (9 * (acc * B) + 7) = (9 * (acc * B) + 7) + m * (9 * (acc * B) + 7) := by
      ring
    rw [e]
    omega

theorem iterate_le (base m : ℕ) :
    MatrixWeightedPower.iterateBound 1 base m ≤ m * (9 * (base ^ m + 1) + 7) := by
  have h := iterate_le_aux 1 base (base ^ m + 1) m 0 (by
    intro j hj
    rcases Nat.eq_zero_or_pos base with h0 | hpos
    · subst h0
      rcases Nat.eq_zero_or_pos j with hj0 | hj0
      · subst hj0; simp
      · rw [Nat.zero_pow hj0]; exact Nat.zero_le _
    · have := Nat.pow_le_pow_right hpos (show j ≤ m by omega)
      omega)
  simpa using h

theorem powerBound_le (base m : ℕ) :
    MatrixWeightedPower.powerBound base m ≤ m * (9 * (base ^ m + 1) + 7) + 1 := by
  unfold MatrixWeightedPower.powerBound
  have := iterate_le base m
  omega

/-! ## Levels -/

/-- A level: a graph and the five level parameters of `Iteration.stepParameters`. -/
structure LI where
  V : Type
  E : Type
  [iV : Fintype V]
  [dV : DecidableEq V]
  [iE : Fintype E]
  [dE : DecidableEq E]
  G : EndpointGraph V E
  c : ℕ
  b : ℕ
  y : ℕ
  lv : ℕ
  M : Iteration.Matrix

attribute [instance] LI.iV LI.dV LI.iE LI.dE

abbrev PL (i : LI) : Parameters.Input := Iteration.stepParameters i.G i.c i.b i.y i.lv i.M
abbrev tI (i : LI) : ℕ := Parameters.balanceOrder (PL i)
abbrev aI (i : LI) : ℕ := Parameters.firstExponent (PL i)
abbrev sI (i : LI) : ℕ := Parameters.bins (PL i)
abbrev qI (i : LI) : ℕ := EthInapproximability.ParameterizedNP.GuardedSourceSlab.q2 i.G (sI i)
abbrev rxI (i : LI) : ℕ := (PL i).rows
abbrev cyI (i : LI) : ℕ := (PL i).columns
abbrev mI (i : LI) : ℕ := Construction.qOne (aI i) * rxI i
abbrev LI' (i : LI) : ℕ := PrimeSampler.size (qI i) (tI i) (mI i)
abbrev pI (i : LI) : ℕ := PrimeSampler.prime (qI i) (tI i) (mI i)
abbrev gI (i : LI) : EncodedGraph.Graph := EncodedETHSource.serializeGraph i.G
abbrev eI (i : LI) : ℕ := Fintype.card i.E

/-- The literal encoded-graph length `|enc G|`. -/
def ell3 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EndpointGraph V E) : ℕ :=
  (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length

/-- The size of a level: `2^(oneLevelBound) * (|enc G| + 1)`. -/
def U (i : LI) : ℕ := 2 ^ (128 * tI i ^ 4) * (ell3 i.G + 1)

theorem card_le_ell3 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EndpointGraph V E) : Fintype.card V + 2 * Fintype.card E + 2 ≤ ell3 G := by
  have h := EncodedGraph.encode_length_lower (EncodedETHSource.serializeGraph G)
  simp only [EncodedETHSource.serializeGraph_vertices, EncodedETHSource.serializeGraph_edges] at h
  exact h

theorem exp_le_U (i : LI) (k : ℕ) (hk : k ≤ 128 * tI i ^ 4) : 2 ^ k ≤ U i := by
  unfold U
  calc 2 ^ k ≤ 2 ^ (128 * tI i ^ 4) := Nat.pow_le_pow_right (by decide) hk
    _ ≤ 2 ^ (128 * tI i ^ 4) * (ell3 i.G + 1) := Nat.le_mul_of_pos_right _ (by omega)

theorem ell_le_U (i : LI) : ell3 i.G + 1 ≤ U i := by
  unfold U
  exact Nat.le_mul_of_pos_left _ (Nat.pow_pos (by decide))

set_option maxHeartbeats 1000000 in
/-- All size facts of a level, pointwise. -/
theorem sizes (i : LI) :
    tI i ≤ U i ∧ 2 ^ tI i ≤ U i ∧ aI i ≤ U i ∧ 2 ^ aI i ≤ U i ∧ sI i ≤ U i ∧
    Construction.qOne (aI i) ≤ U i ∧ Construction.firstLength (aI i) (sI i) ≤ U i ∧
    qI i ≤ U i ∧ rxI i ≤ U i ∧ cyI i ≤ U i ∧ LI' i ≤ U i ∧ pI i ≤ U i ∧
    pI i ^ tI i ≤ U i ∧
    MatrixStage4Digits.wordBase (aI i) (sI i) (cyI i) ≤ U i ∧
    MatrixStage4Digits.binBase (aI i) (sI i) (qI i) (cyI i) ≤ U i ∧
    MatrixStage4Digits.binBase (aI i) (sI i) (qI i) (cyI i) ^ sI i ≤ U i ∧
    cyI i ^ (sI i + 1) ≤ U i ∧
    Parameters.scale (PL i) ≤ U i ∧ (PL i).sourceConstant ≤ U i ∧ (PL i).nextDepth ≤ U i ∧
    (PL i).cost ≤ U i ∧ (PL i).edges ≤ U i ∧ ell3 i.G ≤ U i ∧ (gI i).vertices ≤ U i ∧
    eI i ≤ U i := by
  obtain ⟨h128, _, _, hs, hfl, hsec, _, _, ha, _, _, _, _⟩ :=
    EffectiveIteration.parameter_size_bounds (PL i)
  obtain ⟨hrx, hcy, hed⟩ := EffectiveIteration.input_cardinality_bounds (PL i)
  obtain ⟨hsc, hnd, hco, _, _⟩ := Parameters.public_bounds (PL i)
  have hLb := EffectiveIteration.familySize_bound (PL i)
  have hcard := card_le_ell3 i.G
  have hell := ell_le_U i
  generalize hT : Parameters.balanceOrder (PL i) = T at h128 hs hfl hsec ha hrx hcy hed hLb
  have hT1 : 1 ≤ T := by omega
  have hTT : T ≤ T * T := Nat.le_mul_of_pos_left _ (by omega)
  have hT2 : T * T ≤ T ^ 4 := by
    have : T ^ 2 ≤ T ^ 4 := Nat.pow_le_pow_right hT1 (by decide)
    simpa [sq] using this
  have hT3 : T * T * T ≤ T ^ 4 := by
    have : T ^ 3 ≤ T ^ 4 := Nat.pow_le_pow_right hT1 (by decide)
    simpa [pow_succ, sq] using this
  have hT14 : T ≤ T ^ 4 := hTT.trans hT2
  have tU : tI i ≤ U i := by
    rw [tI, hT]
    exact (Nat.le_of_lt Nat.lt_two_pow_self).trans (exp_le_U i T (by rw [tI, hT]; omega))
  have t2U : 2 ^ tI i ≤ U i := exp_le_U i _ (by rw [tI, hT]; omega)
  have eU : ∀ k, k ≤ 128 * T ^ 4 → 2 ^ k ≤ U i := fun k hk => exp_le_U i k (by rw [tI, hT]; exact hk)
  have leT : ∀ x, x ≤ T → x ≤ U i := fun x hx => le_trans hx (by rw [← hT]; exact tU)
  have le2T : ∀ x, x ≤ 2 ^ T → x ≤ U i := fun x hx => le_trans hx (eU T (by omega))
  -- firstLength
  have hflE : Construction.firstLength (aI i) (sI i) = Parameters.firstLength (PL i) := by
    show Construction.qOne (Parameters.firstExponent (PL i)) + (Parameters.bins (PL i) + 1) =
      Parameters.firstWidth (PL i) + Parameters.bins (PL i) + 1
    unfold Construction.qOne Parameters.firstWidth
    omega
  have hfl' : Construction.firstLength (aI i) (sI i) ≤ T := by rw [hflE]; exact hfl
  have hqOne : Construction.qOne (aI i) ≤ T := by
    have : Construction.qOne (aI i) ≤ Construction.firstLength (aI i) (sI i) := by
      unfold Construction.firstLength; omega
    omega
  have h2a : 2 ^ aI i ≤ T + 2 := by
    have := hqOne; unfold Construction.qOne at this; omega
  have hsI : sI i ≤ T := hs
  have hq : qI i ≤ 2 ^ T := by
    show 2 ^ Parameters.secondExponent (PL i) ≤ 2 ^ T
    exact Nat.pow_le_pow_right (by decide) hsec
  have hL : LI' i ≤ 2 ^ (16 * T ^ 2) := hLb
  have hp2 : 2 ≤ pI i := EthInapproximability.ParameterizedNP.BalancedFamilyBuilder.two_le_balPrime _ _ _
  have hpT : pI i ^ tI i = LI' i := rfl
  have hpL : pI i ≤ LI' i := by
    rw [← hpT]
    calc pI i = pI i ^ 1 := (pow_one _).symm
      _ ≤ pI i ^ tI i := Nat.pow_le_pow_right (by omega) (by rw [tI, hT]; exact hT1)
  have hwb : MatrixStage4Digits.wordBase (aI i) (sI i) (cyI i) ≤ 2 ^ (T * T) := by
    unfold MatrixStage4Digits.wordBase
    calc cyI i ^ Construction.firstLength (aI i) (sI i) ≤ (2 ^ T) ^ Construction.firstLength (aI i) (sI i) :=
          Nat.pow_le_pow_left hcy _
      _ ≤ (2 ^ T) ^ T := Nat.pow_le_pow_right (Nat.pow_pos (by decide)) hfl'
      _ = 2 ^ (T * T) := by rw [← pow_mul]
  have hbb : MatrixStage4Digits.binBase (aI i) (sI i) (qI i) (cyI i) ≤ 2 ^ (T + T * T) := by
    unfold MatrixStage4Digits.binBase
    rw [pow_add]
    exact Nat.mul_le_mul hq hwb
  have hbbs : MatrixStage4Digits.binBase (aI i) (sI i) (qI i) (cyI i) ^ sI i ≤
      2 ^ ((T + T * T) * T) := by
    calc MatrixStage4Digits.binBase (aI i) (sI i) (qI i) (cyI i) ^ sI i ≤ (2 ^ (T + T * T)) ^ sI i :=
          Nat.pow_le_pow_left hbb _
      _ ≤ (2 ^ (T + T * T)) ^ T := Nat.pow_le_pow_right (Nat.pow_pos (by decide)) hsI
      _ = 2 ^ ((T + T * T) * T) := by rw [← pow_mul]
  have hcys : cyI i ^ (sI i + 1) ≤ 2 ^ (T * (T + 1)) := by
    calc cyI i ^ (sI i + 1) ≤ (2 ^ T) ^ (sI i + 1) := Nat.pow_le_pow_left hcy _
      _ ≤ (2 ^ T) ^ (T + 1) := Nat.pow_le_pow_right (Nat.pow_pos (by decide)) (by omega)
      _ = 2 ^ (T * (T + 1)) := by rw [← pow_mul]
  have hscale : Parameters.scale (PL i) ≤ T := by
    have h2 : Parameters.scale (PL i) ≤ Parameters.scale (PL i) ^ 2 :=
      Nat.le_self_pow (by norm_num) _
    unfold Parameters.firstExponent at ha
    omega
  have hsc2 : 2 ^ Parameters.scale (PL i) ≤ 2 ^ T := Nat.pow_le_pow_right (by decide) hscale
  have e1 : (T + T * T) * T ≤ 128 * T ^ 4 := by
    calc (T + T * T) * T = T * T + T * T * T := by ring
      _ ≤ T ^ 4 + T ^ 4 := Nat.add_le_add hT2 hT3
      _ ≤ 128 * T ^ 4 := by omega
  have e2 : T * (T + 1) ≤ 128 * T ^ 4 := by
    calc T * (T + 1) = T * T + T := by ring
      _ ≤ T ^ 4 + T ^ 4 := Nat.add_le_add hT2 hT14
      _ ≤ 128 * T ^ 4 := by omega
  have e3 : 16 * T ^ 2 ≤ 128 * T ^ 4 := by
    have : T ^ 2 = T * T := sq T
    omega
  have e4 : T * T ≤ 128 * T ^ 4 := by omega
  have e5 : T + T * T ≤ 128 * T ^ 4 := by omega
  have hvert : (gI i).vertices ≤ ell3 i.G := by
    rw [EncodedETHSource.serializeGraph_vertices]; omega
  refine ⟨tU, t2U, leT _ ha, eU _ (le_trans ha (hT14.trans (by omega))), leT _ hsI, leT _ hqOne, leT _ hfl', le2T _ hq,
    le2T _ hrx, le2T _ hcy, (hL.trans (eU _ e3)), (hpL.trans (hL.trans (eU _ e3))),
    (by rw [hpT]; exact hL.trans (eU _ e3)), (hwb.trans (eU _ e4)),
    (hbb.trans (eU _ e5)), (hbbs.trans (eU _ e1)), (hcys.trans (eU _ e2)),
    leT _ hscale, le2T _ (hsc.trans hsc2), le2T _ (hnd.trans hsc2), le2T _ (hco.trans hsc2),
    le2T _ hed, by omega, hvert.trans (by omega),
    (show eI i ≤ ell3 i.G by unfold eI; omega).trans (by omega)⟩

end EthInapproximability.CurrentPaper.EntryClockPoly3
