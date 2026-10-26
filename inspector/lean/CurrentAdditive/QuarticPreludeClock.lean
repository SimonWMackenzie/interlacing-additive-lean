import CurrentAdditive.QuarticClockFinal
import CurrentAdditive.QuarticMachineIdent
import Paper2.SC2Pre

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

namespace Paper2.CurrentAdditive.QuarticPreludeClock

open Paper2.SuccessClock2Pre
open EthInapproximability.CurrentPaper
open Paper2.GeneratorCode Paper2.GeneratorSerialization Paper2.GeneratorSource
  Paper2.RecursiveLabelCodecScratch Paper2.RecursiveEntries Paper2.ParameterizedCanonicalSource
  Paper2.SourceProfileParameters
open CurrentAdditive.RandomizedSchedule
open Paper2.SourceRecursiveNoSampling
open Paper2.CurrentAdditive

theorem pre_sched27 (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices] (Δ : ℕ) (γ : ℚ)
    (k L : ℕ) (hLdef : L = Nat.clog 2 g.vertices)
    [NeZero (width L)] [NeZero (width L - 2)] [NeZero (outerWidth L)]
    [NeZero (width27 L)] [NeZero (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ)]
    (hc : CurrentAdditive.QuarticSchedule.Checks27 (V := Fin g.vertices) (Edges := Fin g.edges.length) L Δ γ)
    (xs : Fin (sourceRows L (4 * RestorationWidthScheduleScratch.ell L) (q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) k) →
      Row (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
        (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
        (outerWidth L) (width27 L) (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) k)
    (ys : Fin (sourceCols L (4 * RestorationWidthScheduleScratch.ell L) (q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) k) →
      Column (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
        (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
        (outerWidth L) (width27 L) (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) k) :
    preClock g (LookupSeed.width L) (width L) (width L - 2) (outerWidth L) (width27 L)
        (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) k
        (sourceRows L (4 * RestorationWidthScheduleScratch.ell L) (q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) k)
        (sourceCols L (4 * RestorationWidthScheduleScratch.ell L) (q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) k)
        (sourceBudget L (4 * RestorationWidthScheduleScratch.ell L) (q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) k)
        ((WEntry.colWords g k _ ys).flatten ++ (WEntry.rowWords g k _ xs).flatten).length
        (SuccessXfer.xLmax g k _ _ xs ys) ≤
      2 ^ (preExponent * (k + 1) * L) := by
  obtain ⟨_, hn, hp, hs, hq₁, hq₂, hw, hQ, hm, hL⟩ :=
    QuarticClockCaps.scalar_caps27 (n := g.vertices) (m := g.edges.length) L Δ γ hc
  dsimp [Paper2.GeneratorPublicCap.publicCap] at hn hp hs hq₁ hq₂ hw hQ hm
  have hT1 : 1 ≤ (k + 1) * L := by nlinarith
  have hLT : L ≤ (k + 1) * L := by nlinarith
  have hkT : k + 1 ≤ (k + 1) * L := by nlinarith
  have hXdef : ∀ e, e ≤ (UnaryBinaryEncoding.coefficient + 320) * ((k + 1) * L) →
      2 ^ e ≤ 2 ^ ((UnaryBinaryEncoding.coefficient + 320) * ((k + 1) * L)) := fun e h =>
    two_pow_le h
  have hX20 : 1048576 ≤ 2 ^ ((UnaryBinaryEncoding.coefficient + 320) * ((k + 1) * L)) := by
    have := hXdef 20 (by nlinarith); simpa using this
  have hco : UnaryBinaryEncoding.coefficient ≤
      2 ^ ((UnaryBinaryEncoding.coefficient + 320) * ((k + 1) * L)) := by
    have h1 := Paper2.SuccessClock.pw_const (c := UnaryBinaryEncoding.coefficient) hT1
    exact h1.trans (hXdef _ (Nat.mul_le_mul_right _ (by omega)))
  obtain ⟨hmX, hmY⟩ := QuarticClockCaps.dims_cap27 (n := g.vertices) (m := g.edges.length) L Δ γ hc k
  rw [Nat.mul_assoc] at hmX hmY
  obtain ⟨hl1, hl2⟩ := QuarticClockCaps.label_cap27 (n := g.vertices) (m := g.edges.length)
    L Δ γ hc k k le_rfl
  have hcd := QuarticClockCaps.code_cap27 (n := g.vertices) (m := g.edges.length) L Δ γ hc k k
    (by omega)
  have hb1 := Paper2.SuccessClock.ofFn_flatten_le
    (defaultCarrierCodecs g.vertices (LookupSeed.width L) (width L) (width L - 2) (outerWidth L)
      (width27 L) (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) k).2 _ ys
  have hb2 := Paper2.SuccessClock.ofFn_flatten_le
    (defaultCarrierCodecs g.vertices (LookupSeed.width L) (width L) (width L - 2) (outerWidth L)
      (width27 L) (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) k).1 _ xs
  have hm1 := Nat.mul_le_mul hmY hl2
  have hm2 := Nat.mul_le_mul hmX hl1
  have e1 : 2 ^ (29 * ((k + 1) * L)) * 2 ^ (26 * ((k + 1) * L)) = 2 ^ (55 * ((k + 1) * L)) := by
    rw [← pow_add]; ring_nf
  have hB : 4 * 2 ^ (55 * ((k + 1) * L)) ≤
      2 ^ ((UnaryBinaryEncoding.coefficient + 320) * ((k + 1) * L)) := by
    have := hXdef (55 * ((k + 1) * L) + 2) (by nlinarith)
    rw [pow_add] at this; omega
  have hC : 4 * 2 ^ (288 * ((k + 1) * L)) ≤
      2 ^ ((UnaryBinaryEncoding.coefficient + 320) * ((k + 1) * L)) := by
    have := hXdef (288 * ((k + 1) * L) + 2) (by nlinarith)
    rw [pow_add] at this; omega
  have hD : 4 * 2 ^ (29 * ((k + 1) * L)) ≤ 2 ^ (55 * ((k + 1) * L)) := by
    have := two_pow_le (a := 29 * ((k + 1) * L) + 2) (b := 55 * ((k + 1) * L)) (by nlinarith)
    rw [pow_add] at this; omega
  have h2955 : 2 ^ (55 * ((k + 1) * L)) ≤ 2 ^ (288 * ((k + 1) * L)) := two_pow_le (by nlinarith)
  have hbytes : ((WEntry.colWords g k _ ys).flatten ++ (WEntry.rowWords g k _ xs).flatten).length ≤
      2 * 2 ^ (55 * ((k + 1) * L)) := by
    simp only [List.length_append, WEntry.colWords, WEntry.rowWords]
    omega
  have hxL : SuccessXfer.xLmax g k _ _ xs ys ≤
      2 ^ ((UnaryBinaryEncoding.coefficient + 320) * ((k + 1) * L)) := by
    unfold SuccessXfer.xLmax
    simp only [List.length_append, encodeCode_length, WEntry.colWords, WEntry.rowWords]
    omega
  have hthr := QuarticConstructor.threshold27_eq_budget g.vertices g.edges.length Δ γ k
  subst hLdef
  dsimp only at hthr
  have hXv : ThrProducer.Xv ![LookupSeed.width (Nat.clog 2 g.vertices),
      width (Nat.clog 2 g.vertices), outerWidth (Nat.clog 2 g.vertices),
      width27 (Nat.clog 2 g.vertices),
      Q27 (V := Fin g.vertices) (E := Fin g.edges.length) (Nat.clog 2 g.vertices) γ Δ] ≤
      5 * 2 ^ (7 * Nat.clog 2 g.vertices) :=
    Xv_le _ _ (by intro i; fin_cases i <;> simp <;> omega)
  have hkl : 2 ^ ((k + 1) * Nat.clog 2 g.vertices) ≤
      2 ^ ((k + 1) * Nat.clog 2 g.vertices + 7 * Nat.clog 2 g.vertices) := two_pow_le (by omega)
  have hkX := Nat.mul_le_mul (show k ≤ (k + 1) * Nat.clog 2 g.vertices by omega) hXv
  have hTT : (k + 1) * Nat.clog 2 g.vertices < 2 ^ ((k + 1) * Nat.clog 2 g.vertices) :=
    Nat.lt_two_pow_self
  have hkY : (k + 1) * Nat.clog 2 g.vertices * (5 * 2 ^ (7 * Nat.clog 2 g.vertices)) ≤
      2 ^ ((k + 1) * Nat.clog 2 g.vertices) * (5 * 2 ^ (7 * Nat.clog 2 g.vertices)) :=
    Nat.mul_le_mul_right _ hTT.le
  have e2 : 2 ^ ((k + 1) * Nat.clog 2 g.vertices) * (5 * 2 ^ (7 * Nat.clog 2 g.vertices)) =
      5 * 2 ^ ((k + 1) * Nat.clog 2 g.vertices + 7 * Nat.clog 2 g.vertices) := by
    rw [pow_add]; ring
  have hE : 16 * 2 ^ ((k + 1) * Nat.clog 2 g.vertices + 7 * Nat.clog 2 g.vertices) ≤
      2 ^ (55 * ((k + 1) * Nat.clog 2 g.vertices)) := by
    have := two_pow_le (a := (k + 1) * Nat.clog 2 g.vertices + 7 * Nat.clog 2 g.vertices + 4)
      (b := 55 * ((k + 1) * Nat.clog 2 g.vertices)) (by nlinarith)
    rw [pow_add] at this; omega
  have hcp := clog_le (LookupSeed.width (Nat.clog 2 g.vertices))
  have hY55 : 16 * 2 ^ (7 * Nat.clog 2 g.vertices) ≤
      2 ^ (55 * ((k + 1) * Nat.clog 2 g.vertices)) := by
    have := two_pow_le (a := 7 * Nat.clog 2 g.vertices + 4)
      (b := 55 * ((k + 1) * Nat.clog 2 g.vertices)) (by nlinarith)
    rw [pow_add] at this; omega
  have hG0 := EncodedGraph.encode_length_upper g hg
  have hmul : g.edges.length * (4 * g.vertices + 4) ≤
      2 ^ (7 * Nat.clog 2 g.vertices) * (4 * 2 ^ (7 * Nat.clog 2 g.vertices) + 4) :=
    Nat.mul_le_mul hm (by omega)
  have hY2 : 2 ^ (7 * Nat.clog 2 g.vertices) * (4 * 2 ^ (7 * Nat.clog 2 g.vertices) + 4) =
      4 * 2 ^ (7 * Nat.clog 2 g.vertices + 7 * Nat.clog 2 g.vertices) +
        4 * 2 ^ (7 * Nat.clog 2 g.vertices) := by
    rw [pow_add]; ring
  have hY14 : 16 * 2 ^ (7 * Nat.clog 2 g.vertices + 7 * Nat.clog 2 g.vertices) ≤
      2 ^ (55 * ((k + 1) * Nat.clog 2 g.vertices)) := by
    have := two_pow_le (a := 7 * Nat.clog 2 g.vertices + 7 * Nat.clog 2 g.vertices + 4)
      (b := 55 * ((k + 1) * Nat.clog 2 g.vertices)) (by nlinarith)
    rw [pow_add] at this; omega
  have e2 : (UnaryBinaryEncoding.coefficient + 320) * ((k + 1) * Nat.clog 2 g.vertices) * 4 =
      preExponent * (k + 1) * Nat.clog 2 g.vertices := by
    unfold preExponent; ring
  have e : (2 ^ ((UnaryBinaryEncoding.coefficient + 320) * ((k + 1) * Nat.clog 2 g.vertices))) ^ 4 =
      2 ^ (preExponent * (k + 1) * Nat.clog 2 g.vertices) := by
    rw [← pow_mul, e2]
  refine le_trans (preClock_X g _ _ _ _ _ _ k _ _ _ _ _ hX20 hco ?_ ?_ ?_ hxL) (le_of_eq e)
  · omega
  · omega
  · omega


end Paper2.CurrentAdditive.QuarticPreludeClock

#print axioms Paper2.CurrentAdditive.QuarticPreludeClock.pre_sched27
