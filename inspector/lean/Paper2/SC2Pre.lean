import Paper2.ThrMain
import Paper2.SCCaps

/-! Lane a-success-clock-owner-2, segment (4): the prelude clock of the
success chain (lane a-success-table-owner-9, frozen private objects; under
root admission wave13b-a26). `preClock` collects every summand of the clock of
the one-program endpoint `ThrJoin.success_run_full` except the sampler clock
`SamplerFallbackJoin.clock` and the writer clock `MatrixTableWriter.writerBound`
(the two consumed separately by `SuccessPremiseComposition.composed_all_tape_clock_le`):
the threshold producer `ThrJoin.joinBd`, the graph producer, `SuccessInstall.instBd`,
the charged transfer `3·|bytes|+4` and `6(2·xLmax+3)+1`, and the header clock
`WEntry.hdrBd`. `full_split` shows that the endpoint's clock is at most
`sampler + preClock + writer`; `pre_sched` bounds `preClock` by
`2^(cP (k+1) L)` at `L = clog₂ n` with `cP = 4 (UnaryBinaryEncoding.coefficient + 320)`.
This module imports the frozen private owner-9 chain, so it cannot share a file
with the production `Paper2.WEntry` twin until the gate passes. -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

namespace Paper2.SuccessClock2Pre

open EthInapproximability.CurrentPaper
open Paper2.GeneratorCode Paper2.GeneratorSerialization Paper2.GeneratorSource
  Paper2.RecursiveLabelCodecScratch Paper2.RecursiveEntries

theorem clog_le (v : ℕ) : Nat.clog 2 v ≤ v := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le

theorem natField_len (x : ℕ) : (EncodedCommunication.natField x).length ≤ 2 * x + 1 := by
  rw [EncodedCommunication.natField, EncodedCommunication.field_length, Nat.size_eq_bits_len]
  have h := Nat.size_le.mpr (Nat.lt_two_pow_self : x < 2 ^ x)
  omega

theorem xpow {X : ℕ} (hX : 1048576 ≤ X) :
    1048576 * X ≤ X ^ 2 ∧ 1048576 * X ^ 2 ≤ X ^ 3 ∧ 1048576 * X ^ 3 ≤ X ^ 4 := by
  refine ⟨?_, ?_, ?_⟩
  · calc 1048576 * X ≤ X * X := Nat.mul_le_mul_right _ hX
      _ = X ^ 2 := by ring
  · calc 1048576 * X ^ 2 ≤ X * X ^ 2 := Nat.mul_le_mul_right _ hX
      _ = X ^ 3 := by ring
  · calc 1048576 * X ^ 3 ≤ X * X ^ 3 := Nat.mul_le_mul_right _ hX
      _ = X ^ 4 := by ring

/-- `c * (v + 1)^2 ≤ 8 X^3` for `c + 6 ≤ 2X`, `v + 1 ≤ 2X`. -/
theorem sq_term {X c v : ℕ} (hc : c + 6 ≤ 2 * X) (hv : v + 1 ≤ 2 * X) :
    (c + 6) * (v + 1) ^ 2 ≤ 8 * X ^ 3 := by
  have h1 : (v + 1) ^ 2 ≤ (2 * X) ^ 2 := Nat.pow_le_pow_left hv 2
  have h2 := Nat.mul_le_mul hc h1
  have e : 2 * X * (2 * X) ^ 2 = 8 * X ^ 3 := by ring
  omega

theorem thrBd_X (k : ℕ) (v : Fin 5 → ℕ) {X : ℕ} (hX : 1048576 ≤ X)
    (hco : UnaryBinaryEncoding.coefficient ≤ X) (hv : ∀ i, v i ≤ X) (hk : k ≤ X) :
    ThrProducer.thrBd k v ≤ 64 * X ^ 3 ∧ ThrProducer.Xv v ≤ 5 * X := by
  obtain ⟨h2, h3, h4⟩ := xpow hX
  have hXv : ThrProducer.Xv v ≤ 5 * X := by
    unfold ThrProducer.Xv
    have := clog_le (v 4); have := clog_le (v 3); have := clog_le (v 1); have := clog_le (v 2)
    have := hv 1; have := hv 2; have := hv 3; have := hv 4
    omega
  have hl : ∀ i, ThrProducer.logBd (v i) ≤ 10 * X ^ 3 := by
    intro i
    unfold ThrProducer.logBd
    have := sq_term (X := X) (c := UnaryBinaryEncoding.coefficient) (v := v i) (by omega)
      (by have := hv i; omega)
    have := hv i
    omega
  have hm : k * (2 * ThrProducer.Xv v + 4 + 2) ≤ X * (11 * X) := Nat.mul_le_mul hk (by omega)
  have e : X * (11 * X) = 11 * X ^ 2 := by ring
  have := hl 0; have := hl 1; have := hl 2; have := hl 3; have := hl 4
  have := clog_le (v 0); have := hv 0
  refine ⟨?_, hXv⟩
  unfold ThrProducer.thrBd
  omega

theorem joinBd_X (p s q₂ w Q k : ℕ) {X : ℕ} (hX : 1048576 ≤ X)
    (hco : UnaryBinaryEncoding.coefficient ≤ X) (hS : p + s + q₂ + w + Q + k ≤ X) :
    ThrJoin.joinBd p s q₂ w Q k ≤ 128 * X ^ 3 := by
  obtain ⟨h2, h3, h4⟩ := xpow hX
  have hv : ∀ i, ThrJoin.vv p s q₂ w Q i ≤ X := by
    intro i; fin_cases i <;> simp [ThrJoin.vv] <;> omega
  obtain ⟨ht, hXv⟩ := thrBd_X k (ThrJoin.vv p s q₂ w Q) hX hco hv (by omega)
  have hm : k * ThrProducer.Xv (ThrJoin.vv p s q₂ w Q) ≤ X * (5 * X) := Nat.mul_le_mul (by omega) hXv
  have e : X * (5 * X) = 5 * X ^ 2 := by ring
  have := clog_le p
  unfold ThrJoin.joinBd
  omega

theorem hdrBd_X (rows cols thr : ℕ) {X : ℕ} (hX : 1048576 ≤ X)
    (hco : UnaryBinaryEncoding.coefficient ≤ X) (hS : rows + cols + thr ≤ X) :
    WEntry.hdrBd rows cols thr ≤ 32 * X ^ 3 := by
  obtain ⟨h2, h3, h4⟩ := xpow hX
  have t1 := sq_term (X := X) (c := UnaryBinaryEncoding.coefficient) (v := rows) (by omega) (by omega)
  have t2 := sq_term (X := X) (c := UnaryBinaryEncoding.coefficient) (v := cols) (by omega) (by omega)
  have t3 := sq_term (X := X) (c := UnaryBinaryEncoding.coefficient) (v := thr) (by omega) (by omega)
  have u1 : UnaryBinaryEncoding.coefficient * (rows + 1) ^ 2 ≤
      (UnaryBinaryEncoding.coefficient + 6) * (rows + 1) ^ 2 := Nat.mul_le_mul_right _ (by omega)
  have u2 : UnaryBinaryEncoding.coefficient * (cols + 1) ^ 2 ≤
      (UnaryBinaryEncoding.coefficient + 6) * (cols + 1) ^ 2 := Nat.mul_le_mul_right _ (by omega)
  have u3 : UnaryBinaryEncoding.coefficient * (thr + 1) ^ 2 ≤
      (UnaryBinaryEncoding.coefficient + 6) * (thr + 1) ^ 2 := Nat.mul_le_mul_right _ (by omega)
  have n1 := natField_len rows; have n2 := natField_len cols; have n3 := natField_len thr
  unfold WEntry.hdrBd
  simp only [List.length_append]
  omega

/-- The prelude clock of the success chain: every summand of the clock of
`ThrJoin.success_run_full` except the sampler clock and the writer clock. -/
noncomputable def preClock (g : EncodedGraph.Graph) (p s q₁ q₂ w Q k mX mY thr bytesLen xL : ℕ) : ℕ :=
  ThrJoin.joinBd p s q₂ w Q k +
    (((1 * (2 * (EncodedGraph.encode g).length + 3) + 1) +
      103 * ((EncodedGraph.encode g).length + 1) ^ 3 + 1 +
      (1 * (2 * g.edges.length + 3) + 1) + 1) +
    SuccessInstall.instBd s q₁ Q p w k + (3 * bytesLen + 4) + (6 * (2 * xL + 3) + 1) +
    WEntry.hdrBd mX mY thr + 8)

/-- The clock of `ThrJoin.success_run_full` (literal shape, sampler clock `A`, writer clock `B`)
is at most `A + preClock + B`. -/
theorem full_split (g : EncodedGraph.Graph) (p s q₁ q₂ w Q k mX mY thr bytesLen xL A B : ℕ) :
    ThrJoin.joinBd p s q₂ w Q k + (((1 * (2 * (EncodedGraph.encode g).length + 3) + 1) +
        103 * ((EncodedGraph.encode g).length + 1) ^ 3 + 1 +
        (1 * (2 * g.edges.length + 3) + 1) + 1) + (SuccessInstall.instBd s q₁ Q p w k + (A +
          (3 * bytesLen + 4) + (6 * (2 * xL + 3) + 1 + (B + WEntry.hdrBd mX mY thr + 1) + 1) + 1) +
          1) + 1) + 1 ≤
      A + preClock g p s q₁ q₂ w Q k mX mY thr bytesLen xL + B := by
  unfold preClock
  omega

/-- The prelude clock at a scale `X`. -/
theorem preClock_X (g : EncodedGraph.Graph) (p s q₁ q₂ w Q k mX mY thr bytesLen xL : ℕ) {X : ℕ}
    (hX : 1048576 ≤ X) (hco : UnaryBinaryEncoding.coefficient ≤ X)
    (hS : p + s + q₁ + q₂ + w + Q + k + mX + mY + thr + g.edges.length + 16 ≤ X)
    (hG : (EncodedGraph.encode g).length + 1 ≤ X) (hb : bytesLen ≤ X) (hx : xL ≤ X) :
    preClock g p s q₁ q₂ w Q k mX mY thr bytesLen xL ≤ X ^ 4 := by
  obtain ⟨h2, h3, h4⟩ := xpow hX
  have hj := joinBd_X p s q₂ w Q k hX hco (by omega)
  have hh := hdrBd_X mX mY thr hX hco (by omega)
  have hc3 : ((EncodedGraph.encode g).length + 1) ^ 3 ≤ X ^ 3 := Nat.pow_le_pow_left hG 3
  unfold preClock SuccessInstall.instBd
  omega

theorem Xv_le (v : Fin 5 → ℕ) (Y : ℕ) (hv : ∀ i, v i ≤ Y) : ThrProducer.Xv v ≤ 5 * Y := by
  unfold ThrProducer.Xv
  have := clog_le (v 4); have := clog_le (v 3); have := clog_le (v 1); have := clog_le (v 2)
  have := hv 1; have := hv 2; have := hv 3; have := hv 4
  omega

/-- The prelude-clock exponent. -/
noncomputable def preExponent : ℕ := 4 * (UnaryBinaryEncoding.coefficient + 320)

theorem two_pow_le {a b : ℕ} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) h

open SourceProfileParameters SourceRecursiveNoSampling ParameterizedCanonicalSource in
/-- Segment (4): the prelude clock of the success chain at the public schedule
(`L = clog₂ n`, as in `ThrJoin.success_run_full`), every sample `xs ys` of level `k`. -/
theorem pre_sched (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices] (Δ : ℕ) (γ : ℚ)
    (k L : ℕ) (hLdef : L = Nat.clog 2 g.vertices)
    [NeZero (width L)] [NeZero (width L - 2)] [NeZero (outerWidth L)]
    [NeZero (restorationWidth L)] [NeZero (coverWidth g.vertices g.edges.length L Δ γ)]
    (hc : CompletePublicScheduleScratch.Checks (V := Fin g.vertices) (E := Fin g.edges.length) L Δ γ)
    (xs : Fin (sourceRows L (restorationDepth L) (coverDepth g.vertices g.edges.length L Δ γ) k) →
      Row (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
        (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
        (outerWidth L) (restorationWidth L) (coverWidth g.vertices g.edges.length L Δ γ) k)
    (ys : Fin (sourceCols L (restorationDepth L) (coverDepth g.vertices g.edges.length L Δ γ) k) →
      Column (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
        (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
        (outerWidth L) (restorationWidth L) (coverWidth g.vertices g.edges.length L Δ γ) k) :
    preClock g (LookupSeed.width L) (width L) (width L - 2) (outerWidth L) (restorationWidth L)
        (coverWidth g.vertices g.edges.length L Δ γ) k
        (sourceRows L (restorationDepth L) (coverDepth g.vertices g.edges.length L Δ γ) k)
        (sourceCols L (restorationDepth L) (coverDepth g.vertices g.edges.length L Δ γ) k)
        (sourceBudget L (restorationDepth L) (coverDepth g.vertices g.edges.length L Δ γ) k)
        ((WEntry.colWords g k _ ys).flatten ++ (WEntry.rowWords g k _ xs).flatten).length
        (SuccessXfer.xLmax g k _ _ xs ys) ≤
      2 ^ (preExponent * (k + 1) * L) := by
  obtain ⟨hn, hp, hs, hq₁, hq₂, hw, hQ, hm, hL⟩ :=
    Paper2.SuccessClock.scalar_caps (n := g.vertices) (m := g.edges.length) L Δ γ hc
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
  obtain ⟨hmX, hmY⟩ := Paper2.SuccessClock.dims_cap (n := g.vertices) (m := g.edges.length) L Δ γ hc k
  obtain ⟨hl1, hl2⟩ := Paper2.SuccessClock.label_cap (n := g.vertices) (m := g.edges.length)
    L Δ γ hc k k le_rfl
  have hcd := Paper2.SuccessClock.code_cap (n := g.vertices) (m := g.edges.length) L Δ γ hc k k
    (by omega)
  have hb1 := Paper2.SuccessClock.ofFn_flatten_le
    (defaultCarrierCodecs g.vertices (LookupSeed.width L) (width L) (width L - 2) (outerWidth L)
      (restorationWidth L) (coverWidth g.vertices g.edges.length L Δ γ) k).2 _ ys
  have hb2 := Paper2.SuccessClock.ofFn_flatten_le
    (defaultCarrierCodecs g.vertices (LookupSeed.width L) (width L) (width L - 2) (outerWidth L)
      (restorationWidth L) (coverWidth g.vertices g.edges.length L Δ γ) k).1 _ xs
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
  have hthr := ThrJoin.budget_eq g.vertices g.edges.length Δ γ k
  subst hLdef
  dsimp only at hthr
  have hXv : ThrProducer.Xv ![LookupSeed.width (Nat.clog 2 g.vertices),
      width (Nat.clog 2 g.vertices), outerWidth (Nat.clog 2 g.vertices),
      restorationWidth (Nat.clog 2 g.vertices),
      coverWidth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ] ≤
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

end Paper2.SuccessClock2Pre

#print axioms Paper2.SuccessClock2Pre.full_split
#print axioms Paper2.SuccessClock2Pre.preClock_X
#print axioms Paper2.SuccessClock2Pre.pre_sched
