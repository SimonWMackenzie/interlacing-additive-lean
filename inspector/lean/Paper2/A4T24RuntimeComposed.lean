import Paper2.A4Kof
import Paper2.A4RandomBits
import Paper2.A4LogBounds
import Paper2.A4T24Runtime

/-!
# Unit 4 (Paper A), segment 4: runtime composition of the T24 reduction with `A4T24Runtime`

Owner lane `owner:a-unit4-shell-4` (private, 26 September 2026).

Lock v12 `06-reduction.tex`, proof of `thm:quantitative`: the construction takes
`n^{O(k+1)} = 2^{o(N)}` time and random bits at `k = kOf N`. Here, for ONE fixed machine `M`
(the physical T24 front `KofFront.H_T10FrontT24_holds` — which COMPUTES `kOf N` — composed with
the unit-3 machine of `H_A3`, a HYPOTHESIS), for every `ε > 0` there is `N₀` such that for every
sparse valid `Φ` (`clauses ≤ cs·N`) with `N ≥ N₀` and every tape `t` of the selected law at
`kOf N`: `M` prints exactly `outputBits … (kOf N) t` from `pair (encode Φ) (tapeBits t)` within
some `T ≤ 2^(εN)` steps, the tape has `inputBits ≤ 2^(εN)` bits, and `1 ≤ kOf N`.

The composed clock is NOT pushed through the crude `budgetU` merge (whose exponent would carry
`(k+1)` twice through the tape length); it keeps the front clock `CF·(|input|+1)^EF` and the
unit-3 clock `CA·(n+2)^(EA(k+1))` separate, bounds `|input| + 1 ≤ (N+2)³·(n+2)^(160(k+1))`
(`R4RandomBits`, admitted `formula_length_log`), and applies the admitted
`T24Runtime.subexponential` five times at `ε/4`. The estimator is NOT part of this machine
(D-A1/D-A3 untouched). **No ledger row is closed.**
-/

namespace Paper2.Unit4Shell.T24RuntimeComposed

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-- The sparse formula length is at most `(N+2)³` beyond `N ≥ 28 cs + 9`. -/
theorem encode_length_cube (cs : ℕ) (Φ : ValidFormula)
    (hsparse : Φ.val.clauses.length ≤ cs * Φ.val.variables)
    (hN : 28 * cs + 9 ≤ Φ.val.variables) :
    2 * (EncodedCNF.encode Φ.val).length + 3 ≤ (Φ.val.variables + 2) ^ 3 := by
  set N := Φ.val.variables with hNdef
  have hl := Sparsification.formula_length_log Φ.val Φ.property
  have hs : N.size ≤ N := Nat.size_le.mpr Nat.lt_two_pow_self
  have hM : Φ.val.clauses.length * (6 * N.size + 8) ≤ cs * N * (6 * N + 8) :=
    Nat.mul_le_mul hsparse (by omega)
  have h1 : 2 * (EncodedCNF.encode Φ.val).length + 3 ≤ (28 * cs + 9) * (N + 1) ^ 2 := by
    nlinarith
  have h2 : (28 * cs + 9) * (N + 1) ^ 2 ≤ (N + 2) * (N + 2) ^ 2 :=
    Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) 2)
  calc 2 * (EncodedCNF.encode Φ.val).length + 3 ≤ (28 * cs + 9) * (N + 1) ^ 2 := h1
    _ ≤ (N + 2) * (N + 2) ^ 2 := h2
    _ = (N + 2) ^ 3 := by ring

/-- Natural-number clock arithmetic of the composition. -/
theorem clock_nat (x e b TF m TA CF EF pb N n K : ℕ)
    (hx : x = 2 * e + 1 + b) (he : 2 * e + 3 ≤ (N + 2) ^ 3) (hb : b ≤ (n + 2) ^ (160 * K))
    (hK : 1 ≤ K) (hTF : TF = CF * (x + 1) ^ EF) (hm : m ≤ x + TF * pb) :
    TF + 2 * m + 2 + TA ≤
      ((1 + 2 * pb) * CF + 2) * ((N + 2) ^ (3 * (EF + 1)) * (n + 2) ^ (160 * (EF + 1) * K)) +
        TA := by
  have hP : 2 ≤ (n + 2) ^ (160 * K) := by
    calc 2 ≤ n + 2 := by omega
      _ = (n + 2) ^ 1 := (pow_one _).symm
      _ ≤ (n + 2) ^ (160 * K) := Nat.pow_le_pow_right (by omega) (by omega)
  have hx1 : x + 1 ≤ (N + 2) ^ 3 * (n + 2) ^ (160 * K) := by
    have : (2 * e + 3) + (n + 2) ^ (160 * K) ≤ (2 * e + 3) * (n + 2) ^ (160 * K) + 1 := by
      nlinarith
    calc x + 1 ≤ (2 * e + 3) * (n + 2) ^ (160 * K) := by omega
      _ ≤ (N + 2) ^ 3 * (n + 2) ^ (160 * K) := Nat.mul_le_mul_right _ he
  have hpow : (x + 1) ^ (EF + 1) ≤
      (N + 2) ^ (3 * (EF + 1)) * (n + 2) ^ (160 * (EF + 1) * K) := by
    calc (x + 1) ^ (EF + 1) ≤ ((N + 2) ^ 3 * (n + 2) ^ (160 * K)) ^ (EF + 1) :=
          Nat.pow_le_pow_left hx1 _
      _ = (N + 2) ^ (3 * (EF + 1)) * (n + 2) ^ (160 * (EF + 1) * K) := by
          rw [mul_pow, ← pow_mul, ← pow_mul]; ring_nf
  have hEF : (x + 1) ^ EF ≤ (x + 1) ^ (EF + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hX : x + 1 ≤ (x + 1) ^ (EF + 1) := by
    calc x + 1 = (x + 1) ^ 1 := (pow_one _).symm
      _ ≤ (x + 1) ^ (EF + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hTF' : TF ≤ CF * (x + 1) ^ (EF + 1) := by rw [hTF]; exact Nat.mul_le_mul_left _ hEF
  have hTFpb : TF * pb ≤ CF * pb * (x + 1) ^ (EF + 1) := by
    calc TF * pb ≤ CF * (x + 1) ^ (EF + 1) * pb := Nat.mul_le_mul_right _ hTF'
      _ = CF * pb * (x + 1) ^ (EF + 1) := by ring
  have hsum : TF + 2 * m + 2 ≤ ((1 + 2 * pb) * CF + 2) * (x + 1) ^ (EF + 1) := by
    have e : ((1 + 2 * pb) * CF + 2) * (x + 1) ^ (EF + 1) =
        CF * (x + 1) ^ (EF + 1) + 2 * (CF * pb * (x + 1) ^ (EF + 1)) +
          2 * (x + 1) ^ (EF + 1) := by ring
    rw [e]; omega
  have := Nat.mul_le_mul_left ((1 + 2 * pb) * CF + 2) hpow
  omega

/-- Real-number combination: `Q·a·b + C·c ≤ 2^(εN)` from five `2^(εN/4)` bounds. -/
theorem combine (Q a b C c N ε : ℝ) (hε : 0 < ε) (hN : 4 / ε ≤ N)
    (hQ : Q ≤ (2 : ℝ) ^ (ε / 4 * N)) (ha : a ≤ (2 : ℝ) ^ (ε / 4 * N))
    (hb : b ≤ (2 : ℝ) ^ (ε / 4 * N)) (hC : C ≤ (2 : ℝ) ^ (ε / 4 * N))
    (hc : c ≤ (2 : ℝ) ^ (ε / 4 * N))
    (hQ0 : 0 ≤ Q) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hC0 : 0 ≤ C) (hc0 : 0 ≤ c) :
    Q * a * b + C * c ≤ (2 : ℝ) ^ (ε * N) := by
  set u : ℝ := (2 : ℝ) ^ (ε / 4 * N) with hu
  have hu0 : 0 ≤ u := by positivity
  have hu2 : 2 ≤ u := by
    have h1 : (1 : ℝ) ≤ ε / 4 * N := by
      rw [div_le_iff₀ hε] at hN
      nlinarith
    calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := by norm_num
      _ ≤ u := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
  have hu4 : u * u * u * u = (2 : ℝ) ^ (ε * N) := by
    rw [hu, ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num),
      ← Real.rpow_add (by norm_num)]
    congr 1; ring
  have h1 : Q * a * b ≤ u * u * u := by
    have := mul_le_mul (mul_le_mul hQ ha ha0 hu0) hb hb0 (by positivity)
    simpa using this
  have h2 : C * c ≤ u * u := mul_le_mul hC hc hc0 hu0
  rw [← hu4]
  nlinarith [mul_nonneg hu0 hu0, mul_nonneg (mul_nonneg hu0 hu0) hu0]

/-- **T24 reduction runtime, composed (HYP on H-A3 only; estimator not included).** ONE fixed
machine `M`; for every `ε > 0` there is `N₀` such that for every valid `Φ` with
`clauses ≤ cs·N` and `N ≥ N₀` (`N = Φ.val.variables`) and every tape `t` of the selected law at
`k = kOf N`: `1 ≤ kOf N`; `M` maps `pair (encode Φ) (tapeBits t)` to exactly
`outputBits … (kOf N) t` within some `T` steps with `T ≤ 2^(εN)`; and the tape length
`inputBits ≤ 2^(εN)`. Does not close a ledger row (T24, D04). -/
theorem T24_runtime (hA3 : Shells.H_A3 B.degreeBound (sourceGap D B)) (cs : ℕ) :
    ∃ M : BitMachine.Machine, ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ Φ : ValidFormula,
      Φ.val.clauses.length ≤ cs * Φ.val.variables → N₀ ≤ Φ.val.variables →
      1 ≤ kOf Φ.val.variables ∧
      ((TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
        (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
        B.degreeBound (sourceGap D B) (kOf Φ.val.variables)).inputBits : ℝ) ≤
          (2 : ℝ) ^ (ε * Φ.val.variables) ∧
      ∀ t : (TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
        (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
        B.degreeBound (sourceGap D B) (kOf Φ.val.variables)).Tape,
      ∃ T : ℕ, M.OutputsWithin
          (EncodedComplexity.pair (EncodedCNF.encode Φ.val)
            ((TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
              (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
              B.degreeBound (sourceGap D B) (kOf Φ.val.variables)).tapeBits t))
          (EncodedSelectedOutput.outputBits (t10_vertices_pos D B Φ)
            (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
            B.degreeBound (sourceGap D B) (kOf Φ.val.variables) t) T ∧
        (T : ℝ) ≤ (2 : ℝ) ^ (ε * Φ.val.variables) := by
  obtain ⟨MA, CA, EA, hMA⟩ := hA3
  obtain ⟨MF, CF, EF, hMF⟩ := KofFront.H_T10FrontT24_holds D B
  refine ⟨BitMachineComposition.composition MF MA, fun ε hε => ?_⟩
  have hδ0 : 0 < ε / 4 := by positivity
  obtain ⟨N1, hN1⟩ := T24Runtime.subexponential 1 0 (ε / 4) hδ0
  obtain ⟨N2, hN2⟩ := T24Runtime.subexponential (3 * (EF + 1)) 0 (ε / 4) hδ0
  obtain ⟨N3, hN3⟩ := T24Runtime.subexponential (160 * (EF + 1)) (D.sizeExponent + 2) (ε / 4) hδ0
  obtain ⟨N4, hN4⟩ := T24Runtime.subexponential EA (D.sizeExponent + 2) (ε / 4) hδ0
  obtain ⟨N5, hN5⟩ := T24Runtime.subexponential 160 (D.sizeExponent + 2) ε hε
  refine ⟨max (max (max N1 N2) (max N3 N4)) (max (max N5 36)
    (max (max ((1 + 2 * MF.pushBound) * CF + 2) CA) (max (28 * cs + 9)
      (max (2 ^ (2 ^ (D.sizeExponent + 1) * T10Size.t45C D B cs)) ⌈4 / ε⌉₊)))), ?_⟩
  intro Φ hsparse hN
  have hA : max (max N1 N2) (max N3 N4) ≤ (Φ.val.variables) := le_trans (le_max_left _ _) hN
  have hB : max (max N5 36) (max (max ((1 + 2 * MF.pushBound) * CF + 2) CA) (max (28 * cs + 9)
      (max (2 ^ (2 ^ (D.sizeExponent + 1) * T10Size.t45C D B cs)) ⌈4 / ε⌉₊))) ≤ (Φ.val.variables) :=
    le_trans (le_max_right _ _) hN
  have hN1' : N1 ≤ (Φ.val.variables) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hA
  have hN2' : N2 ≤ (Φ.val.variables) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hA
  have hN3' : N3 ≤ (Φ.val.variables) := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hA
  have hN4' : N4 ≤ (Φ.val.variables) := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hA
  have hB1 : max N5 36 ≤ (Φ.val.variables) := le_trans (le_max_left _ _) hB
  have hB2 : max (max ((1 + 2 * MF.pushBound) * CF + 2) CA) (max (28 * cs + 9)
      (max (2 ^ (2 ^ (D.sizeExponent + 1) * T10Size.t45C D B cs)) ⌈4 / ε⌉₊)) ≤ (Φ.val.variables) :=
    le_trans (le_max_right _ _) hB
  have hN5' : N5 ≤ (Φ.val.variables) := le_trans (le_max_left _ _) hB1
  have h36 : 36 ≤ (Φ.val.variables) := le_trans (le_max_right _ _) hB1
  have hB3 : max ((1 + 2 * MF.pushBound) * CF + 2) CA ≤ (Φ.val.variables) := le_trans (le_max_left _ _) hB2
  have hB4 : max (28 * cs + 9)
      (max (2 ^ (2 ^ (D.sizeExponent + 1) * T10Size.t45C D B cs)) ⌈4 / ε⌉₊) ≤ (Φ.val.variables) :=
    le_trans (le_max_right _ _) hB2
  have hQN : ((1 + 2 * MF.pushBound) * CF + 2) ≤ (Φ.val.variables) := le_trans (le_max_left _ _) hB3
  have hCAN : CA ≤ (Φ.val.variables) := le_trans (le_max_right _ _) hB3
  have hcsN : 28 * cs + 9 ≤ (Φ.val.variables) := le_trans (le_max_left _ _) hB4
  have hB5 : max (2 ^ (2 ^ (D.sizeExponent + 1) * T10Size.t45C D B cs)) ⌈4 / ε⌉₊ ≤ (Φ.val.variables) :=
    le_trans (le_max_right _ _) hB4
  have hbig : 2 ^ (2 ^ (D.sizeExponent + 1) * T10Size.t45C D B cs) ≤ (Φ.val.variables) :=
    le_trans (le_max_left _ _) hB5
  have hεN : ⌈4 / ε⌉₊ ≤ (Φ.val.variables) := le_trans (le_max_right _ _) hB5
  have hk1 : 1 ≤ (kOf Φ.val.variables) := AsymptoticsExplicit.kOf_pos (Φ.val.variables) h36
  have hn1 : 1 ≤ ((t10Graph D B Φ).vertices) := t10_vertices_pos D B Φ
  have hsize : ((t10Graph D B Φ).vertices) ≤ (Φ.val.variables) * (Nat.clog 2 ((Φ.val.variables) + 2)) ^ (D.sizeExponent + 2) := T10Size.t45_shell_form D B cs Φ hsparse hbig
  have hNself : (Φ.val.variables) ≤ (Φ.val.variables) * (Nat.clog 2 ((Φ.val.variables) + 2)) ^ 0 := by simp
  have hN1le : 1 ≤ (Φ.val.variables) := by omega
  -- the random-bit bound
  have hbits : (TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
      (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
      B.degreeBound (sourceGap D B) (kOf Φ.val.variables)).inputBits ≤ (((t10Graph D B Φ).vertices) + 2) ^ (160 * ((kOf Φ.val.variables) + 1)) :=
    RandomBits.inputBits_le_resource D B Φ (kOf Φ.val.variables) hk1
  have hbitsR : ((TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
      (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
      B.degreeBound (sourceGap D B) (kOf Φ.val.variables)).inputBits : ℝ) ≤ (2 : ℝ) ^ (ε * (Φ.val.variables)) := by
    have h := hN5 (Φ.val.variables) hN5' ((t10Graph D B Φ).vertices) hn1 hsize
    have hc : ((TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
        (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
        B.degreeBound (sourceGap D B) (kOf Φ.val.variables)).inputBits : ℝ) ≤
        ((((t10Graph D B Φ).vertices) + 2 : ℕ) : ℝ) ^ (160 * ((kOf Φ.val.variables) + 1)) := by exact_mod_cast hbits
    exact hc.trans h
  refine ⟨hk1, hbitsR, fun t => ?_⟩
  obtain ⟨_, _, hinc, hdeg, _, _, _⟩ := t10_source D B Φ
  have hF := hMF Φ t
  have hA := hMA (t10Graph D B Φ) (t10Graph_valid D B Φ) (t10_vertices_pos D B Φ) (kOf Φ.val.variables) hk1
    hinc hdeg t
  have hC := BitMachineComposition.composition_outputsWithin MF MA hF hA
  refine ⟨_, hC, ?_⟩
  -- natural-number clock bound
  have hlen := RandomBits.tape_length_eq D B Φ (kOf Φ.val.variables) t
  have hnat := clock_nat
    (EncodedComplexity.pair (EncodedCNF.encode Φ.val)
      ((TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
        (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
        B.degreeBound (sourceGap D B) (kOf Φ.val.variables)).tapeBits t)).length
    (EncodedCNF.encode Φ.val).length
    ((TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
        (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
        B.degreeBound (sourceGap D B) (kOf Φ.val.variables)).tapeBits t).length _ _
    (CA * (((t10Graph D B Φ).vertices) + 2) ^ (EA * ((kOf Φ.val.variables) + 1))) CF EF MF.pushBound (Φ.val.variables) ((t10Graph D B Φ).vertices) ((kOf Φ.val.variables) + 1)
    (by rw [EncodedComplexity.pair_length])
    (encode_length_cube cs Φ hsparse hcsN) (by rw [hlen]; exact hbits) (by omega) rfl
    (BitMachine.output_length_bound MF hF)
  -- real bounds
  have hK1 : 1 ≤ (kOf Φ.val.variables) + 1 := by omega
  have hNpow1 : (((Φ.val.variables) + 2 : ℕ) : ℝ) ≤ (((Φ.val.variables) + 2 : ℕ) : ℝ) ^ (1 * ((kOf Φ.val.variables) + 1)) := by
    have : ((Φ.val.variables) + 2 : ℕ) ≤ ((Φ.val.variables) + 2) ^ (1 * ((kOf Φ.val.variables) + 1)) := by
      calc (Φ.val.variables) + 2 = ((Φ.val.variables) + 2) ^ 1 := (pow_one _).symm
        _ ≤ ((Φ.val.variables) + 2) ^ (1 * ((kOf Φ.val.variables) + 1)) := Nat.pow_le_pow_right (by omega) (by omega)
    exact_mod_cast this
  have hsub1 := hN1 (Φ.val.variables) hN1' (Φ.val.variables) hN1le hNself
  have hQR : ((((1 + 2 * MF.pushBound) * CF + 2 : ℕ)) : ℝ) ≤ (2 : ℝ) ^ ((ε / 4) * (Φ.val.variables)) := by
    have : ((((1 + 2 * MF.pushBound) * CF + 2 : ℕ)) : ℝ) ≤ (((Φ.val.variables) + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : ((1 + 2 * MF.pushBound) * CF + 2) ≤ (Φ.val.variables) + 2)
    exact this.trans (hNpow1.trans hsub1)
  have hCAR : (CA : ℝ) ≤ (2 : ℝ) ^ ((ε / 4) * (Φ.val.variables)) := by
    have : (CA : ℝ) ≤ (((Φ.val.variables) + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : CA ≤ (Φ.val.variables) + 2)
    exact this.trans (hNpow1.trans hsub1)
  have haR : ((((Φ.val.variables) + 2) ^ (3 * (EF + 1)) : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((ε / 4) * (Φ.val.variables)) := by
    have h := hN2 (Φ.val.variables) hN2' (Φ.val.variables) hN1le hNself
    have : (((Φ.val.variables) + 2) ^ (3 * (EF + 1)) : ℕ) ≤ ((Φ.val.variables) + 2) ^ (3 * (EF + 1) * ((kOf Φ.val.variables) + 1)) :=
      Nat.pow_le_pow_right (by omega) (Nat.le_mul_of_pos_right _ (by omega))
    have hc : ((((Φ.val.variables) + 2) ^ (3 * (EF + 1)) : ℕ) : ℝ) ≤
        (((Φ.val.variables) + 2 : ℕ) : ℝ) ^ (3 * (EF + 1) * ((kOf Φ.val.variables) + 1)) := by exact_mod_cast this
    exact hc.trans h
  have hbR : (((((t10Graph D B Φ).vertices) + 2) ^ (160 * (EF + 1) * ((kOf Φ.val.variables) + 1)) : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((ε / 4) * (Φ.val.variables)) := by
    have h := hN3 (Φ.val.variables) hN3' ((t10Graph D B Φ).vertices) hn1 hsize
    have hc : (((((t10Graph D B Φ).vertices) + 2) ^ (160 * (EF + 1) * ((kOf Φ.val.variables) + 1)) : ℕ) : ℝ) =
        ((((t10Graph D B Φ).vertices) + 2 : ℕ) : ℝ) ^ (160 * (EF + 1) * ((kOf Φ.val.variables) + 1)) := by push_cast; ring
    rw [hc]; exact h
  have hcR : (((((t10Graph D B Φ).vertices) + 2) ^ (EA * ((kOf Φ.val.variables) + 1)) : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((ε / 4) * (Φ.val.variables)) := by
    have h := hN4 (Φ.val.variables) hN4' ((t10Graph D B Φ).vertices) hn1 hsize
    have hc : (((((t10Graph D B Φ).vertices) + 2) ^ (EA * ((kOf Φ.val.variables) + 1)) : ℕ) : ℝ) = ((((t10Graph D B Φ).vertices) + 2 : ℕ) : ℝ) ^ (EA * ((kOf Φ.val.variables) + 1)) := by
      push_cast; ring
    rw [hc]; exact h
  have hεN' : 4 / ε ≤ ((Φ.val.variables) : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hεN)
  have hcomb := combine ((((1 + 2 * MF.pushBound) * CF + 2 : ℕ)) : ℝ) ((((Φ.val.variables) + 2) ^ (3 * (EF + 1)) : ℕ) : ℝ)
    (((((t10Graph D B Φ).vertices) + 2) ^ (160 * (EF + 1) * ((kOf Φ.val.variables) + 1)) : ℕ) : ℝ) (CA : ℝ)
    (((((t10Graph D B Φ).vertices) + 2) ^ (EA * ((kOf Φ.val.variables) + 1)) : ℕ) : ℝ) (Φ.val.variables) ε hε hεN' hQR haR hbR hCAR hcR
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hnatR := (Nat.cast_le (α := ℝ)).mpr hnat
  refine hnatR.trans (le_of_eq_of_le ?_ hcomb)
  push_cast
  ring

#print axioms encode_length_cube
#print axioms clock_nat
#print axioms combine
#print axioms T24_runtime

end Paper2.Unit4Shell.T24RuntimeComposed
