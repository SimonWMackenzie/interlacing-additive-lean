import CurrentAdditive.IndependentSupport
import CurrentAdditive.CompressionDenominator
import CurrentAdditive.SequentialSourceResource
import CurrentAdditive.SequentialBitBound
import CurrentAdditive.MaterializedCandidateBound

set_option maxHeartbeats 1000000

namespace CurrentAdditive.IntegerBitSupport

open IndependentSupport SequentialCode SequentialSourceCode
open RationalBitBounds RationalCandidateCompletion
open SequentialFeatureCount SequentialFeatureCoverage SequentialSourceResource
open SequentialFiniteLaw
open MaterializedGauss SequentialTotality

/-- A finite prefix of the literal dependence-elimination loop. Each step
records the free-column test and the successful materialized update. -/
inductive EliminationTrace {α : Type*} (n : Nat) (φ : α → Fin n → ℚ) :
    Nat → Array (α × ℚ) → Array (α × ℚ) → Prop where
  | refl (source) : EliminationTrace n φ 0 source source
  | step (source next out)
      (f : Fin (columnCount (featureRows n φ source))) (t : Nat)
      (hfree : sourceFreeColumn n φ source = some f)
      (hstep : compressSourceOnceMaterialized n φ source = some next)
      (hrest : EliminationTrace n φ t next out) :
      EliminationTrace n φ (t + 1) source out

/-- The new independence-terminating loop inherits the existing checked
integer-coefficient denominator factor on every actual elimination call. -/
theorem compressUntilIndependent_denominator {α : Type*}
    (n : Nat) (φ : α → Fin n → ℚ)
    (hn : 0 < n)
    (hφ : ∀ x j, φ x j = 0 ∨ φ x j = 1)
    (source out : Array (α × ℚ)) (fuel : Nat)
    (h : compressUntilIndependent n φ source fuel = some out)
    (enc : CommonDenominator (fun i : Fin source.size => source[i].2)) :
    ∃ encOut : CommonDenominator (fun i : Fin out.size => out[i].2),
      encOut.denominator ≤ enc.denominator *
        (2 ^ (4 * n * Nat.size (n + 1))) ^ fuel := by
  induction fuel generalizing source with
  | zero =>
      simp only [compressUntilIndependent] at h
      cases hf : sourceFreeColumn n φ source with
      | none =>
          simp [hf] at h
          cases h
          exact ⟨enc, by simp⟩
      | some f => simp [hf] at h
  | succ fuel ih =>
      simp only [compressUntilIndependent] at h
      cases hf : sourceFreeColumn n φ source with
      | none =>
          simp [hf] at h
          cases h
          refine ⟨enc, ?_⟩
          have hpow : 1 ≤ (2 ^ (4 * n * Nat.size (n + 1))) ^ (fuel + 1) := by
            exact Nat.one_le_pow _ _ (by positivity)
          calc
            enc.denominator ≤ enc.denominator * 1 := by simp
            _ ≤ enc.denominator *
                (2 ^ (4 * n * Nat.size (n + 1))) ^ (fuel + 1) :=
              Nat.mul_le_mul_left _ hpow
      | some f =>
          cases hs : compressSourceOnceMaterialized n φ source with
          | none => simp [hf, hs] at h
          | some next =>
              simp [hf, hs] at h
              let encMap : CommonDenominator
                  (fun i : Fin (source.map Prod.snd).size =>
                    (source.map Prod.snd)[i]) :=
                { denominator := enc.denominator
                  positive := enc.positive
                  numerator := fun i =>
                    enc.numerator ⟨i.val, by simpa using i.isLt⟩
                  represents := by
                    intro i
                    have hr := enc.represents ⟨i.val, by simpa using i.isLt⟩
                    simpa using hr }
              obtain ⟨encNext, hstep⟩ :=
                compressSourceOnceMaterialized_denominator n φ source next
                  hn hφ hs encMap
              have hstep' : encNext.denominator ≤ enc.denominator *
                  2 ^ (4 * n * Nat.size (n + 1)) := by
                simpa [encMap] using hstep
              obtain ⟨encOut, hrest⟩ := ih next h encNext
              refine ⟨encOut, ?_⟩
              calc
                encOut.denominator ≤ encNext.denominator *
                    (2 ^ (4 * n * Nat.size (n + 1))) ^ fuel := hrest
                _ ≤ (enc.denominator *
                    2 ^ (4 * n * Nat.size (n + 1))) *
                    (2 ^ (4 * n * Nat.size (n + 1))) ^ fuel := by
                    exact Nat.mul_le_mul_right _ hstep'
                _ = enc.denominator *
                    (2 ^ (4 * n * Nat.size (n + 1))) ^ (fuel + 1) := by
                    rw [pow_succ]
                    ring

/-- The same checked bound holds at *every finite prefix* of the actual
elimination path, even before the loop reaches independent columns. -/
theorem eliminationTrace_denominator {α : Type*}
    (n : Nat) (φ : α → Fin n → ℚ)
    (hn : 0 < n)
    (hφ : ∀ x j, φ x j = 0 ∨ φ x j = 1)
    (source out : Array (α × ℚ)) (t : Nat)
    (htrace : EliminationTrace n φ t source out)
    (enc : CommonDenominator (fun i : Fin source.size => source[i].2)) :
    ∃ encOut : CommonDenominator (fun i : Fin out.size => out[i].2),
      encOut.denominator ≤ enc.denominator *
        (2 ^ (4 * n * Nat.size (n + 1))) ^ t := by
  induction htrace with
  | refl source =>
      exact ⟨enc, by simp⟩
  | step source next out f t hfree hstep hrest ih =>
      let encMap : CommonDenominator
          (fun i : Fin (source.map Prod.snd).size =>
            (source.map Prod.snd)[i]) :=
        { denominator := enc.denominator
          positive := enc.positive
          numerator := fun i =>
            enc.numerator ⟨i.val, by simpa using i.isLt⟩
          represents := by
            intro i
            have hr := enc.represents ⟨i.val, by simpa using i.isLt⟩
            simpa using hr }
      obtain ⟨encNext, hstepBound⟩ :=
        compressSourceOnceMaterialized_denominator n φ source next
          hn hφ hstep encMap
      obtain ⟨encOut, hrestBound⟩ := ih encNext
      refine ⟨encOut, ?_⟩
      calc
        encOut.denominator ≤ encNext.denominator *
            (2 ^ (4 * n * Nat.size (n + 1))) ^ t := hrestBound
        _ ≤ (enc.denominator * 2 ^ (4 * n * Nat.size (n + 1))) *
            (2 ^ (4 * n * Nat.size (n + 1))) ^ t := by
            exact Nat.mul_le_mul_right _ (by simpa [encMap] using hstepBound)
        _ = enc.denominator *
            (2 ^ (4 * n * Nat.size (n + 1))) ^ (t + 1) := by
            rw [pow_succ]
            ring

/-- A successful evaluation of the executable loop has an explicit trace
whose length is no larger than the supplied fuel. -/
theorem compressUntilIndependent_trace {α : Type*}
    (n : Nat) (φ : α → Fin n → ℚ)
    (source out : Array (α × ℚ)) (fuel : Nat)
    (hrun : compressUntilIndependent n φ source fuel = some out) :
    ∃ t, t ≤ fuel ∧ EliminationTrace n φ t source out ∧
      sourceFreeColumn n φ out = none := by
  induction fuel generalizing source with
  | zero =>
      simp only [compressUntilIndependent] at hrun
      cases hf : sourceFreeColumn n φ source with
      | none =>
          simp [hf] at hrun
          cases hrun
          exact ⟨0, by omega, .refl out, hf⟩
      | some f => simp [hf] at hrun
  | succ fuel ih =>
      simp only [compressUntilIndependent] at hrun
      cases hf : sourceFreeColumn n φ source with
      | none =>
          simp [hf] at hrun
          cases hrun
          exact ⟨0, by omega, .refl out, hf⟩
      | some f =>
          cases hs : compressSourceOnceMaterialized n φ source with
          | none => simp [hf, hs] at hrun
          | some next =>
              simp [hf, hs] at hrun
              obtain ⟨t, ht, htrace, hnone⟩ := ih next hrun
              exact ⟨t + 1, by omega,
                .step source next out f t hf hs htrace, hnone⟩

/-- Explicit binary-size bound after any number of successful actual
elimination steps, including intermediate retained arrays. -/
theorem eliminationTrace_denominator_bits {α : Type*}
    (n : Nat) (φ : α → Fin n → ℚ)
    (hn : 0 < n)
    (hφ : ∀ x j, φ x j = 0 ∨ φ x j = 1)
    (source out : Array (α × ℚ)) (t : Nat)
    (htrace : EliminationTrace n φ t source out)
    (enc : CommonDenominator (fun i : Fin source.size => source[i].2)) :
    ∃ encOut : CommonDenominator (fun i : Fin out.size => out[i].2),
      Nat.size encOut.denominator ≤ Nat.size enc.denominator +
        4 * t * n * Nat.size (n + 1) + 1 := by
  obtain ⟨encOut, hden⟩ :=
    eliminationTrace_denominator n φ hn hφ source out t htrace enc
  refine ⟨encOut, ?_⟩
  have henc : enc.denominator ≤ 2 ^ Nat.size enc.denominator :=
    le_of_lt (Nat.lt_size_self _)
  have hupper : encOut.denominator ≤
      2 ^ (Nat.size enc.denominator +
        4 * t * n * Nat.size (n + 1)) := by
    calc
      encOut.denominator ≤ enc.denominator *
          (2 ^ (4 * n * Nat.size (n + 1))) ^ t := hden
      _ ≤ 2 ^ Nat.size enc.denominator *
          (2 ^ (4 * n * Nat.size (n + 1))) ^ t :=
        Nat.mul_le_mul_right _ henc
      _ = 2 ^ (Nat.size enc.denominator +
          4 * t * n * Nat.size (n + 1)) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        ring
  have hlt : encOut.denominator <
      2 ^ (Nat.size enc.denominator +
        4 * t * n * Nat.size (n + 1) + 1) := by
    exact hupper.trans_lt
      (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))
  exact (Nat.size_le).mpr hlt

theorem eliminationTrace_mass_positive {α : Type*}
    (n : Nat) (φ : α → Fin n → ℚ)
    (source out : Array (α × ℚ)) (t : Nat)
    (htrace : EliminationTrace n φ t source out)
    (hpos : SourcePositive source)
    (hmass : sourceMass source = 1) :
    SourcePositive out ∧ sourceMass out = 1 := by
  induction htrace with
  | refl source => exact ⟨hpos, hmass⟩
  | step source next out f t hfree hstep hrest ih =>
      have hpnext :=
        compressSourceOnceMaterialized_positive n φ source next hstep
      have hmnext :=
        (compressSourceOnceMaterialized_moments n φ source next hstep).1
      exact ih hpnext (hmnext ▸ hmass)

/-- Every traced intermediate rational weight has both numerator and
denominator bounded by the same explicit binary budget. -/
theorem eliminationTrace_weight_bits {α : Type*}
    (n : Nat) (φ : α → Fin n → ℚ)
    (hn : 0 < n)
    (hφ : ∀ x j, φ x j = 0 ∨ φ x j = 1)
    (source out : Array (α × ℚ)) (t : Nat)
    (htrace : EliminationTrace n φ t source out)
    (hpos : SourcePositive source)
    (hmass : sourceMass source = 1)
    (enc : CommonDenominator (fun i : Fin source.size => source[i].2)) :
    ∃ encOut : CommonDenominator (fun i : Fin out.size => out[i].2),
      Nat.size encOut.denominator ≤ Nat.size enc.denominator +
        4 * t * n * Nat.size (n + 1) + 1 ∧
      ∀ i : Fin out.size,
        Nat.size (encOut.numerator i).natAbs ≤
          Nat.size encOut.denominator := by
  obtain ⟨encOut, hbits⟩ :=
    eliminationTrace_denominator_bits n φ hn hφ source out t htrace enc
  obtain ⟨hpositive, hmassOut⟩ :=
    eliminationTrace_mass_positive n φ source out t htrace hpos hmass
  refine ⟨encOut, hbits, ?_⟩
  intro i
  have hnonneg : ∀ j : Fin out.size, 0 ≤ out[j].2 := by
    intro j
    have hj := (Array.all_eq_true.mp hpositive) j.val j.isLt
    have hj' : 0 < out[j].2 := by
      simpa [SourcePositive] using hj
    exact le_of_lt hj'
  have hle : out[i].2 ≤ 1 := by
    have hsingle := Finset.single_le_sum
      (s := Finset.univ) (f := fun j : Fin out.size => out[j].2)
      (by intro j hj; exact hnonneg j) (Finset.mem_univ i)
    rw [sourceMass_eq_sum_fin] at hmassOut
    have hsingle' : out[i].2 ≤
        ∑ j : Fin out.size, out[j].2 := by simpa using hsingle
    exact hsingle'.trans_eq hmassOut
  exact numerator_bits_le_denominator encOut i (hnonneg i) hle

theorem sequentialIndependent_size_le_features_all {Y : Type*}
    [DecidableEq Y] (D : Nat) (alphabet : Array (Y × ℚ))
    (q : Nat) (out : Array ((Fin q → Y) × ℚ))
    (h : sequentialIndependent D alphabet q = some out) :
    out.size ≤ (generatedFeatures q D (alphabet.map Prod.fst)).size := by
  cases q with
  | zero =>
      simp [sequentialIndependent] at h
      cases h
      simp [generatedFeatures]
  | succ q =>
      exact sequentialIndependent_size_le_features D alphabet q out h

private theorem generatedFeatures_size_le {Y : Type*}
    (t q D : Nat) (alphabet : Array Y) (ht : t ≤ q) :
    (generatedFeatures t D alphabet).size ≤
      (generatedFeatures q D alphabet).size := by
  induction q with
  | zero =>
      have : t = 0 := by omega
      subst t
      rfl
  | succ q ih =>
      by_cases h : t ≤ q
      · exact (ih h).trans (generatedFeatures_size_mono q D alphabet)
      · have : t = q + 1 := by omega
        subst t
        rfl

/-- The literal independence loop has the same polynomial-order
intermediate denominator budget as the old size-threshold loop. The bound
uses the already checked Gram/minor coefficients, not the manuscript's
numerically sharper Hadamard constant. -/
theorem sequentialIndependent_denominator_bounded {Y : Type*}
    [DecidableEq Y] (D : Nat) (alphabet : Array (Y × ℚ))
    (ea : CommonDenominator
      (fun j : Fin alphabet.size => alphabet[j].2))
    (Q M : Nat)
    (hM : ∀ t, t ≤ Q →
      (generatedFeatures t D (alphabet.map Prod.fst)).size ≤ M) :
    ∀ q (_hq : q ≤ Q) (out : Array ((Fin q → Y) × ℚ)),
      sequentialIndependent D alphabet q = some out →
      ∃ enc : CommonDenominator (fun i : Fin out.size => out[i].2),
        enc.denominator ≤ ea.denominator ^ q *
          (2 ^ (4 * M * Nat.size (M + 1))) ^
            (q * alphabet.size * M) := by
  intro q
  induction q with
  | zero =>
      intro _ out hrun
      let base : Array ((Fin 0 → Y) × ℚ) :=
        #[(fun i : Fin 0 => Fin.elim0 i, (1 : ℚ))]
      change some base = some out at hrun
      have hout : out = base := (Option.some.inj hrun).symm
      subst out
      let enc0 : CommonDenominator
          (fun i : Fin base.size => base[i].2) :=
        { denominator := 1
          positive := by decide
          numerator := fun _ => 1
          represents := by
            intro i
            fin_cases i
            simp [base] }
      exact ⟨enc0, by simp [enc0]⟩
  | succ q ih =>
      intro hq out hrun
      let F := generatedFeatures (q + 1) D (alphabet.map Prod.fst)
      let n := F.size
      let φ : (Fin (q + 1) → Y) → Fin n → ℚ :=
        fun v j => generatedFeatureValue v F[j]
      simp only [sequentialIndependent] at hrun
      cases hprev : sequentialIndependent D alphabet q with
      | none => simp [hprev] at hrun
      | some prev =>
          simp [hprev] at hrun
          let extended := appendSource prev alphabet
          change compressUntilIndependent n φ extended extended.size = some out at hrun
          obtain ⟨encPrev, hprevBound⟩ := ih (by omega) prev hprev
          let encExtended :=
            appendSource_commonDenominator prev alphabet encPrev ea
          have hn : 0 < n := by
            simpa [n, F] using
              generatedFeatures_pos (q + 1) D (alphabet.map Prod.fst)
          have hφ : ∀ x j, φ x j = 0 ∨ φ x j = 1 := by
            intro x j
            dsimp [φ, generatedFeatureValue]
            split_ifs
            · exact Or.inr rfl
            · exact Or.inl rfl
          obtain ⟨encOut, hcompBound⟩ :=
            compressUntilIndependent_denominator n φ hn hφ
              extended out extended.size hrun encExtended
          have hnM : n ≤ M := hM (q + 1) hq
          have hprevSize :=
            sequentialIndependent_size_le_features_all D alphabet q prev hprev
          have hprevM : prev.size ≤ M :=
            hprevSize.trans (hM q (by omega))
          have hfuel : extended.size ≤ alphabet.size * M := by
            rw [appendSource_size]
            exact (Nat.mul_le_mul_right _ hprevM).trans_eq (Nat.mul_comm _ _)
          let A := 2 ^ (4 * M * Nat.size (M + 1))
          let Astep := 2 ^ (4 * n * Nat.size (n + 1))
          have hH : 4 * n * Nat.size (n + 1) ≤
              4 * M * Nat.size (M + 1) := by
            apply Nat.mul_le_mul
            · omega
            · exact Nat.size_le_size (by omega)
          have hAstep : Astep ≤ A := Nat.pow_le_pow_right (by omega) hH
          have hApow : Astep ^ extended.size ≤ A ^ (alphabet.size * M) :=
            (Nat.pow_le_pow_left hAstep _).trans
              (Nat.pow_le_pow_right (by positivity) hfuel)
          refine ⟨encOut, ?_⟩
          calc
            encOut.denominator ≤
                encExtended.denominator * Astep ^ extended.size := hcompBound
            _ ≤ (encPrev.denominator * ea.denominator) *
                  Astep ^ extended.size := by rfl
            _ ≤ ((ea.denominator ^ q * A ^ (q * alphabet.size * M)) *
                  ea.denominator) * A ^ (alphabet.size * M) := by
                exact Nat.mul_le_mul
                  (Nat.mul_le_mul_right _ hprevBound) hApow
            _ = ea.denominator ^ (q + 1) *
                  A ^ ((q + 1) * alphabet.size * M) := by
                rw [pow_succ]
                rw [show (q + 1) * alphabet.size * M =
                  q * alphabet.size * M + alphabet.size * M by ring, pow_add]
                ring

theorem sequentialIndependent_denominator_final {Y : Type*}
    [DecidableEq Y] (D : Nat) (alphabet : Array (Y × ℚ))
    (ea : CommonDenominator
      (fun j : Fin alphabet.size => alphabet[j].2))
    (q : Nat) (out : Array ((Fin q → Y) × ℚ))
    (hrun : sequentialIndependent D alphabet q = some out) :
    ∃ enc : CommonDenominator (fun i : Fin out.size => out[i].2),
      enc.denominator ≤ ea.denominator ^ q *
        (2 ^ (4 * (generatedFeatures q D (alphabet.map Prod.fst)).size *
            Nat.size ((generatedFeatures q D
              (alphabet.map Prod.fst)).size + 1))) ^
          (q * alphabet.size *
            (generatedFeatures q D (alphabet.map Prod.fst)).size) := by
  exact sequentialIndependent_denominator_bounded D alphabet ea q
    (generatedFeatures q D (alphabet.map Prod.fst)).size
    (by intro t ht; exact generatedFeatures_size_le t q D _ ht)
    q (le_refl q) out hrun

/-- Explicit polynomial-order binary length for a shared denominator of
all final weights of the new independence-terminating constructor. -/
theorem sequentialIndependent_denominator_bits {Y : Type*}
    [DecidableEq Y] (D : Nat) (alphabet : Array (Y × ℚ))
    (ea : CommonDenominator
      (fun j : Fin alphabet.size => alphabet[j].2))
    (q : Nat) (out : Array ((Fin q → Y) × ℚ))
    (hrun : sequentialIndependent D alphabet q = some out) :
    ∃ enc : CommonDenominator (fun i : Fin out.size => out[i].2),
      Nat.size enc.denominator ≤
        q * Nat.size ea.denominator +
        4 * q * alphabet.size *
          (generatedFeatures q D (alphabet.map Prod.fst)).size ^ 2 *
          Nat.size ((generatedFeatures q D
            (alphabet.map Prod.fst)).size + 1) + 1 := by
  let M := (generatedFeatures q D (alphabet.map Prod.fst)).size
  obtain ⟨enc, henc⟩ :=
    sequentialIndependent_denominator_final D alphabet ea q out hrun
  refine ⟨enc, ?_⟩
  have hB : ea.denominator ≤ 2 ^ Nat.size ea.denominator :=
    le_of_lt (Nat.lt_size_self _)
  have hpow : ea.denominator ^ q ≤
      2 ^ (q * Nat.size ea.denominator) := by
    rw [mul_comm, pow_mul]
    exact Nat.pow_le_pow_left hB _
  have hupper : enc.denominator ≤
      2 ^ (q * Nat.size ea.denominator +
        4 * q * alphabet.size * M ^ 2 * Nat.size (M + 1)) := by
    calc
      enc.denominator ≤ ea.denominator ^ q *
          (2 ^ (4 * M * Nat.size (M + 1))) ^
            (q * alphabet.size * M) := by simpa [M] using henc
      _ ≤ 2 ^ (q * Nat.size ea.denominator) *
          (2 ^ (4 * M * Nat.size (M + 1))) ^
            (q * alphabet.size * M) :=
        Nat.mul_le_mul_right _ hpow
      _ = 2 ^ (q * Nat.size ea.denominator +
          4 * q * alphabet.size * M ^ 2 * Nat.size (M + 1)) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        ring
  have hb : enc.denominator <
      2 ^ (q * Nat.size ea.denominator +
        4 * q * alphabet.size * M ^ 2 * Nat.size (M + 1) + 1) := by
    calc
      enc.denominator ≤ 2 ^ (q * Nat.size ea.denominator +
          4 * q * alphabet.size * M ^ 2 * Nat.size (M + 1)) := hupper
      _ < 2 ^ (q * Nat.size ea.denominator +
          4 * q * alphabet.size * M ^ 2 * Nat.size (M + 1) + 1) := by
        exact Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _)
  have hbits := (Nat.size_le).mpr hb
  simpa [M, pow_two, mul_assoc] using hbits

/-- For a positive normalized input law, each output probability lies in
`[0,1]`. Its integer numerator therefore fits the same binary budget as
the checked common denominator. -/
theorem sequentialIndependent_numerator_bits {Y : Type*}
    [DecidableEq Y] (D : Nat) (alphabet : Array (Y × ℚ))
    (halphabetPositive : SourcePositive alphabet)
    (halphabetMass : sourceMass alphabet = 1)
    (ea : CommonDenominator
      (fun j : Fin alphabet.size => alphabet[j].2))
    (q : Nat) (out : Array ((Fin q → Y) × ℚ))
    (hrun : sequentialIndependent D alphabet q = some out) :
    ∃ enc : CommonDenominator (fun i : Fin out.size => out[i].2),
      Nat.size enc.denominator ≤
        q * Nat.size ea.denominator +
        4 * q * alphabet.size *
          (generatedFeatures q D (alphabet.map Prod.fst)).size ^ 2 *
          Nat.size ((generatedFeatures q D
            (alphabet.map Prod.fst)).size + 1) + 1 ∧
      ∀ i : Fin out.size,
        Nat.size (enc.numerator i).natAbs ≤ Nat.size enc.denominator := by
  obtain ⟨enc, hbits⟩ :=
    sequentialIndependent_denominator_bits D alphabet ea q out hrun
  obtain ⟨out', hout', hpos'⟩ :=
    sequentialIndependent_total D alphabet halphabetPositive q
  rw [hrun] at hout'
  have hpos : SourcePositive out := by
    cases Option.some.inj hout'
    exact hpos'
  have hmass : sourceMass out = 1 :=
    sequentialIndependent_mass D alphabet halphabetMass q out hrun
  refine ⟨enc, hbits, ?_⟩
  intro i
  have hpositive : ∀ j : Fin out.size, 0 ≤ out[j].2 := by
    intro j
    have hj := (Array.all_eq_true.mp hpos) j.val j.isLt
    have hj' : 0 < out[j].2 := by
      simpa [SourcePositive] using hj
    exact le_of_lt hj'
  have hle : out[i].2 ≤ 1 := by
    have hsingle := Finset.single_le_sum
      (s := Finset.univ) (f := fun j : Fin out.size => out[j].2)
      (by intro j hj; exact hpositive j) (Finset.mem_univ i)
    rw [sourceMass_eq_sum_fin] at hmass
    have hsingle' : out[i].2 ≤
        ∑ j : Fin out.size, out[j].2 := by simpa using hsingle
    exact hsingle'.trans_eq hmass
  exact numerator_bits_le_denominator enc i (hpositive i) hle

/-- The actual first-free-column relation has a bounded integer scaling and
vanishes away from that free column and the recorded pivot columns. This
records the basis-plus-one shape with the checked Gram bound; the sharper
Hadamard coefficient bound in the manuscript remains separate. -/
theorem materialized_integer_basis_plus_one {m k : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (hzeroOne : ∀ i j, A i j = 0 ∨ A i j = 1)
    (x : Fin k → ℚ)
    (hx : dependenceMaterialized (fun i j => (A i j : ℚ)) = some x) :
    let out := echelonTyped (fun i j => (A i j : ℚ)) 0 0 k
    ∃ (f : Fin k) (D : Nat) (coeff : Fin k → ℤ),
      typedFree out.2 = some f ∧
      0 < D ∧ D ≤ (m.factorial * m ^ m) ^ 2 ∧
      (∀ j, (coeff j).natAbs ≤ (m.factorial * m ^ m) ^ 2) ∧
      (∀ j, x j = (coeff j : ℚ) / (D : ℚ)) ∧
      (∀ j, j ≠ f → j ∉ out.2.map Prod.snd → coeff j = 0) := by
  let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
  let out := echelonTyped Aq 0 0 k
  have hxorig := hx
  rw [dependenceMaterialized_eq] at hx
  change (typedFree out.2).map (typedCandidate out.1 out.2) = some x at hx
  cases hf : typedFree out.2 with
  | none => simp [hf] at hx
  | some f =>
      have hxval : x = typedCandidate out.1 out.2 f := by
        simpa [hf] using hx.symm
      obtain ⟨D, coeff, hD, hDB, hcoeff, hrep⟩ :=
        materialized_dependence_shared A hzeroOne x
          hxorig
      refine ⟨f, D, coeff, hf, hD, hDB, hcoeff, hrep, ?_⟩
      intro j hjf hjp
      have hxzero : x j = 0 := by
        rw [hxval]
        exact typedCandidate_support_basis_plus_one out.1 out.2 f j hjf hjp
      have hq : (coeff j : ℚ) / (D : ℚ) = 0 := by
        rw [← hrep j]
        exact hxzero
      have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
      have hcq : (coeff j : ℚ) = 0 := by
        exact (div_eq_zero_iff).mp hq |>.resolve_right hDq
      exact_mod_cast hcq

#print axioms compressUntilIndependent_denominator
#print axioms eliminationTrace_denominator
#print axioms compressUntilIndependent_trace
#print axioms eliminationTrace_weight_bits
#print axioms sequentialIndependent_denominator_bounded
#print axioms sequentialIndependent_denominator_bits
#print axioms sequentialIndependent_numerator_bits
#print axioms materialized_integer_basis_plus_one

end CurrentAdditive.IntegerBitSupport
