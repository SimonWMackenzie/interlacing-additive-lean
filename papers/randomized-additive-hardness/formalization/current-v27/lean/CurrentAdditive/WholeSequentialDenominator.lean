import CurrentAdditive.SequentialDenominator
import CurrentAdditive.SequentialSourceResource

set_option maxHeartbeats 1000000

namespace CurrentAdditive.RationalCandidateCompletion

open CurrentAdditive.SequentialCode
open CurrentAdditive.SequentialSourceCode
open CurrentAdditive.SequentialSourceResource
open CurrentAdditive.RationalBitBounds

/-- A fixed feature cap M for all stages through Q gives the exact displayed
manuscript-scale common-denominator recurrence for the successful literal
sequential constructor. The alphabet law contributes one factor per stage;
the support reductions contribute at most Q·m·M factors. -/
theorem sequentialMaterialized_denominator_bounded {Y : Type*}
    [DecidableEq Y] (D : Nat) (alphabet : Array (Y × ℚ))
    (ea : CommonDenominator
      (fun j : Fin alphabet.size => alphabet[j].2))
    (Q M : Nat)
    (hM : ∀ t, t ≤ Q →
      (generatedFeatures t D (alphabet.map Prod.fst)).size ≤ M) :
    ∀ q (hq : q ≤ Q) (out : Array ((Fin q → Y) × ℚ)),
      sequentialMaterialized D alphabet q = some out →
      ∃ enc : CommonDenominator (fun i : Fin out.size => out[i].2),
        enc.denominator ≤ ea.denominator ^ q *
          (2 ^ (4 * M * Nat.size (M + 1))) ^
            (q * alphabet.size * M) := by
  intro q
  induction q with
  | zero =>
      intro _hq out hrun
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
      simp only [sequentialMaterialized] at hrun
      cases hprev : sequentialMaterialized D alphabet q with
      | none => simp [hprev] at hrun
      | some prev =>
          simp [hprev] at hrun
          let extended := appendSource prev alphabet
          change compressSourceFuelMaterialized n φ extended extended.size = some out at hrun
          cases hcomp : compressSourceFuelMaterialized n φ extended extended.size with
          | none => rw [hcomp] at hrun; cases hrun
          | some stageOut =>
              have hout : out = stageOut := by
                rw [hcomp] at hrun
                exact (Option.some.inj hrun).symm
              subst out
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
                compressSourceFuel_denominator n φ hn hφ
                  extended.size extended stageOut hcomp encExtended
              have hnM : n ≤ M := by
                exact hM (q + 1) hq
              have hprevSize :=
                sequentialMaterialized_size_le_features_all D alphabet q prev hprev
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
                      Astep ^ extended.size := by
                    rfl
                _ ≤ ((ea.denominator ^ q * A ^ (q * alphabet.size * M)) *
                      ea.denominator) * A ^ (alphabet.size * M) := by
                    exact Nat.mul_le_mul
                      (Nat.mul_le_mul_right _ hprevBound) hApow
                _ = ea.denominator ^ (q + 1) *
                      A ^ ((q + 1) * alphabet.size * M) := by
                    rw [pow_succ]
                    rw [show (q + 1) * alphabet.size * M =
                      q * alphabet.size * M + alphabet.size * M by ring,
                      pow_add]
                    ring

#print axioms sequentialMaterialized_denominator_bounded

end CurrentAdditive.RationalCandidateCompletion
