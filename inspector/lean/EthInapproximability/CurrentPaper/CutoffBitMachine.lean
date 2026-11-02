import EthInapproximability.CurrentPaper.CutoffBitMachineCore
import EthInapproximability.CurrentPaper.CutoffOutputDecoder
import EthInapproximability.CurrentPaper.CutoffInputEncoding
import EthInapproximability.CurrentPaper.BG34Canon
import EthInapproximability.CurrentPaper.BitMachineComposition

/-!
# Private strengthened physical cutoff selection

This candidate replaces only the selection after the old core's generic
clock lemmas. The chosen machine itself is total on every physical bitstring.
All downstream public names and their integer-input interfaces are retained.
The inherited core and helpers are private copies, not production edits.
-/

namespace EthInapproximability.CurrentPaper.CutoffBitMachine

open EffectiveIteration

namespace Totalizer

theorem bitsValue_append_false (l : List Bool) (j : ℕ) :
    EncodedCommunication.bitsValue (l ++ List.replicate j false) =
      EncodedCommunication.bitsValue l := by
  induction l with
  | nil =>
      induction j with
      | zero => rfl
      | succ j ih =>
          simp only [List.nil_append, List.replicate_succ, EncodedCommunication.bitsValue] at ih ⊢
          rw [ih]; rfl
  | cons b l ih =>
      simp only [List.cons_append, EncodedCommunication.bitsValue, ih]

theorem reverse_trim_split (w : List Bool) :
    ∃ j, w = List.replicate j false ++ BitMachineTrimLeadingZeros.trim w := by
  induction w with
  | nil => exact ⟨0, rfl⟩
  | cons b w ih =>
      cases b with
      | false =>
          obtain ⟨j, hj⟩ := ih
          refine ⟨j + 1, ?_⟩
          simp only [BitMachineTrimLeadingZeros.trim, List.replicate_succ, List.cons_append]
          exact congrArg _ hj
      | true => exact ⟨0, rfl⟩

theorem bitsValue_canon (q : List Bool) :
    EncodedCommunication.bitsValue (BG34Canon.canon q) = EncodedCommunication.bitsValue q := by
  obtain ⟨j, hj⟩ := reverse_trim_split q.reverse
  have hq : q = (BitMachineTrimLeadingZeros.trim q.reverse).reverse ++ List.replicate j false := by
    have := congrArg List.reverse hj
    rw [List.reverse_reverse, List.reverse_append, List.reverse_replicate] at this
    exact this
  conv_rhs => rw [hq]
  rw [bitsValue_append_false]
  rfl

theorem canon_decoder (w : List Bool) :
    BG34Canon.canon (CutoffOutputDecoder.bits w) = (decodedNat w).bits := by
  obtain ⟨m, hm⟩ := BG34Canon.canon_canonical (CutoffOutputDecoder.bits w)
  have hv := bitsValue_canon (CutoffOutputDecoder.bits w)
  rw [hm, EncodedCommunication.bitsValue_bits, CutoffOutputDecoder.bits_value] at hv
  rw [hm, hv]

noncomputable def sanitizer : BitMachine.Machine :=
  BitMachineComposition.composition
    (BitMachineComposition.composition CutoffOutputDecoder.machine BG34Canon.machine)
    CutoffInputEncoding.machine

theorem sanitizer_outputs (w : List Bool) :
    ∃ t, sanitizer.OutputsWithin w (encodedNat (decodedNat w)) t := by
  have s1 := CutoffOutputDecoder.outputs_all w
  have s2 := BG34Canon.outputs (CutoffOutputDecoder.bits w)
  have s12 := BitMachineComposition.composition_outputsWithin _ _ s1 s2
  have s3 := CutoffInputEncoding.outputs_all (BG34Canon.canon (CutoffOutputDecoder.bits w))
  have s123 := BitMachineComposition.composition_outputsWithin _ _ s12 s3
  rw [canon_decoder, ← CutoffInputEncoding.encodedNat_eq] at s123
  exact ⟨_, s123⟩

noncomputable def totalize (M : BitMachine.Machine) : BitMachine.Machine :=
  BitMachineComposition.composition sanitizer M

theorem totalize_outputs (M : BitMachine.Machine) (c A d : ℕ)
    (hM : ∀ k, ∃ t, M.OutputsWithin (encodedNat k) (encodedNat (cutoff c A d k)) t)
    (w : List Bool) :
    ∃ t, (totalize M).OutputsWithin w (encodedNat (cutoff c A d (decodedNat w))) t := by
  obtain ⟨t1, h1⟩ := sanitizer_outputs w
  obtain ⟨t2, h2⟩ := hM (decodedNat w)
  exact ⟨_, BitMachineComposition.composition_outputsWithin _ _ h1 h2⟩

end Totalizer

/-- Strengthened witness: on every word, the SAME physical cutoff machine
halts, and on integer codes it returns the source cutoff. -/
theorem exists_cutoff_machine_total (c A d : ℕ) :
    ∃ M : BitMachine.Machine,
      (∀ w, ∃ t, M.OutputsWithin w (encodedNat (cutoff c A d (decodedNat w))) t) ∧
      (∀ k, ∃ t, M.OutputsWithin (encodedNat k) (encodedNat (cutoff c A d k)) t) := by
  obtain ⟨M, hM⟩ := exists_cutoff_machine c A d
  refine ⟨Totalizer.totalize M, Totalizer.totalize_outputs M c A d hM, ?_⟩
  intro k
  simpa only [decoded_encodedNat] using
    Totalizer.totalize_outputs M c A d hM (encodedNat k)

noncomputable def actualMachine (c A d : ℕ) : BitMachine.Machine :=
  Classical.choose (exists_cutoff_machine_total c A d)

theorem actualMachine_total (c A d : ℕ) (w : List Bool) :
    ∃ t, (actualMachine c A d).OutputsWithin w
      (encodedNat (cutoff c A d (decodedNat w))) t :=
  (Classical.choose_spec (exists_cutoff_machine_total c A d)).1 w

theorem actualMachine_outputs (c A d k : ℕ) : ∃ time,
    (actualMachine c A d).OutputsWithin (encodedNat k) (encodedNat (cutoff c A d k)) time :=
  (Classical.choose_spec (exists_cutoff_machine_total c A d)).2 k

noncomputable def actualClock (c A d : ℕ) := clock (actualMachine c A d)

theorem actualClock_terminates (c A d : ℕ) : SlowClock.Terminates (actualClock c A d) :=
  clock_terminates _ c A d (actualMachine_outputs c A d)

theorem actualClock_doubled (c A d : ℕ) : ClockedPadding.DoubledCutoffs (actualClock c A d) :=
  clock_doubled _ c A d (actualMachine_outputs c A d)

theorem actualClock_selected_cutoff (c A d n k : ℕ) (hk : 1 ≤ k)
    (hselected : k ≤ SlowClock.repetitions (actualClock c A d) n) :
    sourceCutoff c A d k ≤ n :=
  selected_cutoff _ c A d (actualMachine_outputs c A d) n k hk hselected

theorem actualClock_selected_levels
    {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : ParameterizedNP.GuardedSourceGraph.EndpointGraph V E) (c A d n k : ℕ)
    (hv : Fintype.card V ≤ 2 * Fintype.card E)
    (hlower : n ≤ Fintype.card E)
    (hupper : Fintype.card E ≤ A * n * sourceDepth n ^ d)
    (hk : 1 ≤ k) (hselected : k ≤ SlowClock.repetitions (actualClock c A d) n) :
    ∀ i < k,
      Parameters.Accepted (runParameters G c (sourceDepth n) (Iteration.seedState (sourceDepth n)) i) ∧
      2 * k * oneLevelBound
        (runParameters G c (sourceDepth n) (Iteration.seedState (sourceDepth n)) i) < n :=
  run_indexing_beyond_cutoff G c A d n k (actualClock_selected_cutoff c A d n k hk hselected)
    hv hlower hupper

theorem actualClock_allowance_unbounded (c A d : ℕ) : ∀ K, ∃ T,
    K ≤ FinalPadding.allowance (SlowClock.repetitions (actualClock c A d)) T :=
  ClockedPadding.allowance_unbounded _ (actualClock_terminates c A d)

theorem actualClock_exponent_eventually_pos (c A d : ℕ) :
    ∀ᶠ n in Filter.atTop,
      0 < FinalPadding.exponent (SlowClock.repetitions (actualClock c A d)) n :=
  ClockedPadding.exponent_eventually_pos _ (actualClock_terminates c A d) (actualClock_doubled c A d)

theorem actualClock_exponent_ratio_tendsto_zero (c A d : ℕ) :
    Filter.Tendsto
      (fun n : ℕ => (FinalPadding.exponent (SlowClock.repetitions (actualClock c A d)) n : ℝ) / n)
      Filter.atTop (nhds 0) :=
  ClockedPadding.exponent_ratio_tendsto_zero _ (actualClock_terminates c A d)

theorem actualClock_gap_fit_eventually (c A d : ℕ) :
    ∀ᶠ n in Filter.atTop,
      2 * FinalPadding.allowance (SlowClock.repetitions (actualClock c A d))
        (FinalPadding.tableSize (SlowClock.repetitions (actualClock c A d)) n) <
          SlowClock.repetitions (actualClock c A d) n :=
  ClockedPadding.gap_fit_eventually _ (actualClock_terminates c A d)

#print axioms EthInapproximability.CurrentPaper.CutoffBitMachine.actualMachine_total
#print axioms EthInapproximability.CurrentPaper.CutoffBitMachine.actualClock_terminates

end EthInapproximability.CurrentPaper.CutoffBitMachine
