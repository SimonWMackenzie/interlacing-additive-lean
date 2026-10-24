import Paper2.E2Sel
import Paper2.E2Sq
import EthInapproximability.CurrentPaper.EncodedGraph

/-! Private audit of the literal eventually-large estimator domain. This
module does not assume an all-decodable estimator. -/

noncomputable section

namespace CurrentAdditive.Eventual

open Paper2

open EthInapproximability.CurrentPaper

/-- The decoded number of table entries, zero on malformed words. -/
def entries (w : List Bool) : ℕ :=
  match AModel.decodeMatrix w with
  | some (r, c, _) => r * c
  | none => 0

/-- Literal eventual-size version of v27 `thm:quantitative`. The fixed threshold
is on table entries, not on the length of the encoded word. -/
def EstimatesGrowingEventuallySel (E : SelectedTape.Algorithm) (c : ℝ) : Prop :=
  ∃ T₀ : ℕ, ∀ w (d : ℕ), AModel.targetD w = some d → T₀ ≤ entries w →
    2 / 3 ≤ E.prob w (fun out => ∃ v, AModel.decodeDyadic out = some v ∧
      |v - d| ≤ ADecider.accT c w)

/-- Square power-of-two version of the same literal eventual-size domain. -/
def EstimatesGrowingEventuallySelSq (E : SelectedTape.Algorithm) (c : ℝ) : Prop :=
  ∃ T₀ : ℕ, ∀ w (d : ℕ), AModel.targetD w = some d →
    ADecider.SquareWord w → T₀ ≤ entries w →
    2 / 3 ≤ E.prob w (fun out => ∃ v, AModel.decodeDyadic out = some v ∧
      |v - d| ≤ ADecider.accT c w)

theorem all_domain_implies_eventual (E : SelectedTape.Algorithm) (c : ℝ)
    (h : AEth.EstimatesGrowingSel E c) : EstimatesGrowingEventuallySel E c := by
  refine ⟨0, ?_⟩
  intro w d hd _
  exact h w d hd

theorem all_square_implies_eventual (E : SelectedTape.Algorithm) (c : ℝ)
    (h : AEth2.EstimatesGrowingSelSq E c) : EstimatesGrowingEventuallySelSq E c := by
  refine ⟨0, ?_⟩
  intro w d hd hsq _
  exact h w d hd hsq

/-- A canonical matrix word below a fixed entry threshold has bounded total
length. This is the finite-exception fact that a physical patching machine
would have to exploit. -/
theorem small_entry_word_length (w : List Bool) (r c T₀ : ℕ)
    (table : List Bool) (hdec : AModel.decodeMatrix w = some (r, c, table))
    (hsmall : r * c < T₀) : w.length ≤ 5 * T₀ + 2 := by
  obtain ⟨hword, hvalid⟩ := AModel.decodeMatrix_sound hdec
  rcases hvalid with ⟨hr, hc, htable⟩
  have hrle : r ≤ r * c := Nat.le_mul_of_pos_right r hc
  have hcle : c ≤ r * c := Nat.le_mul_of_pos_left c hr
  have hfr : (EncodedCommunication.natField r).length ≤ 2 * r + 1 :=
    EncodedGraph.natField_length_upper r
  have hfc : (EncodedCommunication.natField c).length ≤ 2 * c + 1 :=
    EncodedGraph.natField_length_upper c
  calc
    w.length = (EncodedCommunication.natField r).length +
        (EncodedCommunication.natField c).length + table.length := by
      rw [← hword]
      simp [AModel.matrixWord, Nat.add_assoc]
    _ ≤ (2 * r + 1) + (2 * c + 1) + r * c := by omega
    _ ≤ 5 * T₀ + 2 := by omega

/-- The repetition count used in T24 eventually exceeds any fixed integer.
This is independent of graph data and therefore can absorb an estimator's
fixed entry-count threshold. -/
theorem kOf_eventually_ge (K : ℕ) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → K ≤ Unit4Shell.Asymptotics.kOf N := by
  let I : ℕ := max 1 K
  let Y : ℝ := max 361 (2 * Real.logb 2 I + 1)
  refine ⟨max 2 ⌈(2 : ℝ) ^ Y⌉₊, ?_⟩
  intro N hN
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hY : Y ≤ Real.logb 2 N :=
    Unit4Shell.Asymptotics.logb_ge_of_ge Y N ((le_max_right _ _).trans hN)
  have h361 : (361 : ℝ) ≤ Real.logb 2 N + 2 := by
    have := le_max_left (361 : ℝ) (2 * Real.logb 2 I + 1)
    linarith
  obtain ⟨hk1, hklog⟩ := Unit4Shell.Asymptotics.k_log_ge N (1 / 2 : ℝ)
    (by norm_num) (by norm_num) hN2 (by norm_num; exact h361)
  have hI : 1 ≤ I := le_max_left _ _
  have hIk : Real.logb 2 I ≤ Real.logb 2
      (Unit4Shell.Asymptotics.kOf N) := by
    have := le_max_right (361 : ℝ) (2 * Real.logb 2 I + 1)
    linarith
  have hIpos : (0 : ℝ) < I := by exact_mod_cast hI
  have hkpos : (0 : ℝ) < Unit4Shell.Asymptotics.kOf N := by exact_mod_cast hk1
  have hnat : I ≤ Unit4Shell.Asymptotics.kOf N := by
    exact_mod_cast (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) hIpos hkpos).mp hIk
  exact (le_max_right 1 K).trans hnat

private theorem self_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      calc
        n + 1 ≤ 2 ^ n + 2 ^ n := by omega
        _ = 2 ^ (n + 1) := by rw [pow_succ]; omega

/-- Every scheduled rectangle, independent of its public depth choices,
eventually has at least any fixed number of entries when the paper's growing
`kOf N` is used. -/
theorem generic_entries_eventually_ge (T₀ : ℕ) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ L r q : ℕ, 1 ≤ L →
      T₀ ≤ SourceRecursiveNoSampling.sourceRows L r q
          (Unit4Shell.Asymptotics.kOf N) *
        SourceRecursiveNoSampling.sourceCols L r q
          (Unit4Shell.Asymptotics.kOf N) := by
  obtain ⟨N₀, hN₀⟩ := kOf_eventually_ge T₀
  refine ⟨N₀, ?_⟩
  intro N hN L r q hL
  have hk := hN₀ N hN
  have hpow : 2 ^ T₀ ≤ 2 ^ Unit4Shell.Asymptotics.kOf N :=
    Nat.pow_le_pow_right (by decide) hk
  exact (self_le_two_pow T₀).trans (hpow.trans
    (Unit4Shell.Asymptotics.two_pow_le_entries L r q
      (Unit4Shell.Asymptotics.kOf N) hL))

/-- The exact rectangular count printed by the old T24 source eventually
passes any fixed entry threshold. The lower bound does not depend on its
particular (v12) public depth schedule. -/
theorem printedT_eventually_ge (T₀ : ℕ) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ n m Δ : ℕ, ∀ γ : ℚ, 2 ≤ n →
      T₀ ≤ Unit4Shell.Asymptotics.printedT n m Δ γ
        (Unit4Shell.Asymptotics.kOf N) := by
  obtain ⟨N₀, hN₀⟩ := generic_entries_eventually_ge T₀
  refine ⟨N₀, ?_⟩
  intro N hN n m Δ γ hn
  have hL : 1 ≤ Nat.clog 2 n :=
    Nat.succ_le_of_lt (Nat.clog_pos (by decide) (by omega))
  exact hN₀ N hN (Nat.clog 2 n)
    (Paper2.ParameterizedCanonicalSource.restorationDepth (Nat.clog 2 n))
    (Paper2.ParameterizedCanonicalSource.coverDepth n m (Nat.clog 2 n) Δ γ)
    hL

theorem printedTsq_eventually_ge (T₀ : ℕ) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ n m Δ : ℕ, ∀ γ : ℚ, 2 ≤ n →
      T₀ ≤ Unit4Shell.Asymptotics.printedTsq n m Δ γ
        (Unit4Shell.Asymptotics.kOf N) := by
  obtain ⟨N₀, hN₀⟩ := kOf_eventually_ge T₀
  refine ⟨N₀, ?_⟩
  intro N hN n m Δ γ hn
  have hL : 1 ≤ Nat.clog 2 n :=
    Nat.succ_le_of_lt (Nat.clog_pos (by decide) (by omega))
  have hpow : 2 ^ T₀ ≤ 2 ^ Unit4Shell.Asymptotics.kOf N :=
    Nat.pow_le_pow_right (by decide) (hN₀ N hN)
  exact (self_le_two_pow T₀).trans (hpow.trans
    (Unit4Shell.Asymptotics.square_log_bounds n m Δ γ
      (Unit4Shell.Asymptotics.kOf N) hL).2)

theorem entries_matrixWord (r c : ℕ) (table : List Bool)
    (h : AModel.MatrixValid r c table) :
    entries (AModel.matrixWord r c table) = r * c := by
  unfold entries
  rw [AModel.decodeMatrix_matrixWord h]


#print axioms all_domain_implies_eventual
#print axioms all_square_implies_eventual
#print axioms small_entry_word_length
#print axioms kOf_eventually_ge
#print axioms generic_entries_eventually_ge
#print axioms printedT_eventually_ge
#print axioms printedTsq_eventually_ge
#print axioms entries_matrixWord

end CurrentAdditive.Eventual
