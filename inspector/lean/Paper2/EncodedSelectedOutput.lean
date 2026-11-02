import Paper2.TotalFiniteConstructor
import EthInapproximability.CurrentPaper.EncodedCommunication

/-!
Literal binary output format for the v12 uniform reduction. Reuses only the
existing explicit communication-instance codec, not another paper's hardness
theorem. Encoding/list correctness is separate from machine running time.
-/

namespace Paper2.EncodedSelectedOutput

open YaoMaterialization TotalFiniteConstructorScratch
open EthInapproximability.CurrentPaper
open Workspace.Types.CommComplexity

theorem tableGame_eq_matrix {r c : ℕ} (T : SerializedTable r c) :
    ProtocolVerifier.tableGame r c T.bits = T.matrix := by
  funext i j
  have hb : i.val * c + j.val < T.bits.length := by
    rw [T.length]
    have := (rowMajorIndex i j).isLt
    simpa only [rowMajorIndex_value] using this
  simp only [ProtocolVerifier.tableGame, ProtocolVerifier.tableEntry,
    List.getElem?_eq_getElem hb, Option.getD_some,
    SerializedTable.matrix, List.get_eq_getElem, Fin.val_cast,
    rowMajorIndex_value]

def instanceOf {r c : ℕ} (T : SerializedTable r c) (budget : ℕ) :
    EncodedCommunication.Instance := ⟨r, c, budget, T.bits⟩

theorem instanceOf_valid {r c : ℕ} (T : SerializedTable r c) (budget : ℕ)
    (hr : 0 < r) (hc : 0 < c) : (instanceOf T budget).Valid :=
  ⟨hr, hc, T.length⟩

theorem encode_instance_language_iff {r c : ℕ}
    (T : SerializedTable r c) (budget : ℕ) (hr : 0 < r) (hc : 0 < c) :
    EncodedCommunication.encodeInstance (instanceOf T budget) ∈
      EncodedCommunication.Language ↔ D T.matrix ≤ budget := by
  have hd := EncodedCommunication.decode_encode (instanceOf T budget)
    (instanceOf_valid T budget hr hc)
  constructor
  · rintro ⟨i, hi, hcost⟩
    rw [hd] at hi
    cases Option.some.inj hi
    simpa only [instanceOf, tableGame_eq_matrix] using hcost
  · intro hcost
    refine ⟨instanceOf T budget, hd, ?_⟩
    simpa only [instanceOf, tableGame_eq_matrix] using hcost

theorem selected_dimensions_pos {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ) :
    0 < (select hn edge Δ γ k).rows ∧
    0 < (select hn edge Δ γ k).cols := by
  by_cases hc : CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) (Nat.clog 2 n) Δ γ
  · rw [select_good hn edge Δ γ k hc]
    have hL : 1 ≤ Nat.clog 2 n := by
      rcases hc with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, hL, _⟩
      omega
    constructor
    · exact compressionRowDraws_pos _ _ hL
    · change 0 < 2 * (_ + 12)
      omega
  · rw [select_bad hn edge Δ γ k hc]
    change 0 < FiniteFallbackOutput.rows k ∧ 0 < FiniteFallbackOutput.cols k
    cases k with
    | zero => decide
    | succ k =>
      cases k with
      | zero => decide
      | succ k =>
        simp only [FiniteFallbackOutput.rows, FiniteFallbackOutput.cols]
        constructor <;> positivity

def selectedInstance {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (t : (select hn edge Δ γ k).Tape) : EncodedCommunication.Instance :=
  instanceOf ((select hn edge Δ γ k).table t) (select hn edge Δ γ k).budget

def outputBits {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (t : (select hn edge Δ γ k).Tape) : List Bool :=
  EncodedCommunication.encodeInstance (selectedInstance hn edge Δ γ k t)

theorem decode_outputBits {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (t : (select hn edge Δ γ k).Tape) :
    EncodedCommunication.decodeInstance (outputBits hn edge Δ γ k t) =
      some (selectedInstance hn edge Δ γ k t) := by
  have hp := selected_dimensions_pos hn edge Δ γ k
  exact EncodedCommunication.decode_encode _ (instanceOf_valid _ _ hp.1 hp.2)

theorem outputBits_language_iff {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (t : (select hn edge Δ γ k).Tape) :
    outputBits hn edge Δ γ k t ∈ EncodedCommunication.Language ↔
      D ((select hn edge Δ γ k).table t).matrix ≤ (select hn edge Δ γ k).budget := by
  have hp := selected_dimensions_pos hn edge Δ γ k
  exact encode_instance_language_iff _ _ hp.1 hp.2

theorem outputBits_length {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (t : (select hn edge Δ γ k).Tape) :
    let o := select hn edge Δ γ k
    (outputBits hn edge Δ γ k t).length =
      2 * (o.rows.bits.length + o.cols.bits.length + o.budget.bits.length) +
        3 + o.rows * o.cols := by
  rw [outputBits, EncodedCommunication.encodeInstance_length]
  simp only [selectedInstance, instanceOf, SerializedTable.length]

theorem every_yes_output_language {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (loopless : ∀ e, edge e false ≠ edge e true)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hm : 0 < m)
    (hcolour : FiniteFallbackOutput.ThreeColourable edge)
    (t : (select hn edge Δ γ k).Tape) :
    outputBits hn edge Δ γ k t ∈ EncodedCommunication.Language := by
  exact (outputBits_language_iff hn edge Δ γ k t).mpr
    (selected_yes_cost_le hn edge Δ γ k loopless hdegree hγ hΔ hm hcolour t)

theorem exact_gap_output_not_language {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hk : 1 ≤ k) (t : (select hn edge Δ γ k).Tape)
    (hcost : D ((select hn edge Δ γ k).table t).matrix =
      (select hn edge Δ γ k).budget + k) :
    outputBits hn edge Δ γ k t ∉ EncodedCommunication.Language := by
  rw [outputBits_language_iff, hcost]
  omega

noncomputable def noLanguageProbability {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ) : ℝ := by
  let e := experiment hn edge Δ γ k
  letI := e.tapeFintype
  exact e.tapeLaw.prob (fun t => EncodedCommunication.encodeInstance
    (instanceOf (e.output.table t) e.output.budget) ∉ EncodedCommunication.Language)

theorem successProbability_le_noLanguageProbability {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hk : 1 ≤ k) :
    successProbability hn edge Δ γ k ≤ noLanguageProbability hn edge Δ γ k := by
  let e := experiment hn edge Δ γ k
  letI := e.tapeFintype
  have hp : 0 < e.output.rows ∧ 0 < e.output.cols := by
    dsimp only [e]
    rw [experiment_output_eq_select]
    exact selected_dimensions_pos hn edge Δ γ k
  change e.tapeLaw.prob (fun t => D (e.output.table t).matrix = e.output.budget + k) ≤
    e.tapeLaw.prob (fun t => EncodedCommunication.encodeInstance
      (instanceOf (e.output.table t) e.output.budget) ∉ EncodedCommunication.Language)
  apply FiniteLaw.prob_mono
  intro t ht
  rw [encode_instance_language_iff _ _ hp.1 hp.2, ht]
  omega

theorem positive_gap_noLanguageProbability {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hk : 1 ≤ k)
    (loopless : ∀ e, edge e false ≠ edge e true)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hm : 0 < m)
    (gap : ∀ colour : Fin n → Fin 3, (γ : ℝ) * m ≤
      ((Finset.univ.filter (fun e => colour (edge e false) =
        colour (edge e true))).card : ℝ)) :
    1 - (1 / 2 : ℝ) ^ 11 ≤ noLanguageProbability hn edge Δ γ k :=
  (selected_no_success hn edge Δ γ k hk loopless hdegree hγ hΔ hm gap).trans
    (successProbability_le_noLanguageProbability hn edge Δ γ k hk)

end Paper2.EncodedSelectedOutput
