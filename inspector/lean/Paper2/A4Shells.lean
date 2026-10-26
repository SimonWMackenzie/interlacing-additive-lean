import Paper2.A4T10Finite
import Paper2.A4Amplification
import EthInapproximability.CurrentPaper.BitMachineBankCodec
import EthInapproximability.CurrentPaper.EncodedComplexity
import EthInapproximability.CurrentPaper.BitMachineComposition

/-!
# Unit 4 (Paper A), segment A4-S10: HYP composition shells

Owner lane `owner:a-unit4-shell` (private, 25 September 2026).

**An HYP shell is never an endpoint closure. None of these statements closes a ledger row**
(T01, T02, T24 stay open). Every upstream input is a NAMED hypothesis:

* `H_A3 Δ γ` — unit 3's endpoint in the map's absolute-exponent form (06-reduction.tex:30-31
  "an absolute exponent independent of k"): one fixed machine `MA` and absolute `CA, EA` such
  that on the bank `![graph bytes, unary k, tape bits]` it prints exactly
  `EncodedSelectedOutput.outputBits … t` within `CA·(n+2)^(EA·(k+1))`. The input layout is the
  map's proposal; unit 3 fixes the literal layout.
* `H_T10Front D B k` — the charged glue from `pair (encode Φ) tape` to that bank for the T10 graph
  (front packetizer + A4-S3 `T10Machine.chain` + bank assembly; not yet built).
* `H_T10Size D B` — polynomial vertex count of the T10 graph in `|encode Φ|` (follows from the
  record size fields; not yet proved).
* The cited records `D` (X03) and `B` (X04) are parameters (D-A7 is the author's).

The shells use the `select` tape law (D-A1-neutral) and the banked finite guarantees.
-/

namespace Paper2.Unit4Shell.Shells

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2.Unit4Shell.T10Finite

/-- HYP interface H-A3 (unit-3 endpoint; absolute `CA`, `EA`). -/
def H_A3 (Δ : ℕ) (γ : ℚ) : Prop :=
  ∃ (MA : BitMachine.Machine) (CA EA : ℕ),
    ∀ (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices) (k : ℕ), 1 ≤ k →
      (∀ v, ∃ e b, CanonicalEdgeTape.graphEdge g hg e b = v) →
      (∀ v, SourceItems.degree (CanonicalEdgeTape.graphEdge g hg) v ≤ Δ) →
      ∀ t : (TotalFiniteConstructorScratch.select hn
          (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape,
        MA.OutputsWithin
          (BitMachineBankCodec.encode ![EncodedGraph.encode g, List.replicate k true,
            (TotalFiniteConstructorScratch.select hn
              (CanonicalEdgeTape.graphEdge g hg) Δ γ k).tapeBits t])
          (EncodedSelectedOutput.outputBits hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k t)
          (CA * (g.vertices + 2) ^ (EA * (k + 1)))

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-- HYP interface: charged front glue for fixed `k`. -/
def H_T10Front (k : ℕ) : Prop :=
  ∃ (MF : BitMachine.Machine) (CF EF : ℕ), ∀ (Φ : ValidFormula) (t : (TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ) (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound (sourceGap D B) k).Tape),
    MF.OutputsWithin (EncodedComplexity.pair (EncodedCNF.encode Φ.val) ((TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ) (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound (sourceGap D B) k).tapeBits t))
      (BitMachineBankCodec.encode ![EncodedGraph.encode (t10Graph D B Φ), List.replicate k true,
        (TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ) (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound (sourceGap D B) k).tapeBits t])
      (CF * ((EncodedComplexity.pair (EncodedCNF.encode Φ.val)
        ((TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ) (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound (sourceGap D B) k).tapeBits t)).length + 1) ^ EF)

/-- HYP interface: polynomial size of the T10 graph. -/
def H_T10Size : Prop :=
  ∃ CS ES : ℕ, ∀ Φ : ValidFormula,
    (t10Graph D B Φ).vertices + 2 ≤ CS * ((EncodedCNF.encode Φ.val).length + 1) ^ ES

private theorem pow_mono_base {a b e : ℕ} (h : a ≤ b) : a ^ e ≤ b ^ e := Nat.pow_le_pow_left h e

private theorem pow_le_pow_of_le {x a b : ℕ} (h : a ≤ b) : (x + 1) ^ a ≤ (x + 1) ^ b :=
  Nat.pow_le_pow_right (Nat.succ_pos x) h

/-- Pure arithmetic of the composed clock. -/
private theorem budget (x y m V CF EF pb CA CS ES EA k : ℕ)
    (hxy : y ≤ x) (hm : m ≤ x + CF * (x + 1) ^ EF * pb)
    (hV : V + 2 ≤ CS * (y + 1) ^ ES) :
    CF * (x + 1) ^ EF + 2 * m + 2 + CA * (V + 2) ^ (EA * (k + 1)) ≤
      (CF + 2 * (1 + CF * pb) + 2 + CA * CS ^ (EA * (k + 1))) *
        (x + 1) ^ (EF + ES * (EA * (k + 1)) + 1) := by
  set E := EF + ES * (EA * (k + 1)) + 1
  have hP1 : (x + 1) ^ EF ≤ (x + 1) ^ E := pow_le_pow_of_le (by omega)
  have hPx : x + 1 ≤ (x + 1) ^ E := by
    calc x + 1 = (x + 1) ^ 1 := (pow_one _).symm
      _ ≤ (x + 1) ^ E := pow_le_pow_of_le (by omega)
  have hV' : V + 2 ≤ CS * (x + 1) ^ ES :=
    hV.trans (Nat.mul_le_mul_left _ (pow_mono_base (by omega)))
  have hVpow : (V + 2) ^ (EA * (k + 1)) ≤ CS ^ (EA * (k + 1)) * (x + 1) ^ E := by
    calc (V + 2) ^ (EA * (k + 1))
        ≤ (CS * (x + 1) ^ ES) ^ (EA * (k + 1)) := pow_mono_base hV'
      _ = CS ^ (EA * (k + 1)) * (x + 1) ^ (ES * (EA * (k + 1))) := by
        rw [mul_pow, ← pow_mul]
      _ ≤ CS ^ (EA * (k + 1)) * (x + 1) ^ E :=
        Nat.mul_le_mul_left _ (pow_le_pow_of_le (by omega))
  have hF' : CF * (x + 1) ^ EF ≤ CF * (x + 1) ^ E := Nat.mul_le_mul_left _ hP1
  have hFpb : CF * (x + 1) ^ EF * pb ≤ CF * pb * (x + 1) ^ E := by
    have := Nat.mul_le_mul_right pb hF'
    calc CF * (x + 1) ^ EF * pb ≤ CF * (x + 1) ^ E * pb := this
      _ = CF * pb * (x + 1) ^ E := by ring
  have hm' : m ≤ (1 + CF * pb) * (x + 1) ^ E := by
    calc m ≤ x + CF * (x + 1) ^ EF * pb := hm
      _ ≤ (x + 1) ^ E + CF * pb * (x + 1) ^ E := by omega
      _ = (1 + CF * pb) * (x + 1) ^ E := by ring
  have hA' : CA * (V + 2) ^ (EA * (k + 1)) ≤ CA * CS ^ (EA * (k + 1)) * (x + 1) ^ E := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hVpow
  have h1E : 1 ≤ (x + 1) ^ E := Nat.one_le_pow _ _ (Nat.succ_pos x)
  have hexp : (CF + 2 * (1 + CF * pb) + 2 + CA * CS ^ (EA * (k + 1))) * (x + 1) ^ E =
      CF * (x + 1) ^ E + 2 * ((1 + CF * pb) * (x + 1) ^ E) + 2 * (x + 1) ^ E +
        CA * CS ^ (EA * (k + 1)) * (x + 1) ^ E := by ring
  rw [hexp]
  omega

/-- **T01 shell (fixed `k`), HYP on H-A3, the T10 front glue and T10 size; the cited records
are parameters.** One fixed machine per `k` prints, on `pair (encode Φ) tape` for every valid
`Φ` and every tape of the selected law, exactly `outputBits` within a polynomial (degree
depending on `k`) of the input length; the output is in the language on every tape when `Φ` is
satisfiable, and otherwise `D(M) = B + k` with probability at least `981/1000` under the selected
tape law. Does not close a ledger row (T01). -/
theorem T01_of_interfaces (hA3 : H_A3 B.degreeBound (sourceGap D B)) (k : ℕ) (hk : 1 ≤ k)
    (hFront : H_T10Front D B k) (hSize : H_T10Size D B) :
    (∃ (M : BitMachine.Machine) (C E : ℕ), ∀ (Φ : ValidFormula) (t : (TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ) (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound (sourceGap D B) k).Tape),
      M.OutputsWithin
        (EncodedComplexity.pair (EncodedCNF.encode Φ.val) ((TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ) (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound (sourceGap D B) k).tapeBits t))
        (EncodedSelectedOutput.outputBits (t10_vertices_pos D B Φ)
          (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
          B.degreeBound (sourceGap D B) k t)
        (C * ((EncodedComplexity.pair (EncodedCNF.encode Φ.val)
          ((TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ) (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound (sourceGap D B) k).tapeBits t)).length + 1) ^ E)) ∧
    (∀ Φ : ValidFormula, EncodedCNF.Satisfiable Φ.val → ∀ t : (TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ) (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound (sourceGap D B) k).Tape,
      EncodedSelectedOutput.outputBits (t10_vertices_pos D B Φ)
        (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
        B.degreeBound (sourceGap D B) k t ∈ EncodedCommunication.Language) ∧
    (∀ Φ : ValidFormula, ¬ EncodedCNF.Satisfiable Φ.val →
      (981 / 1000 : ℝ) ≤ TotalFiniteConstructorScratch.successProbability (t10_vertices_pos D B Φ)
        (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
        B.degreeBound (sourceGap D B) k) := by
  obtain ⟨MA, CA, EA, hMA⟩ := hA3
  obtain ⟨MF, CF, EF, hMF⟩ := hFront
  obtain ⟨CS, ES, hS⟩ := hSize
  refine ⟨⟨BitMachineComposition.composition MF MA,
    CF + 2 * (1 + CF * MF.pushBound) + 2 + CA * CS ^ (EA * (k + 1)),
    EF + ES * (EA * (k + 1)) + 1, ?_⟩, ?_, ?_⟩
  · intro Φ t
    obtain ⟨hm, _, hinc, hdeg, _, _, _⟩ := t10_source D B Φ
    have hF := hMF Φ t
    have hA := hMA (t10Graph D B Φ) (t10Graph_valid D B Φ) (t10_vertices_pos D B Φ) k hk
      hinc hdeg t
    have hC := BitMachineComposition.composition_outputsWithin MF MA hF hA
    apply BitMachine.outputsWithin_mono _ hC
    exact budget _ _ _ _ CF EF MF.pushBound CA CS ES EA k
      (by simp only [EncodedComplexity.pair_length]; omega)
      (BitMachine.output_length_bound MF hF) (hS Φ)
  · intro Φ hsat t
    exact (t01_finite_core D B Φ k hk).1 hsat t
  · intro Φ hunsat
    obtain ⟨hm, _, _, hdeg, hloop, _, hno⟩ := t10_source D B Φ
    have h := TotalFiniteConstructorScratch.selected_no_success (t10_vertices_pos D B Φ)
      (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
      B.degreeBound (sourceGap D B) k hk hloop hdeg (source_gap_pos D B) B.degreeBound_pos hm
      (hno hunsat)
    have hnum : (981 / 1000 : ℝ) ≤ 1 - (1 / 2 : ℝ) ^ 11 := by norm_num
    linarith

section T02

open Paper2 Paper2.FiniteLaw Paper2.Unit4Shell.Amplification

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The T02 midpoint decider on one joint tape: reduction tape `x.1` (law `ρ`), `147` estimator
tapes `x.2` (law `μ`), accept iff the lower median of the `147` estimates is below `Bud + k/2`. -/
noncomputable def accepts (est : β → α → ℝ) (Bud k : ℕ) (x : β × (Fin reps → α)) : Prop :=
  lowerMedian (by decide : 0 < reps) (fun i => est x.1 (x.2 i)) < (Bud : ℝ) + (k : ℝ) / 2

/-- **T02 error shell (law-generic).** Reduction law `ρ` with per-tape cost `cost` and public
budget `Bud`; an estimator run law `μ` whose estimate `est b t` of `cost b` has error `≤ a` with
probability `≥ 2/3` for every reduction tape; a fixed integer `k > 2a`. YES (`cost ≤ Bud` on every
tape): the median test rejects with probability `≤ 1/100`. NO (`cost = Bud + k` except with
probability `≤ 2^-11`, the banked `selected_no_success` form): it accepts with probability
`≤ 2^-11 + 1/100 < 1/3`. Instantiating `ρ` with the selected tape law is a named step (not done
here). Does not close a ledger row (T02). -/
theorem T02_error_shell (ρ : FiniteLaw β) (μ : FiniteLaw α) (cost : β → ℕ) (Bud k : ℕ)
    (a : ℝ) (hk : 2 * a < k) (est : β → α → ℝ)
    (hμ : ∀ b, 2 / 3 ≤ μ.prob (fun t => |est b t - cost b| ≤ a)) :
    ((∀ b, cost b ≤ Bud) →
      (ρ.prod (μ.iid reps)).prob (fun x => ¬ accepts est Bud k x) ≤ 1 / 100) ∧
    (ρ.prob (fun b => ¬ cost b = Bud + k) ≤ (1 / 2) ^ 11 →
      (ρ.prod (μ.iid reps)).prob (fun x => accepts est Bud k x) ≤ (1 / 2) ^ 11 + 1 / 100 ∧
      (1 / 2 : ℝ) ^ 11 + 1 / 100 < 1 / 3) := by
  classical
  constructor
  · intro hyes
    have h := two_stage_majority_failure_le ρ μ (fun _ => True)
      (fun b t => |est b t - cost b| ≤ a) 0 (by simp) (fun b _ => hμ b)
    refine le_trans (FiniteLaw.prob_mono _ ?_) (by simpa using h)
    intro x hx
    by_contra hcon
    apply hx
    unfold accepts
    exact median_midpoint_yes _ _ a (cost x.1) Bud k (hyes x.1) hk
      (by convert (not_le.mp hcon) using 3)
  · intro hno
    refine ⟨?_, (error_budget).1⟩
    have h := two_stage_majority_failure_le ρ μ (fun b => cost b = Bud + k)
      (fun b t => |est b t - cost b| ≤ a) ((1 / 2) ^ 11) hno (fun b _ => hμ b)
    refine le_trans (FiniteLaw.prob_mono _ ?_) h
    intro x hx hgood
    obtain ⟨hc, hmaj⟩ := hgood
    have hlt := median_midpoint_no (by decide : 0 < reps) (fun i => est x.1 (x.2 i)) a Bud k hk
      (by
        have e : ((Bud + k : ℕ) : ℝ) = (cost x.1 : ℝ) := by rw [hc]
        simp only [e]
        convert hmaj using 3)
    exact absurd hx (not_lt.mpr hlt.le)

end T02

end Paper2.Unit4Shell.Shells
