import EthInapproximability.CurrentPaper.QFinal
import EthInapproximability.CurrentPaper.BitMachineStackGrowth
import EthInapproximability.CurrentPaper.ExactSourcePadding
import Mathlib.Tactic

/-! Public clock for the same-graph q₂ producer with charged cleanup.

The frozen `QFinal.same_graph_q_clean_run` charges `QCleanup.cost C` for the
actual pre-cleanup bank `C`, but its statement does not bound `C`. This
successor recomposes the same checked producer (`QGraphJoined.same_graph_q_run`)
and cleanup (`QCleanup.run`) on the same literal program `QFinal.program`,
keeps `C` as the producer's own final bank, and bounds its private stacks by
the fixed per-transition push bound of the fixed producer program times the
producer's own running time. The arithmetic charge
`QArithmeticJoined.cost s |E|` is then majorized by an explicit polynomial in
the graph-byte length and the unary bin count `s`. -/

namespace EthInapproximability.CurrentPaper.QPublicGrowth

open Turing BitMachineEncoding BitMachineStackEmbedding
open scoped BigOperators
noncomputable section

def referenceGraph : EncodedGraph.Graph := ⟨0, []⟩
def referenceWriter : Fin 64 → List Bool := fun _ => []

/-- The per-transition push bound of the fixed producer program: a finite
supremum over its finite instruction labels, independent of every input
(`pushConstant_eq`). -/
def pushConstant : Nat :=
  BitMachineStackGrowth.perStep
    (QFinal.qProgram referenceGraph referenceWriter)

theorem pushConstant_eq (g : EncodedGraph.Graph)
    (W : Fin 64 → List Bool) :
    BitMachineStackGrowth.perStep (QFinal.qProgram g W) = pushConstant := by
  rw [QFinal.qProgram_fixed g referenceGraph W referenceWriter]
  rfl

theorem initial_private_blank (g : EncodedGraph.Graph)
    (W : Fin 64 → List Bool) (j : QCleanup.ClearIndex) :
    QGraphJoined.startBank g W (QCleanup.embed j) = [] := by
  have hj : ¬ ∃ k : GraphCountBridge.Stack,
      QProduct.parserWriterSlots k = QCleanup.embed j := by
    rcases j with i | i
    · simp [QCleanup.embed,QProduct.parserWriterSlots,QProduct.temp]
    · simp [QCleanup.embed,QProduct.parserWriterSlots,QProduct.log]
  exact (bank_outside QProduct.parserWriterSlots QGraphJoined.emptyForeign
    (GraphCountBridge.start g W).stk (QCleanup.embed j) hj)

theorem cleanup_cost_le_of_run (g : EncodedGraph.Graph)
    (W : Fin 64 → List Bool) (t : Nat)
    (C : QProduct.Stack → List Bool)
    (hr : ((advance (QFinal.qProgram g W))^[t])
      (⟨some (BitMachineRawSequence.leftLabel
          (Sum.inr SourceNormalizationMachineDecode.Admin.gate)),
        QFinal.qInitial g W,QGraphJoined.startBank g W⟩ :
          TM2.Cfg (fun _ : QProduct.Stack => Bool) _ _) =
      ⟨none,QFinal.qInitial g W,C⟩) :
    QCleanup.cost C ≤ QCleanup.count * (pushConstant * t) +
      QCleanup.count + 2 := by
  have hcell (i : Fin QCleanup.count) :
      (C (QCleanup.key i)).length ≤ pushConstant * t := by
    have hg := BitMachineStackGrowth.run_growth
      (QFinal.qProgram g W)
      (⟨some (BitMachineRawSequence.leftLabel
          (Sum.inr SourceNormalizationMachineDecode.Admin.gate)),
        QFinal.qInitial g W,QGraphJoined.startBank g W⟩ :
          TM2.Cfg (fun _ : QProduct.Stack => Bool) _ _)
      t (QCleanup.key i)
    have hb := initial_private_blank g W (QCleanup.enumerate i)
    simpa only [hr,QCleanup.key,hb,List.length_nil,Nat.zero_add,
      pushConstant_eq] using hg
  have hsum : (∑ i : Fin QCleanup.count,
      (C (QCleanup.key i)).length) ≤
      QCleanup.count * (pushConstant * t) := by
    calc
      _ ≤ ∑ _i : Fin QCleanup.count, pushConstant * t :=
        Finset.sum_le_sum (fun i _ => hcell i)
      _ = _ := by simp
  unfold QCleanup.cost
  omega

#print axioms cleanup_cost_le_of_run

/-! ### Polynomial majorization of the arithmetic charge -/

theorem clog_le_self (n : ℕ) : Nat.clog 2 n ≤ n :=
  Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n := n)).le

theorem pow_clog_le (n : ℕ) : 2 ^ Nat.clog 2 n ≤ 2 * n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have := ExactSourcePadding.pow_clog_le_twice hn
    omega

theorem suffix_cost_le (n : ℕ) :
    QSuffixJoin.cost n ≤
      (UnaryBinaryEncoding.coefficient + 23) * (n + 1) ^ 2 := by
  have h1 := pow_clog_le n
  have h2 := clog_le_self n
  have hX : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hsplit : (UnaryBinaryEncoding.coefficient + 23) * (n + 1) ^ 2 =
      (UnaryBinaryEncoding.coefficient + 6) * (n + 1) ^ 2 +
        17 * (n + 1) ^ 2 := by ring
  rw [hsplit]
  unfold QSuffixJoin.cost
  omega

theorem product_cost_eq (s e : ℕ) :
    QProductJoined.cost s e = 30 * (s * e) + 4 * s + 11 := by
  unfold QProductJoined.cost MatrixAddressMachine.exactTime
  ring

/-- Fixed coefficient of the arithmetic-phase majorization. -/
def arithmeticCoefficient : ℕ := 144 * UnaryBinaryEncoding.coefficient + 4000

theorem arithmetic_cost_le (s e : ℕ) :
    QArithmeticJoined.cost s e ≤
      arithmeticCoefficient * (s + e + 1) ^ 4 := by
  set m := s + e + 1 with hm
  have hse : s * e + 1 ≤ m ^ 2 := by
    have : m ^ 2 = s * e + (s * s + e * e + s * e + 2 * s + 2 * e + 1) := by
      rw [hm]; ring
    omega
  have hn : 12 * s * e + 1 ≤ 12 * m ^ 2 := by
    have : 12 * s * e = 12 * (s * e) := by ring
    omega
  have hsq : (12 * s * e + 1) ^ 2 ≤ 144 * m ^ 4 := by
    calc
      (12 * s * e + 1) ^ 2 ≤ (12 * m ^ 2) ^ 2 := Nat.pow_le_pow_left hn 2
      _ = 144 * m ^ 4 := by ring
  have hsuf := suffix_cost_le (12 * s * e)
  have hsuf2 : QSuffixJoin.cost (12 * s * e) ≤
      (UnaryBinaryEncoding.coefficient + 23) * (144 * m ^ 4) :=
    hsuf.trans (Nat.mul_le_mul_left _ hsq)
  have hexp : (UnaryBinaryEncoding.coefficient + 23) * (144 * m ^ 4) =
      144 * (UnaryBinaryEncoding.coefficient * m ^ 4) + 3312 * m ^ 4 := by
    ring
  have hrhs : arithmeticCoefficient * m ^ 4 =
      144 * (UnaryBinaryEncoding.coefficient * m ^ 4) + 4000 * m ^ 4 := by
    unfold arithmeticCoefficient; ring
  have hm1 : 1 ≤ m := by omega
  have hsm : s ≤ m := by omega
  have hm2 : m ^ 2 ≤ m ^ 4 := Nat.pow_le_pow_right hm1 (by norm_num)
  have hm4 : m ≤ m ^ 4 := Nat.le_self_pow (by norm_num) _
  have hprod := product_cost_eq s e
  rw [hrhs]
  unfold QArithmeticJoined.cost
  omega

#print axioms arithmetic_cost_le

theorem edges_le_bytes {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (G : ParameterizedNP.GuardedSourceGraph.EndpointGraph V E) :
    Fintype.card E ≤
      (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length := by
  have h := EncodedGraph.encode_length_lower (EncodedETHSource.serializeGraph G)
  rw [EncodedETHSource.serializeGraph_edges] at h
  omega

/-- `QArithmeticJoined.cost s |E|` is majorized by a fixed polynomial in the
graph-byte length and the unary bin count `s`. -/
theorem arithmetic_cost_graph_le {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (G : ParameterizedNP.GuardedSourceGraph.EndpointGraph V E) (s : ℕ) :
    QArithmeticJoined.cost s (Fintype.card E) ≤
      arithmeticCoefficient *
        (s + (EncodedGraph.encode
          (EncodedETHSource.serializeGraph G)).length + 1) ^ 4 := by
  refine (arithmetic_cost_le s (Fintype.card E)).trans ?_
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  have := edges_le_bytes G
  omega

#print axioms arithmetic_cost_graph_le

/-! ### One public clock for the same producer/cleanup run -/

/-- Fixed coefficient of the q public clock. -/
def publicCoefficient : ℕ :=
  (1 + QCleanup.count * pushConstant) * (arithmeticCoefficient + 102) +
    QCleanup.count + 3

/-- The q public clock in graph-byte length `N` and unary bin count `s`. -/
def publicClock (N s : ℕ) : ℕ := publicCoefficient * (s + N + 1) ^ 4

theorem producer_bound_le (N s e : ℕ) (he : e ≤ N) :
    101 * (N + 1) ^ 3 + QArithmeticJoined.cost s e + 1 ≤
      (arithmeticCoefficient + 102) * (s + N + 1) ^ 4 := by
  set M := s + N + 1 with hM
  have hM1 : 1 ≤ M := by omega
  have ha := arithmetic_cost_le s e
  have ha2 : arithmeticCoefficient * (s + e + 1) ^ 4 ≤
      arithmeticCoefficient * M ^ 4 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)
  have h3 : (N + 1) ^ 3 ≤ M ^ 4 :=
    (Nat.pow_le_pow_left (show N + 1 ≤ M by omega) 3).trans
      (Nat.pow_le_pow_right hM1 (by norm_num))
  have h1 : 1 ≤ M ^ 4 := Nat.one_le_pow _ _ hM1
  have hexp : (arithmeticCoefficient + 102) * M ^ 4 =
      arithmeticCoefficient * M ^ 4 + 102 * M ^ 4 := by ring
  rw [hexp]
  omega

theorem total_le_public (N s tq c : ℕ)
    (htq : tq ≤ (arithmeticCoefficient + 102) * (s + N + 1) ^ 4)
    (hc : c ≤ QCleanup.count * (pushConstant * tq) + QCleanup.count + 2) :
    tq + c + 1 ≤ publicClock N s := by
  set M := s + N + 1 with hM
  set K := arithmeticCoefficient + 102 with hK
  set a := QCleanup.count * pushConstant with ha
  have hM1 : 1 ≤ M ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hmul : QCleanup.count * (pushConstant * tq) = a * tq := by
    rw [ha]; ring
  have hat : a * tq ≤ a * (K * M ^ 4) := Nat.mul_le_mul_left _ htq
  have hrhs : publicClock N s =
      K * M ^ 4 + a * (K * M ^ 4) +
        (QCleanup.count + 3) * M ^ 4 := by
    unfold publicClock publicCoefficient
    rw [← hK, ← ha, ← hM]
    ring
  have hcnt : QCleanup.count + 3 ≤ (QCleanup.count + 3) * M ^ 4 :=
    Nat.le_mul_of_pos_right _ hM1
  rw [hrhs]
  omega

/-- Successor of the frozen `QFinal.same_graph_q_clean_run`: the same fixed
program and start configuration, with the cleanup bank `C` identified as the
producer's own final bank, a same-run bound on `QCleanup.cost C`, and one
public polynomial clock in graph-byte length and unary `s`. The hypotheses
are exactly those of the frozen theorem. -/
theorem same_graph_q_clean_run_public {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (G : ParameterizedNP.GuardedSourceGraph.EndpointGraph V E)
    (W : QFinal.WriterStack → List Bool) (s : ℕ)
    (hs : W 28 = List.replicate s true)
    (hq : W 56 = []) :
    let g := EncodedETHSource.serializeGraph G
    ∃ (tq t : ℕ) (F C : QFinal.Stack → List Bool),
      tq ≤ 101*((EncodedGraph.encode g).length+1)^3 +
        QArithmeticJoined.cost s (Fintype.card E) + 1 ∧
      ((advance (QFinal.qProgram g W))^[tq])
        (⟨some (BitMachineRawSequence.leftLabel
            (Sum.inr SourceNormalizationMachineDecode.Admin.gate)),
          QFinal.qInitial g W,QGraphJoined.startBank g W⟩ :
          TM2.Cfg (fun _ : QProduct.Stack => Bool) _ _) =
        ⟨none,QFinal.qInitial g W,C⟩ ∧
      QCleanup.cost C ≤
        QCleanup.count * (pushConstant * tq) + QCleanup.count + 2 ∧
      t ≤ tq + QCleanup.cost C + 1 ∧
      t ≤ publicClock (EncodedGraph.encode g).length s ∧
      F = QCleanup.cleared C ∧
      ((advance (QFinal.program g W))^[t])
          (⟨some (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (Sum.inr SourceNormalizationMachineDecode.Admin.gate))),
            (QFinal.qInitial g W,((),none)),QGraphJoined.startBank g W⟩ :
              TM2.Cfg (fun _ : QProduct.Stack => Bool) _ _) =
          ⟨none,(QFinal.qInitial g W,((),none)),F⟩ ∧
      F QProduct.q =
        List.replicate (ParameterizedNP.GuardedSourceSlab.q2 G s) true ∧
      (∀ j : QFinal.WriterStack, j ≠ 56 → F (.inl (.inr j)) = W j) ∧
      F QProduct.edge = List.replicate (Fintype.card E) true ∧
      (∀ j : QCleanup.ClearIndex, F (QCleanup.embed j) = []) := by
  intro g
  obtain ⟨tq,htq,C,hqrun,hout,hwriter,hedge⟩ :=
    QGraphJoined.same_graph_q_run G W s hs hq
  have hqrun' : ((advance (QFinal.qProgram g W))^[tq])
        (⟨some (BitMachineRawSequence.leftLabel
            (Sum.inr SourceNormalizationMachineDecode.Admin.gate)),
          QFinal.qInitial g W,QGraphJoined.startBank g W⟩ :
          TM2.Cfg (fun _ : QProduct.Stack => Bool) _ _) =
        ⟨none,QFinal.qInitial g W,C⟩ := by
    simpa only [QFinal.qProgram,QFinal.qInitial,g] using hqrun
  have hcost := cleanup_cost_le_of_run g W tq C hqrun'
  have hc := QCleanup.run C
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    (QFinal.qProgram g W) QCleanup.program
    (BitMachineRawSequence.leftLabel
      (Sum.inr SourceNormalizationMachineDecode.Admin.gate))
    (.inl (0 : Fin (QCleanup.count+1)))
    (QFinal.qInitial g W) (QFinal.qInitial g W)
    ((),none) ((),none)
    (QGraphJoined.startBank g W) C (QCleanup.cleared C)
    tq (QCleanup.cost C) hqrun' hc
  have hprod := producer_bound_le (EncodedGraph.encode g).length s
    (Fintype.card E) (edges_le_bytes G)
  have htq2 : tq ≤ (arithmeticCoefficient + 102) *
      (s + (EncodedGraph.encode g).length + 1) ^ 4 := htq.trans hprod
  have hpub := total_le_public (EncodedGraph.encode g).length s tq
    (QCleanup.cost C) htq2 hcost
  refine ⟨tq,t,QCleanup.cleared C,C,htq,hqrun',hcost,ht,
    ht.trans hpub,rfl,?_,?_,?_,?_,?_⟩
  · simpa only [QFinal.program,QFinal.qInitial] using hr
  · exact (QCleanup.cleared_parser_writer C (.inr 56)).trans hout
  · intro j hj
    exact (QCleanup.cleared_parser_writer C (.inr j)).trans (hwriter j hj)
  · exact (QCleanup.cleared_parser_writer C (.inl (.inr 1))).trans hedge
  · exact QCleanup.cleared_private C

#print axioms same_graph_q_clean_run_public

/-! Axiom audit of every helper declaration used above. -/
#print axioms pushConstant_eq
#print axioms initial_private_blank
#print axioms clog_le_self
#print axioms pow_clog_le
#print axioms suffix_cost_le
#print axioms product_cost_eq
#print axioms edges_le_bytes
#print axioms producer_bound_le
#print axioms total_le_public

end
end EthInapproximability.CurrentPaper.QPublicGrowth
