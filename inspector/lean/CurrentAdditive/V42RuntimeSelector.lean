import CurrentAdditive.V42RuntimePacket
import CurrentAdditive.V42PublicCutoff
import CurrentAdditive.V40SourceClockBounds

/-! The exact least-dyadic v42 selector as a finite stack program. It reads
the counted number of vertices, takes an integer ceiling logarithm, divides
by four with upward rounding, and takes the maximum with the fixed cutoff. -/
namespace CurrentAdditive.V42RuntimeSelector
open EthInapproximability.CurrentPaper D22NatExpression
open D22PacketPrimitives V40SourceLocal V40SourceClockBounds
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

def expression (k₀ : ℕ) : Expr := .binary (.old .max) (.const k₀)
  (.binary .quot (.binary (.old .add) (.unary .clog (.var 0)) (.const 3)) (.const 4))

theorem expression_eval (k₀ n m L : ℕ) :
    (expression k₀).eval n m L=V42PublicCutoff.generatedExponent n k₀ := rfl

theorem peak (k₀ n m L : ℕ) : (expression k₀).peak n m L≤(k₀+5)*(n+m+L+1) := by
  have hc : Nat.clog 2 n≤n := (Nat.clog_le_iff_le_pow (by decide : 1<2)).2 Nat.lt_two_pow_self.le
  have hd : (Nat.clog 2 n+3)/4≤Nat.clog 2 n+3 := Nat.div_le_self _ _
  have hn : n≤(k₀+5)*(n+m+L+1) := by nlinarith
  have hk : k₀≤(k₀+5)*(n+m+L+1) := by nlinarith
  have hfour : 4≤(k₀+5)*(n+m+L+1) := by nlinarith
  have hsum : Nat.clog 2 n+3≤(k₀+5)*(n+m+L+1) := by nlinarith
  simp only [expression,Expr.peak,Expr.eval,Binary.value,V22UnaryExpression.Binary.value,
    V22UnaryExpression.Unary.value,values,Matrix.cons_val_zero]
  exact max_le (max_le hk (hd.trans hsum))
    (max_le hk (max_le (hd.trans hsum) (max_le (max_le hsum (max_le (max_le (hc.trans hn) hn) (by omega))) hfour)))

def expressionCoefficient (k₀ : ℕ) := (expression k₀).coefficient*(k₀+12)^2

theorem expression_outputs (k₀ n m L : ℕ) :
    (expression k₀).machine.OutputsWithin (D22NatExpression.input n m L)
      (List.replicate (V42PublicCutoff.generatedExponent n k₀) true)
      (expressionCoefficient k₀*((D22NatExpression.input n m L).length+1)^2) := by
  have he := (expression k₀).clock_le_of_peak n m L ((k₀+5)*(n+m+L+1)) (peak k₀ n m L)
  have hlen : n+m+L+1≤(D22NatExpression.input n m L).length+1 := by
    simp [D22NatExpression.input,BitMachineBankCodec.encode_length,Fin.sum_univ_succ,values];omega
  have hb : inputLength n m L+(k₀+5)*(n+m+L+1)+2≤
      (k₀+12)*((D22NatExpression.input n m L).length+1) := by
    unfold inputLength
    nlinarith
  apply BitMachine.outputsWithin_mono _ ((expression k₀).outputs n m L)
  exact he.trans (by
    calc
      _ ≤ (expression k₀).coefficient*((k₀+12)*((D22NatExpression.input n m L).length+1))^2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb _)
      _ = _ := by rw [mul_pow];unfold expressionCoefficient;ring)

def query (k₀ : ℕ) := finiteRun (expression k₀).machine (expressionCoefficient k₀) 2
def request : V40SourceLocal.Producer := serialise ![project (1 : Fin 5),project (2 : Fin 5),project (3 : Fin 5)]
def selected (k₀ : ℕ) := V40SourceLocal.compose request (query k₀)
def fields (k₀ : ℕ) : Fin 5 → V40SourceLocal.Producer :=
  ![project (0 : Fin 5),project (1 : Fin 5),project (2 : Fin 5),selected k₀,project (4 : Fin 5)]
def producer (k₀ : ℕ) := serialise (fields k₀)
def machine (k₀ : ℕ) := (producer k₀).machine

theorem request_result (graph : List Bool) (n m L K : ℕ) :
    request.result (V42RuntimePacket.input graph n m L K)=D22NatExpression.input n m L := by
  rw [request,serialise_result]
  apply congrArg BitMachineBankCodec.encode
  funext j
  fin_cases j <;> simp [project,V42RuntimePacket.input,V42RuntimePacket.rawWords,D22NatExpression.input,values]

theorem selected_result (k₀ : ℕ) (graph : List Bool) (n m L K : ℕ) :
    (selected k₀).result (V42RuntimePacket.input graph n m L K)=
      List.replicate (V42PublicCutoff.generatedExponent n k₀) true := by
  change (query k₀).result (request.result (V42RuntimePacket.input graph n m L K))=_
  rw [request_result]
  exact (BitMachine.outputsWithin_at_bound _ (expression_outputs k₀ n m L)).2

theorem result (k₀ : ℕ) (graph : List Bool) (n m L K : ℕ) :
    (producer k₀).result (V42RuntimePacket.input graph n m L K)=
      V42RuntimePacket.input graph n m (V42PublicCutoff.generatedExponent n k₀) K := by
  rw [producer,serialise_result]
  apply congrArg BitMachineBankCodec.encode
  funext j
  fin_cases j
  all_goals first
    | solve | simp [fields,project,V42RuntimePacket.input,V42RuntimePacket.rawWords]
    | exact selected_result k₀ graph n m L K

theorem local_outputs (k₀ : ℕ) (graph : List Bool) (n m L K : ℕ) :
    (producer k₀).machine.OutputsWithin (V42RuntimePacket.input graph n m L K)
      ((producer k₀).result (V42RuntimePacket.input graph n m L K))
      ((producer k₀).clock (V42RuntimePacket.input graph n m L K)) := by
  have hs : (selected k₀).machine.OutputsWithin (V42RuntimePacket.input graph n m L K)
      ((selected k₀).result (V42RuntimePacket.input graph n m L K))
      ((selected k₀).clock (V42RuntimePacket.input graph n m L K)) := by
    apply compose_outputs
    · apply serialise_outputs
      intro j
      fin_cases j <;> exact project_outputs _ _
    · rw [request_result]
      have h := expression_outputs k₀ n m L
      have hr : (query k₀).result (D22NatExpression.input n m L)=
          List.replicate (V42PublicCutoff.generatedExponent n k₀) true :=
        (BitMachine.outputsWithin_at_bound _ h).2
      rw [hr]
      exact h
  apply serialise_outputs
  intro j
  fin_cases j
  all_goals first | exact project_outputs _ _ | exact hs

theorem polynomial (k₀ : ℕ) : HasPolynomialEnvelope (producer k₀) := by
  have hs : HasPolynomialEnvelope (selected k₀) := compose_polynomial (by
    apply serialise_polynomial
    intro j
    fin_cases j <;> exact project_polynomial _)
      (finite_run_polynomial _ _ _)
  apply serialise_polynomial
  intro j
  fin_cases j
  all_goals first | exact project_polynomial _ | exact hs

def coefficient (k₀ : ℕ) := Classical.choose (polynomial k₀)
def degree (k₀ : ℕ) := Classical.choose (Classical.choose_spec (polynomial k₀))

theorem outputs (k₀ : ℕ) (graph : List Bool) (n m L K : ℕ) :
    (machine k₀).OutputsWithin (V42RuntimePacket.input graph n m L K)
      (V42RuntimePacket.input graph n m (V42PublicCutoff.generatedExponent n k₀) K)
      (coefficient k₀*((V42RuntimePacket.input graph n m L K).length+1)^degree k₀) := by
  have h := local_outputs k₀ graph n m L K
  rw [result] at h
  apply BitMachine.outputsWithin_mono _ h
  have hb := Classical.choose_spec (Classical.choose_spec (polynomial k₀))
    (V42RuntimePacket.input graph n m L K)
  exact (Nat.le_add_right _ _).trans hb

#print axioms outputs
end
end CurrentAdditive.V42RuntimeSelector
