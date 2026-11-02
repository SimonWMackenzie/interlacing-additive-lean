import CurrentAdditive.V42DeterministicETHEndpoint
import Paper2.A4T24RuntimeComposed

/-! Private candidate for v43 `det:time`, source 354--365 and 2910--2952.
The round count is computed from the original variable count. All clocks
below are charged executions of the existing finite stack machines. -/
namespace CurrentAdditive.V43DeterministicRate
noncomputable section
open Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition Unit4Shell.T10Finite
open V39RuntimeETHNumerics V39ActualETHNumerics DeterministicEndpointNumeric
open V39PermittedDeterministicExtraction V39FramedNumerical
open V39PermittedNumericalExtraction
open V40DeterministicSourcePack V40DeterministicETHEndpoint
open PhysicalProducer V40StoredOutputPrimitives
open scoped Classical
set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

def rounds (A M : ℕ) := Nat.log 2 (Nat.log 2 M) / amplificationLog A
def coefficient (A : ℕ) : ℝ := 1/(8*(amplificationLog A:ℝ))
def numericCutoff (A C b : ℕ) := 2^(2^(2*amplificationLog A+Nat.clog 2 (C*b)+1))
def quasiLog (M : ℕ) := Nat.clog 2 (M+2)

theorem coefficient_pos (A : ℕ) (hA : 2^64 ≤ A) : 0 < coefficient A := by
  have ha := amplificationLog_ge A hA
  have har : (0:ℝ)<amplificationLog A := by exact_mod_cast (show 0<amplificationLog A by omega)
  exact div_pos (by norm_num) (mul_pos (by norm_num) har)

theorem amplification_rounds_le (A M : ℕ) (hM : 2 ≤ M) :
    A^(rounds A M) ≤ Nat.log 2 M := by
  let a := amplificationLog A
  let j := Nat.log 2 M
  have hj : 1 ≤ j := Nat.le_log_of_pow_le (by decide) (by simpa using hM)
  have he : a*rounds A M ≤ Nat.log 2 j := by
    simpa only [rounds,a,j,mul_comm] using Nat.div_mul_le_self (Nat.log 2 j) a
  calc
    A^(rounds A M) ≤ (2^a)^(rounds A M) := Nat.pow_le_pow_left (amplification_le A) _
    _ = 2^(a*rounds A M) := by rw [pow_mul]
    _ ≤ 2^(Nat.log 2 j) := Nat.pow_le_pow_right (by decide) he
    _ ≤ j := Nat.pow_log_le_self 2 (by omega)

theorem double_log_bound (A C b M N T : ℕ) (ha : 1 ≤ amplificationLog A)
    (hM : 2 ≤ M) (hN : N ≤ M^b) (hNpos : 0<N)
    (hT : T ≤ N^(C*A^(rounds A M))) :
    Nat.clog 2 (Nat.clog 2 T) ≤
      2*amplificationLog A*rounds A M+amplificationLog A+Nat.clog 2 (C*b)+1 := by
  let a := amplificationLog A
  let j := Nat.log 2 M
  let l := Nat.log 2 j
  let k := rounds A M
  have hm : M ≤ 2^(j+1) := (Nat.lt_pow_succ_log_self (by decide) M).le
  have hn : N ≤ 2^((j+1)*b) := by
    calc
      N ≤ M^b := hN
      _ ≤ (2^(j+1))^b := Nat.pow_le_pow_left hm _
      _ = _ := by rw [pow_mul]
  have hclog : Nat.clog 2 N ≤ (j+1)*b := (Nat.clog_le_iff_le_pow (by decide)).2 hn
  have hj : j+1 ≤ 2^(l+1) := by
    have h : j < 2^(l+1) := Nat.lt_pow_succ_log_self (by decide : 1<(2:ℕ)) j
    omega
  have hcb : C*b ≤ 2^(Nat.clog 2 (C*b)) := Nat.le_pow_clog (by decide) _
  have hproduct : C*Nat.clog 2 N ≤ 2^(Nat.clog 2 (C*b)+l+1) := by
    calc
      C*Nat.clog 2 N ≤ C*((j+1)*b) := Nat.mul_le_mul_left C hclog
      _ = (C*b)*(j+1) := by ring
      _ ≤ (2^(Nat.clog 2 (C*b)))*(2^(l+1)) := Nat.mul_le_mul hcb hj
      _ = _ := by simp only [←pow_add,Nat.add_assoc]
  have hcorr : Nat.clog 2 (C*Nat.clog 2 N) ≤ Nat.clog 2 (C*b)+l+1 :=
    (Nat.clog_le_iff_le_pow (by decide)).2 hproduct
  have hk : l < a*(k+1) := by
    have h := Nat.mod_lt l (show 0<a by exact Nat.zero_lt_of_lt ha)
    have hd := Nat.mod_add_div l a
    change l%a+a*(l/a)=l at hd
    dsimp [k,rounds,l,j,a] at *
    nlinarith
  have ht : T ≤ N^(C*(2^a)^k) := hT.trans (Nat.pow_le_pow_right hNpos
    (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (amplification_le A) k)))
  have hout := double_log_output_bound N C a k T ht
  change Nat.clog 2 (Nat.clog 2 T) ≤ 2*a*k+a+Nat.clog 2 (C*b)+1
  nlinarith

theorem numeric_gap (A C b M N T : ℕ) (hA : 2^64 ≤ A)
    (hM : 2 ≤ M) (hN : N ≤ M^b) (hNpos : 0<N)
    (hT : T ≤ N^(C*A^(rounds A M))) (hT2 : 2 ≤ T)
    (hlarge : numericCutoff A C b ≤ M) :
    1 ≤ rounds A M ∧
      2*coefficient A*Real.logb 2 (Real.logb 2 T) < (rounds A M:ℝ) := by
  let a := amplificationLog A
  let k := rounds A M
  let l := Nat.log 2 (Nat.log 2 M)
  have ha : 1 ≤ a := (by decide : 1 ≤ 64).trans (amplificationLog_ge A hA)
  have hpow : 2^(2*a+Nat.clog 2 (C*b)+1) ≤ Nat.log 2 M :=
    Nat.le_log_of_pow_le (by decide) hlarge
  have hl : 2*a+Nat.clog 2 (C*b)+1 ≤ l := Nat.le_log_of_pow_le (by decide) hpow
  have hk : l < a*(k+1) := by
    have hmod := Nat.mod_lt l (show 0<a by omega)
    have hd := Nat.mod_add_div l a
    change l%a+a*(l/a)=l at hd
    have hdef : k=l/a := rfl
    nlinarith
  have hkpos : 1 ≤ k := by nlinarith
  have hcorr : a+Nat.clog 2 (C*b)+1 ≤ a*k := by nlinarith
  have hd := double_log_bound A C b M N T ha hM hN hNpos hT
  have hthree : Nat.clog 2 (Nat.clog 2 T) ≤ 3*a*k := by nlinarith
  have hr : Real.logb 2 (Real.logb 2 T) ≤ 3*(a:ℝ)*(k:ℝ) := by
    have hc : (Nat.clog 2 (Nat.clog 2 T):ℝ) ≤ (3:ℝ)*a*k := by exact_mod_cast hthree
    exact (real_double_log_le_clog T hT2).trans hc
  have har : (0:ℝ)<a := by exact_mod_cast (show 0<a by omega)
  have hkr : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  refine ⟨hkpos,?_⟩
  change 2*(1/(8*(a:ℝ)))*_ < (k:ℝ)
  have hm := mul_le_mul_of_nonneg_left hr (show (0:ℝ)≤2*(1/(8*(a:ℝ))) by positivity)
  have hid : 2*(1/(8*(a:ℝ)))*(3*(a:ℝ)*(k:ℝ))=3*(k:ℝ)/4 := by field_simp; ring
  rw [hid] at hm
  linarith

theorem main_clock_quasipoly (A C b M N : ℕ) (hM : 2 ≤ M) (hN : N ≤ M^b) :
    N^(C*A^(rounds A M)) ≤ 2^(b*C*(quasiLog M)^2) := by
  have hj : Nat.log 2 M ≤ quasiLog M :=
    (Nat.log_le_clog 2 M).trans (Nat.clog_mono_right 2 (by omega : M ≤ M+2))
  have hMpow : M ≤ 2^(quasiLog M) :=
    (show M ≤ M+2 by omega).trans (Nat.le_pow_clog (by decide) (M+2))
  have hp := amplification_rounds_le A M hM
  calc
    N^(C*A^(rounds A M)) ≤ (M^b)^(C*A^(rounds A M)) := Nat.pow_le_pow_left hN _
    _ = M^(b*C*A^(rounds A M)) := by rw [←pow_mul]; congr 1; ring
    _ ≤ (2^(quasiLog M))^(b*C*A^(rounds A M)) := Nat.pow_le_pow_left hMpow _
    _ = 2^(quasiLog M*(b*C*A^(rounds A M))) := by rw [←pow_mul]
    _ ≤ 2^(b*C*(quasiLog M)^2) := by
      apply Nat.pow_le_pow_right (by decide)
      have hm := Nat.mul_le_mul_left (quasiLog M*(b*C)) (hp.trans hj)
      nlinarith

theorem actual_numerics (Δ k₀ M e T₀ : ℕ) (g : EncodedGraph.Graph) (hg : g.Valid)
    (hΔ : 0<Δ) (hk₀ : 2 ≤ k₀) (hn : 0<g.vertices)
    (hdegree : 2*g.edges.length ≤ Δ*g.vertices) (hcut : 2*Δ ≤ k₀)
    (hM : 16 ≤ M) (he : 1 ≤ e) (hsource : M ≤ Δ*g.vertices) (hgraph : g.vertices ≤ M^e)
    (hN₀ : 2^(4*k₀) ≤ M) (hT₀ : Δ*T₀ ≤ M)
    (hlarge : numericCutoff (V42GraphRuntime.amplification k₀)
      (V42ETHNumerics.sizeExponent Δ k₀) (e+1) ≤ M) :
    let A := V42GraphRuntime.amplification k₀
    let K := rounds A M
    let R := V42GraphRuntime.publicRun Δ k₀ g hg hk₀ hn hdegree hcut K
    1 ≤ K ∧ T₀ ≤ V42ActualLower.entryCount R ∧
      2*coefficient A*Real.logb 2 (Real.logb 2 (V42ActualLower.entryCount R))<K := by
  let A := V42GraphRuntime.amplification k₀
  let K := rounds A M
  dsimp only
  generalize hR : V42GraphRuntime.publicRun Δ k₀ g hg hk₀ hn hdegree hcut K=R
  let N := V42RuntimePrefix.N k₀ g
  let C := V42ETHNumerics.sizeExponent Δ k₀
  have hword : R.squareWord.length ≤ N^(C*A^K) := by
    rw [←hR]
    exact V42ETHNumerics.actual_size Δ k₀ g hg K hk₀ hn hdegree hcut
  have hside : N ≤ SquarePadding.side R.rows R.cols := by
    rw [←hR]
    exact V42ActualLower.public_side (V42RuntimePrefix.selected k₀ g)
      (V42GraphRuntime.selected_ge_two k₀ hk₀ g) hn
      (V42GraphRuntime.selected_width Δ k₀ g hdegree hcut) (LiteralEdgeEncoder.edge g hg) K
  have hnN : g.vertices ≤ N := by
    simpa only [V42PublicSchedule.generatedN_exact] using
      (V42PublicCutoff.generatedExponent_spec g.vertices k₀).2
  have hT₀n : T₀ ≤ g.vertices := Nat.le_of_mul_le_mul_left (hT₀.trans hsource) hΔ
  have hmin : T₀ ≤ V42ActualLower.entryCount R :=
    (hT₀n.trans (hnN.trans hside)).trans (Nat.le_self_pow (by decide : 2≠0) _)
  have hN2 : 2 ≤ N := by
    change 2 ≤ 2^(4*V42RuntimePrefix.selected k₀ g)
    have hk := V42GraphRuntime.selected_ge_two k₀ hk₀ g
    exact (by decide : 2 ≤ 2^1).trans (Nat.pow_le_pow_right (by decide)
      (show 1 ≤ 4*V42RuntimePrefix.selected k₀ g by omega))
  have hT2 : 2 ≤ V42ActualLower.entryCount R :=
    (hN2.trans hside).trans (Nat.le_self_pow (by decide : 2≠0) _)
  have hN : N ≤ M^(e+1) := V42ETHNumerics.selected_polynomial k₀ M e g hM he hgraph hN₀
  have hentries : V42ActualLower.entryCount R ≤ N^(C*A^K) := (entries_le_length R).trans hword
  have hgap := numeric_gap A C (e+1) M N (V42ActualLower.entryCount R)
    (V42GraphRuntime.amplification_ge k₀) (by omega) hN (by omega) hentries hT2 hlarge
  exact ⟨hgap.1,hmin,hgap.2⟩

#print axioms numeric_gap
#print axioms main_clock_quasipoly

set_option maxHeartbeats 100000
set_option maxRecDepth 4096

def loglogUnary : UnaryProducer where
  value w := Nat.log 2 (Nat.log 2 w.length)
  producer := compose V40DeterministicRounds.logFloor.producer V40DeterministicRounds.logFloor.producer
  result_eq w := by
    change V40DeterministicRounds.logFloor.producer.result
      (V40DeterministicRounds.logFloor.producer.result w)=_
    rw [V40DeterministicRounds.logFloor.result_eq,V40DeterministicRounds.logFloor.result_eq,
      V40DeterministicRounds.logFloor_value,V40DeterministicRounds.logFloor_value]
    simp only [List.length_replicate]

def roundUnary (A : ℕ) := UnaryProducer.binary .quot loglogUnary
  (UnaryProducer.constant (amplificationLog A))

theorem roundUnary_value (A : ℕ) (w : List Bool) :
    (roundUnary A).value w=rounds A w.length := rfl

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

abbrev amplification := V42ETHPhysical.amplification D B
def constructionError : ℝ := coefficient (amplification D B)

theorem constructionError_pos : 0<constructionError D B :=
  coefficient_pos _ (V42GraphRuntime.amplification_ge _)

def growingPackAt (amp : ℕ) := bank3 (graph D B) (UnaryProducer.constant 0).producer
  (compose originalVariables (roundUnary amp).producer)
def growingPack := growingPackAt D B (amplification D B)

theorem growing_result_at (amp : ℕ) (Φ : ValidFormula) (hN : 1 ≤ Φ.val.variables) :
    (growingPackAt D B amp).result (EncodedCNF.encode Φ.val)=
      V42RuntimePrefix.input (EncodedGraph.encode (t10Graph D B Φ))
        (rounds amp Φ.val.variables) := by
  rw [growingPackAt,bank3_result,graph_result D B Φ hN]
  change BitMachineBankCodec.encode ![_,[],
    (roundUnary amp).producer.result
      (originalVariables.result (EncodedCNF.encode Φ.val))]=_
  rw [original_result,(roundUnary amp).result_eq,roundUnary_value]
  simp only [List.length_replicate]
  rfl

theorem growing_result (Φ : ValidFormula) (hN : 1 ≤ Φ.val.variables) :
    (growingPack D B).result (EncodedCNF.encode Φ.val)=
      V42RuntimePrefix.input (EncodedGraph.encode (t10Graph D B Φ))
        (rounds (amplification D B) Φ.val.variables) :=
  growing_result_at D B (amplification D B) Φ hN

def front (cs cutoff : ℕ) (hcut : 1 ≤ cutoff) :=
  compose (sparseRoute cs cutoff hcut) (growingPack D B)

theorem front_result (cs cutoff : ℕ) (hcut : 1 ≤ cutoff) (w : List Bool) :
    (front D B cs cutoff hcut).result w=
      V42RuntimePrefix.input (EncodedGraph.encode (t10Graph D B (sparseFormula cs cutoff hcut w)))
        (rounds (amplification D B) (sparseFormula cs cutoff hcut w).val.variables) := by
  change (growingPack D B).result (AEth4.route3Out (cs+2) cutoff w)=_
  rw [AEth4.route3Out_eq]
  exact growing_result D B (sparseFormula cs cutoff hcut w)
    (hcut.trans (AEth4.routed4_variables (cs+2) cutoff w))

def machine (E : Estimator) (cs cutoff : ℕ) (hcut : 1 ≤ cutoff) :=
  BitMachineComposition.composition (front D B cs cutoff hcut).machine (V42ETHPhysical.mainMachine D B E)

def time (E : Estimator) (cs cutoff : ℕ) (hcut : 1 ≤ cutoff) (w : List Bool) :=
  let Φ := sparseFormula cs cutoff hcut w
  frontClock (front D B cs cutoff hcut) w+
    V42ETHPhysical.mainTime D B E Φ (rounds (amplification D B) Φ.val.variables)

theorem outputs (E : Estimator) (cs cutoff : ℕ) (hcut : 1 ≤ cutoff) (w : List Bool) :
    (machine D B E cs cutoff hcut).OutputsWithin w
      (E.run (V42ActualSource.request D B (sparseFormula cs cutoff hcut w)
        (rounds (amplification D B) (sparseFormula cs cutoff hcut w).val.variables)))
      (time D B E cs cutoff hcut w) := by
  let Φ := sparseFormula cs cutoff hcut w
  have hf := (front D B cs cutoff hcut).outputs w
  rw [front_result] at hf
  have hm := V42ETHPhysical.main_outputs D B E Φ (rounds (amplification D B) Φ.val.variables)
  have hr := BitMachineComposition.composition_outputsWithin _ _ hf hm
  apply BitMachine.outputsWithin_mono _ hr
  unfold time frontClock
  rw [front_result]

theorem source_numerics (cs T₀ : ℕ) :
    ∃ M₀ : ℕ, ∀ Φ : ValidFormula,
      Φ.val.clauses.length ≤ cs*Φ.val.variables → M₀ ≤ Φ.val.variables →
      let K := rounds (amplification D B) Φ.val.variables
      let R := V42ActualSource.run D B Φ K
      1 ≤ K ∧ T₀ ≤ V42ActualLower.entryCount R ∧
        2*constructionError D B*Real.logb 2 (Real.logb 2 (V42ActualLower.entryCount R)) < K := by
  let k₀ := V42ActualSource.k0 D B
  let A := amplification D B
  let C := V42ETHNumerics.sizeExponent B.degreeBound k₀
  let e := D.sizeExponent+3
  refine ⟨max (DeterministicETHSourceBridge.graphPolynomialCutoff D B cs)
    (max (2^(4*k₀)) (max 16 (max (B.degreeBound*T₀) (numericCutoff A C (e+1))))),?_⟩
  intro Φ hsp hlarge
  let M := Φ.val.variables
  have hgcut := (le_max_left _ _).trans hlarge
  have hrest := (le_max_right _ _).trans hlarge
  have hN₀ : 2^(4*k₀) ≤ M := (le_max_left _ _).trans hrest
  have hrest' := (le_max_right _ _).trans hrest
  have hM : 16 ≤ M := (le_max_left _ _).trans hrest'
  have hrest'' := (le_max_right _ _).trans hrest'
  have hT₀ : B.degreeBound*T₀ ≤ M := (le_max_left _ _).trans hrest''
  have hnum : numericCutoff A C (e+1) ≤ M := (le_max_right _ _).trans hrest''
  have hgeom := V39CurrentSourceJoin.source_geometry D B Φ
  have hsource : M ≤ B.degreeBound*(t10Graph D B Φ).vertices := by
    have hs := (DeterministicETHSourceBridge.fixed_graph_source D B Φ).2.1
    exact hs.trans ((Nat.le_mul_of_pos_left _ (by decide : 0<2)).trans hgeom.2.2)
  have hg : (t10Graph D B Φ).vertices ≤ M^e :=
    DeterministicETHSourceBridge.sparse_graph_vertices_polynomial D B cs Φ hsp hgcut
  have h := actual_numerics B.degreeBound k₀ M e T₀ (t10Graph D B Φ)
    (t10Graph_valid D B Φ) B.degreeBound_pos (V42ActualSource.k0_two D B) hgeom.1 hgeom.2.2
    (V42ActualSource.k0_degree D B) hM (by unfold e;omega) hsource hg hN₀ hT₀ hnum
  exact h

theorem classification_all_large (A : PermittedDeterministicEstimator) (cs T₀ : ℕ)
    (hA : GrowingSquareAccuracy A (constructionError D B) T₀) :
    ∃ M₀ : ℕ, ∀ Φ : ValidFormula,
      Φ.val.clauses.length ≤ cs*Φ.val.variables → M₀ ≤ Φ.val.variables →
      (V42PermittedExtraction.estimator A).run
        (V42ActualSource.request D B Φ (rounds (amplification D B) Φ.val.variables))=
          [decide (EncodedCNF.Satisfiable Φ.val)] := by
  obtain ⟨M₀,hnum⟩ := source_numerics D B cs T₀
  refine ⟨M₀,?_⟩
  intro Φ hsp hlarge
  obtain ⟨hk,hT,hgap⟩ := hnum Φ hsp hlarge
  let K := rounds (amplification D B) Φ.val.variables
  let E := V42PermittedExtraction.estimator A
  have hv : ValidTable (V42ActualSource.word D B Φ K) :=
    valid_of_target (V42ActualSource.word_target D B Φ K)
  have hacc : |E.value (E.output (V42ActualSource.word D B Φ K))-
      (Workspace.Types.CommComplexity.D (V42ActualSource.run D B Φ K).entry:ℝ)| ≤
      constructionError D B*Real.logb 2
        (Real.logb 2 (V42ActualLower.entryCount (V42ActualSource.run D B Φ K))) := by
    rw [V42PermittedExtraction.estimator_value,V42PermittedExtraction.estimator_output A _ hv]
    simpa only [V42ActualSource.word] using stored_accuracy A _ T₀ hA (V42ActualSource.run D B Φ K) hT
  have hm := midpoint_outputs E (V42ActualSource.word D B Φ K)
    (Workspace.Types.CommComplexity.D (V42ActualSource.run D B Φ K).entry)
    (V42ActualSource.threshold D B Φ K) K
    (constructionError D B*Real.logb 2
      (Real.logb 2 (V42ActualLower.entryCount (V42ActualSource.run D B Φ K))))
    (by simpa only [mul_assoc] using hgap) hacc (V42ActualSource.source_comparison D B A Φ K)
  by_cases hs : EncodedCNF.Satisfiable Φ.val
  · simpa only [V42ActualSource.request,hs,decide_true] using hm.1 (V42ActualSource.run_yes D B Φ K hs)
  · simpa only [V42ActualSource.request,hs,decide_false] using hm.2 (V42ActualSource.run_no D B Φ K hs).ge

#print axioms outputs
#print axioms classification_all_large

def semanticCutoff (A : PermittedDeterministicEstimator) (cs T₀ : ℕ)
    (hA : GrowingSquareAccuracy A (constructionError D B) T₀) : ℕ :=
  max 1 (Classical.choose (classification_all_large D B A (cs+2) T₀ hA))

theorem semanticCutoff_pos (A : PermittedDeterministicEstimator) (cs T₀ : ℕ)
    (hA : GrowingSquareAccuracy A (constructionError D B) T₀) :
    1 ≤ semanticCutoff D B A cs T₀ hA := le_max_left _ _

def algorithm (A : PermittedDeterministicEstimator) (cs T₀ : ℕ)
    (hA : GrowingSquareAccuracy A (constructionError D B) T₀) :
    DeterministicSparseETH.Algorithm where
  machine := machine D B (V42PermittedExtraction.estimator A) cs
    (semanticCutoff D B A cs T₀ hA) (semanticCutoff_pos D B A cs T₀ hA)
  answer w := decide (EncodedCNF.Satisfiable
    (sparseFormula cs (semanticCutoff D B A cs T₀ hA) (semanticCutoff_pos D B A cs T₀ hA) w).val)
  time := time D B (V42PermittedExtraction.estimator A) cs
    (semanticCutoff D B A cs T₀ hA) (semanticCutoff_pos D B A cs T₀ hA)
  run w := by
    let cut := semanticCutoff D B A cs T₀ hA
    let hc := semanticCutoff_pos D B A cs T₀ hA
    let Φ := sparseFormula cs cut hc w
    have hclass := Classical.choose_spec (classification_all_large D B A (cs+2) T₀ hA) Φ
      (routed_sparse cs cut hc w)
      ((le_max_right _ _).trans (AEth4.routed4_variables (cs+2) cut w))
    have hr := outputs D B (V42PermittedExtraction.estimator A) cs cut hc w
    rw [hclass] at hr
    exact hr

theorem algorithm_correct (A : PermittedDeterministicEstimator) (cs T₀ : ℕ)
    (hA : GrowingSquareAccuracy A (constructionError D B) T₀) :
    ∀ Φ : ValidFormula, Φ.val.clauses.length ≤ cs*Φ.val.variables →
      ((algorithm D B A cs T₀ hA).answer (EncodedCNF.encode Φ.val)=true ↔
        EncodedCNF.Satisfiable Φ.val) := by
  intro Φ hsp
  change decide (EncodedCNF.Satisfiable (sparseFormula cs _ _ (EncodedCNF.encode Φ.val)).val)=true ↔ _
  simp only [decide_eq_true_eq]
  exact routed_sat_iff cs _ _ Φ hsp

theorem combine_clock_quasipoly (F : Producer) (w : List Bool) (A C b M N : ℕ)
    (hM : 2 ≤ M) (hN : N ≤ M^b) (hlen : w.length+1 ≤ (M+2)^3) :
    frontClock F w+N^(C*A^(rounds A M)) ≤
      2^((frontClockCoefficient F+3*frontClockDegree F+b*C+1)*(quasiLog M)^2) := by
  let L := quasiLog M
  let K := frontClockCoefficient F
  let d := frontClockDegree F
  have hL : 1 ≤ L := by
    have h := Nat.clog_mono_right 2 (show 2 ≤ M+2 by omega)
    exact (show 1=Nat.clog 2 2 by decide).le.trans h
  have hLsq : L ≤ L^2 := Nat.le_self_pow (by decide : 2≠0) L
  have hsq : 1 ≤ L^2 := Nat.one_le_pow _ _ hL
  have hMp : M+2 ≤ 2^L := Nat.le_pow_clog (by decide) _
  have hXp : (w.length+1)^d ≤ 2^(3*d*L) := by
    calc
      (w.length+1)^d ≤ ((M+2)^3)^d := Nat.pow_le_pow_left hlen _
      _ ≤ ((2^L)^3)^d := Nat.pow_le_pow_left (Nat.pow_le_pow_left hMp 3) _
      _ = _ := by simp only [←pow_mul]; congr 1; ring
  have hfront : frontClock F w ≤ 2^((K+3*d)*L^2) := by
    calc
      frontClock F w ≤ K*(w.length+1)^d := frontClock_le F w
      _ ≤ (2^K)*(2^(3*d*L)) := Nat.mul_le_mul (V39UniformResource.self_le_two_pow K) hXp
      _ = 2^(K+3*d*L) := by rw [pow_add]
      _ ≤ _ := by
        apply Nat.pow_le_pow_right (by decide)
        have hk := Nat.mul_le_mul_left K hsq
        have hd := Nat.mul_le_mul_left (3*d) hLsq
        nlinarith
  have hmain := main_clock_quasipoly A C b M N hM hN
  let E := K+3*d+b*C
  have hf : frontClock F w ≤ 2^(E*L^2) := hfront.trans
    (Nat.pow_le_pow_right (by decide)
      (Nat.mul_le_mul_right (L^2) (show K+3*d ≤ E by dsimp [E]; omega)))
  have hm : N^(C*A^(rounds A M)) ≤ 2^(E*L^2) := hmain.trans
    (Nat.pow_le_pow_right (by decide)
      (Nat.mul_le_mul_right (L^2) (show b*C ≤ E by dsimp [E]; omega)))
  calc
    _ ≤ 2^(E*L^2)+2^(E*L^2) := Nat.add_le_add hf hm
    _ = 2^(E*L^2+1) := by rw [pow_succ]; ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by dsimp [E,L,K,d]; nlinarith)

theorem physical_clock_all_large (E : Estimator) (cs cutoff : ℕ) (hcut : 1 ≤ cutoff) :
    ∃ C M₀ : ℕ, ∀ Φ : ValidFormula,
      Φ.val.clauses.length ≤ cs*Φ.val.variables → M₀ ≤ Φ.val.variables →
      time D B E cs cutoff hcut (EncodedCNF.encode Φ.val) ≤
        2^(C*(quasiLog Φ.val.variables)^2) := by
  let F := front D B cs cutoff hcut
  let C := V42ETHPhysical.mainExponent D B E
  let e := D.sizeExponent+3
  refine ⟨frontClockCoefficient F+3*frontClockDegree F+(e+1)*C+1,
    max cutoff (max (DeterministicETHSourceBridge.graphPolynomialCutoff D B cs)
      (max (2^(4*V42ActualSource.k0 D B)) (max 16 (28*cs+9)))),?_⟩
  intro Φ hsp hlarge
  let M := Φ.val.variables
  have hcutΦ : cutoff ≤ M := (le_max_left _ _).trans hlarge
  have hrest := (le_max_right _ _).trans hlarge
  have hgcut := (le_max_left _ _).trans hrest
  have hrest' := (le_max_right _ _).trans hrest
  have hN₀ : 2^(4*V42ActualSource.k0 D B) ≤ M := (le_max_left _ _).trans hrest'
  have hrest'' := (le_max_right _ _).trans hrest'
  have hM : 16 ≤ M := (le_max_left _ _).trans hrest''
  have hlenCut : 28*cs+9 ≤ M := (le_max_right _ _).trans hrest''
  have hg : (t10Graph D B Φ).vertices ≤ M^e :=
    DeterministicETHSourceBridge.sparse_graph_vertices_polynomial D B cs Φ hsp hgcut
  have hN : V42ETHPhysical.N D B Φ ≤ M^(e+1) :=
    V42ETHNumerics.selected_polynomial (V42ActualSource.k0 D B) M e (t10Graph D B Φ)
      hM (by unfold e;omega) hg hN₀
  have hlen : (EncodedCNF.encode Φ.val).length+1 ≤ (M+2)^3 := by
    have h := Unit4Shell.T24RuntimeComposed.encode_length_cube cs Φ hsp hlenCut
    change 2*(EncodedCNF.encode Φ.val).length+3 ≤ (M+2)^3 at h
    omega
  have h := combine_clock_quasipoly F (EncodedCNF.encode Φ.val) (amplification D B) C (e+1) M
    (V42ETHPhysical.N D B Φ) (by omega) hN hlen
  unfold time
  rw [routed_original cs cutoff hcut Φ hsp hcutΦ]
  exact h

include D B in
/-- The target corollary: the same fixed physical machine decides every
sparse formula. The quasipolynomial clock is eventual, as in asymptotic O.
Its finite exceptions are already decided by the charged sparse router. -/
theorem deterministic_estimation_to_sparse3SAT :
    ∃ c : ℝ, 0<c ∧
      ∀ A : PermittedDeterministicEstimator, ∀ T₀ : ℕ,
      GrowingSquareAccuracy A c T₀ → ∀ cs : ℕ,
      ∃ P : DeterministicSparseETH.Algorithm,
        (∀ Φ : ValidFormula, Φ.val.clauses.length ≤ cs*Φ.val.variables →
          (P.answer (EncodedCNF.encode Φ.val)=true ↔ EncodedCNF.Satisfiable Φ.val)) ∧
        ∃ C M₀ : ℕ, ∀ Φ : ValidFormula,
          Φ.val.clauses.length ≤ cs*Φ.val.variables → M₀ ≤ Φ.val.variables →
          P.time (EncodedCNF.encode Φ.val) ≤ 2^(C*(quasiLog Φ.val.variables)^2) := by
  refine ⟨constructionError D B,constructionError_pos D B,?_⟩
  intro A T₀ hA cs
  refine ⟨algorithm D B A cs T₀ hA,algorithm_correct D B A cs T₀ hA,?_⟩
  exact physical_clock_all_large D B (V42PermittedExtraction.estimator A) cs
    (semanticCutoff D B A cs T₀ hA) (semanticCutoff_pos D B A cs T₀ hA)

#print axioms algorithm
#print axioms algorithm_correct
#print axioms physical_clock_all_large
#print axioms deterministic_estimation_to_sparse3SAT
end
end CurrentAdditive.V43DeterministicRate
