import CurrentAdditive.V22FullSchedulePeak
import CurrentAdditive.V22RawGraphParameters

set_option maxHeartbeats 2000000
set_option maxRecDepth 32768
namespace V22FullScheduleClock
noncomputable section
open V22UnaryExpression V22FullScheduleExpressions V22FullScheduleBatch V22FullSchedulePeak
open V38Schedule V39PublicSchedule V39FullSampleResources

def coefficientSum : ℕ := ∑ i : Fin 19, ((expressions i).coefficient+11)
def coefficient : ℕ := 19*coefficientSum+1
def exponent : ℕ := 25*coefficient+600

private theorem prefix_le {q : ℕ} (bits : List Bool) (outs : Fin q → List Bool)
    (times : Fin q → ℕ) (C : ℕ)
    (h : ∀ i, 2*bits.length+times i+2*(outs i).length+7 ≤ C)
    (j : ℕ) (hj : j ≤ q) :
    V22ParameterBatch.clockPrefix bits outs times j ≤ j*C := by
  induction j with
  | zero => simp [V22ParameterBatch.clockPrefix]
  | succ j ih =>
      have hlt : j<q := by omega
      rw [V22ParameterBatch.clockPrefix,dif_pos hlt]
      have hp := ih (by omega)
      have hi := h ⟨j,hlt⟩
      nlinarith

theorem batch_polynomial (n k edgeCount : ℕ) (cc δv ζ : ℚ)
    (hn : 2 ≤ n) (hk : 1 ≤ k)
    (ht : FullTests cc (Nat.clog 2 n) edgeCount δv ζ) :
    V22FullScheduleBatch.clock n k ≤ coefficient*(n+k+cap n k+2)^2 := by
  let M := cap n k
  let W := n+k+M+2
  have hW : 1 ≤ W := by dsimp [W]; omega
  have hW2 : W ≤ W^2 := by nlinarith
  have hlen : (EthInapproximability.CurrentPaper.MatrixUnaryArithmetic.encodeInput n k).length ≤ W := by
    simp only [EthInapproximability.CurrentPaper.MatrixUnaryArithmetic.encodeInput,
      List.length_append,List.length_replicate,List.length_cons]
    dsimp [W]; omega
  have hp := all_peaks n k edgeCount cc δv ζ hn hk ht
  have hcost (i : Fin 19) :
      2*(EthInapproximability.CurrentPaper.MatrixUnaryArithmetic.encodeInput n k).length+
        times n k i+2*(results n k i).length+7 ≤ coefficientSum*W^2 := by
    have hv := ((expressions i).eval_le_peak n k).trans (hp i)
    have htime := (expressions i).clock_le_of_peak n k M (hp i)
    change times n k i ≤ (expressions i).coefficient*W^2 at htime
    have hsum : (expressions i).coefficient+11 ≤ coefficientSum := by
      change (expressions i).coefficient+11 ≤ ∑ j : Fin 19,((expressions j).coefficient+11)
      exact Finset.single_le_sum (f := fun j : Fin 19 => (expressions j).coefficient+11)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hmul := Nat.mul_le_mul_right (W^2) hsum
    have hval : (results n k i).length ≤ W := by
      simp only [results,List.length_replicate]
      exact hv.trans (by dsimp [W,M]; omega)
    nlinarith
  have hprefix := prefix_le _ (results n k) (times n k) (coefficientSum*W^2) hcost 19 le_rfl
  change V22ParameterBatch.clockPrefix _ _ _ 19+1 ≤ coefficient*W^2
  unfold coefficient
  nlinarith

/-- One absolute exponential constant bounds the actual schedule compiler,
uniformly for every supplied k ≥ 1. -/
theorem batch_exponential (n k edgeCount : ℕ) (cc δv ζ : ℚ)
    (hn : 2 ≤ n) (hk : 1 ≤ k)
    (ht : FullTests cc (Nat.clog 2 n) edgeCount δv ζ) :
    V22FullScheduleBatch.clock n k ≤ 2^(exponent*R n k) := by
  have hL : 16 ≤ Nat.clog 2 n := ht.2.2.1
  have hR : 1 ≤ R n k := by unfold R; nlinarith
  let M := cap n k
  have hM : 1 ≤ M := Nat.one_le_two_pow
  have hp := all_peaks n k edgeCount cc δv ζ hn hk ht
  have hnM : n ≤ M := by simpa only [expressions,Expr.peak] using hp 3
  have hkM : k ≤ M := by simpa only [expressions,Expr.peak] using hp 7
  have hW : n+k+M+2 ≤ 5*M := by omega
  have hp2 := Nat.pow_le_pow_left hW 2
  have hclock := batch_polynomial n k edgeCount cc δv ζ hn hk ht
  have hc : coefficient*(n+k+M+2)^2 ≤ 25*coefficient*M^2 := by nlinarith
  have hC : 25*coefficient ≤ 2^(25*coefficient*R n k) := by
    exact Nat.lt_two_pow_self.le.trans
      (Nat.pow_le_pow_right (by decide) (by nlinarith))
  calc
    V22FullScheduleBatch.clock n k ≤ 25*coefficient*M^2 := hclock.trans hc
    _ ≤ 2^(25*coefficient*R n k)*M^2 := Nat.mul_le_mul_right _ hC
    _=2^(exponent*R n k) := by
      dsimp [M,cap,exponent]
      rw [←pow_mul,←pow_add]
      congr 1
      ring

/-- The actual raw-input clock includes the physical graph parser. Its graph
input term is polynomial in the literal encoded length, and every remaining
operation is bounded by the same source-uniform exponential constant. -/
theorem raw_exponential (bits : List Bool) (n k edgeCount : ℕ) (cc δv ζ : ℚ)
    (hn : 2 ≤ n) (hk : 1 ≤ k)
    (ht : FullTests cc (Nat.clog 2 n) edgeCount δv ζ) :
    V22RawGraphParameters.clock bits n k ≤
      102*(bits.length+1)^3+2^((exponent+6)*R n k) := by
  have hL : 16 ≤ Nat.clog 2 n := ht.2.2.1
  have hR : 1 ≤ R n k := by unfold R; nlinarith
  have hclock := batch_exponential n k edgeCount cc δv ζ hn hk ht
  let Z := 2^(exponent*R n k)
  have hp := all_peaks n k edgeCount cc δv ζ hn hk ht
  have hcap : cap n k ≤ Z := Nat.pow_le_pow_right (by decide) (by
    unfold exponent
    nlinarith)
  have hnCap : n ≤ cap n k := by simpa only [expressions,Expr.peak] using hp 3
  have hkCap : k ≤ cap n k := by simpa only [expressions,Expr.peak] using hp 7
  have hnZ : n ≤ Z := hnCap.trans hcap
  have hkZ : k ≤ Z := hkCap.trans hcap
  have hZ : 1 ≤ Z := Nat.one_le_two_pow
  have hlen : bits.length ≤ (bits.length+1)^3 := by
    nlinarith [Nat.zero_le (bits.length^3),Nat.zero_le (bits.length^2)]
  have hexp : 64*Z ≤ 2^((exponent+6)*R n k) := by
    calc
      64*Z=2^(exponent*R n k+6) := by dsimp [Z]; rw [pow_add]; norm_num; ring
      _ ≤ 2^((exponent+6)*R n k) := Nat.pow_le_pow_right (by decide) (by nlinarith)
  unfold V22RawGraphParameters.clock V22RawGraphParameters.vertexClock V22RawGraphParameters.pairClock
  simp only [EthInapproximability.CurrentPaper.MatrixUnaryArithmetic.encodeInput,
    List.length_append,List.length_replicate,List.length_cons]
  change V22FullScheduleBatch.clock n k ≤ Z at hclock
  nlinarith

#print axioms batch_polynomial
#print axioms batch_exponential
#print axioms raw_exponential

/-- The source's proved large-input cutoff discharges every numerical clock
premise for the same actual raw graph+k run. No prepared count bank, scalar
oracle, or separately assumed physical running-time bound is used. -/
theorem promised_run
    (g : EthInapproximability.CurrentPaper.EncodedGraph.Graph) (hg : g.Valid)
    (k Δ : ℕ) (γ : ℚ) (hk : 1 ≤ k) (hγ : 0<γ) (hΔ : 0<Δ)
    (hnm : g.vertices ≤ 2*g.edges.length) (hdeg : 2*g.edges.length ≤ Δ*g.vertices)
    (hlarge : V39FullCutoff.sourceCutoff γ Δ ≤ g.vertices) :
    ∃ t ≤ 102*((EthInapproximability.CurrentPaper.EncodedGraph.encode g).length+1)^3+
        2^((exponent+6)*R g.vertices k),
      ((EthInapproximability.CurrentPaper.BitMachineEncoding.advance V22RawGraphParameters.program)^[t])
        (⟨some V22RawGraphParameters.start,V22RawGraphParameters.control,
          V22RawGraphParameters.initial (EthInapproximability.CurrentPaper.EncodedGraph.encode g) k⟩ :
          Turing.TM2.Cfg (fun _ : V22RawGraphParameters.Stack => Bool) _ _) =
        ⟨none,V22RawGraphParameters.control,
          V22RawGraphParameters.final (EthInapproximability.CurrentPaper.EncodedGraph.encode g) g.vertices k⟩ := by
  have hcut : 0<V39FullCutoff.sourceCutoff γ Δ := by
    unfold V39FullCutoff.sourceCutoff
    positivity
  have hn0 : 0<g.vertices := hcut.trans_le hlarge
  have ht := V39FullCutoff.fullPublicTests_all_large γ Δ g.vertices g.edges.length
    hγ hΔ hn0 hnm hdeg hlarge
  have hL : 16 ≤ Nat.clog 2 g.vertices := ht.2.2.1
  have hn : 2 ≤ g.vertices := by
    by_contra h
    have he : g.vertices=1 := by omega
    norm_num [he] at hL
  obtain ⟨t,htr,hr⟩ := V22RawGraphParameters.run g hg k
  refine ⟨t,htr.trans ?_,hr⟩
  exact raw_exponential _ g.vertices k g.edges.length
    (fullConstant γ Δ g.vertices g.edges.length)
    (sourceDeltaV γ Δ g.vertices g.edges.length) (sourceZeta γ) hn hk ht

#print axioms promised_run
end
end V22FullScheduleClock
