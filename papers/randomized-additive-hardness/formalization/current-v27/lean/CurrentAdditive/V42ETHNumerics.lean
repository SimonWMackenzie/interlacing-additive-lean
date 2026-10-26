import CurrentAdditive.V42ActualLower
import CurrentAdditive.V42RuntimeDyadic
import CurrentAdditive.V39RuntimeETHNumerics

namespace CurrentAdditive.V42ETHNumerics
noncomputable section
open Paper2 EthInapproximability.CurrentPaper
open V42Schedule V42GraphRuntime V42ActualLower
open V39RuntimeETHNumerics DeterministicEndpointNumeric V39ActualETHNumerics
set_option maxHeartbeats 300000
set_option maxRecDepth 32768

def sizeExponent (Δ k₀:ℕ) := (8*Δ+8)*squareExponent k₀+1040

theorem sizeExponent_ge (Δ k₀:ℕ) : 1040  ≤  sizeExponent Δ k₀ := by unfold sizeExponent;omega

theorem actual_size (Δ k₀:ℕ) (g:EncodedGraph.Graph) (hg:g.Valid) (K:ℕ)
    (hk₀:2  ≤  k₀) (hn:0<g.vertices) (hdegree:2*g.edges.length  ≤  Δ*g.vertices) (hcut:2*Δ  ≤  k₀) :
    (publicRun Δ k₀ g hg hk₀ hn hdegree hcut K).squareWord.length  ≤
      (V42RuntimePrefix.N k₀ g)^(sizeExponent Δ k₀*(amplification k₀)^K) := by
  have h:=(public_outputs Δ k₀ g hg hk₀ hn hdegree hcut K).2
  have hN:2  ≤  V42RuntimePrefix.N k₀ g := by
    have hk:=selected_ge_two k₀ hk₀ g
    change 2  ≤  2^(4*V42RuntimePrefix.selected k₀ g)
    exact (by decide : 2  ≤  2^1).trans (Nat.pow_le_pow_right (by decide) (show 1  ≤  4*V42RuntimePrefix.selected k₀ g by omega))
  exact V40GraphConstructorInputBounds.dyadic_clock_bound _ _ _ (8*Δ+6)
    (squareExponent k₀) (amplification k₀) K hN (base_le_dyadic Δ k₀ g hg hk₀ hdegree) h

#print axioms actual_size

theorem selected_polynomial (k₀ M e:ℕ) (g:EncodedGraph.Graph)
    (hM:16  ≤  M) (he:1  ≤  e) (hg:g.vertices  ≤  M^e) (hcut:2^(4*k₀)  ≤  M) :
    V42RuntimePrefix.N k₀ g  ≤  M^(e+1) := by
  have hm:M  ≤  M^e := by
    calc
      M=M^1 := by simp
      _   ≤  M^e := Nat.pow_le_pow_right (by omega) he
  have hmax:max g.vertices (2^(4*k₀))  ≤  M^e := max_le hg (hcut.trans hm)
  have hp:=(V42PublicCutoff.generated_padding g.vertices k₀).2
  rw [V42PublicSchedule.generatedN_exact,V42PublicSchedule.generatedN_exact] at hp
  change V42RuntimePrefix.N k₀ g  ≤  M^(e+1)
  calc
    _   ≤  16*M^e := hp.le.trans (Nat.mul_le_mul_left _ hmax)
    _   ≤  M^(e+1) := by rw [pow_succ];nlinarith

#print axioms selected_polynomial


/-- Generic integer/real arithmetic is proved before substituting the very
large concrete machine constants. This prevents numeral evaluation of A. -/
theorem numeric_from_upper (A C M N e T W:ℕ)
    (hA:2^64 ≤ A) (hC:1040 ≤ C) (hM:2 ≤ M) (he:1 ≤ e)
    (hN:N ≤ M^e) (hTW:T ≤ W) (hW:W ≤ N^(C*A^(rounds A M))) (hT2:2 ≤ T) (hNpos:0<N)
    (hlarge:2^(max (32*(C*e)+16) (8*amplificationLog A)) ≤ M) :
    0<errorCoefficient A ∧ 1 ≤ rounds A M ∧
      2*(errorCoefficient A:ℝ)*Real.logb 2 (Real.logb 2 T)<rounds A M ∧
      W ≤ M^(e*C*(2^amplificationLog A)^(rounds A M)) := by
  let a:=amplificationLog A
  let K:=rounds A M
  have ha:1 ≤ a := (by decide : 1 ≤ 64).trans (amplificationLog_ge A hA)
  have hT:T ≤ N^(C*(2^a)^K) := hTW.trans (hW.trans
    (Nat.pow_le_pow_right hNpos (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (amplification_le A) K))))
  have hmargin:=eth_margin_from_polynomial_source a C e M N ha (by omega) he hN hlarge
  have hgap:=eth_loglog_gap N C a K T ha hT hmargin
  have hreal:=real_double_log_le_clog T hT2
  have har:(0:ℝ)<a := by exact_mod_cast (Nat.zero_lt_of_lt ha)
  have hcoeff:0 ≤ 2*(1/(4*(a:ℝ))) := mul_nonneg (by norm_num)
    (div_nonneg (by norm_num) (mul_nonneg (by norm_num) har.le))
  have hgapR:=lt_of_le_of_lt (mul_le_mul_of_nonneg_left hreal hcoeff) hgap
  have hk:1 ≤ K := ethIterations_positive a M ha
    ((Nat.pow_le_pow_right (by decide) (show 2*a ≤ max (32*(C*e)+16) (8*a) by omega)).trans hlarge)
  have hsize:W ≤ M^(e*C*(2^a)^K) := by
    calc
      W ≤ N^(C*A^K) := hW
      _  ≤ (M^e)^(C*A^K) := Nat.pow_le_pow_left hN _
      _ =M^(e*C*A^K) := by rw [←pow_mul];congr 1;ring
      _  ≤ _ := Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (amplification_le A) K))
  exact ⟨coefficient_positive A hA,hk,by simpa only [coefficient_cast] using hgapR,hsize⟩

theorem actual_numerics (Δ k₀ M e T₀:ℕ) (g:EncodedGraph.Graph) (hg:g.Valid)
    (hΔ:0<Δ) (hk₀:2 ≤ k₀) (hn:0<g.vertices)
    (hdegree:2*g.edges.length ≤ Δ*g.vertices) (hcut:2*Δ ≤ k₀)
    (hM:16 ≤ M) (he:1 ≤ e) (hsource:M ≤ Δ*g.vertices) (hgraph:g.vertices ≤ M^e)
    (hN₀:2^(4*k₀) ≤ M) (hT₀:Δ*T₀ ≤ M)
    (hlarge:2^(max (32*(sizeExponent Δ k₀*(e+1))+16)
      (8*amplificationLog (amplification k₀))) ≤ M) :
    let K:=rounds (amplification k₀) M
    let R:=publicRun Δ k₀ g hg hk₀ hn hdegree hcut K
    0<errorCoefficient (amplification k₀) ∧ 1 ≤ K ∧ T₀ ≤ V42ActualLower.entryCount R ∧
      2*(errorCoefficient (amplification k₀):ℝ)*
        Real.logb 2 (Real.logb 2 (V42ActualLower.entryCount R))<K ∧
      R.squareWord.length ≤ M^((e+1)*sizeExponent Δ k₀*(2^amplificationLog (amplification k₀))^K) := by
  let K:=rounds (amplification k₀) M
  dsimp only
  generalize hR:publicRun Δ k₀ g hg hk₀ hn hdegree hcut K=R
  let N:=V42RuntimePrefix.N k₀ g
  have hW:R.squareWord.length ≤ N^(sizeExponent Δ k₀*(amplification k₀)^K) := by
    rw [←hR]
    exact actual_size Δ k₀ g hg K hk₀ hn hdegree hcut
  have hside:N ≤ SquarePadding.side R.rows R.cols := by
    rw [←hR]
    exact V42ActualLower.public_side (V42RuntimePrefix.selected k₀ g) (selected_ge_two k₀ hk₀ g) hn
      (selected_width Δ k₀ g hdegree hcut) (LiteralEdgeEncoder.edge g hg) K
  have hnN:g.vertices ≤ N := by
    simpa only [V42PublicSchedule.generatedN_exact] using
      (V42PublicCutoff.generatedExponent_spec g.vertices k₀).2
  have hT₀n:T₀ ≤ g.vertices := Nat.le_of_mul_le_mul_left (hT₀.trans hsource) hΔ
  have hmin:T₀ ≤ V42ActualLower.entryCount R :=
    (hT₀n.trans (hnN.trans hside)).trans (Nat.le_self_pow (by decide : 2≠0) _)
  have hN2:2 ≤ N := by
    change 2 ≤ 2^(4*V42RuntimePrefix.selected k₀ g)
    have hk:=selected_ge_two k₀ hk₀ g
    have hpk:1 ≤ 4*V42RuntimePrefix.selected k₀ g :=
      (by decide : 1 ≤ 4*2).trans (Nat.mul_le_mul_left 4 hk)
    exact (by decide : 2 ≤ 2^1).trans (Nat.pow_le_pow_right (by decide) hpk)
  have hT2:2 ≤ V42ActualLower.entryCount R :=
    (hN2.trans hside).trans (Nat.le_self_pow (by decide : 2≠0) _)
  have h:=numeric_from_upper (amplification k₀) (sizeExponent Δ k₀) M N (e+1)
    (V42ActualLower.entryCount R) R.squareWord.length (amplification_ge k₀) (sizeExponent_ge Δ k₀)
    ((by decide : 2 ≤ 16).trans hM) (Nat.succ_pos e)
    (selected_polynomial k₀ M e g hM he hgraph hN₀) (entries_le_length R) hW hT2 (Nat.zero_lt_of_lt hN2) hlarge
  exact ⟨h.1,h.2.1,hmin,h.2.2.1,h.2.2.2⟩

#print axioms numeric_from_upper
#print axioms actual_numerics
end
end CurrentAdditive.V42ETHNumerics


