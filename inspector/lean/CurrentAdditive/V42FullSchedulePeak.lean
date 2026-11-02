import CurrentAdditive.V22ExpressionClock
import CurrentAdditive.V42FullScheduleBatch

set_option maxHeartbeats 2000000
namespace V42FullSchedulePeak
open V22UnaryExpression V42FullScheduleExpressions V42FullScheduleBatch
open V42RuntimeSchedule
open CurrentAdditive.V38OneStep CurrentAdditive.V39RecursiveGenerator

def SP (e : Expr) (n k M : ℕ) := e.Positive n k ∧ e.Safe M n k
private theorem sp_const (n k M a : ℕ) (ha : 0<a) (hM : a ≤ M) : SP (c a) n k M := ⟨ha,hM⟩
private theorem sp_add (a b : Expr) (n k M : ℕ) (ha : SP a n k M) (hb : SP b n k M) :
    SP (add a b) n k M := by
  exact ⟨⟨by have := a.eval_pos n k ha.1; change 0<a.eval n k+b.eval n k; omega,ha.1,hb.1⟩,ha.2,hb.2⟩
private theorem sp_mul (a b : Expr) (n k M : ℕ) (ha : SP a n k M) (hb : SP b n k M) :
    SP (mul a b) n k M := by
  exact ⟨⟨Nat.mul_pos (a.eval_pos n k ha.1) (b.eval_pos n k hb.1),ha.1,hb.1⟩,ha.2,hb.2⟩
private theorem sp_max (a b : Expr) (n k M : ℕ) (ha : SP a n k M) (hb : SP b n k M) :
    SP (maxE a b) n k M := by
  exact ⟨⟨lt_of_lt_of_le (a.eval_pos n k ha.1) (le_max_left _ _),ha.1,hb.1⟩,ha.2,hb.2⟩
private theorem sp_pow (a : Expr) (n k M : ℕ) (ha : SP a n k M) : SP (pow a) n k M :=
  ⟨⟨by change 0<2^a.eval n k; positivity,ha.1⟩,ha.2⟩
private theorem sp_log (a : Expr) (n k M : ℕ) (ha : SP a n k M)
    (hpos : 1<a.eval n k) (hbound : a.eval n k ≤ M) : SP (log a) n k M :=
  ⟨⟨Nat.clog_pos (by decide) hpos,ha.1⟩,hbound,ha.2⟩
private theorem sp_pred (a : Expr) (n k M : ℕ) (ha : SP a n k M)
    (hpos : 2 ≤ a.eval n k) (hbound : a.eval n k ≤ M) : SP (sub1 a) n k M :=
  ⟨⟨by change 0<a.eval n k-1; omega,ha.1⟩,hbound,ha.2⟩

def R (n k : ℕ) := (k+1)*Nat.clog 2 n
def cap (n k : ℕ) := 2^(300*R n k)
private theorem exp_mono (a b : ℕ) (h : a ≤ b) : 2^a ≤ 2^b :=
  Nat.pow_le_pow_right (by decide) h

/-- The largest intermediate scalar used by the literal physical compiler
has one absolute exponential bound. This includes log operands, the complete
sample argument, the exact max alphabet, and the entire reserved bit count. -/
theorem all_peaks (n k edgeCount : ℕ) (cc δv ζ : ℚ)
    (hn : 2 ≤ n) (hk : 1 ≤ k)
    (ht : FullTests cc (Nat.clog 2 n) edgeCount δv ζ) :
    ∀ i : Fin 19, (expressions i).peak n k ≤ cap n k := by
  let LL := Nat.clog 2 n
  let E := fullWidthExponent LL
  let F := fullSampleExponent LL k
  let K := fullDrawExponent LL k
  let M := cap n k
  have hL : 16 ≤ LL := ht.1.2.2.1
  have hR : 16 ≤ R n k := by dsimp [R,LL] at *; nlinarith
  have hLR : LL ≤ R n k := by dsimp [R,LL]; nlinarith
  have hkR : k ≤ R n k := by dsimp [R,LL] at *; nlinarith
  have hpower : 300*R n k ≤ M := Nat.lt_two_pow_self.le
  have hsmall (a : ℕ) (ha : a ≤ 300*R n k) : a ≤ M := ha.trans hpower
  have h512 : 512 ≤ M := hsmall _ (by omega)
  have hc (a : ℕ) (ha : 0<a) (ha512 : a ≤ 512) : SP (c a) n k M :=
    sp_const n k M a ha (ha512.trans h512)
  have hE : E=16*LL := rfl
  have hK : K ≤ 112*R n k := by
    simpa only [K,R,LL,Nat.mul_assoc] using (budget_exponents_linear LL k ht.2).1
  have hBlock : 2*E+K+17 ≤ 160*R n k := by
    simpa only [E,K,R,LL,Nat.mul_assoc] using (budget_exponents_linear LL k ht.2).2.1
  have hBits : 2*E+2*K+17 ≤ 272*R n k := by
    simpa only [E,K,R,LL,Nat.mul_assoc] using (budget_exponents_linear LL k ht.2).2.2
  obtain ⟨hnE,hpE,hq1E,hq2E,hsE,hwE,hQE⟩ :=
    full_widths_le_pow n LL (Nat.le_pow_clog (by decide) n) ht.2
  have hEM : 2^E ≤ M := exp_mono _ _ (by rw [hE]; omega)
  have hnM : n ≤ M := hnE.trans hEM
  have hkM : k ≤ M := hsmall _ (by omega)
  have hL1M : LL+1 ≤ M := hsmall _ (by omega)
  have hSM : fullS LL ≤ M := hsE.trans hEM
  have hS256 : 256 ≤ fullS LL := fullS_ge_256 LL
  have hB7 : 7 ≤ V42RuntimeSchedule.B LL k := CurrentAdditive.V42PublicSchedule.B_ge_seven LL k
  have hb := CurrentAdditive.V42PublicCutoff.full_cutoff_bounds 0 LL ht.2
  have hB : V42RuntimeSchedule.B LL k ≤ 8*(k+1)*LL :=
    CurrentAdditive.V42PublicSize.budget_linear LL k hb.2.2.1 hb.2.2.2.1
  have hH : V42RuntimeSchedule.H LL k ≤ 9*(k+1)*LL := by
    change V42RuntimeSchedule.B LL k+k ≤ _
    nlinarith
  have hBM : V42RuntimeSchedule.B LL k ≤ M := hsmall _ (by dsimp [R,LL] at *; nlinarith)
  have hHM : V42RuntimeSchedule.H LL k ≤ M := hsmall _ (by dsimp [R,LL] at *; nlinarith)
  have hmF := full_sampleSide_le_pow LL k ht.2
  have hmM : sampleSide LL k ≤ M := hmF.trans (exp_mono _ _ (by
    change 40*(k+1)*LL ≤ 300*R n k
    dsimp [R,LL]; nlinarith))
  have hr : 0<rankBound LL k := by change 0<2^(V42RuntimeSchedule.B LL k-1); positivity
  have hlogr : 0<Nat.clog 2 (rankBound LL k+2) := Nat.clog_pos (by decide) (by omega)
  have hHpow : 0<2^V42RuntimeSchedule.H LL k := by positivity
  have harg : sampleArgument.eval n k ≤ sampleSide LL k :=
    V39PublicSchedule.pow2Ceil_lower _
  have hargM : sampleArgument.eval n k ≤ M := harg.trans hmM
  have harg16 : 16 ≤ sampleArgument.eval n k := by
    change 16 ≤ 16*(rankBound LL k+1)*Nat.clog 2 (rankBound LL k+2)*2^V42RuntimeSchedule.H LL k
    have h1 : 1 ≤ rankBound LL k+1 := by omega
    have h2 : 1 ≤ Nat.clog 2 (rankBound LL k+2) := by omega
    have h3 : 1 ≤ 2^V42RuntimeSchedule.H LL k := by omega
    exact ((Nat.le_mul_of_pos_right 16 (by omega : 0<rankBound LL k+1)).trans
      (Nat.le_mul_of_pos_right _ hlogr)).trans (Nat.le_mul_of_pos_right _ hHpow)
  have hr2M : rankBound LL k+2 ≤ M := by
    have hbound : rankBound LL k+2 ≤ sampleArgument.eval n k := by
      change rankBound LL k+2 ≤ 16*(rankBound LL k+1)*Nat.clog 2 (rankBound LL k+2)*2^V42RuntimeSchedule.H LL k
      have h1 : 16*(rankBound LL k+1) ≤ 16*(rankBound LL k+1)*Nat.clog 2 (rankBound LL k+2) :=
        Nat.le_mul_of_pos_right _ hlogr
      have h2 : 16*(rankBound LL k+1)*Nat.clog 2 (rankBound LL k+2) ≤
          16*(rankBound LL k+1)*Nat.clog 2 (rankBound LL k+2)*2^V42RuntimeSchedule.H LL k :=
        Nat.le_mul_of_pos_right _ hHpow
      omega
    exact hbound.trans hargM
  have hA := fullAlphabet_le n LL (Nat.le_pow_clog (by decide) n) ht.2
  have hAM : fullAlphabet n LL ≤ M := hA.trans (exp_mono _ _ (by change 2*(16*LL)+9 ≤ 300*R n k; omega))
  have hN : draws.eval n k=2^K := rfl
  have hNM : draws.eval n k ≤ M := by rw [hN]; exact exp_mono _ _ (by omega)
  have hargb : (mul (mul (c 200) alphabet) draws).eval n k ≤ 2^(2*E+K+17) := by
    simp only [mul,c,Expr.eval,Binary.value,eval_alphabet,eval_draws]
    change 200*fullAlphabet n LL*2^K ≤ _
    calc
      200*fullAlphabet n LL*2^K ≤ 2^8*2^(2*E+9)*2^K := by gcongr; norm_num
      _=2^(2*E+K+17) := by rw [←pow_add,←pow_add]; congr 1; omega
  have hargbM : (mul (mul (c 200) alphabet) draws).eval n k ≤ M :=
    hargb.trans (exp_mono _ _ (hBlock.trans (by omega)))
  have hA512 : 512 ≤ fullAlphabet n LL := le_max_left _ _
  have hargb2 : 1<(mul (mul (c 200) alphabet) draws).eval n k := by
    simp only [mul,c,Expr.eval,Binary.value,eval_alphabet,eval_draws]
    change 1<200*fullAlphabet n LL*2^K
    have hNpos : 0<2^K := by positivity
    have hprod := Nat.le_mul_of_pos_right (200*fullAlphabet n LL) hNpos
    omega
  have hbM : precision.eval n k ≤ M := by
    change Nat.clog 2 ((mul (mul (c 200) alphabet) draws).eval n k) ≤ M
    have hclog (a : ℕ) : Nat.clog 2 a ≤ a :=
      Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
    exact (hclog _).trans hargbM
  have hbitsM : totalBits.eval n k ≤ M := by
    have h := randomBits_le_expSum (fullAlphabet n LL) (2^K) E K hA le_rfl
    have hh : totalBits.eval n k ≤ 2^(2*E+2*K+17) := by
      simpa only [eval_totalBits] using h
    exact hh.trans (exp_mono _ _ (hBits.trans (by omega)))

  have pn : SP Expr.vertex n k M := ⟨by change 0<n; omega,hnM⟩
  have pk : SP Expr.iteration n k M := ⟨by change 0<k; omega,hkM⟩
  have pL : SP L n k M := sp_log _ _ _ _ pn (by exact hn) hnM
  have pell : SP ellE n k M := sp_log _ _ _ _
    (sp_add _ _ _ _ _ pL (hc 1 (by decide) (by decide)))
    (by change 1<LL+1; omega) hL1M
  have pseed : SP seed n k M := sp_pow _ _ _ _
    (sp_add _ _ _ _ _ (hc 6 (by decide) (by decide)) pell)
  have ps : SP s n k M := sp_pow _ _ _ _
    (sp_add _ _ _ _ _ (hc 16 (by decide) (by decide)) pell)
  have pq1 : SP q1 n k M := sp_pred _ _ _ _
    (sp_pred _ _ _ _ ps (by simpa using hS256.trans' (by decide : 2 ≤ 256)) hSM)
    (by change 2 ≤ fullS LL-1; omega) ((Nat.sub_le _ _).trans hSM)
  have pq2 : SP q2 n k M := sp_pow _ _ _ _
    (sp_add _ _ _ _ _ pL (sp_mul _ _ _ _ _ (hc 2 (by decide) (by decide))
      (sp_add _ _ _ _ _ (hc 16 (by decide) (by decide)) pell)))
  have pkE : SP (add (c 16) ellE) n k M :=
    sp_add _ _ _ _ _ (hc 16 (by decide) (by decide)) pell
  have pw : SP w n k M := sp_pow _ _ _ _ (sp_mul _ _ _ _ _ (hc 8 (by decide) (by decide)) pkE)
  have pQ : SP Q n k M := sp_pow _ _ _ _ (sp_mul _ _ _ _ _ (hc 24 (by decide) (by decide)) pkE)
  have ph : SP overhead n k M := sp_add _ _ _ _ _ pL
    (sp_mul _ _ _ _ _ (hc 36 (by decide) (by decide)) pkE)
  have pB : SP V42FullScheduleExpressions.B n k M := sp_add _ _ _ _ _
    (sp_add _ _ _ _ _ pell (hc 7 (by decide) (by decide))) (sp_mul _ _ _ _ _ pk ph)
  have pH : SP V42FullScheduleExpressions.H n k M := sp_add _ _ _ _ _ pB pk
  have prank : SP rank n k M := sp_pow _ _ _ _
    (sp_pred _ _ _ _ pB (by exact (by omega : 2 ≤ V42RuntimeSchedule.B LL k)) hBM)
  have parg : SP sampleArgument n k M := sp_mul _ _ _ _ _
    (sp_mul _ _ _ _ _
      (sp_mul _ _ _ _ _ (hc 16 (by decide) (by decide))
        (sp_add _ _ _ _ _ prank (hc 1 (by decide) (by decide))))
      (sp_log _ _ _ _ (sp_add _ _ _ _ _ prank (hc 2 (by decide) (by decide)))
        (by change 1<rankBound LL k+2; omega) hr2M))
    (sp_pow _ _ _ _ pH)
  have pm : SP sample n k M := sp_pow _ _ _ _ (sp_log _ _ _ _ parg (by omega) hargM)
  have pE : SP widthExponent n k M := sp_mul _ _ _ _ _ (hc 16 (by decide) (by decide)) pL
  have pF : SP sampleExponentE n k M := sp_mul _ _ _ _ _
    (sp_mul _ _ _ _ _ (hc 40 (by decide) (by decide))
      (sp_add _ _ _ _ _ pk (hc 1 (by decide) (by decide)))) pL
  have pD : SP drawExponent n k M := sp_add _ _ _ _ _
    (sp_add _ _ _ _ _ pF (hc 1 (by decide) (by decide)))
    (sp_add _ _ _ _ _
      (sp_add _ _ _ _ _
        (sp_mul _ _ _ _ _
          (sp_add _ _ _ _ _ (sp_mul _ _ _ _ _ (hc 3 (by decide) (by decide)) pE)
            (hc 3 (by decide) (by decide))) pk) pE) (hc 1 (by decide) (by decide)))
  have pN : SP draws n k M := sp_pow _ _ _ _ pD
  have pA : SP alphabet n k M := sp_max _ _ _ _ _ (hc 512 (by decide) (by decide))
    (sp_max _ _ _ _ _
      (sp_mul _ _ _ _ _ (sp_mul _ _ _ _ _ (hc 4 (by decide) (by decide)) ps)
        (sp_add _ _ _ _ _ pn ps))
      (sp_max _ _ _ _ _ pq2 (sp_max _ _ _ _ _ pw (sp_max _ _ _ _ _ pQ pseed))))
  have pb : SP precision n k M := sp_log _ _ _ _
    (sp_mul _ _ _ _ _ (sp_mul _ _ _ _ _ (hc 200 (by decide) (by decide)) pA) pN) hargb2 hargbM
  have pbits : SP totalBits n k M := sp_mul _ _ _ _ _ pb pN
  have pAll : ∀ i : Fin 19, SP (expressions i) n k M := by
    intro i
    fin_cases i
    · exact pq2
    · exact pq1
    · exact ps
    · exact pn
    · exact pw
    · exact pQ
    · exact pseed
    · exact pk
    · exact pm
    · exact pm
    · exact pb
    · exact pN
    · exact pbits
    · exact pA
    · exact pL
    · exact pell
    · exact pB
    · exact pH
    · exact prank
  have values : ∀ i : Fin 19, (expressions i).eval n k ≤ M := by
    intro i
    fin_cases i
    · change q2.eval n k ≤ M; rw [eval_q2]; exact hq2E.trans hEM
    · change q1.eval n k ≤ M; rw [eval_q1]; exact hq1E.trans hEM
    · change s.eval n k ≤ M; rw [eval_s]; exact hSM
    · exact hnM
    · change w.eval n k ≤ M; rw [eval_w]; exact hwE.trans hEM
    · change Q.eval n k ≤ M; rw [eval_Q]; exact hQE.trans hEM
    · change seed.eval n k ≤ M; rw [eval_seed]; exact hpE.trans hEM
    · exact hkM
    · change sample.eval n k ≤ M; rw [eval_sample]; exact hmM
    · change sample.eval n k ≤ M; rw [eval_sample]; exact hmM
    · exact hbM
    · exact hNM
    · exact hbitsM
    · change alphabet.eval n k ≤ M; rw [eval_alphabet]; exact hAM
    · change LL ≤ M; exact hsmall _ (by omega)
    · change ell LL ≤ M; exact (V39PublicSchedule.ell_le LL).trans (hsmall _ (by omega))
    · exact hBM
    · exact hHM
    · change rankBound LL k ≤ M; omega
  intro i
  exact (expressions i).peak_le n k M (pAll i).1 (pAll i).2 (values i)

#print axioms all_peaks
end V42FullSchedulePeak



