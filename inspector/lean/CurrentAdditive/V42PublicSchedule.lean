import CurrentAdditive.V42Schedule

/-! Literal public schedule for v42, def:amplification-parameters,
lem:full-schedule, lem:generated-schedule, prop:iteration and thm:uniform-reduction.
Only numerical parameters are defined here; no matrix, sampler or clock is assumed.
The width exponent `k` and iteration count `i` are separate variables. -/
namespace CurrentAdditive.V42PublicSchedule
open V42Schedule

def ell (L : ℕ) : ℕ := Nat.clog 2 (L+1)
def fullExponent (L : ℕ) : ℕ := 16+ell L
def fullOverhead (L : ℕ) : ℕ := L+36*fullExponent L
def generatedLog (k : ℕ) : ℕ := 4*k
def generatedN (k : ℕ) : ℕ := s k ^ 4
def generatedOverhead (k : ℕ) : ℕ := 40*k
def seedWidth (L : ℕ) : ℕ := V39PublicSchedule.seedWidth L
def seedCost (L : ℕ) : ℕ := ell L+7

theorem fullS_rounding (L : ℕ) :
    2^16*(L+1) ≤ s (fullExponent L) ∧
    s (fullExponent L) < 2^17*(L+1) :=
  V39PublicSchedule.fullS_rounding L

theorem full_power_logs (L : ℕ) :
    Nat.clog 2 (s (fullExponent L))=fullExponent L ∧
    Nat.clog 2 (q₂ (fullExponent L) L)=L+2*fullExponent L ∧
    Nat.clog 2 (w (fullExponent L))=8*fullExponent L ∧
    Nat.clog 2 (Q (fullExponent L))=24*fullExponent L := by
  simp [s,q₂,w,Q,Nat.clog_pow 2 _ (by decide)]

theorem fullOverhead_exact (L : ℕ) :
    2*Nat.clog 2 (s (fullExponent L)) + Nat.clog 2 (q₂ (fullExponent L) L) +
    Nat.clog 2 (w (fullExponent L)) + Nat.clog 2 (Q (fullExponent L)) =
      fullOverhead L := by
  obtain ⟨hs,hq,hw,hQ⟩:=full_power_logs L
  rw [hs,hq,hw,hQ]; unfold fullOverhead; omega

theorem generatedN_exact (k : ℕ) : generatedN k=2^(4*k) := by
  unfold generatedN s; rw [←pow_mul]; congr 1; omega

theorem generated_recipe (k : ℕ) :
    q₂ k (generatedLog k)=(s k)^6 ∧ w k=(s k)^8 ∧ Q k=(s k)^24 ∧
    rho (generatedLog k)=1/(generatedN k : ℚ) ∧
    Nat.clog 2 (generatedN k)=generatedLog k := by
  refine ⟨?_,(recipe_exact k 0).2.1,(recipe_exact k 0).2.2.1,?_,?_⟩
  · unfold q₂ generatedLog s; rw [←pow_mul]; congr 1; omega
  · rw [generatedN_exact]; simp [rho,generatedLog]
  · rw [generatedN_exact]; simp [generatedLog,Nat.clog_pow 2 _ (by decide)]

theorem generatedOverhead_exact (k : ℕ) :
    2*Nat.clog 2 (s k)+Nat.clog 2 (q₂ k (generatedLog k))+
    Nat.clog 2 (w k)+Nat.clog 2 (Q k)=generatedOverhead k ∧
    generatedOverhead k=10*Nat.clog 2 (generatedN k) := by
  rw [(generated_recipe k).2.2.2.2]
  simp only [s,q₂,w,Q,generatedLog,Nat.clog_pow 2 _ (by decide)]
  unfold generatedOverhead; omega

theorem seedWidth_exact (L : ℕ) : seedWidth L=2^(6+ell L) :=
  V39PublicSchedule.seedWidth_exact L

theorem seedCost_exact (L : ℕ) : Nat.clog 2 (seedWidth L)+1=seedCost L :=
  V39PublicSchedule.seedCost_exact L

def B (L i : ℕ) : ℕ := seedCost L+i*fullOverhead L
def H (L i : ℕ) : ℕ := B L i+i
def rankBound (L i : ℕ) : ℕ := 2^(B L i-1)

theorem B_zero (L : ℕ) : B L 0=seedCost L := by simp [B]
theorem B_succ (L i : ℕ) : B L (i+1)=B L i+fullOverhead L := by unfold B; ring
theorem H_succ (L i : ℕ) : H L (i+1)=H L i+fullOverhead L+1 := by
  unfold H; rw [B_succ]; omega
theorem B_ge_seven (L i : ℕ) : 7≤B L i := by unfold B seedCost; omega
theorem rankBound_succ (L i : ℕ) :
    rankBound L (i+1)=2^(fullOverhead L)*rankBound L i := by
  have hb:=B_ge_seven L i
  unfold rankBound
  rw [B_succ,show B L i+fullOverhead L-1=fullOverhead L+(B L i-1) by omega,pow_add]

def sampleSide (L i : ℕ) : ℕ :=
  V38Schedule.pow2Ceil (16*(rankBound L i+1)*Nat.clog 2 (rankBound L i+2)*2^(H L i))
def sampleEntries (L i : ℕ) : ℕ := sampleSide L i ^ 2

theorem rankBound_add_one_le (L i : ℕ) : rankBound L i+1 ≤ 2^(B L i) := by
  have hb:=B_ge_seven L i
  have hr : 1≤rankBound L i := by
    have hp : 0<rankBound L i := by unfold rankBound; positivity
    omega
  have he : 2^(B L i)=2*rankBound L i := by
    unfold rankBound
    calc
      2^(B L i)=2^((B L i-1)+1) := by congr 1; omega
      _ = 2*2^(B L i-1) := by rw [pow_succ]; omega
  omega

theorem rankBound_clog_le (L i : ℕ) :
    Nat.clog 2 (rankBound L i+2) ≤ B L i+1 := by
  apply (Nat.clog_le_iff_le_pow (by decide : 1<2)).2
  rw [pow_succ]
  have hr:=rankBound_add_one_le L i
  have hp : 1≤2^(B L i) := Nat.one_le_two_pow
  omega

theorem sampleSide_le_power (L i : ℕ) :
    sampleSide L i ≤ 2^(4+B L i+Nat.clog 2 (B L i+2)+H L i) := by
  apply (V39PublicSchedule.pow2Ceil_le_iff _ _).2
  have hr:=rankBound_add_one_le L i
  have hc : Nat.clog 2 (rankBound L i+2) ≤ 2^(Nat.clog 2 (B L i+2)) :=
    (rankBound_clog_le L i).trans ((by omega : B L i+1≤B L i+2).trans
      (Nat.le_pow_clog (by decide) (B L i+2)))
  calc
    _ ≤ 16*2^(B L i)*2^(Nat.clog 2 (B L i+2))*2^(H L i) := by gcongr
    _ = _ := by rw [pow_add,pow_add,pow_add]; norm_num <;> ring

theorem sampleEntries_clog_upper (L i : ℕ) :
    Nat.clog 2 (sampleEntries L i) ≤
      4*B L i+2*i+2*Nat.clog 2 (B L i+2)+8 := by
  apply (Nat.clog_le_iff_le_pow (by decide : 1<2)).2
  have hsq:=Nat.pow_le_pow_left (sampleSide_le_power L i) 2
  unfold sampleEntries
  calc
    sampleSide L i ^ 2 ≤ (2^(4+B L i+Nat.clog 2 (B L i+2)+H L i))^2 := hsq
    _ = _ := by rw [←pow_mul]; congr 1; unfold H; omega

theorem sampleSide_lower (L i : ℕ) : 2^(H L i) ≤ sampleSide L i := by
  have hr : 0<rankBound L i := by unfold rankBound; positivity
  have hc : 0<Nat.clog 2 (rankBound L i+2) := Nat.clog_pos (by decide) (by omega)
  have hf : 1≤16*(rankBound L i+1)*Nat.clog 2 (rankBound L i+2) := by
    have hpos : 0 < 16*(rankBound L i+1)*Nat.clog 2 (rankBound L i+2) := by positivity
    omega
  exact (Nat.le_mul_of_pos_left _ hf).trans (V39PublicSchedule.pow2Ceil_lower _)

theorem sampleEntries_lower (L i : ℕ) : 2^i ≤ sampleEntries L i := by
  have hm:=sampleSide_lower L i
  have hp : 2^i≤2^(H L i) := Nat.pow_le_pow_right (by decide) (by unfold H; omega)
  have hs : 1 ≤ sampleSide L i := Nat.one_le_two_pow.trans hm
  unfold sampleEntries; nlinarith only [hm,hp,hs]

#print axioms fullOverhead_exact
#print axioms generatedOverhead_exact
#print axioms rankBound_succ
#print axioms sampleEntries_clog_upper
end CurrentAdditive.V42PublicSchedule

