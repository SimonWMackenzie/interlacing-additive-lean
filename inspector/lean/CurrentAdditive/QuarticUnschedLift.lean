import CurrentAdditive.QuarticUnschedClock
import CurrentAdditive.QuarticLayout
import Paper2.A3LUnsched

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.CurrentAdditive.QuarticUnschedLift

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2 Paper2.A3Assembly Paper2.A3Assembly.Lift
open Paper2.CurrentAdditive.QuarticDispatchSpec
open Paper2.CurrentAdditive.QuarticLayout
open Paper2.CurrentAdditive.QuarticConstructor

variable (FS : Type) [Fintype FS] [DecidableEq FS]

/-- Branch clock constant with the literal v27 finite-exception threshold. -/
def UCk27 (Δ : ℕ) (γ : ℚ) : ℕ :=
  16 * Δ + 44 + QuarticUnschedClock.CU27 Δ γ

/-- Branch clock and final-size constant on the existing physical layout. -/
def UC27 (Δ : ℕ) (γ : ℚ) (CM : ℕ) : ℕ :=
  UCk27 Δ γ + CM + 2 * (a FS + 3) * PSU FS * UCk27 Δ γ
theorem hUnsched_spec27 (Δ : ℕ) (γ : ℚ) (hΔ : 0 < Δ) (hγ : 0 < γ) (CM EM : ℕ) :
    BranchSpec Δ γ (a FS) (uProg FS) uStart ((none : Option Bool), Unsched.ctlU) (outJ FS)
      (fun g hg hn k t S => Mid1_27 FS Δ γ CM EM g hg hn k t S ∧ ¬ ChecksCond27 Δ γ g hg hn k t)
      (UC27 FS Δ γ CM) (max EM 160) := by
  intro g hg hn k hH t S hpre
  obtain ⟨⟨⟨b, Z, hS⟩, hsz⟩, hnc⟩ := hpre
  obtain ⟨hk, hsurj, hdeg⟩ := hH
  have hI := QuarticDispatchSize.inputSize27 Δ γ g hg hn k ⟨hk, hsurj, hdeg⟩ t
  have hg0 : (EncodedGraph.encode g).length ≤
      (BitMachineBankCodec.encode (inputBank27 Δ γ g hg hn k t)).length := by
    have := BitMachineBankCodec.word_length_le_encode (inputBank27 Δ γ g hg hn k t) 0
    simpa [inputBank27] using this
  have hk0 : k ≤ (BitMachineBankCodec.encode (inputBank27 Δ γ g hg hn k t)).length := by
    have := BitMachineBankCodec.word_length_le_encode (inputBank27 Δ γ g hg hn k t) 1
    simpa [inputBank27] using this
  obtain ⟨I, hIdef⟩ : ∃ I, I = (BitMachineBankCodec.encode (inputBank27 Δ γ g hg hn k t)).length :=
    ⟨_, rfl⟩
  rw [← hIdef] at hI hg0 hk0
  -- the packet cells and the blank cells of the entry bank
  have hS0 : S (pk FS 0) = EncodedGraph.encode g := by
    rw [hS, pk, layoutBank_inr]; rfl
  have hS1 : S (pk FS 1) = List.replicate k true := by
    rw [hS, pk, layoutBank_inr]; rfl
  have hSf : S (flag₂ FS) = [] := by
    rw [hS, flag₂, layoutBank_inl]; rfl
  have hSU : ∀ x, S (ιU FS x) = [] := by
    intro x; rw [hS]; exact layout_U_blank FS _ _ _ rfl Z x
  -- stage 1: the fan-out copies
  obtain ⟨tc, htc, vc, hcopy⟩ := CopyAll.all_run (cpU FS) (cpU_sd FS) (cpU_zd FS) (cpU_dd FS) S
    (by intro i; fin_cases i <;> exact hSf) I
    (by
      intro i; fin_cases i
      · change (S (pk FS 0)).length ≤ I; rw [hS0]; exact hg0
      · change (S (pk FS 1)).length ≤ I; rw [hS1, List.length_replicate]; exact hk0)
    none
  obtain ⟨S1, hS1def⟩ : ∃ S1, S1 = CopyAll.done (cpU FS) 2 S := ⟨_, rfl⟩
  rw [← hS1def] at hcopy
  have hE : ∀ x, Unsched.entry g k x = S1 (ιU FS x) := by
    intro x
    rw [entry_spec, hS1def]
    split_ifs with h1 h2
    · subst h1
      have := CopyAll.done_dst (cpU FS) (cpU_dd FS) S 0
      rw [cpU_dst] at this
      change CopyAll.done (cpU FS) 2 S (ιU FS inCell) = _ at this
      rw [this]
      change EncodedGraph.encode g = S (pk FS 0) ++ S (ιU FS inCell)
      rw [hS0, hSU, List.append_nil]
    · subst h2
      have := CopyAll.done_dst (cpU FS) (cpU_dd FS) S 1
      rw [cpU_dst] at this
      change CopyAll.done (cpU FS) 2 S (ιU FS Unsched.kIn) = _ at this
      rw [this]
      change List.replicate k true = S (pk FS 1) ++ S (ιU FS Unsched.kIn)
      rw [hS1, hSU, List.append_nil]
    · rw [CopyAll.done_off (cpU FS) S (ιU FS x) ?_ 2, hSU]
      intro j hj
      rw [cpU_dst] at hj
      have := (ιU FS).injective hj
      fin_cases j
      · exact h1 this.symm
      · exact h2 this.symm
  have hbank : bank (ιU FS) S1 (Unsched.entry g k) = S1 := bank_eq_self _ _ _ hE
  -- stage 2: the lifted unscheduled program
  obtain ⟨TU, hTU, ctl, q, F, hrun, hF, -⟩ :=
    QuarticUnschedRun.unscheduled_run27 g hg hn Δ γ hγ hΔ k hsurj hdeg hnc t
  have hL := BitMachineStackRun.run (ιU FS) S1 Unsched.progU
    ⟨some Unsched.startU, Unsched.ctlU, Unsched.entry g k⟩ TU
  rw [hrun] at hL
  simp only [stackCfg] at hL
  rw [hbank] at hL
  obtain ⟨T, hT, hr⟩ := BitMachineRawSequence.runs (CopyAll.prog (cpU FS))
    (liftP (ιU FS) Unsched.progU) (.inl ⟨0, by omega⟩) Unsched.startU (none : Option Bool) vc
    Unsched.ctlU ctl S S1 (bank (ιU FS) S1 (Unsched.exitU g hg k q F)) tc TU hcopy hL
  -- clock
  have hN : 1 ≤ g.vertices + 2 := by omega
  obtain ⟨P, hPdef⟩ : ∃ P, P = (g.vertices + 2) ^ (160 * (k + 1)) := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q, Q = (g.vertices + 2) ^ (max EM 160 * (k + 1)) := ⟨_, rfl⟩
  have hP1 : 1 ≤ P := by rw [hPdef]; exact Nat.one_le_pow _ _ hN
  have hPQ : P ≤ Q := by
    rw [hPdef, hQdef]; exact Nat.pow_le_pow_right hN (Nat.mul_le_mul_right _ (le_max_right _ _))
  have hMQ : (g.vertices + 2) ^ (EM * (k + 1)) ≤ Q := by
    rw [hQdef]; exact Nat.pow_le_pow_right hN (Nat.mul_le_mul_right _ (le_max_left _ _))
  have hCU := QuarticUnschedClock.clockU_HA3_27 g hg hn Δ γ k hk hdeg
  have h6 : (g.vertices + 2) ^ (6 * (k + 1)) ≤ P := by
    rw [hPdef]; exact Nat.pow_le_pow_right hN (Nat.mul_le_mul_right _ (by norm_num))
  have hCU' : QuarticUnschedRun.clockU27 g hg Δ γ k ≤ QuarticUnschedClock.CU27 Δ γ * P := hCU.trans (Nat.mul_le_mul_left _ h6)
  rw [← hPdef] at hI
  have hTk : T ≤ UCk27 Δ γ * P := by
    have e : UCk27 Δ γ * P = 4 * ((4 * Δ + 9) * P) + 8 * P + QuarticUnschedClock.CU27 Δ γ * P := by
      unfold UCk27; ring
    rw [e]
    generalize QuarticUnschedClock.CU27 Δ γ * P = X at hCU'
    generalize (4 * Δ + 9) * P = Y at hI
    omega
  have hTQ : T ≤ UCk27 Δ γ * Q := hTk.trans (Nat.mul_le_mul_left _ hPQ)
  -- size
  have hsize := size_run (uProg FS) ⟨some uStart, ((none : Option Bool), Unsched.ctlU), S⟩ T
  have hr' : ((advance (uProg FS))^[T]) ⟨some uStart, ((none : Option Bool), Unsched.ctlU), S⟩ =
      ⟨none, ((none : Option Bool), ctl), bank (ιU FS) S1 (Unsched.exitU g hg k q F)⟩ := hr
  rw [hr'] at hsize
  rw [← hQdef]
  refine ⟨T, _, bank (ιU FS) S1 (Unsched.exitU g hg k q F), ?_, hr', ?_, ?_⟩
  · have : UCk27 Δ γ ≤ UC27 FS Δ γ CM := by unfold UC27; omega
    exact hTQ.trans (Nat.mul_le_mul_right _ this)
  · rw [← ιU_out, bank_at]
    exact hF
  · have h1 : (BitMachineBankCodec.encode S).length ≤ CM * Q := hsz.trans (Nat.mul_le_mul_left _ hMQ)
    have h2 : 2 * (a FS + 3) * (PSU FS * T) ≤ 2 * (a FS + 3) * PSU FS * UCk27 Δ γ * Q := by
      have := Nat.mul_le_mul_left (2 * (a FS + 3)) (Nat.mul_le_mul_left (PSU FS) hTQ)
      calc 2 * (a FS + 3) * (PSU FS * T) ≤ 2 * (a FS + 3) * (PSU FS * (UCk27 Δ γ * Q)) := this
        _ = 2 * (a FS + 3) * PSU FS * UCk27 Δ γ * Q := by ring
    have e : UC27 FS Δ γ CM * Q = UCk27 Δ γ * Q + CM * Q + 2 * (a FS + 3) * PSU FS * UCk27 Δ γ * Q := by
      unfold UC27; ring
    change (BitMachineBankCodec.encode (bank (ιU FS) S1 (Unsched.exitU g hg k q F))).length ≤
      (BitMachineBankCodec.encode S).length + 2 * (a FS + 3) * (PSU FS * T) at hsize
    rw [e]
    generalize 2 * (a FS + 3) * PSU FS * UCk27 Δ γ * Q = X at h2
    generalize 2 * (a FS + 3) * (PSU FS * T) = Y at h2 hsize
    generalize UCk27 Δ γ * Q = Z
    omega

#print axioms hUnsched_spec27

end

end Paper2.CurrentAdditive.QuarticUnschedLift
