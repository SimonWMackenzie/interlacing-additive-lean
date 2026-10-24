import Paper2.A3LLayout
import Paper2.A3H3ClockU
import Mathlib.Tactic.DeriveFintype

/-!
# Unit 3 lift, segment 4: hUnsched (the not-Checks branch) on the H_A3 layout bank

Lane `owner:a-h-a3-lift-1` (private, 26 September 2026).

ONE fixed program `uProg FS = copies ; lift(ιU, Unsched.progU)` (production `BitMachineRawSequence` handoff):
1. `CopyAll.prog cpU`: two charged source-preserving copies from the H_A3 packet, `encode g` (packet cell 0)
   into the decoder input cell of the unscheduled region and unary `k` (packet cell 1) into its `k` cell,
   scratch `flag₂` (blank under Mid1);
2. the frozen owner-2 `Unsched.progU` lifted by the stack embedding `ιU`, which places the unscheduled
   region `JU` in its own layout region except its header output cell `outH`, placed at the common output
   cell `outJ`.
-/

namespace Paper2.A3Assembly.Lift

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2

variable (FS : Type) [Fintype FS] [DecidableEq FS]

/-- The unscheduled region cell of a `JU` cell. -/
def uReg (x : Unsched.JU) : W FS := .inr (.inr (.inr (.inr (.inr (.inl x)))))

/-- Layout position map of the unscheduled bank: its header output cell goes to the common output cell. -/
def uMap : Unsched.JU → W FS ⊕ Fin 3
  | .inl x => .inl (uReg FS (.inl x))
  | .inr (.inl u) => .inl (uReg FS (.inr (.inl u)))
  | .inr (.inr (.inl f)) => .inl (uReg FS (.inr (.inr (.inl f))))
  | .inr (.inr (.inr (.inl h))) => .inl (uReg FS (.inr (.inr (.inr (.inl h)))))
  | .inr (.inr (.inr (.inr i))) =>
      if i = 5 then .inl (.inl 2) else .inl (uReg FS (.inr (.inr (.inr (.inr i)))))

theorem uMap_injective : Function.Injective (uMap FS) := by
  intro x y h
  rcases x with x | x | x | x | x <;> rcases y with y | y | y | y | y <;>
    simp only [uMap, uReg] at h <;> (try split_ifs at h) <;> simp_all

def ιU : Unsched.JU ↪ Fin (a FS + 3) :=
  ⟨fun x => pos FS (uMap FS x), fun x y h => uMap_injective FS (pos_injective FS h)⟩

theorem ιU_out : ιU FS Unsched.hOut = outJ FS := by
  simp [ιU, Unsched.hOut, uMap, outJ]

/-- Every unscheduled cell is blank in a layout bank whose output cell is blank. -/
theorem layout_U_blank (P : Fin 3 → List Bool) (st : SuccessOrient.Stack → List Bool)
    (c : Fin 3 → List Bool) (hc : c 2 = []) (Z : FS → List Bool) (x : Unsched.JU) :
    layoutBank FS P (region FS st c Z) (ιU FS x) = [] := by
  change layoutBank FS P (region FS st c Z) (pos FS (uMap FS x)) = []
  rcases x with x | x | x | x | x <;> simp only [uMap] <;> (try split_ifs) <;>
    simp [layoutBank_inl, region, uReg, hc]

/-- The decoder input cell and the `k` cell of `JU`. -/
def inCell : Unsched.JU := .inl (.inl (.inl 0))

theorem entry_spec (g : EncodedGraph.Graph) (k : ℕ) (x : Unsched.JU) :
    Unsched.entry g k x =
      if x = inCell then EncodedGraph.encode g
      else if x = Unsched.kIn then List.replicate k true else [] := by
  rcases x with ((f | f) | f) | x | x
  · fin_cases f <;> simp [Unsched.entry, PublicGraphEndpointMachine.initialBank,
      SourceNormalizationMachineDecode.start, inCell, Unsched.kIn]
  · fin_cases f <;> simp [Unsched.entry, PublicGraphEndpointMachine.initialBank,
      SourceNormalizationMachineDecode.start, inCell, Unsched.kIn]
  · fin_cases f <;> simp [Unsched.entry, PublicGraphEndpointMachine.initialBank, inCell, Unsched.kIn]
  · cases x; simp [Unsched.entry, Unsched.restA, inCell, Unsched.kIn]
  · simp [Unsched.entry, Unsched.restA, inCell, Unsched.kIn]

/-- The fan-out copies (packet → unscheduled region), scratch `flag₂`. -/
def cpU (i : Fin 2) : Fin 3 ↪ Fin (a FS + 3) :=
  ⟨![pk FS i.castSucc, ιU FS (![inCell, Unsched.kIn] i), flag₂ FS], by
    intro x y h
    fin_cases i <;> fin_cases x <;> fin_cases y <;>
      simp_all [pk, flag₂, ιU, uMap, inCell, Unsched.kIn, uReg,
        (pos_injective FS).eq_iff]⟩

/-- The branch program. -/
def uProg := BitMachineRawSequence.program (CopyAll.prog (cpU FS)) (liftP (ιU FS) Unsched.progU)
  Unsched.startU (none : Option Bool) Unsched.ctlU

def uStart : BitMachineRawSequence.Label (CopyAll.Lab 2) Unsched.LabU :=
  BitMachineRawSequence.leftLabel (.inl ⟨0, by omega⟩)


/-! Finite-control instances for the owner-2 unscheduled program (the label/control inductives of the
admitted fallback machines carry no `Fintype` instance; these are derived here, privately, by the
Mathlib derive handler; no production declaration is changed). -/
set_option synthInstance.maxSize 16384

deriving instance Fintype for Paper2.FallbackBranch.Mode
deriving instance Fintype for Paper2.FallbackBranch.Adm
deriving instance Fintype for Paper2.TernaryColourSearch.TAdm
deriving instance Fintype for Paper2.FallbackColourSearch.Lab
deriving instance Fintype for Paper2.FallbackColourSearch.Ctl
deriving instance Fintype for Paper2.FallbackIdentityCell.Label
deriving instance Fintype for Paper2.FallbackDimsPrinter.Lab

set_option synthInstance.maxSize 16384 in
noncomputable instance instFtLabU : Fintype Unsched.LabU := inferInstance

/-- The per-step push bound of the branch program. -/
def PSU : ℕ := BitMachineStackGrowth.perStep (uProg FS)

/-- Clock constant (exponent 160). -/
def UCk (Δ : ℕ) (γ : ℚ) : ℕ := 16 * Δ + 44 + Clocks.CU Δ γ

/-- Branch constant (clock and final bank size). -/
def UC (Δ : ℕ) (γ : ℚ) (CM : ℕ) : ℕ := UCk Δ γ + CM + 2 * (a FS + 3) * PSU FS * UCk Δ γ

theorem cpU_sd (i j : Fin 2) : cpU FS i 0 ≠ cpU FS j 1 := by
  fin_cases i <;> fin_cases j <;>
    simp [cpU, pk, ιU, uMap, inCell, Unsched.kIn, uReg, (pos_injective FS).eq_iff]

theorem cpU_zd (i j : Fin 2) : cpU FS i 2 ≠ cpU FS j 1 := by
  fin_cases i <;> fin_cases j <;>
    simp [cpU, flag₂, ιU, uMap, inCell, Unsched.kIn, uReg, (pos_injective FS).eq_iff]

theorem cpU_dd (i j : Fin 2) (h : cpU FS i 1 = cpU FS j 1) : i = j := by
  fin_cases i <;> fin_cases j <;>
    simp_all [cpU, ιU, uMap, inCell, Unsched.kIn, uReg, (pos_injective FS).eq_iff]

theorem cpU_dst (i : Fin 2) : cpU FS i 1 = ιU FS (![inCell, Unsched.kIn] i) := rfl

/-- **Segment 4 (hUnsched).** Under Mid1 and not Checks (and R12), the fixed branch program halts within
`UC·(n+2)^(max EM 160 (k+1))` with `outputBits` in the common output cell and final bank within the same bound. -/
theorem hUnsched_spec (Δ : ℕ) (γ : ℚ) (hΔ : 0 < Δ) (hγ : 0 < γ) (CM EM : ℕ) :
    Run.BranchSpec Δ γ (a FS) (uProg FS) uStart ((none : Option Bool), Unsched.ctlU) (outJ FS)
      (fun g hg hn k t S => Mid1 FS Δ γ CM EM g hg hn k t S ∧ ¬ Run.ChecksCond Δ γ g hg hn k t)
      (UC FS Δ γ CM) (max EM 160) := by
  intro g hg hn k hH t S hpre
  obtain ⟨⟨⟨b, Z, hS⟩, hsz⟩, hnc⟩ := hpre
  obtain ⟨hk, hsurj, hdeg⟩ := hH
  have hI := Size.inputSize Δ γ g hg hn k hk hsurj hdeg t
  have hg0 : (EncodedGraph.encode g).length ≤
      (BitMachineBankCodec.encode (Wrap.inputBank Δ γ g hg hn k t)).length := by
    have := BitMachineBankCodec.word_length_le_encode (Wrap.inputBank Δ γ g hg hn k t) 0
    simpa [Wrap.inputBank] using this
  have hk0 : k ≤ (BitMachineBankCodec.encode (Wrap.inputBank Δ γ g hg hn k t)).length := by
    have := BitMachineBankCodec.word_length_le_encode (Wrap.inputBank Δ γ g hg hn k t) 1
    simpa [Wrap.inputBank] using this
  obtain ⟨I, hIdef⟩ : ∃ I, I = (BitMachineBankCodec.encode (Wrap.inputBank Δ γ g hg hn k t)).length :=
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
    Unsched.unscheduled_run g hg hn Δ γ hγ hΔ k hsurj hdeg hnc t
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
  have hCU := Clocks.clockU_HA3 g hg hn Δ γ k hk hdeg
  have h6 : (g.vertices + 2) ^ (6 * (k + 1)) ≤ P := by
    rw [hPdef]; exact Nat.pow_le_pow_right hN (Nat.mul_le_mul_right _ (by norm_num))
  have hCU' : Unsched.clockU g hg Δ γ k ≤ Clocks.CU Δ γ * P := hCU.trans (Nat.mul_le_mul_left _ h6)
  rw [← hPdef] at hI
  have hTk : T ≤ UCk Δ γ * P := by
    have e : UCk Δ γ * P = 4 * ((4 * Δ + 9) * P) + 8 * P + Clocks.CU Δ γ * P := by
      unfold UCk; ring
    rw [e]
    generalize Clocks.CU Δ γ * P = X at hCU'
    generalize (4 * Δ + 9) * P = Y at hI
    omega
  have hTQ : T ≤ UCk Δ γ * Q := hTk.trans (Nat.mul_le_mul_left _ hPQ)
  -- size
  have hsize := size_run (uProg FS) ⟨some uStart, ((none : Option Bool), Unsched.ctlU), S⟩ T
  have hr' : ((advance (uProg FS))^[T]) ⟨some uStart, ((none : Option Bool), Unsched.ctlU), S⟩ =
      ⟨none, ((none : Option Bool), ctl), bank (ιU FS) S1 (Unsched.exitU g hg k q F)⟩ := hr
  rw [hr'] at hsize
  rw [← hQdef]
  refine ⟨T, _, bank (ιU FS) S1 (Unsched.exitU g hg k q F), ?_, hr', ?_, ?_⟩
  · have : UCk Δ γ ≤ UC FS Δ γ CM := by unfold UC; omega
    exact hTQ.trans (Nat.mul_le_mul_right _ this)
  · rw [← ιU_out, bank_at]
    exact hF
  · have h1 : (BitMachineBankCodec.encode S).length ≤ CM * Q := hsz.trans (Nat.mul_le_mul_left _ hMQ)
    have h2 : 2 * (a FS + 3) * (PSU FS * T) ≤ 2 * (a FS + 3) * PSU FS * UCk Δ γ * Q := by
      have := Nat.mul_le_mul_left (2 * (a FS + 3)) (Nat.mul_le_mul_left (PSU FS) hTQ)
      calc 2 * (a FS + 3) * (PSU FS * T) ≤ 2 * (a FS + 3) * (PSU FS * (UCk Δ γ * Q)) := this
        _ = 2 * (a FS + 3) * PSU FS * UCk Δ γ * Q := by ring
    have e : UC FS Δ γ CM * Q = UCk Δ γ * Q + CM * Q + 2 * (a FS + 3) * PSU FS * UCk Δ γ * Q := by
      unfold UC; ring
    change (BitMachineBankCodec.encode (bank (ιU FS) S1 (Unsched.exitU g hg k q F))).length ≤
      (BitMachineBankCodec.encode S).length + 2 * (a FS + 3) * (PSU FS * T) at hsize
    rw [e]
    generalize 2 * (a FS + 3) * PSU FS * UCk Δ γ * Q = X at h2
    generalize 2 * (a FS + 3) * (PSU FS * T) = Y at h2 hsize
    generalize UCk Δ γ * Q = Z
    omega

end

end Paper2.A3Assembly.Lift

#print axioms Paper2.A3Assembly.Lift.uMap_injective
#print axioms Paper2.A3Assembly.Lift.layout_U_blank
#print axioms Paper2.A3Assembly.Lift.entry_spec
#print axioms Paper2.A3Assembly.Lift.hUnsched_spec
