import EthInapproximability.CurrentPaper.U4ArmPost
import EthInapproximability.CurrentPaper.U4ItemLength
import EthInapproximability.CurrentPaper.SourceGenericPipelineClock
import EthInapproximability.CurrentPaper.SourceListMachineOuterRun
import EthInapproximability.CurrentPaper.Shell

/-!
# B4-S6e: absorption of the explicit main-arm time (lane owner:b-unit4-shell-4)

Source: frozen v8 `06-eth.tex:204-243` ("sum over its at most `2^(eps n)` branches"; "the
hypothetical approximation takes `T(n)^O(1)` time per branch").

The explicit `Unit4ItemAssembly.armTime` of the fixed main arm (post stage FIXED to
`Unit4Post.Body.postMachine M`, per-item bound `itemBound Mtab C₂ E₂ F₂ (Body.Cp _) 6 T`,
source time `Csrc ⌈2^(η n)⌉ (|w|+1)^Esrc`) is bounded by

  `C * ⌈2^(η n)⌉ * tableSize(L, n)^Bx * (|encode f|+1)^Dx`

with the exponential factor to the FIRST power. The branch count `K = |S.branches f|` enters
only as a multiplier (`count_le_ceil`: `K ≤ ⌈2^(η n)⌉`); every per-item quantity is bounded by
a fixed polynomial in `N = tableSize * (|w|+1)` alone: the item word by the per-item length
lemma (`U4ItemLength`), the estimator packet by `2 W (tableSize + 2n) + W` (table length from
`phys_branch_facts` 3rd conjunct, threshold and `k` below `n` from its 4th), the list framing
digits by `digits_le`. The constants `C Bx Dx` are chosen after `S D B c M c' d' Mtab C₂ E₂ F₂
Csrc Esrc` and before `f`; nothing is absorbed by shrinking `η`.
-/

namespace EthInapproximability.CurrentPaper.Unit4Clock

open EncodedETHSource EncodedETHSourceComposition EffectiveIteration
open Unit4Bridges Unit4PhysBridges Unit4MainArm Unit4ItemAssembly
open SourceGenericComposite SourceGenericComposite.PolyEnvelope

/-! ## Fixed-width estimator packet length -/

/-- Text adapted from the Codex private `b-main-arm-clock-20260926/BMainArmClock.lean`
(`packet_length_le`, SHA-256 `33f27155…90ef`); nothing from that lane is imported. -/
theorem packet_length_le (M : BitMachine.Machine) (table : List Bool) (Y k : ℕ) :
    (SignedMidpointApproxCanonical.packet M table Y k).length ≤
      2 * SignedMidpointApproxPacket.Width M * (table.length + Y + k) +
        SignedMidpointApproxPacket.Width M := by
  have hcell : ∀ j : Fin (SignedMidpointApproxPacket.Width M),
      (SignedMidpointApproxCanonical.bank M table Y k j).length ≤ table.length + Y + k := by
    intro j
    cases h : (SignedMidpointApproxPacket.stackEquiv M).symm j with
    | inl x =>
        by_cases hx : x = M.input
        · simp [SignedMidpointApproxCanonical.bank, h, hx]; omega
        · simp [SignedMidpointApproxCanonical.bank, h, hx]
    | inr i =>
        fin_cases i <;> simp [SignedMidpointApproxCanonical.bank, h] <;> omega
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun j _ => hcell j)
  rw [SignedMidpointApproxCanonical.packet, BitMachineBankCodec.encode_length]
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul] at hsum
  nlinarith

/-! ## Per-item envelopes in `N` (all fixed before the formula) -/

/-- Item-word length envelope. -/
def lx (Cw Ew N : ℕ) : ℕ := Cw * N ^ Ew

/-- Estimator packet length envelope. -/
def lp (M : BitMachine.Machine) (N : ℕ) : ℕ :=
  2 * SignedMidpointApproxPacket.Width M * (3 * N) + SignedMidpointApproxPacket.Width M

/-- `itemBound` at item length `lx N` and table size `N`. -/
def ibN (Mtab : BitMachine.Machine) (C₂ E₂ F₂ Cp Ep Cw Ew N : ℕ) : ℕ :=
  C₂ * (lx Cw Ew N + 1) ^ E₂ * N ^ F₂ +
    2 * (lx Cw Ew N + C₂ * (lx Cw Ew N + 1) ^ E₂ * N ^ F₂ * Mtab.pushBound) + 2 +
    Cp * (lx Cw Ew N + C₂ * (lx Cw Ew N + 1) ^ E₂ * N ^ F₂ * Mtab.pushBound + 1) ^ Ep * N ^ Ep

/-- Framed item output length envelope. -/
noncomputable def fo (M : BitMachine.Machine) (N : ℕ) : ℕ := 3 * lp M N + 1

/-- Framed item clock envelope. -/
noncomputable def fb (Mtab M : BitMachine.Machine) (C₂ E₂ F₂ Cp Ep Cw Ew N : ℕ) : ℕ :=
  ibN Mtab C₂ E₂ F₂ Cp Ep Cw Ew N + 2 * lp M N + 2 +
    (UnaryBinaryEncoding.coefficient + 7) * (lp M N + 1) ^ 2

/-- Per-item controller cost envelope (`itemCost_le_envelope` shape). -/
noncomputable def ic (Mtab M F : BitMachine.Machine) (C₂ E₂ F₂ Cp Ep Cw Ew N : ℕ) : ℕ :=
  20 * (lx Cw Ew N + 1) * (lx Cw Ew N + 1) + fb Mtab M C₂ E₂ F₂ Cp Ep Cw Ew N +
    4 * lx Cw Ew N + fo M N +
    F.stackCount * (lx Cw Ew N + fb Mtab M C₂ E₂ F₂ Cp Ep Cw Ew N * F.pushBound + 1) + 9

/-- Branch-count digit envelope. -/
def bw (cη N : ℕ) : ℕ := (cη + 1) * N

/-- Estimator back-end per-packet envelope (admitted `itemEnvelope` at `lp N`). -/
noncomputable def ienv (M : BitMachine.Machine) (c' d' N : ℕ) : ℕ :=
  SignedMidpointApproxActualMapper.itemEnvelope M c' d' (lp M N)

/-- The whole per-branch polynomial (the factor multiplying `⌈2^(η n)⌉`). -/
noncomputable def G (Mtab M F : BitMachine.Machine) (C₂ E₂ F₂ Cp Ep Cw Ew Csrc Esrc cη c' d' N : ℕ) :
    ℕ :=
  Csrc * N ^ Esrc + (6 * (lx Cw Ew N + 1) + 4) +
    (5 * bw cη N + 7 + ic Mtab M F C₂ E₂ F₂ Cp Ep Cw Ew N + (4 * bw cη N + 7) +
      4 * bw cη N + (2 * bw cη N + 1) + fo M N + 9) +
    (6 * (lp M N + 1) + 4) +
    (5 * bw cη N + 7 + ienv M c' d' N + (4 * bw cη N + 7) + 4 * bw cη N +
      (2 * bw cη N + 1) + 4 + 9) + 24

theorem lx_env (Cw Ew : ℕ) : PolyEnv (lx Cw Ew) := by
  show PolyEnv (fun N => Cw * N ^ Ew); poly_env

theorem lp_env (M : BitMachine.Machine) : PolyEnv (lp M) := by
  show PolyEnv (fun N => 2 * SignedMidpointApproxPacket.Width M * (3 * N) +
    SignedMidpointApproxPacket.Width M); poly_env

theorem ibN_env (Mtab : BitMachine.Machine) (C₂ E₂ F₂ Cp Ep Cw Ew : ℕ) :
    PolyEnv (ibN Mtab C₂ E₂ F₂ Cp Ep Cw Ew) := by
  have hlx := lx_env Cw Ew
  show PolyEnv (fun N => C₂ * (lx Cw Ew N + 1) ^ E₂ * N ^ F₂ +
    2 * (lx Cw Ew N + C₂ * (lx Cw Ew N + 1) ^ E₂ * N ^ F₂ * Mtab.pushBound) + 2 +
    Cp * (lx Cw Ew N + C₂ * (lx Cw Ew N + 1) ^ E₂ * N ^ F₂ * Mtab.pushBound + 1) ^ Ep *
      N ^ Ep); poly_env

theorem fo_env (M : BitMachine.Machine) : PolyEnv (fo M) := by
  have hlp := lp_env M
  show PolyEnv (fun N => 3 * lp M N + 1); poly_env

theorem fb_env (Mtab M : BitMachine.Machine) (C₂ E₂ F₂ Cp Ep Cw Ew : ℕ) :
    PolyEnv (fb Mtab M C₂ E₂ F₂ Cp Ep Cw Ew) := by
  have hlp := lp_env M
  have hib := ibN_env Mtab C₂ E₂ F₂ Cp Ep Cw Ew
  show PolyEnv (fun N => ibN Mtab C₂ E₂ F₂ Cp Ep Cw Ew N + 2 * lp M N + 2 +
    (UnaryBinaryEncoding.coefficient + 7) * (lp M N + 1) ^ 2); poly_env

theorem ic_env (Mtab M F : BitMachine.Machine) (C₂ E₂ F₂ Cp Ep Cw Ew : ℕ) :
    PolyEnv (ic Mtab M F C₂ E₂ F₂ Cp Ep Cw Ew) := by
  have hlx := lx_env Cw Ew
  have hfo := fo_env M
  have hfb := fb_env Mtab M C₂ E₂ F₂ Cp Ep Cw Ew
  show PolyEnv (fun N => 20 * (lx Cw Ew N + 1) * (lx Cw Ew N + 1) +
    fb Mtab M C₂ E₂ F₂ Cp Ep Cw Ew N + 4 * lx Cw Ew N + fo M N +
    F.stackCount * (lx Cw Ew N + fb Mtab M C₂ E₂ F₂ Cp Ep Cw Ew N * F.pushBound + 1) + 9)
  poly_env

theorem bw_env (cη : ℕ) : PolyEnv (bw cη) := by
  show PolyEnv (fun N => (cη + 1) * N); poly_env

theorem uf_env (M : BitMachine.Machine) (c' d' : ℕ) :
    PolyEnv (SignedMidpointApproxActualMapper.uniformFramedBound M c' d') := by
  show PolyEnv (fun L => SignedMidpointApproxPolynomial.decisionCoefficient M c' * (L+1)^(d'+2) +
    4 + 4*(UnaryBinaryEncoding.coefficient+7)); poly_env

theorem mapperItem_env (M : BitMachine.Machine) (c' d' : ℕ) :
    PolyEnv (SignedMidpointApproxActualMapper.itemEnvelope M c' d') := by
  have huf := uf_env M c' d'
  have h : PolyEnv (fun L => 20*(L+1)*(L+1) +
      SignedMidpointApproxActualMapper.uniformFramedBound M c' d' L + 4*L + 4 +
      (SourceListMachineOuterFramed.itemMachine
        (SignedMidpointApproxPacket.decisionMachine M)).stackCount *
        (L + SignedMidpointApproxActualMapper.uniformFramedBound M c' d' L *
          (SourceListMachineOuterFramed.itemMachine
            (SignedMidpointApproxPacket.decisionMachine M)).pushBound + 1) + 9) := by
    poly_env
  exact h

theorem ienv_env (M : BitMachine.Machine) (c' d' : ℕ) : PolyEnv (ienv M c' d') := by
  have h := PolyEnv.comp (mapperItem_env M c' d') (lp_env M)
  exact h

theorem G_env (Mtab M F : BitMachine.Machine) (C₂ E₂ F₂ Cp Ep Cw Ew Csrc Esrc cη c' d' : ℕ) :
    PolyEnv (G Mtab M F C₂ E₂ F₂ Cp Ep Cw Ew Csrc Esrc cη c' d') := by
  have hlx := lx_env Cw Ew
  have hlp := lp_env M
  have hfo := fo_env M
  have hic := ic_env Mtab M F C₂ E₂ F₂ Cp Ep Cw Ew
  have hbw := bw_env cη
  have hie := ienv_env M c' d'
  show PolyEnv (fun N => Csrc * N ^ Esrc + (6 * (lx Cw Ew N + 1) + 4) +
    (5 * bw cη N + 7 + ic Mtab M F C₂ E₂ F₂ Cp Ep Cw Ew N + (4 * bw cη N + 7) +
      4 * bw cη N + (2 * bw cη N + 1) + fo M N + 9) +
    (6 * (lp M N + 1) + 4) +
    (5 * bw cη N + 7 + ienv M c' d' N + (4 * bw cη N + 7) + 4 * bw cη N +
      (2 * bw cη N + 1) + 4 + 9) + 24)
  poly_env

/-! ## The absorption -/

section Main

variable {η : ℚ} (S : Sparsification η) (D : DinurReduction)
  (B : BOTReduction (booleanOccurrence D))

/-- Estimator packet of every physical branch, bounded by `lp N` (`N ≥ tableSize`, `N > n`). -/
theorem phys_packet_le (c : ℕ) (hsource : 2 ^ 44 * (B.degreeBound : ℚ) / sourceGap D B ≤ c)
    (M : BitMachine.Machine) (f : ValidFormula) (hn : 1 ≤ f.val.variables)
    (hk : 1 ≤ ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
      (sourceSizeExponent S D B) f.val.variables)
    (N : ℕ) (hTN : FinalPadding.tableSize (ETHTailGrowth.repetitions c
        (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)) f.val.variables ≤ N)
    (hnN : f.val.variables ≤ N)
    (g : ValidFormula) (hg : g ∈ S.branches f) :
    (SignedMidpointApproxCanonical.packet M
      (physBranchOf D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
        f.val.variables g).table
      (physBranchOf D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
        f.val.variables g).threshold
      (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
        (sourceSizeExponent S D B) f.val.variables)).length ≤ lp M N := by
  obtain ⟨-, -, htab, hfit⟩ := phys_branch_facts S D B c f hn hk hsource g hg
  have hp := packet_length_le M
    (physBranchOf D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
      f.val.variables g).table
    (physBranchOf D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
      f.val.variables g).threshold
    (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
      (sourceSizeExponent S D B) f.val.variables)
  rw [htab] at hp
  set Y := (physBranchOf D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
      f.val.variables g).threshold
  set k := ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
      (sourceSizeExponent S D B) f.val.variables
  set T := FinalPadding.tableSize (ETHTailGrowth.repetitions c
        (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)) f.val.variables
  have hYk : Y + k ≤ 2 * k * (Y + k) := Nat.le_mul_of_pos_left _ (by omega)
  have hsum : T + Y + k ≤ 3 * N := by omega
  have hm := Nat.mul_le_mul_left (2 * SignedMidpointApproxPacket.Width M) hsum
  unfold lp
  omega

/-- **B4-S6e.** The explicit time of the fixed main arm (post stage fixed to
`Unit4Post.Body.postMachine M`) is at most `C * ⌈2^(η n)⌉ * tableSize(L,n)^Bx * (|w|+1)^Dx`,
the exponential factor to the first power, for constants chosen before the formula. -/
theorem arm_time_absorbed (c : ℕ)
    (hsource : 2 ^ 44 * (B.degreeBound : ℚ) / sourceGap D B ≤ c)
    (M : BitMachine.Machine) (c' d' : ℕ) (answer : List Bool → ℤ)
    (hM : M.ComputesWithin (fun table => EncodedETHTail.encodeInteger (answer table))
      (fun n => c' * (n + 1) ^ d'))
    (Mtab : BitMachine.Machine) (C₂ E₂ F₂ : ℕ)
    (htab : HB2Body c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
      B.degreeBound (sourceGap D B) Mtab C₂ E₂ F₂)
    (Csrc Esrc : ℕ) :
    ∃ C Bx Dx : ℕ, ∀ f : ValidFormula, 1 ≤ f.val.variables →
      1 ≤ ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
        (sourceSizeExponent S D B) f.val.variables →
      armTime S D B c M c' d'
          (BitMachineComposition.composition Mtab (Unit4Post.Body.postMachine M))
          (itemBound Mtab C₂ E₂ F₂ (Unit4Post.Body.Cp M.stackCount) 6
            (FinalPadding.tableSize (ETHTailGrowth.repetitions c
              (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)) f.val.variables))
          (Csrc * ⌈(2 : ℝ) ^ ((η : ℝ) * f.val.variables)⌉₊ *
            ((EncodedCNF.encode f.val).length + 1) ^ Esrc) f ≤
        C * ⌈(2 : ℝ) ^ ((η : ℝ) * f.val.variables)⌉₊ *
          FinalPadding.tableSize (ETHTailGrowth.repetitions c
            (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)) f.val.variables ^ Bx *
          ((EncodedCNF.encode f.val).length + 1) ^ Dx := by
  obtain ⟨Cw, Ew, hw⟩ := itemWord_length_poly S D B
  obtain ⟨-, CG, EG, hG⟩ := G_env Mtab M
    (SourceListMachineOuterFramed.itemMachine
      (BitMachineComposition.composition Mtab (Unit4Post.Body.postMachine M)))
    C₂ E₂ F₂ (Unit4Post.Body.Cp M.stackCount) 6 Cw Ew Csrc Esrc ⌈η⌉₊ c' d'
  refine ⟨CG * 2 ^ EG, EG, EG, fun f hn hk => ?_⟩
  -- the item interface (H-B2 + fixed post stage)
  have hitem : ∀ g ∈ S.branches f,
      (BitMachineComposition.composition Mtab (Unit4Post.Body.postMachine M)).OutputsWithin
        (itemWord D B f.val.variables g)
        (SignedMidpointApproxCanonical.packet M
          (physBranchOf D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
            f.val.variables g).table
          (physBranchOf D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
            f.val.variables g).threshold
          (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
            (sourceSizeExponent S D B) f.val.variables))
        (itemBound Mtab C₂ E₂ F₂ (Unit4Post.Body.Cp M.stackCount) 6
          (FinalPadding.tableSize (ETHTailGrowth.repetitions c
            (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)) f.val.variables)
          (itemWord D B f.val.variables g)) :=
    fun g hg => item_run S D B c M hsource Mtab C₂ E₂ F₂ htab (Unit4Post.Body.postMachine M)
      (Unit4Post.Body.Cp M.stackCount) 6 (Unit4Post.Body.post_body M) f hn hk g hg
  -- scalar facts
  have hT1 : 1 ≤ FinalPadding.tableSize (ETHTailGrowth.repetitions c
      (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)) f.val.variables :=
    Unit4Shell.tableSize_pos _ _
  have hnw := SourceOriginalVariableCapture.original_n_le_input f.val
  obtain ⟨N, hN⟩ : ∃ N, N = FinalPadding.tableSize (ETHTailGrowth.repetitions c
      (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)) f.val.variables *
      ((EncodedCNF.encode f.val).length + 1) := ⟨_, rfl⟩
  have hZN : (EncodedCNF.encode f.val).length + 1 ≤ N := by
    rw [hN]; exact Nat.le_mul_of_pos_left _ hT1
  have hTN : FinalPadding.tableSize (ETHTailGrowth.repetitions c
      (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)) f.val.variables ≤ N := by
    rw [hN]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hnN : f.val.variables + 1 ≤ N := by omega
  have hK := PipelineClock.count_le_ceil S f
  have hX1 := PipelineClock.one_le_ceil (η := η) f
  have hdig := PipelineClock.digits_le S f
  unfold W at hdig
  have hbits : (S.branches f).length.bits.length ≤ bw ⌈η⌉₊ N := by
    unfold bw
    have := Nat.mul_le_mul_left ⌈η⌉₊ (show f.val.variables ≤ N by omega)
    nlinarith
  -- per-item bounds
  have hlx : ∀ g ∈ S.branches f, (itemWord D B f.val.variables g).length ≤ lx Cw Ew N := by
    intro g hg
    have h := hw f hn g hg
    unfold lx
    exact h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  have hpk := phys_packet_le S D B c hsource M f hn hk N hTN (by omega)
  have hpe := fun g hg => physItemFun_eq S D B c (2 ^ sourceSizeExponent S D B)
    (sourceSizeExponent S D B) M f
    (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
      (sourceSizeExponent S D B) f.val.variables)
    (BitMachineComposition.composition Mtab (Unit4Post.Body.postMachine M))
    (itemBound Mtab C₂ E₂ F₂ (Unit4Post.Body.Cp M.stackCount) 6
      (FinalPadding.tableSize (ETHTailGrowth.repetitions c
        (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)) f.val.variables))
    hitem g hg
  -- (i) the H-B1 list word
  have h1 := SourceListEncoding.encode_map_length_le (S.branches f)
    (itemWord D B f.val.variables) (lx Cw Ew N) hlx
  -- (ii) the framed list mapper over the item machine
  have hib : ∀ x : List Bool, x.length ≤ lx Cw Ew N →
      itemBound Mtab C₂ E₂ F₂ (Unit4Post.Body.Cp M.stackCount) 6
        (FinalPadding.tableSize (ETHTailGrowth.repetitions c
          (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)) f.val.variables) x ≤
        ibN Mtab C₂ E₂ F₂ (Unit4Post.Body.Cp M.stackCount) 6 Cw Ew N := by
    intro x hx
    unfold itemBound ibN
    gcongr
  have hout : ∀ x ∈ (S.branches f).map (itemWord D B f.val.variables),
      (SourceListMachineOuterFramed.framedOutput
        (physItemFun S D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B) M f
          (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
            (sourceSizeExponent S D B) f.val.variables)) x).length ≤ fo M N := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
    unfold SourceListMachineOuterFramed.framedOutput
    rw [hpe g hg, List.length_append]
    have h2 := EncodedGraph.natField_length_upper
      (SignedMidpointApproxCanonical.packet M
        (physBranchOf D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
          f.val.variables g).table
        (physBranchOf D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
          f.val.variables g).threshold
        (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
          (sourceSizeExponent S D B) f.val.variables)).length
    have h3 := hpk g hg
    unfold fo
    omega
  have hfb : ∀ x ∈ (S.branches f).map (itemWord D B f.val.variables),
      SourceListMachineOuterFramed.framedBound
        (physItemFun S D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B) M f
          (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
            (sourceSizeExponent S D B) f.val.variables))
        (itemBound Mtab C₂ E₂ F₂ (Unit4Post.Body.Cp M.stackCount) 6
          (FinalPadding.tableSize (ETHTailGrowth.repetitions c
            (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)) f.val.variables)) x ≤
        fb Mtab M C₂ E₂ F₂ (Unit4Post.Body.Cp M.stackCount) 6 Cw Ew N := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
    unfold SourceListMachineOuterFramed.framedBound
    rw [hpe g hg]
    have h2 := hib _ (hlx g hg)
    have h3 := hpk g hg
    have h4 := Nat.mul_le_mul_left (UnaryBinaryEncoding.coefficient + 7)
      (Nat.pow_le_pow_left (Nat.add_le_add_right h3 1) 2)
    unfold fb
    omega
  have hic : ∀ x ∈ (S.branches f).map (itemWord D B f.val.variables),
      SourceListMachineWork.itemCost
        (SourceListMachineOuterFramed.itemMachine
          (BitMachineComposition.composition Mtab (Unit4Post.Body.postMachine M))) x
        (SourceListMachineOuterFramed.framedOutput
          (physItemFun S D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B) M f
            (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
              (sourceSizeExponent S D B) f.val.variables)) x)
        (SourceListMachineOuterFramed.framedBound
          (physItemFun S D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B) M f
            (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
              (sourceSizeExponent S D B) f.val.variables))
          (itemBound Mtab C₂ E₂ F₂ (Unit4Post.Body.Cp M.stackCount) 6
            (FinalPadding.tableSize (ETHTailGrowth.repetitions c
              (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)) f.val.variables)) x) ≤
        ic Mtab M (SourceListMachineOuterFramed.itemMachine
          (BitMachineComposition.composition Mtab (Unit4Post.Body.postMachine M)))
          C₂ E₂ F₂ (Unit4Post.Body.Cp M.stackCount) 6 Cw Ew N := by
    intro x hx
    have hxl : x.length ≤ lx Cw Ew N := by
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
      exact hlx g hg
    exact SourceListMachineWork.itemCost_le_envelope _ x _ _ _ _ _ hxl (hout x hx) (hfb x hx)
  have hcb := SourceListMachineOuter.canonicalBound_le_count
    (SourceListMachineOuterFramed.itemMachine
      (BitMachineComposition.composition Mtab (Unit4Post.Body.postMachine M)))
    ((S.branches f).map (itemWord D B f.val.variables))
    (SourceListMachineOuterFramed.framedOutput
      (physItemFun S D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B) M f
        (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
          (sourceSizeExponent S D B) f.val.variables)))
    (SourceListMachineOuterFramed.framedBound
      (physItemFun S D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B) M f
        (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
          (sourceSizeExponent S D B) f.val.variables))
      (itemBound Mtab C₂ E₂ F₂ (Unit4Post.Body.Cp M.stackCount) 6
        (FinalPadding.tableSize (ETHTailGrowth.repetitions c
          (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)) f.val.variables)))
    _ _ hic hout
  rw [List.length_map, PipelineClock.natField_length] at hcb
  -- (iii) the estimator packet list and (iv) the estimator back end
  have hpb : ∀ b ∈ physBranches S D B c (2 ^ sourceSizeExponent S D B)
      (sourceSizeExponent S D B) f,
      (SignedMidpointApproxCanonical.packet M b.table b.threshold
        (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
          (sourceSizeExponent S D B) f.val.variables)).length ≤ lp M N := by
    intro b hb
    unfold physBranches at hb
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hb
    exact hpk g hg
  have hlen : (physBranches S D B c (2 ^ sourceSizeExponent S D B)
      (sourceSizeExponent S D B) f).length = (S.branches f).length := by
    unfold physBranches; exact List.length_map _
  have hpl : (SignedMidpointApproxCanonical.packetList M
      (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
        (sourceSizeExponent S D B) f.val.variables)
      (physBranches S D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B) f)).length ≤
      3 * (S.branches f).length * (lp M N + 1) + 1 := by
    have h := SourceListEncoding.encode_map_length_le
      (physBranches S D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B) f)
      (fun b => SignedMidpointApproxCanonical.packet M b.table b.threshold
        (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
          (sourceSizeExponent S D B) f.val.variables)) (lp M N) hpb
    rw [hlen] at h
    exact h
  have hmt := SignedMidpointApproxActualMapper.mapTime_le_count M c' d' answer hM
    (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
      (sourceSizeExponent S D B) f.val.variables) (lp M N)
    (physBranches S D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B) f) hpb
  rw [hlen, PipelineClock.natField_length] at hmt
  have hienv : SignedMidpointApproxActualMapper.itemEnvelope M c' d' (lp M N) =
      ienv M c' d' N := rfl
  rw [hienv] at hmt
  -- (v) the source clock
  have hsrc : Csrc * ⌈(2 : ℝ) ^ ((η : ℝ) * f.val.variables)⌉₊ *
      ((EncodedCNF.encode f.val).length + 1) ^ Esrc ≤
      ⌈(2 : ℝ) ^ ((η : ℝ) * f.val.variables)⌉₊ * (Csrc * N ^ Esrc) := by
    have h5 := Nat.pow_le_pow_left hZN Esrc
    have h6 := Nat.mul_le_mul_left (Csrc * ⌈(2 : ℝ) ^ ((η : ℝ) * f.val.variables)⌉₊) h5
    calc _ ≤ Csrc * ⌈(2 : ℝ) ^ ((η : ℝ) * f.val.variables)⌉₊ * N ^ Esrc := h6
      _ = _ := by ring
  -- the branch count as the ONE multiplier
  set X := ⌈(2 : ℝ) ^ ((η : ℝ) * f.val.variables)⌉₊ with hX
  set K := (S.branches f).length with hKdef
  set bits := K.bits.length with hbitsdef
  have p1 := Nat.mul_le_mul_right (lx Cw Ew N + 1) hK
  have p2 := Nat.mul_le_mul_right (ic Mtab M (SourceListMachineOuterFramed.itemMachine
          (BitMachineComposition.composition Mtab (Unit4Post.Body.postMachine M)))
          C₂ E₂ F₂ (Unit4Post.Body.Cp M.stackCount) 6 Cw Ew N) hK
  have p3 : K * (4 * bits + 7) ≤ X * (4 * bw ⌈η⌉₊ N + 7) := Nat.mul_le_mul hK (by omega)
  have p4 := Nat.mul_le_mul_right (fo M N) hK
  have p5 := Nat.mul_le_mul_right (lp M N + 1) hK
  have p6 := Nat.mul_le_mul_right (ienv M c' d' N) hK
  have p7 : bw ⌈η⌉₊ N ≤ X * bw ⌈η⌉₊ N := Nat.le_mul_of_pos_left _ hX1
  have stepA : armTime S D B c M c' d'
          (BitMachineComposition.composition Mtab (Unit4Post.Body.postMachine M))
          (itemBound Mtab C₂ E₂ F₂ (Unit4Post.Body.Cp M.stackCount) 6
            (FinalPadding.tableSize (ETHTailGrowth.repetitions c
              (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)) f.val.variables))
          (Csrc * X * ((EncodedCNF.encode f.val).length + 1) ^ Esrc) f ≤
        X * G Mtab M (SourceListMachineOuterFramed.itemMachine
          (BitMachineComposition.composition Mtab (Unit4Post.Body.postMachine M)))
          C₂ E₂ F₂ (Unit4Post.Body.Cp M.stackCount) 6 Cw Ew Csrc Esrc ⌈η⌉₊ c' d' N := by
    unfold armTime G
    linarith
  calc _ ≤ X * G Mtab M (SourceListMachineOuterFramed.itemMachine
          (BitMachineComposition.composition Mtab (Unit4Post.Body.postMachine M)))
          C₂ E₂ F₂ (Unit4Post.Body.Cp M.stackCount) 6 Cw Ew Csrc Esrc ⌈η⌉₊ c' d' N := stepA
    _ ≤ X * (CG * (N + 1) ^ EG) := Nat.mul_le_mul_left _ (hG N)
    _ ≤ X * (CG * ((2 * N) ^ EG)) := by
        gcongr
        omega
    _ = CG * 2 ^ EG * X *
          FinalPadding.tableSize (ETHTailGrowth.repetitions c
            (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)) f.val.variables ^ EG *
          ((EncodedCNF.encode f.val).length + 1) ^ EG := by
        rw [hN, mul_pow, mul_pow]; ring

/-- **The main arm within the consumer budget.** From `hsource`, H-B2 in the exact
`HB2Physical` form and the paper's approximation premise at the allowance fixed BEFORE the
estimator: ONE fixed machine answers `satAnswer` on every valid `f` with `1 ≤ n`, `1 ≤ L n`
within `C * ⌈2^(η n)⌉ * tableSize(L,n)^Bx * (|encode f|+1)^Dx`. -/
theorem main_arm_budget (c : ℕ)
    (hsource : 2 ^ 44 * (B.degreeBound : ℚ) / sourceGap D B ≤ c)
    (hB2 : PhysicalLevelRun.HB2Physical c (2 ^ sourceSizeExponent S D B)
      (sourceSizeExponent S D B) B.degreeBound (sourceGap D B))
    (happrox : EncodedETHTail.PolynomialApproximation
      (FinalPadding.allowance (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
        (sourceSizeExponent S D B)))) :
    ∃ (Mmain : BitMachine.Machine) (C Bx Dx : ℕ),
      ∀ f : ValidFormula, 1 ≤ f.val.variables →
        1 ≤ ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
          (sourceSizeExponent S D B) f.val.variables →
        Mmain.OutputsWithin (EncodedCNF.encode f.val)
          [EncodedETHTail.satAnswer (EncodedCNF.encode f.val)]
          (C * ⌈(2 : ℝ) ^ ((η : ℝ) * f.val.variables)⌉₊ *
            FinalPadding.tableSize (ETHTailGrowth.repetitions c
              (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)) f.val.variables ^ Bx *
            ((EncodedCNF.encode f.val).length + 1) ^ Dx) := by
  obtain ⟨Msrc, Csrc, Esrc, harm⟩ := Unit4Post.main_arm_endpoint_post S D B
  obtain ⟨answer, M, c', d', hM, herr, -⟩ :=
    SignedMidpointApproxWitness.approximation_supplies_callback _ happrox
  obtain ⟨Mtab, C₂, E₂, F₂, htab⟩ := (hb2_iff _ _ _ _ _).mp hB2
  obtain ⟨C, Bx, Dx, habs⟩ :=
    arm_time_absorbed S D B c hsource M c' d' answer hM Mtab C₂ E₂ F₂ htab Csrc Esrc
  exact ⟨_, C, Bx, Dx, fun f hn hk => BitMachine.outputsWithin_mono _
    (harm c M c' d' answer hM herr hsource Mtab C₂ E₂ F₂ htab f hn hk) (habs f hn hk)⟩

end Main

end EthInapproximability.CurrentPaper.Unit4Clock
