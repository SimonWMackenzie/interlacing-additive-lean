import EthInapproximability.CurrentPaper.U4PostFrame
import EthInapproximability.CurrentPaper.U4ItemAssembly

/-!
# Unit 4 (Paper B), segment B4-S5 (part 2): the post machine on the encoded H-B2 word

Lane owner:b-unit4-shell-3 (private, 26 September 2026).

For the fixed estimator machine `M` (packet width `W = M.stackCount + 4`), ONE machine

  `postMachine M = composition (Pre (W + 19)) (composition (Wrapper M) (Drop 25))`

where `Wrapper M` is the admitted `BitMachineBankWrapper.machine` at width `W + 25` around the
local post program `U4PostLocal.Local.program` inlined at the fixed injective stack map `ι0`:
H-B2 fields 0-5 ↦ `W+19 … W+24` (where `Pre` put them), table ↦ `M.input`, unary `y` ↦ `W-4`,
unary `k` ↦ `W-3` (the canonical packet slots), scratch ↦ `W … W+15`. On every H-B2 word it
outputs exactly `SignedMidpointApproxCanonical.packet M (FinalPadding.table R p hm hr) y k`.
-/

namespace EthInapproximability.CurrentPaper.Unit4Post.Body

open Turing BitMachineEncoding

variable (M : BitMachine.Machine)

/-- The stack map of the local program into the wrapper bank. -/
def ι0f (j : Fin 25) : Fin (M.stackCount + 4 + 25) :=
  if h : j.val < 6 then ⟨M.stackCount + 4 + 19 + j.val, by omega⟩
  else if j.val = 6 then ⟨M.input.val, by have := M.input.isLt; omega⟩
  else if j.val = 7 then ⟨M.stackCount, by omega⟩
  else if j.val = 8 then ⟨M.stackCount + 1, by omega⟩
  else ⟨M.stackCount + 4 + (j.val - 9), by have := j.isLt; omega⟩

theorem ι0f_val (j : Fin 25) : (ι0f M j).val =
    if j.val < 6 then M.stackCount + 4 + 19 + j.val
    else if j.val = 6 then M.input.val
    else if j.val = 7 then M.stackCount
    else if j.val = 8 then M.stackCount + 1
    else M.stackCount + 4 + (j.val - 9) := by
  unfold ι0f
  split_ifs <;> rfl

theorem ι0f_injective : Function.Injective (ι0f M) := by
  intro a b h
  have h' := congrArg Fin.val h
  rw [ι0f_val, ι0f_val] at h'
  have := M.input.isLt
  have := a.isLt
  have := b.isLt
  apply Fin.ext
  split_ifs at h' <;> omega

def ι0 : Fin 25 ↪ Fin (M.stackCount + 4 + 25) := ⟨ι0f M, ι0f_injective M⟩

/-- The local post program, inlined into the wrapper bank. -/
def localP := fun l => BitMachineStackEmbedding.stackStmt (ι0 M) (Local.program l)

noncomputable def wrapper : BitMachine.Machine :=
  BitMachineBankWrapper.machine (localP M) (BitMachineRawSequence.leftLabel Exponent.start)
    Local.initial

noncomputable def postMachine : BitMachine.Machine :=
  BitMachineComposition.composition (Pre.machine (M.stackCount + 4 + 19))
    (BitMachineComposition.composition (wrapper M) (Drop.machine 25))


/-! ## The input bank (after `Pre`) and the output bank (before `Drop`) -/

abbrev rp (n : ℕ) : List Bool := List.replicate n true

def f6 (n k m r y : ℕ) (R : List Bool) : Fin 6 → List Bool :=
  ![rp n, rp k, rp m, rp r, R, rp y]

def Sin (n k m r y : ℕ) (R : List Bool) : Fin (M.stackCount + 4 + 25) → List Bool :=
  fun j => if h : M.stackCount + 4 + 19 ≤ j.val then
    f6 n k m r y R ⟨j.val - (M.stackCount + 4 + 19), by have := j.isLt; omega⟩ else []

theorem Sin_lo (n k m r y : ℕ) (R : List Bool) (j : Fin (M.stackCount + 4 + 25))
    (h : j.val < M.stackCount + 4 + 19) : Sin M n k m r y R j = [] := by
  unfold Sin
  rw [dif_neg (by omega)]

theorem Sin_hi (n k m r y : ℕ) (R : List Bool) (i : Fin 6) (j : Fin (M.stackCount + 4 + 25))
    (h : j.val = M.stackCount + 4 + 19 + i.val) : Sin M n k m r y R j = f6 n k m r y R i := by
  unfold Sin
  rw [dif_pos (by omega)]
  congr 1
  ext
  simp only
  omega

theorem encode_Sin (n k m r y : ℕ) (R : List Bool) :
    BitMachineBankCodec.encode (Sin M n k m r y R) =
      List.replicate (M.stackCount + 4 + 19) false ++ Unit4ItemAssembly.hb2Word n k m r y R := by
  rw [encode_cast (show M.stackCount + 4 + 25 = (M.stackCount + 4 + 19) + 6 by omega),
    encode_split]
  congr 1
  · rw [← encode_nil (M.stackCount + 4 + 19)]
    congr 1
    funext i
    apply Sin_lo
    simp
  · unfold Unit4ItemAssembly.hb2Word
    congr 1
    funext j
    rw [Sin_hi M n k m r y R j]
    · rfl
    · simp

theorem decode_input (n k m r y : ℕ) (R : List Bool) :
    BitMachineBankCodec.decode (M.stackCount + 4 + 25)
      (List.replicate (M.stackCount + 4 + 19) false ++ Unit4ItemAssembly.hb2Word n k m r y R) =
      some (Sin M n k m r y R) := by
  rw [← encode_Sin]
  exact BitMachineBankCodec.decode_encode _

def Fout (T : List Bool) (y k : ℕ) : Fin (M.stackCount + 4 + 25) → List Bool :=
  fun j => if h : j.val < M.stackCount + 4 then
    SignedMidpointApproxCanonical.bank M T y k ⟨j.val, h⟩ else []

theorem encode_Fout (T : List Bool) (y k : ℕ) :
    BitMachineBankCodec.encode (Fout M T y k) =
      SignedMidpointApproxCanonical.packet M T y k ++ List.replicate 25 false := by
  rw [encode_split]
  congr 1
  · unfold SignedMidpointApproxCanonical.packet
    congr 1
    funext i
    unfold Fout
    rw [dif_pos (by simp)]
    rfl
  · rw [← encode_nil 25]
    congr 1
    funext j
    unfold Fout
    rw [dif_neg (by simp)]

theorem Fout_hi (T : List Bool) (y k : ℕ) (j : Fin (M.stackCount + 4 + 25))
    (h : M.stackCount + 4 ≤ j.val) : Fout M T y k j = [] := by
  unfold Fout
  rw [dif_neg (by omega)]

theorem Fout_T (T : List Bool) (y k : ℕ) (j : Fin (M.stackCount + 4 + 25))
    (h : j.val = M.input.val) : Fout M T y k j = T := by
  have hl := M.input.isLt
  unfold Fout
  rw [dif_pos (by omega)]
  have e : (⟨j.val, by omega⟩ : Fin (M.stackCount + 4)) = Fin.castAdd 4 M.input :=
    Fin.ext (by simp [h])
  rw [e]
  simp [SignedMidpointApproxCanonical.bank, SignedMidpointApproxPacket.stackEquiv,
    finSumFinEquiv_symm_apply_castAdd]

theorem Fout_slot (T : List Bool) (y k : ℕ) (j : Fin (M.stackCount + 4 + 25)) (i : Fin 4)
    (h : j.val = M.stackCount + i.val) :
    Fout M T y k j = ![List.replicate y true, List.replicate k true, [], []] i := by
  unfold Fout
  rw [dif_pos (by omega)]
  have e : (⟨j.val, by omega⟩ : Fin (M.stackCount + 4)) = Fin.natAdd M.stackCount i :=
    Fin.ext (by simp [h])
  rw [e]
  simp [SignedMidpointApproxCanonical.bank, SignedMidpointApproxPacket.stackEquiv,
    finSumFinEquiv_symm_apply_natAdd]

theorem Fout_other (T : List Bool) (y k : ℕ) (j : Fin (M.stackCount + 4 + 25))
    (h1 : j.val < M.stackCount + 4) (h2 : j.val ≠ M.input.val) (h3 : j.val ≠ M.stackCount)
    (h4 : j.val ≠ M.stackCount + 1) : Fout M T y k j = [] := by
  by_cases hs : j.val < M.stackCount
  · unfold Fout
    rw [dif_pos h1]
    have e : (⟨j.val, h1⟩ : Fin (M.stackCount + 4)) = Fin.castAdd 4 ⟨j.val, hs⟩ := rfl
    rw [e]
    simp only [SignedMidpointApproxCanonical.bank, SignedMidpointApproxPacket.stackEquiv,
      finSumFinEquiv_symm_apply_castAdd]
    rw [if_neg]
    intro he
    exact h2 (congrArg Fin.val he)
  · have : j.val = M.stackCount + 2 ∨ j.val = M.stackCount + 3 := by omega
    rcases this with h | h
    · rw [Fout_slot M T y k j 2 (by simp [h])]
      rfl
    · rw [Fout_slot M T y k j 3 (by simp [h])]
      rfl

theorem ι0_apply (j : Fin 25) : (ι0 M j) = ι0f M j := rfl

theorem Sin_ι0 (n k m r y : ℕ) (R : List Bool) (j : Fin 25) :
    Sin M n k m r y R (ι0 M j) = if h : j.val < 6 then f6 n k m r y R ⟨j.val, h⟩ else [] := by
  have hl := M.input.isLt
  have hj := j.isLt
  by_cases h : j.val < 6
  · rw [dif_pos h]
    apply Sin_hi
    rw [ι0_apply, ι0f_val, if_pos h]
  · rw [dif_neg h]
    apply Sin_lo
    rw [ι0_apply, ι0f_val]
    split_ifs <;> omega

theorem Fout_ι0 (T : List Bool) (y k : ℕ) (j : Fin 25) :
    Fout M T y k (ι0 M j) =
      if j.val = 6 then T else if j.val = 7 then List.replicate y true
      else if j.val = 8 then List.replicate k true else [] := by
  have hl := M.input.isLt
  have hj := j.isLt
  have hv := ι0f_val M j
  rw [← ι0_apply] at hv
  by_cases h6 : j.val = 6
  · rw [if_pos h6]
    apply Fout_T
    rw [hv]; simp [h6]
  · rw [if_neg h6]
    by_cases h7 : j.val = 7
    · rw [if_pos h7, Fout_slot M T y k _ 0 (by rw [hv]; simp [h7])]
      rfl
    · rw [if_neg h7]
      by_cases h8 : j.val = 8
      · rw [if_pos h8, Fout_slot M T y k _ 1 (by rw [hv]; simp [h8])]
        rfl
      · rw [if_neg h8]
        apply Fout_hi
        rw [hv]
        split_ifs <;> omega

/-! ## The embedded local run -/

theorem local_embedded {m r : ℕ} (n k y : ℕ) (Rf : Fin m → Fin r → Bool) (hm : 0 < m)
    (hr : 0 < r) :
    ∃ t ≤ Local.localBound n k m r y, ∃ v,
      ((advance (localP M))^[t])
        ⟨some (BitMachineRawSequence.leftLabel Exponent.start), Local.initial,
          Sin M n k m r y (MatrixMaterialization.rowMajor Rf)⟩ =
        ⟨none, v, Fout M (FinalPadding.table Rf (Exponent.pexp n k) hm hr) y k⟩ := by
  obtain ⟨t, ht, v, h⟩ := Local.local_run n k y Rf hm hr
  refine ⟨t, ht, v, embed_run (ι0 M) Local.program _ Local.initial v _ _ _ _ t h ?_ ?_ ?_⟩
  · intro j
    rw [Sin_ι0]
    fin_cases j <;> rfl
  · intro j
    rw [Fout_ι0]
    fin_cases j <;> rfl
  · intro j hj
    have hl := M.input.isLt
    have hjl := j.isLt
    have hS : Sin M n k m r y (MatrixMaterialization.rowMajor Rf) j = [] := by
      apply Sin_lo
      by_contra hc
      apply hj ⟨j.val - (M.stackCount + 4 + 19), by omega⟩
      apply Fin.ext
      rw [ι0_apply, ι0f_val, if_pos (by simp only; omega)]
      simp only
      omega
    have hF : Fout M (FinalPadding.table Rf (Exponent.pexp n k) hm hr) y k j = [] := by
      by_cases h1 : j.val < M.stackCount + 4
      · apply Fout_other M _ y k j h1
        · intro h2
          apply hj 6
          apply Fin.ext
          rw [ι0_apply, ι0f_val]
          simp [h2]
        · intro h3
          apply hj 7
          apply Fin.ext
          rw [ι0_apply, ι0f_val]
          simp [h3]
        · intro h4
          apply hj 8
          apply Fin.ext
          rw [ι0_apply, ι0f_val]
          simp [h4]
      · exact Fout_hi M _ y k j (by omega)
    rw [hS, hF]

/-! ## The wrapper and the composite post machine -/

theorem wrapper_outputs {m r : ℕ} (n k y : ℕ) (Rf : Fin m → Fin r → Bool) (hm : 0 < m)
    (hr : 0 < r) :
    (wrapper M).OutputsWithin
      (List.replicate (M.stackCount + 4 + 19) false ++
        Unit4ItemAssembly.hb2Word n k m r y (MatrixMaterialization.rowMajor Rf))
      (SignedMidpointApproxCanonical.packet M (FinalPadding.table Rf (Exponent.pexp n k) hm hr)
        y k ++ List.replicate 25 false)
      ((2 * (M.stackCount + 4 + 25) + 1) *
          ((List.replicate (M.stackCount + 4 + 19) false ++
            Unit4ItemAssembly.hb2Word n k m r y (MatrixMaterialization.rowMajor Rf)).length + 1) +
        Local.localBound n k m r y +
        2 * (SignedMidpointApproxCanonical.packet M
          (FinalPadding.table Rf (Exponent.pexp n k) hm hr) y k ++
            List.replicate 25 false).length + 4) := by
  have hd := decode_input M n k m r y (MatrixMaterialization.rowMajor Rf)
  have ho := BitMachineBankWrapper.outputs (localP M)
    (BitMachineRawSequence.leftLabel Exponent.start) Local.initial
    (fun _ => Fout M (FinalPadding.table Rf (Exponent.pexp n k) hm hr) y k)
    (List.replicate (M.stackCount + 4 + 19) false ++
      Unit4ItemAssembly.hb2Word n k m r y (MatrixMaterialization.rowMajor Rf))
    (Local.localBound n k m r y)
    (SignedMidpointApproxCanonical.packet M
      (FinalPadding.table Rf (Exponent.pexp n k) hm hr) y k ++ List.replicate 25 false).length
    (by
      intro S hS
      rw [hd] at hS
      cases hS
      obtain ⟨t, ht, v, h⟩ := local_embedded M n k y Rf hm hr
      exact ⟨t, _, ht, h, rfl, rfl⟩)
    (by
      intro S _
      rw [encode_Fout])
  have hres : BitMachineBankWrapper.result
      (fun _ => Fout M (FinalPadding.table Rf (Exponent.pexp n k) hm hr) y k)
      (List.replicate (M.stackCount + 4 + 19) false ++
        Unit4ItemAssembly.hb2Word n k m r y (MatrixMaterialization.rowMajor Rf)) =
      SignedMidpointApproxCanonical.packet M (FinalPadding.table Rf (Exponent.pexp n k) hm hr)
        y k ++ List.replicate 25 false := by
    unfold BitMachineBankWrapper.result
    rw [hd]
    exact encode_Fout M _ y k
  rw [hres] at ho
  exact ho

/-- The explicit time of the post machine (before polynomial absorption). -/
def postTime (a wl P L : ℕ) (K : ℕ) : ℕ :=
  (a + 1) + 2 * (a + wl) + 2 +
    (((2 * K + 1) * (a + wl + 1) + L + 2 * (P + 25) + 4) + 2 * (P + 25) + 2 +
      (2 * P + 2 * 25 + 3))

/-- **B4-S4 + B4-S5: the post machine.** For the fixed estimator machine `M`, the ONE machine
`postMachine M` maps every H-B2 word to the exact estimator packet of the padded table. -/
theorem post_outputs {m r : ℕ} (n k y : ℕ) (Rf : Fin m → Fin r → Bool) (hm : 0 < m)
    (hr : 0 < r) :
    (postMachine M).OutputsWithin
      (Unit4ItemAssembly.hb2Word n k m r y (MatrixMaterialization.rowMajor Rf))
      (SignedMidpointApproxCanonical.packet M (FinalPadding.table Rf (Exponent.pexp n k) hm hr)
        y k)
      (postTime (M.stackCount + 4 + 19)
        (Unit4ItemAssembly.hb2Word n k m r y (MatrixMaterialization.rowMajor Rf)).length
        (SignedMidpointApproxCanonical.packet M
          (FinalPadding.table Rf (Exponent.pexp n k) hm hr) y k).length
        (Local.localBound n k m r y) (M.stackCount + 4 + 25)) := by
  have h1 := Pre.outputs (M.stackCount + 4 + 19)
    (Unit4ItemAssembly.hb2Word n k m r y (MatrixMaterialization.rowMajor Rf))
  have h2 := wrapper_outputs M n k y Rf hm hr
  have h3 := Drop.outputs 25 (SignedMidpointApproxCanonical.packet M
    (FinalPadding.table Rf (Exponent.pexp n k) hm hr) y k)
  have h23 := BitMachineComposition.composition_outputsWithin (wrapper M) (Drop.machine 25) h2 h3
  have h123 := BitMachineComposition.composition_outputsWithin
    (Pre.machine (M.stackCount + 4 + 19)) _ h1 h23
  apply BitMachine.outputsWithin_mono _ h123
  unfold postTime
  simp only [List.length_append, List.length_replicate]
  omega

end EthInapproximability.CurrentPaper.Unit4Post.Body
