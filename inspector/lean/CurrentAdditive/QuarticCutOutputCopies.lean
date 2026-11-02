import CurrentAdditive.QuarticFrontCutRun

/-! Copy graph, unary gap, and the cut raw prefix into the first three cells
of the enlarged bank, ready for physical serialization. -/

namespace Paper2.CurrentAdditive.QuarticCutOutputCopies

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2 Paper2.A3Assembly
open Paper2.CurrentAdditive.QuarticFrontLift
open Paper2.CurrentAdditive.QuarticNumericFront
open Paper2.CurrentAdditive.QuarticFrontWord

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

def outC (i : Fin 3) : K := Lift.pos FS (.inl (.inl i))
def srcC (i : Fin 3) : K :=
  ![Lift.pk FS 0, Lift.pk FS 1,
    Lift.ιOS FS (SuccessOrient.preSlots (SamplerParameterJoin.bitCountSlot 0))] i
def scratchC : K := Lift.ιFS FS Packet27.scratch

def postBank (g : EncodedGraph.Graph) (Δ : ℕ) (γ : ℚ)
    (k : ℕ) (raw : List Bool) (B : FS → List Bool)
    (H : SamplerParameterBank.Stack → List Bool) : K → List Bool :=
  bank (Lift.ιOS FS)
    (afterMaster (FullFront.X0 g k raw) B (startWordBank g Δ γ k raw))
    (bank SuccessOrient.preSlots (startWordBank g Δ γ k raw) H)

def outPacket (g : EncodedGraph.Graph) (k : ℕ)
    (cut : List Bool) : Fin 3 → List Bool :=
  ![EncodedGraph.encode g, List.replicate k true, cut]

theorem post_blank (g : EncodedGraph.Graph) (Δ : ℕ) (γ : ℚ)
    (k : ℕ) (raw : List Bool) (B : FS → List Bool)
    (H : SamplerParameterBank.Stack → List Bool) (i : Fin 3) :
    postBank g Δ γ k raw B H (outC i) = [] := by
  unfold postBank
  rw [bank_outside]
  · change afterMaster (FullFront.X0 g k raw) B
        (startWordBank g Δ γ k raw)
        (Lift.pos FS (.inl (.inl i))) = []
    rw [afterMaster, Lift.layoutBank_inl]
    fin_cases i <;> rfl
  · rintro ⟨x, hx⟩
    have hh := Lift.pos_injective FS hx
    exact nomatch hh

theorem post_scratch (g : EncodedGraph.Graph) (Δ : ℕ) (γ : ℚ)
    (k : ℕ) (raw : List Bool) (B : FS → List Bool)
    (H : SamplerParameterBank.Stack → List Bool)
    (hB : B Packet27.scratch = []) :
    postBank g Δ γ k raw B H scratchC = [] := by
  unfold postBank
  rw [bank_outside]
  · change afterMaster (FullFront.X0 g k raw) B
        (startWordBank g Δ γ k raw)
        (Lift.ιFS FS Packet27.scratch) = []
    change Lift.layoutBank FS (FullFront.X0 g k raw)
      (Lift.region FS (startWordBank g Δ γ k raw) ![[], [], []] B)
      (Lift.pos FS (.inl (workRaw Packet27.scratch))) = []
    rw [Lift.layoutBank_inl]
    exact hB
  · rintro ⟨x, hx⟩
    have hh := Lift.pos_injective FS hx
    exact nomatch hh

theorem os_ne_pk (x : SuccessOrient.Stack) (i : Fin 3) :
    Lift.ιOS FS x ≠ Lift.pk FS i := by
  intro h
  have hs : (Lift.ιOS FS x).val < Lift.a FS := by
    simp [Lift.ιOS, Lift.pos, finSumFinEquiv_apply_left]
  have hd : (Lift.pk FS i).val = Lift.a FS + i.val := by
    simp [Lift.pk, Lift.pos, finSumFinEquiv_apply_right]
  have hv := congrArg Fin.val h
  omega

theorem post_packet (g : EncodedGraph.Graph) (Δ : ℕ) (γ : ℚ)
    (k : ℕ) (raw : List Bool) (B : FS → List Bool)
    (H : SamplerParameterBank.Stack → List Bool) (i : Fin 3) :
    postBank g Δ γ k raw B H (Lift.pk FS i) =
      (FullFront.X0 g k raw) i := by
  unfold postBank
  rw [bank_outside]
  · change afterMaster (FullFront.X0 g k raw) B
        (startWordBank g Δ γ k raw) (Lift.pk FS i) = _
    exact Lift.layoutBank_inr FS (FullFront.X0 g k raw) _ i
  · rintro ⟨x, hx⟩
    exact os_ne_pk x i hx

theorem post_cut (g : EncodedGraph.Graph) (Δ : ℕ) (γ : ℚ)
    (k : ℕ) (raw : List Bool) (B : FS → List Bool)
    (H : SamplerParameterBank.Stack → List Bool) :
    postBank g Δ γ k raw B H
      (Lift.ιOS FS (SuccessOrient.preSlots
        (SamplerParameterJoin.bitCountSlot 0))) =
      H (SamplerParameterJoin.bitCountSlot 0) := by
  unfold postBank
  rw [bank_at, bank_at]

theorem post_sources (g : EncodedGraph.Graph) (Δ : ℕ) (γ : ℚ)
    (k : ℕ) (raw : List Bool) (B : FS → List Bool)
    (H : SamplerParameterBank.Stack → List Bool)
    (hcut : H (SamplerParameterJoin.bitCountSlot 0) =
      raw.take (QuarticCutCount.count27 g.vertices g.edges.length
        (Nat.clog 2 g.vertices) Δ γ k)) (i : Fin 3) :
    postBank g Δ γ k raw B H (srcC i) =
      outPacket g k (raw.take (QuarticCutCount.count27
        g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ k)) i := by
  fin_cases i
  · simpa [srcC, outPacket, FullFront.X0] using
      post_packet g Δ γ k raw B H 0
  · simpa [srcC, outPacket, FullFront.X0] using
      post_packet g Δ γ k raw B H 1
  · simpa [srcC, outPacket, post_cut] using hcut

theorem pk_ne_out (i j : Fin 3) : Lift.pk FS i ≠ outC j := by
  intro h
  have hs : (Lift.pk FS i).val = Lift.a FS + i.val := by
    simp [Lift.pk, Lift.pos, finSumFinEquiv_apply_right]
  have hd : (outC j).val < Lift.a FS := by
    simp [outC, Lift.pos, finSumFinEquiv_apply_left]
  have hv := congrArg Fin.val h
  omega

theorem cut_ne_out (j : Fin 3) :
    Lift.ιOS FS (SuccessOrient.preSlots
      (SamplerParameterJoin.bitCountSlot 0)) ≠ outC j := by
  intro h
  have hh := Lift.pos_injective FS h
  exact nomatch hh

theorem scratch_ne_out (j : Fin 3) : scratchC ≠ outC j := by
  intro h
  have hh := Lift.pos_injective FS h
  exact nomatch hh

theorem src_ne_scratch (i : Fin 3) : srcC i ≠ scratchC := by
  fin_cases i
  · change Lift.pk FS 0 ≠ scratchC
    intro h
    have hv := congrArg Fin.val h
    have hs : (Lift.pk FS 0).val = Lift.a FS := by
      simp [Lift.pk, Lift.pos, finSumFinEquiv_apply_right]
    have hd : scratchC.val < Lift.a FS := by
      simp [scratchC, Lift.ιFS, Lift.pos, finSumFinEquiv_apply_left]
    omega
  · change Lift.pk FS 1 ≠ scratchC
    intro h
    have hv := congrArg Fin.val h
    have hs : (Lift.pk FS 1).val = Lift.a FS + 1 := by
      simp [Lift.pk, Lift.pos, finSumFinEquiv_apply_right]
    have hd : scratchC.val < Lift.a FS := by
      simp [scratchC, Lift.ιFS, Lift.pos, finSumFinEquiv_apply_left]
    omega
  · intro h
    have hh := Lift.pos_injective FS h
    exact nomatch hh

theorem src_ne_out (i j : Fin 3) : srcC i ≠ outC j := by
  fin_cases i
  · exact pk_ne_out 0 j
  · exact pk_ne_out 1 j
  · exact cut_ne_out j

def copies (i : Fin 3) : Fin 3 ↪ K :=
  ⟨![srcC i, outC i, scratchC], by
    intro x y h
    fin_cases x <;> fin_cases y
    · rfl
    · exact False.elim (src_ne_out i i (by simpa using h))
    · exact False.elim (src_ne_scratch i (by simpa using h))
    · exact False.elim (src_ne_out i i (by simpa using h.symm))
    · rfl
    · exact False.elim (scratch_ne_out i (by simpa using h.symm))
    · exact False.elim (src_ne_scratch i (by simpa using h.symm))
    · exact False.elim (scratch_ne_out i (by simpa using h))
    · rfl⟩

theorem src_ne_dst (i j : Fin 3) : copies i 0 ≠ copies j 1 := by
  fin_cases i
  · exact pk_ne_out 0 j
  · exact pk_ne_out 1 j
  · exact cut_ne_out j

theorem scratch_ne_dst (i j : Fin 3) : copies i 2 ≠ copies j 1 := by
  exact scratch_ne_out j

theorem dst_injective (i j : Fin 3)
    (h : copies i 1 = copies j 1) : i = j := by
  have hh : outC i = outC j := by simpa [copies] using h
  exact (show Function.Injective outC from by
    intro x y e
    exact Sum.inl.inj (Sum.inl.inj (Lift.pos_injective FS e))) hh

theorem copy_run (S : K → List Bool)
    (hScratch : S scratchC = []) :
    ∃ t ≤ 3 * (2 * (BitMachineBankCodec.encode S).length + 3) + 1,
      ∃ v,
      ((advance (CopyAll.prog copies))^[t])
        (⟨some (.inl ⟨0, by omega⟩), none, S⟩ :
          TM2.Cfg (fun _ : K => Bool) _ _) =
        ⟨none, v, CopyAll.done copies 3 S⟩ := by
  apply CopyAll.all_run copies src_ne_dst scratch_ne_dst dst_injective
    S (fun _ => hScratch) (BitMachineBankCodec.encode S).length
    (fun i => BitMachineBankCodec.word_length_le_encode S (srcC i)) none

#print axioms copy_run

end
end Paper2.CurrentAdditive.QuarticCutOutputCopies
