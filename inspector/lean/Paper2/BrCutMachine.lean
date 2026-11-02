import Paper2.BrCutRun
import Paper2.A3Wrap

/-! Lane a-bridge-owner-1: the cut stage as ONE fixed `BitMachine.Machine`.

`cutMachine a b Δ = Pre (nJ+3) ; BankWrapper (cut controller embedded in Fin (nJ+6)) ; Drop (nJ+3)`
(all three admitted machines). On the literal three-field H_A3-layout bank word
`encode ![encode g, 1^k, word]` it prints exactly
`encode ![encode g, 1^k, word.take (frontD a b Δ g k)]` within an explicit clock.
No premise about the graph beyond `g.Valid` is used. -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

namespace Paper2.ABridge

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding

def posK : KC → Fin (nJ + 3 + 3)
  | .inr (.inl i) => ⟨i.val, by omega⟩
  | .inl x => ⟨3 + (eJ x).val, by have := (eJ x).isLt; omega⟩
  | .inr (.inr i) => ⟨nJ + 3 + i.val, by omega⟩

theorem posK_inj : Function.Injective posK := by
  intro x y h
  have hv := congrArg Fin.val h
  rcases x with x | i | i <;> rcases y with y | j | j <;> simp only [posK] at hv
  · have : eJ x = eJ y := Fin.ext (by omega)
    exact congrArg Sum.inl ((Fintype.equivFin FullFront.JF).injective this)
  · omega
  · have := (eJ x).isLt; omega
  · omega
  · exact congrArg (fun t => Sum.inr (Sum.inl t)) (Fin.ext hv)
  · omega
  · have := (eJ y).isLt; omega
  · omega
  · exact congrArg (fun t => Sum.inr (Sum.inr t)) (Fin.ext (by omega))

def εK : KC ↪ Fin (nJ + 3 + 3) := ⟨posK, posK_inj⟩

def cutQ (a b Δ : ℕ) := fun l => stackStmt εK (cutProgram a b Δ l)

set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 4000000 in
instance instFtCutLabel (a b Δ : ℕ) : Fintype (labelT (cutProgram a b Δ)) := by
  unfold labelT; infer_instance

set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 4000000 in
instance instFtCutCtl (a b Δ : ℕ) : Fintype (ctlT (cutProgram a b Δ)) := by
  unfold ctlT; infer_instance

def cutWrapper (a b Δ : ℕ) : BitMachine.Machine :=
  @BitMachineBankWrapper.machine (nJ + 3 + 3) _ _ (instFtCutLabel a b Δ) (instFtCutCtl a b Δ)
    (cutQ a b Δ) (cutStart a b Δ) (cutCtl0 a b Δ)

/-- The fixed cut machine (constants `a b Δ` fixed before the input). -/
def cutMachine (a b Δ : ℕ) : BitMachine.Machine :=
  BitMachineComposition.composition (Unit4Post.Pre.machine (nJ + 3))
    (BitMachineComposition.composition (cutWrapper a b Δ) (Unit4Post.Drop.machine (nJ + 3)))

/-- The output bank: three fields first, then `nJ+3` empty fields. -/
def outBank (Y : Fin 3 → List Bool) : Fin (nJ + 3 + 3) → List Bool :=
  fun j => if h : j.val < 3 then Y ⟨j.val, h⟩ else []

theorem start_pull (X : Fin 3 → List Bool) :
    bank εK (A3Assembly.Wrap.widen (nJ + 3) X) (startKC X) =
      A3Assembly.Wrap.widen (nJ + 3) X := by
  apply bank_eq_self
  intro z
  rcases z with x | i | i
  · have := (eJ x).isLt
    simp only [startKC, εK, Function.Embedding.coeFn_mk, posK, A3Assembly.Wrap.widen]
    rw [dif_neg (by omega)]
  · simp only [startKC, εK, Function.Embedding.coeFn_mk, posK, A3Assembly.Wrap.widen]
    rw [dif_neg (by have := i.isLt; omega)]
  · simp only [startKC, εK, Function.Embedding.coeFn_mk, posK, A3Assembly.Wrap.widen]
    rw [dif_pos (by omega)]
    congr 1
    ext
    simp

theorem exit_pull (X Y : Fin 3 → List Bool) :
    bank εK (A3Assembly.Wrap.widen (nJ + 3) X) (exitKC Y) = outBank Y := by
  funext j
  by_cases hj : ∃ z, εK z = j
  · obtain ⟨z, rfl⟩ := hj
    rw [bank_at]
    rcases z with x | i | i
    · have := (eJ x).isLt
      simp only [exitKC, εK, Function.Embedding.coeFn_mk, posK, outBank]
      rw [dif_neg (by omega)]
    · simp only [exitKC, εK, Function.Embedding.coeFn_mk, posK, outBank]
      rw [dif_pos i.isLt]
    · simp only [exitKC, εK, Function.Embedding.coeFn_mk, posK, outBank]
      rw [dif_neg (by omega)]
  · rw [bank_outside _ _ _ _ hj]
    have hlo : 3 ≤ j.val := by
      by_contra hlt
      exact hj ⟨.inr (.inl ⟨j.val, by omega⟩), Fin.ext (by simp [εK, posK])⟩
    have hhi : j.val < nJ + 3 := by
      by_contra hge
      exact hj ⟨.inr (.inr ⟨j.val - (nJ + 3), by omega⟩),
        Fin.ext (by simp [εK, posK]; omega)⟩
    simp only [A3Assembly.Wrap.widen, outBank]
    rw [dif_neg (by omega), dif_neg (by omega)]

theorem encode_outBank (Y : Fin 3 → List Bool) :
    BitMachineBankCodec.encode (outBank Y) =
      BitMachineBankCodec.encode Y ++ List.replicate (nJ + 3) false := by
  rw [Unit4Post.encode_cast (show nJ + 3 + 3 = 3 + (nJ + 3) by omega),
    Unit4Post.encode_split 3 (nJ + 3)]
  have h1 : (fun i : Fin 3 => outBank Y (Fin.cast (show nJ + 3 + 3 = 3 + (nJ + 3) by omega).symm
      (i.castLE (Nat.le_add_right 3 (nJ + 3))))) = Y := by
    funext i
    simp only [outBank, Fin.val_cast, Fin.val_castLE]
    rw [dif_pos i.isLt]
  have h2 : (fun j : Fin (nJ + 3) => outBank Y (Fin.cast
      (show nJ + 3 + 3 = 3 + (nJ + 3) by omega).symm (j.natAdd 3))) =
      fun _ => ([] : List Bool) := by
    funext j
    simp only [outBank, Fin.val_cast, Fin.val_natAdd]
    rw [dif_neg (by omega)]
  rw [h1, h2, Unit4Post.encode_nil]

/-- The explicit clock of the cut machine. -/
def cutClock (a b Δ : ℕ) (g : EncodedGraph.Graph) (k : ℕ) (word : List Bool) : ℕ :=
  (nJ + 3 + 1) +
    2 * (nJ + 3 + (BitMachineBankCodec.encode
      ![EncodedGraph.encode g, List.replicate k true, word]).length) + 2 +
    (((2 * (nJ + 3 + 3) + 1) * ((nJ + 3 + (BitMachineBankCodec.encode
        ![EncodedGraph.encode g, List.replicate k true, word]).length) + 1) +
      cutBd a b Δ g k word +
      2 * ((BitMachineBankCodec.encode
        ![EncodedGraph.encode g, List.replicate k true, word]).length + (nJ + 3)) + 4) +
     2 * ((BitMachineBankCodec.encode
        ![EncodedGraph.encode g, List.replicate k true, word]).length + (nJ + 3)) + 2 +
     (2 * (BitMachineBankCodec.encode
        ![EncodedGraph.encode g, List.replicate k true, word]).length + 2 * (nJ + 3) + 3))

theorem encode_take_le (A B W : List Bool) (D : ℕ) :
    (BitMachineBankCodec.encode ![A, B, W.take D]).length ≤
      (BitMachineBankCodec.encode ![A, B, W]).length := by
  rw [BitMachineBankCodec.encode_length, BitMachineBankCodec.encode_length]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  have := List.length_take_le' D W
  omega

/-- **The cut machine.** One fixed machine; on the literal bank word of
`![encode g, 1^k, word]` it prints exactly the bank word of
`![encode g, 1^k, word.take (frontD a b Δ g k)]` within `cutClock`. -/
theorem cut_machine_outputs (a b Δ : ℕ) (g : EncodedGraph.Graph) (hg : g.Valid)
    (k : ℕ) (word : List Bool) :
    (cutMachine a b Δ).OutputsWithin
      (BitMachineBankCodec.encode ![EncodedGraph.encode g, List.replicate k true, word])
      (BitMachineBankCodec.encode ![EncodedGraph.encode g, List.replicate k true,
        word.take (FrontPreparedCut.frontD a b Δ g k)])
      (cutClock a b Δ g k word) := by
  set X : Fin 3 → List Bool := ![EncodedGraph.encode g, List.replicate k true, word] with hX
  set Y : Fin 3 → List Bool := ![EncodedGraph.encode g, List.replicate k true,
    word.take (FrontPreparedCut.frontD a b Δ g k)] with hY
  obtain ⟨t, ht, v, hr⟩ := cut_local_run a b Δ g hg k word
  have hQ := BitMachineStackRun.run εK (A3Assembly.Wrap.widen (nJ + 3) X) (cutProgram a b Δ)
    (⟨some (cutStart a b Δ), cutCtl0 a b Δ, startKC X⟩ :
      TM2.Cfg (fun _ : KC => Bool) _ _) t
  rw [hr] at hQ
  simp only [stackCfg, start_pull, exit_pull] at hQ
  have hpre := Unit4Post.Pre.outputs (nJ + 3) (BitMachineBankCodec.encode X)
  rw [← A3Assembly.Wrap.encode_widen] at hpre
  have hwrap := @BitMachineBankWrapper.outputs (nJ + 3 + 3) _ _ (instFtCutLabel a b Δ) (instFtCutCtl a b Δ)
    (cutQ a b Δ) (cutStart a b Δ) (cutCtl0 a b Δ) (fun _ => outBank Y)
    (BitMachineBankCodec.encode (A3Assembly.Wrap.widen (nJ + 3) X))
    (cutBd a b Δ g k word) ((BitMachineBankCodec.encode Y).length + (nJ + 3))
    (by
      intro S hd
      rw [BitMachineBankCodec.decode_encode] at hd
      cases Option.some.inj hd
      exact ⟨t, _, ht, hQ, rfl, rfl⟩)
    (by
      intro S _
      rw [encode_outBank, List.length_append, List.length_replicate])
  have hres : BitMachineBankWrapper.result (fun _ => outBank Y)
      (BitMachineBankCodec.encode (A3Assembly.Wrap.widen (nJ + 3) X)) =
      BitMachineBankCodec.encode Y ++ List.replicate (nJ + 3) false := by
    simp only [BitMachineBankWrapper.result, BitMachineBankCodec.decode_encode, encode_outBank]
  rw [hres] at hwrap
  have hdrop := Unit4Post.Drop.outputs (nJ + 3) (BitMachineBankCodec.encode Y)
  have h23 := BitMachineComposition.composition_outputsWithin _ _ hwrap hdrop
  have h123 := BitMachineComposition.composition_outputsWithin _ _ hpre h23
  apply BitMachine.outputsWithin_mono _ h123
  have hlen1 : (BitMachineBankCodec.encode (A3Assembly.Wrap.widen (nJ + 3) X)).length =
      nJ + 3 + (BitMachineBankCodec.encode X).length := by
    rw [A3Assembly.Wrap.encode_widen, List.length_append, List.length_replicate]
  have hYX : (BitMachineBankCodec.encode Y).length ≤ (BitMachineBankCodec.encode X).length := by
    rw [hX, hY]
    exact encode_take_le _ _ _ _
  rw [hlen1, List.length_append, List.length_replicate]
  unfold cutClock
  rw [← hX]
  omega

#print axioms cut_machine_outputs

end

end Paper2.ABridge
