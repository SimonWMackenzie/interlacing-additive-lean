import Paper2.BrCutLocal

/-! Lane a-bridge-owner-1: the charged local run of the cut controller from the
literal three-input start bank to the exact three-output exit bank. -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

namespace Paper2.ABridge

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding

theorem cost3 (S : KC → List Bool) (x y z : Fin 3 ↪ KC)
    (hyx : y 0 ≠ x 1) (hzx : z 0 ≠ x 1) (hzy : z 0 ≠ y 1) :
    CopyList.cost S [x, y, z] =
      2 * (S (x 0)).length + 2 * (S (y 0)).length + 2 * (S (z 0)).length + 10 := by
  simp only [CopyList.cost, Function.update_of_ne hyx, Function.update_of_ne hzx,
    Function.update_of_ne hzy]
  omega

theorem jc_ne_jc {x y : FullFront.JF} (h : x ≠ y) : jc x ≠ jc y := by
  intro e; exact h (Sum.inl_injective e)

theorem pk_ne_pk {i j : Fin 3} (h : i ≠ j) : FullFront.pk i ≠ FullFront.pk j := by
  intro e; apply h; simpa [FullFront.pk] using e

theorem inCopy_src (i : Fin 3) : inCopy i 0 = inC i := rfl
theorem inCopy_tgt (i : Fin 3) : inCopy i 1 = jc (FullFront.pk i) := rfl
theorem inCopy_scr (i : Fin 3) : inCopy i 2 = jc FullFront.zs := rfl
theorem outCopy_src (i : Fin 3) : outCopy i 0 = jc (FullFront.pk i) := rfl
theorem outCopy_tgt (i : Fin 3) : outCopy i 1 = outC i := rfl
theorem outCopy_scr (i : Fin 3) : outCopy i 2 = jc FullFront.zs := rfl

/-- Bank after the input copies. -/
theorem in_apply (X : Fin 3 → List Bool) :
    (∀ x : FullFront.JF, FullFront.F0 X x = CopyList.apply (startKC X) inList (inJ x)) ∧
    (∀ r : Fin 3 ⊕ Fin 3, CopyList.apply (startKC X) inList (.inr r) = startKC X (.inr r)) := by
  have hf := CopyList.apply_fresh inList (startKC X)
    (by
      intro x hx y hy
      simp only [inList, List.mem_cons, List.not_mem_nil, or_false] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
        simp [inCopy, mk3, jc, inC])
    (by simp [inList, inCopy, mk3, jc, FullFront.pk])
    (by
      intro x hx
      simp only [inList, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> rfl)
  obtain ⟨h1, h2⟩ := hf
  constructor
  · intro x
    rcases x with y | y | y | i | z
    · rw [h2]; · rfl
      intro c hc
      simp only [inList, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> simp [inCopy, mk3, jc, inJ, FullFront.pk]
    · rw [h2]; · rfl
      intro c hc
      simp only [inList, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> simp [inCopy, mk3, jc, inJ, FullFront.pk]
    · rw [h2]; · rfl
      intro c hc
      simp only [inList, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> simp [inCopy, mk3, jc, inJ, FullFront.pk]
    · have hmem : inCopy i ∈ inList := by
        fin_cases i <;> simp [inList]
      have := h1 (inCopy i) hmem
      rw [inCopy_tgt, inCopy_src] at this
      change FullFront.F0 X (FullFront.pk i) = CopyList.apply (startKC X) inList (jc (FullFront.pk i))
      rw [this]
      rfl
    · rw [h2]; · rfl
      intro c hc
      simp only [inList, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> simp [inCopy, mk3, jc, inJ, FullFront.pk]
  · intro r
    rw [h2]
    intro c hc
    simp only [inList, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> simp [inCopy, mk3, jc]

theorem inList_scr : ∀ x ∈ inList, x 2 = jc FullFront.zs := by
  intro x hx
  simp only [inList, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> rfl

theorem outList_scr : ∀ x ∈ outList, x 2 = jc FullFront.zs := by
  intro x hx
  simp only [outList, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> rfl

theorem bank_inJ_jc (W : KC → List Bool) (T : FullFront.JF → List Bool) (x : FullFront.JF) :
    bank inJ W T (jc x) = T x := bank_at inJ W T x

theorem bank_inJ_inr (W : KC → List Bool) (T : FullFront.JF → List Bool) (r : Fin 3 ⊕ Fin 3) :
    bank inJ W T (.inr r) = W (.inr r) := by
  apply bank_outside
  rintro ⟨k, hk⟩
  simp [inJ] at hk

/-- Bank after the output copies. -/
theorem out_apply (W : KC → List Bool) (hout : ∀ i, W (outC i) = []) :
    (∀ i, CopyList.apply W outList (outC i) = W (jc (FullFront.pk i))) ∧
    (∀ z, (∀ i, z ≠ outC i) → CopyList.apply W outList z = W z) := by
  have hf := CopyList.apply_fresh outList W
    (by
      intro x hx y hy
      simp only [outList, List.mem_cons, List.not_mem_nil, or_false] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
        simp [outCopy, mk3, jc, outC])
    (by simp [outList, outCopy, mk3, outC])
    (by
      intro x hx
      simp only [outList, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> exact hout _)
  obtain ⟨h1, h2⟩ := hf
  constructor
  · intro i
    have hmem : outCopy i ∈ outList := by fin_cases i <;> simp [outList]
    have := h1 (outCopy i) hmem
    rwa [outCopy_tgt, outCopy_src] at this
  · intro z hz
    apply h2
    intro c hc
    simp only [outList, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> exact (hz _).symm

/-- The three packet cells after the repack. -/
theorem update_pk (H : FullFront.JF → List Bool) (g : EncodedGraph.Graph) (k : ℕ)
    (word : List Bool) (D : ℕ)
    (h0 : H (FullFront.pk 0) = EncodedGraph.encode g)
    (h1 : H (FullFront.pk 1) = List.replicate k true) :
    ∀ i, Function.update H (FullFront.pk 2) (word.take D) (FullFront.pk i) =
      ![EncodedGraph.encode g, List.replicate k true, word.take D] i := by
  intro i
  match i with
  | ⟨0, _⟩ => exact (Function.update_of_ne (pk_ne_pk (by simp [Fin.ext_iff])) _ _).trans h0
  | ⟨1, _⟩ => exact (Function.update_of_ne (pk_ne_pk (by simp [Fin.ext_iff])) _ _).trans h1
  | ⟨2, _⟩ => exact Function.update_self _ _ _

theorem len_triple_take (A B W : List Bool) (D n : ℕ) (hA : A.length ≤ n)
    (hB : B.length ≤ n) (hW : W.length ≤ n) :
    ∀ i, ((![A, B, W.take D] : Fin 3 → List Bool) i).length ≤ n := by
  intro i
  fin_cases i
  · exact hA
  · exact hB
  · show (W.take D).length ≤ n
    rw [List.length_take]
    omega

/-- The packet-stage clock of segment 1. -/
def packetBd (a b Δ : ℕ) (g : EncodedGraph.Graph) (k : ℕ) (word : List Bool) : ℕ :=
  FullFront.fullBd a b Δ g k word +
    FrontPreparedCut.prepBd g.vertices (FullFront.pV g) (FullFront.sV g)
      (FullFront.q1V g) (FullFront.q2V g) (FullFront.wV g)
      (FullFront.QV a b Δ g) k
      (FrontPreparedCut.frontMX a b Δ g k)
      (FrontPreparedCut.frontMY a b Δ g k) word + 1 +
    (word.length + 2 * (word.take (FrontPreparedCut.frontD a b Δ g k)).length + 5) + 1

/-- The clear-stage clock. -/
def clearBd (a b Δ n P : ℕ) : ℕ := (nJ + 3) * (n + packetPerStep a b Δ * P + 1) + 1

/-- The whole local cut clock, in terms of the input bank length `n` and the
packet clock `P`. -/
def cutBdN (a b Δ n P : ℕ) : ℕ := (6 * n + 10) + P + (6 * n + 10) + clearBd a b Δ n P + 3

/-- The whole local cut clock (explicit). -/
def cutBd (a b Δ : ℕ) (g : EncodedGraph.Graph) (k : ℕ) (word : List Bool) : ℕ :=
  cutBdN a b Δ
    (BitMachineBankCodec.encode ![EncodedGraph.encode g, List.replicate k true, word]).length
    (packetBd a b Δ g k word)

/-- **Local cut run.** From the literal start bank (three input cells
`encode g, 1^k, word`), the fixed controller halts with EXACTLY the exit bank
whose output cells are `encode g, 1^k, word.take (frontD a b Δ g k)` and every
other cell empty, within `cutBd`. -/
theorem cut_local_run (a b Δ : ℕ) (g : EncodedGraph.Graph) (hg : g.Valid)
    (k : ℕ) (word : List Bool) :
    ∃ t ≤ cutBd a b Δ g k word, ∃ v,
      ((advance (cutProgram a b Δ))^[t])
        (⟨some (cutStart a b Δ), cutCtl0 a b Δ,
          startKC ![EncodedGraph.encode g, List.replicate k true, word]⟩ :
          TM2.Cfg (fun _ : KC => Bool) _ _) =
        ⟨none, v, exitKC ![EncodedGraph.encode g, List.replicate k true,
          word.take (FrontPreparedCut.frontD a b Δ g k)]⟩ := by
  set X : Fin 3 → List Bool := ![EncodedGraph.encode g, List.replicate k true, word] with hXdef
  set D := FrontPreparedCut.frontD a b Δ g k with hD
  set Y : Fin 3 → List Bool := ![EncodedGraph.encode g, List.replicate k true, word.take D]
    with hYdef
  set n := (BitMachineBankCodec.encode X).length with hn
  have hXn : ∀ i, (X i).length ≤ n := fun i => BitMachineBankCodec.word_length_le_encode X i
  -- stage 1: input copies
  obtain ⟨t1, ht1, hr1⟩ := CopyList.run (jc FullFront.zs) inList (startKC X) rfl inList_scr
  obtain ⟨hW1j, hW1r⟩ := in_apply X
  set W1 := CopyList.apply (startKC X) inList with hW1
  have hc1 : CopyList.cost (startKC X) inList = 2 * (X 0).length + 2 * (X 1).length +
      2 * (X 2).length + 10 := by
    rw [inList, cost3]
    · rfl
    all_goals simp [inCopy, mk3, jc, inC]
  -- stage 2: the segment-1 packet controller, lifted
  obtain ⟨tP, htP, vP, H, hrP, h0, h1, hpre, hz, h2, -⟩ :=
    packet_repack_run a b Δ g hg k word
  set T := Function.update H (FullFront.pk 2) (word.take D) with hT
  have hrP' := Paper2.HeaderJoin.liftG inJ (packetProgram a b Δ) W1 (FullFront.F0 X) T
    hW1j _ _ _ tP hrP
  set W2 := bank inJ W1 T with hW2
  -- stage 3: output copies
  have hW2out : ∀ i, W2 (outC i) = [] := by
    intro i
    rw [hW2, outC, bank_inJ_inr, hW1r]
    rfl
  have hW2zs : W2 (jc FullFront.zs) = [] := by
    rw [hW2, bank_inJ_jc, hT, Function.update_of_ne (by simp [FullFront.pk, FullFront.zs])]
    exact hz
  obtain ⟨t3, ht3, hr3⟩ := CopyList.run (jc FullFront.zs) outList W2 hW2zs outList_scr
  obtain ⟨hW3o, hW3r⟩ := out_apply W2 hW2out
  set W3 := CopyList.apply W2 outList with hW3
  have hTpk : ∀ i, T (FullFront.pk i) = Y i := update_pk H g k word D h0 h1
  have hc3 : CopyList.cost W2 outList = 2 * (Y 0).length + 2 * (Y 1).length +
      2 * (Y 2).length + 10 := by
    rw [outList, cost3]
    · simp only [outCopy_src, hW2, bank_inJ_jc, hTpk]
    all_goals simp [outCopy, mk3, jc, outC]
  -- stage 4: clear everything except the outputs
  set L := n + packetPerStep a b Δ * packetBd a b Δ g k word
    with hL
  have hgrow : ∀ x : FullFront.JF, (T x).length ≤ L := by
    intro x
    have hg' := packet_growth a b Δ
      (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel (FullFront.fullStart a b Δ))),
        ((FullFront.fullCtl,
          (((SamplerParameterJoin.startControl, (false, false)), (none, ())), ((), none))),
          ((none : Option Bool), (none : Option Bool))),
        FullFront.F0 (FullFront.X0 g k word)⟩) tP x
    rw [hrP] at hg'
    have hF0 : (FullFront.F0 X x).length ≤ n := by
      rcases x with y | y | y | i | z
      · simp [FullFront.F0]
      · simp [FullFront.F0]
      · simp [FullFront.F0]
      · exact hXn i
      · simp [FullFront.F0]
    have hmul := Nat.mul_le_mul_left (packetPerStep a b Δ) htP
    change (T x).length ≤ (FullFront.F0 X x).length + _ at hg'
    have hpb : FullFront.fullBd a b Δ g k word +
        FrontPreparedCut.prepBd g.vertices (FullFront.pV g) (FullFront.sV g)
          (FullFront.q1V g) (FullFront.q2V g) (FullFront.wV g)
          (FullFront.QV a b Δ g) k
          (FrontPreparedCut.frontMX a b Δ g k)
          (FrontPreparedCut.frontMY a b Δ g k) word + 1 +
        (word.length + 2 * (word.take (FrontPreparedCut.frontD a b Δ g k)).length + 5) + 1 =
        packetBd a b Δ g k word := rfl
    rw [hpb] at hmul
    omega
  have hLcells : ∀ j, (W3 (clearCells j)).length ≤ L := by
    intro j
    unfold clearCells
    split
    · rw [hW3r _ (fun i => by simp [jc, outC]), hW2, bank_inJ_jc]
      exact hgrow _
    · rw [hW3r _ (fun i => by simp [inC, outC]), hW2, inC, bank_inJ_inr, hW1r]
      simp only [startKC]
      exact (hXn _).trans (by omega)
  obtain ⟨t4, ht4, v4, hr4⟩ := ClearAll.all_run clearCells clearCells_inj L W3 hLcells none
  have hfin : ClearAll.clearFrom clearCells 0 W3 = exitKC Y := by
    rw [clearFrom_eq]
    funext z
    rcases z with x | i | i
    · rfl
    · simp only [exitKC]
      rw [hW3o, hW2, bank_inJ_jc, hTpk]
    · rfl
  rw [hfin] at hr4
  -- sequencing
  obtain ⟨u34, hu34, hr34⟩ := BitMachineRawSequence.runs
    (CopyList.program outList) (ClearAll.prog clearCells)
    (CopyList.first outList) (⟨0, by omega⟩ : Fin (nJ + 3 + 1))
    (CopyList.initialControl outList) (CopyList.initialControl outList)
    (none : Option Bool) v4 W2 W3 (exitKC Y) t3 t4 hr3 hr4
  obtain ⟨u24, hu24, hr24⟩ := BitMachineRawSequence.runs
    (liftedPacket a b Δ) tailProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (FullFront.fullStart a b Δ)))
    (BitMachineRawSequence.leftLabel (CopyList.first outList))
    (packetCtl0 a b Δ) vP
    (CopyList.initialControl outList, (none : Option Bool)) (CopyList.initialControl outList, v4)
    W1 W2 (exitKC Y) tP u34 hrP' hr34
  obtain ⟨u, hu, hr⟩ := BitMachineRawSequence.runs
    (CopyList.program inList) (midProgram a b Δ)
    (CopyList.first inList)
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (FullFront.fullStart a b Δ))))
    (CopyList.initialControl inList) (CopyList.initialControl inList)
    (packetCtl0 a b Δ, (CopyList.initialControl outList, (none : Option Bool)))
    (packetCtl0 a b Δ, (CopyList.initialControl outList, v4))
    (startKC X) W1 (exitKC Y) t1 u24 hr1 hr24
  refine ⟨u, ?_, _, hr⟩
  have hE0 : (EncodedGraph.encode g).length ≤ n := hXn 0
  have hE1 : (List.replicate k true).length ≤ n := hXn 1
  have hE2 : word.length ≤ n := hXn 2
  have hYn : ∀ i, (Y i).length ≤ n := by
    rw [hYdef]
    exact len_triple_take _ _ _ D n hE0 hE1 hE2
  have hY0 := hYn 0
  have hY1 := hYn 1
  have hY2 := hYn 2
  have hX0 : (X 0).length ≤ n := hE0
  have hX1 : (X 1).length ≤ n := hE1
  have hX2 : (X 2).length ≤ n := hE2
  rw [hc1] at ht1
  rw [hc3] at ht3
  have ht4' : t4 ≤ clearBd a b Δ n (packetBd a b Δ g k word) := ht4
  have hmono : tP ≤ packetBd a b Δ g k word := htP
  have key : u ≤ cutBdN a b Δ n (packetBd a b Δ g k word) := by
    unfold cutBdN
    omega
  exact key

#print axioms cut_local_run

end

end Paper2.ABridge
