import Paper2.HeaderJoin

/-! Unit 3, segment (6), reviewer note N3: `HeaderJoin.header_join` and
`header_join_outputBits` restated with the exit of the retained threshold cell `thrM`
(unchanged: `replicate thr true`) and of the copy scratch `scrH` (blank). Exact reuse of
the owner-7 program `HeaderJoin.hjProg`, bank `hjIn`, placements, `CopyAll`, and
`HeaderA.header_run`; the proof is the owner-7 proof with two added cell facts
(`thrM`, `scrH` are outside the header placement and are not copy destinations). The
header region (`HeaderA.HB` cells other than `outH`) remains named existential scratch. -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.HeaderJoinX

noncomputable section

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open EthInapproximability.CurrentPaper.EncodedCommunication
open Paper2.HeaderJoin

variable {K : ℕ}

theorem header_join_exact (WB : WS K → List Bool) (rows cols thr : ℕ) (table suffix : List Bool)
    (hr : WB (.inr .rows) = List.replicate rows true)
    (hc : WB (.inr .cols) = List.replicate cols true)
    (ho : WB (.inr .output) = table ++ suffix) :
    ∃ t ≤ 3 * (2 * (rows + cols + thr) + 3) + 1 +
        (UnaryBinaryEncoding.coefficient * (rows + 1) ^ 2 +
          UnaryBinaryEncoding.coefficient * (cols + 1) ^ 2 +
          UnaryBinaryEncoding.coefficient * (thr + 1) ^ 2 +
          (2 * (natField rows ++ natField cols ++ natField thr).length + 2) + 3) + 1,
      ∃ v, ∃ F : JH K → List Bool,
      ((advance (hjProg K))^[t])
        (⟨some (BitMachineRawSequence.leftLabel (.inl ⟨0, by omega⟩)),
          ((none : Option Bool), HeaderA.progCtl), hjIn WB thr⟩ :
          TM2.Cfg (fun _ : JH K => Bool) _ _) = ⟨none, v, F⟩ ∧
      F wOut = natField rows ++ natField cols ++ natField thr ++ table ++ suffix ∧
      (∀ a : WS K, a ≠ .inr .output → F (.inl a) = WB a) ∧
      F thrM = List.replicate thr true ∧ F scrH = [] := by
  set W0 := hjIn WB thr with hW0
  have hdd : ∀ i j, (cpH (K := K)) i 1 = (cpH (K := K)) j 1 → i = j := by
    intro i j h; fin_cases i <;> fin_cases j <;> simp_all [cpH, cp3, hb, HeaderA.fuel]
  obtain ⟨t1, ht1, v1, r1⟩ := CopyAll.all_run (cpH (K := K))
    (by intro i j; fin_cases i <;> fin_cases j <;> simp [cpH, cp3, wRows, wCols, thrM, hb])
    (by intro i j; fin_cases i <;> fin_cases j <;> simp [cpH, cp3, scrH, hb])
    hdd W0 (fun i => by fin_cases i <;> rfl) (rows + cols + thr)
    (by
      intro i; fin_cases i
      · show (WB (.inr .rows)).length ≤ _; rw [hr]; simp; omega
      · show (WB (.inr .cols)).length ≤ _; rw [hc]; simp; omega
      · show (List.replicate thr true).length ≤ _; simp)
    none
  set B1 := CopyAll.done (cpH (K := K)) 3 W0 with hB1
  have hS : ∀ x : HeaderA.HB, HeaderA.Hin rows cols thr table suffix x = B1 (ιH x) := by
    intro x
    rcases x with x | j
    · show [] = B1 (hb (.inl x))
      rw [hB1, CopyAll.done_off _ W0 _ (by
        intro j; fin_cases j <;> simp [cpH, cp3, hb, HeaderA.fuel]) 3]
      rfl
    · fin_cases j
      · show List.replicate rows true = B1 ((cpH (K := K)) 0 1)
        rw [hB1, CopyAll.done_dst _ hdd W0 0]
        show _ = WB (.inr .rows) ++ []
        rw [hr, List.append_nil]
      · show List.replicate cols true = B1 ((cpH (K := K)) 1 1)
        rw [hB1, CopyAll.done_dst _ hdd W0 1]
        show _ = WB (.inr .cols) ++ []
        rw [hc, List.append_nil]
      · show List.replicate thr true = B1 ((cpH (K := K)) 2 1)
        rw [hB1, CopyAll.done_dst _ hdd W0 2]
        exact (List.append_nil _).symm
      · show [] = B1 (hb (.inr 3))
        rw [hB1, CopyAll.done_off _ W0 _ (by
          intro j; fin_cases j <;> simp [cpH, cp3, hb, HeaderA.fuel]) 3]
        rfl
      · show [] = B1 (hb (.inr 4))
        rw [hB1, CopyAll.done_off _ W0 _ (by
          intro j; fin_cases j <;> simp [cpH, cp3, hb, HeaderA.fuel]) 3]
        rfl
      · show table ++ suffix = B1 wOut
        rw [hB1, CopyAll.done_off _ W0 _ (by
          intro j; fin_cases j <;> simp [cpH, cp3, hb, wOut]) 3]
        exact ho.symm
  obtain ⟨t2, ht2, v2, F, r2, hF⟩ := HeaderA.header_run rows cols thr table suffix
  have r2L := liftG (ιH (K := K)) HeaderA.prog B1 _ _ hS _ _ _ _ r2
  obtain ⟨u, hu, hrun⟩ := BitMachineRawSequence.runs (CopyAll.prog (cpH (K := K))) (hdrL (K := K))
    (.inl ⟨0, by omega⟩) HeaderA.progStart none v1 HeaderA.progCtl v2 W0 B1 _ t1 t2 r1 r2L
  have hout : ∀ z : JH K, (∀ x, ιHf x ≠ z) → bank ιH B1 F z = B1 z := fun z hz =>
    bank_outside ιH B1 F z (by rintro ⟨x, hx⟩; exact hz x hx)
  have hthr : bank ιH B1 F thrM = List.replicate thr true := by
    rw [hout thrM (by intro x; unfold ιHf; split_ifs <;> simp [wOut, hb, thrM]), hB1,
      CopyAll.done_off _ W0 _ (by intro j; fin_cases j <;> simp [cpH, cp3, hb, thrM]) 3]
    rfl
  have hscr : bank ιH B1 F scrH = [] := by
    rw [hout scrH (by intro x; unfold ιHf; split_ifs <;> simp [wOut, hb, scrH]), hB1,
      CopyAll.done_off _ W0 _ (by intro j; fin_cases j <;> simp [cpH, cp3, hb, scrH]) 3]
    rfl
  refine ⟨u, by omega, _, _, hrun, ?_, ?_, hthr, hscr⟩
  · show bank ιH B1 F (ιH HeaderA.outH) = _
    rw [bank_at, hF]
  · intro a ha
    rw [bank_outside ιH B1 F (.inl a) (by
      rintro ⟨x, hx⟩
      change ιHf x = _ at hx
      unfold ιHf at hx
      split_ifs at hx with h1
      · exact ha (by simpa [wOut] using hx.symm)
      · simp [hb] at hx), hB1,
      CopyAll.done_off _ W0 _ (by intro j; fin_cases j <;> simp [cpH, cp3, hb]) 3]
    rfl

theorem header_join_outputBits_exact {n m : ℕ} (hn : 0 < n) (edge : Fin m → Bool → Fin n) (Δ : ℕ)
    (γ : ℚ) (k : ℕ) (tp : (TotalFiniteConstructorScratch.select hn edge Δ γ k).Tape)
    (WB : WS K → List Bool) (suffix : List Bool)
    (hr : WB (.inr .rows) =
      List.replicate (EncodedSelectedOutput.selectedInstance hn edge Δ γ k tp).rows true)
    (hc : WB (.inr .cols) =
      List.replicate (EncodedSelectedOutput.selectedInstance hn edge Δ γ k tp).cols true)
    (ho : WB (.inr .output) =
      (EncodedSelectedOutput.selectedInstance hn edge Δ γ k tp).table ++ suffix) :
    let i := EncodedSelectedOutput.selectedInstance hn edge Δ γ k tp
    ∃ t, ∃ v, ∃ F : JH K → List Bool,
      ((advance (hjProg K))^[t])
        (⟨some (BitMachineRawSequence.leftLabel (.inl ⟨0, by omega⟩)),
          ((none : Option Bool), HeaderA.progCtl), hjIn WB i.threshold⟩ :
          TM2.Cfg (fun _ : JH K => Bool) _ _) = ⟨none, v, F⟩ ∧
      F wOut = EncodedSelectedOutput.outputBits hn edge Δ γ k tp ++ suffix ∧
      (∀ a : WS K, a ≠ .inr .output → F (.inl a) = WB a) ∧
      F thrM = List.replicate i.threshold true ∧ F scrH = [] := by
  intro i
  obtain ⟨t, -, v, F, hrun, hF, hfr, hthr, hscr⟩ :=
    header_join_exact WB i.rows i.cols i.threshold i.table suffix hr hc ho
  refine ⟨t, v, F, hrun, ?_, hfr, hthr, hscr⟩
  rw [hF]
  show _ = encodeInstance i ++ suffix
  simp [encodeInstance, List.append_assoc]

end

#print axioms header_join_exact
#print axioms header_join_outputBits_exact

end Paper2.HeaderJoinX
