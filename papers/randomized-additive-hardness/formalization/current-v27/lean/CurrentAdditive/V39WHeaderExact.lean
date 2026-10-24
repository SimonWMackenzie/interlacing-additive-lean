import Paper2.HeaderJoinX
import Paper2.YaoFrameHdr

/-! Exact complete-bank endpoint for the unchanged physical header join.
The only change to the older interface is retaining the established exact
header cleanup theorem instead of naming its work bank existentially. -/
namespace CurrentAdditive.V39WHeaderExact
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
open Paper2 Turing
open EthInapproximability.CurrentPaper
open BitMachineEncoding BitMachineStackEmbedding EncodedCommunication
open Paper2.HeaderJoin
variable {K : Nat}
local instance : DecidableEq (JH K) := Classical.decEq _

def clock (rows cols thr : Nat) : Nat :=
  3*(2*(rows+cols+thr)+3)+1 +
    (UnaryBinaryEncoding.coefficient*(rows+1)^2+
      UnaryBinaryEncoding.coefficient*(cols+1)^2+
      UnaryBinaryEncoding.coefficient*(thr+1)^2+
      (2*(natField rows++natField cols++natField thr).length+2)+3)+1

def finalBank (WB : WS K → List Bool) (rows cols thr : Nat) (table suffix : List Bool) :
    JH K → List Bool :=
  bank ιH (CopyAll.done (cpH (K:=K)) 3 (hjIn WB thr))
    (Paper2.YaoFrame.Hout rows cols thr table suffix)

theorem physical_header (WB : WS K → List Bool) (rows cols thr : Nat) (table suffix : List Bool)
    (hr : WB (.inr .rows)=List.replicate rows true)
    (hc : WB (.inr .cols)=List.replicate cols true)
    (ho : WB (.inr .output)=table++suffix) :
    ∃ t ≤ clock rows cols thr,
      ((advance (hjProg K))^[t])
        (⟨some (BitMachineRawSequence.leftLabel (.inl (0:Fin 4) : CopyAll.Lab 3)),
          ((none:Option Bool),HeaderA.progCtl),hjIn WB thr⟩ :
          TM2.Cfg (fun _ : JH K => Bool) _ _) =
        ⟨none,((none:Option Bool),HeaderA.progCtl),finalBank WB rows cols thr table suffix⟩ := by
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
  obtain ⟨t2, ht2, r2⟩ := Paper2.YaoFrame.header_run_exact rows cols thr table suffix
  have r2L := liftG (ιH (K := K)) HeaderA.prog B1 _ _ hS _ _ _ _ r2
  obtain ⟨u, hu, hrun⟩ := BitMachineRawSequence.runs (CopyAll.prog (cpH (K := K))) (hdrL (K := K))
    (.inl ⟨0, by omega⟩) HeaderA.progStart none v1 HeaderA.progCtl HeaderA.progCtl
    W0 B1 _ t1 t2 r1 r2L
  exact ⟨u,by unfold clock; omega,by simpa only [hjProg,finalBank,hB1,hW0] using hrun⟩

theorem final_out (WB : WS K → List Bool) (rows cols thr : Nat) (table suffix : List Bool) :
    finalBank WB rows cols thr table suffix wOut =
      natField rows++natField cols++natField thr++table++suffix := by
  change bank ιH _ (Paper2.YaoFrame.Hout rows cols thr table suffix) (ιH HeaderA.outH)=_
  rw [bank_at]
  simp [Paper2.YaoFrame.Hout]

theorem final_writer (WB : WS K → List Bool) (rows cols thr : Nat) (table suffix : List Bool)
    (a : WS K) (ha : a≠.inr .output) :
    finalBank WB rows cols thr table suffix (.inl a)=WB a := by
  rw [finalBank,bank_outside ιH _ _ (.inl a) (by
    rintro ⟨x,hx⟩
    change ιHf x=_ at hx
    unfold ιHf at hx
    split_ifs at hx
    · exact ha (by simpa [wOut] using hx.symm)
    · simp [hb] at hx),CopyAll.done_off _ _ _ (by
      intro j; fin_cases j <;> simp [cpH,cp3,hb]) 3]
  rfl

#print axioms physical_header
#print axioms final_out
#print axioms final_writer
end
end CurrentAdditive.V39WHeaderExact
