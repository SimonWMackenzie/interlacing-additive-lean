import CurrentAdditive.V39WRawFields

/-! Literal final output and preservation of every original raw cell by the
embedded encoded table printer. -/
namespace CurrentAdditive.V39WRaw
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
open Paper2 EthInapproximability.CurrentPaper
open BitMachineEncoding BitMachineStackEmbedding EncodedCommunication
open V39WEntry
local instance : DecidableEq Stack := Classical.decEq _
local instance : DecidableEq (HeaderJoin.JH Kw) := Classical.decEq _

def finished (W : Stack → List Bool) (S : Fin 14 → List Bool)
    (WB : V39WTablePrepare.WriterStack → List Bool)
    (m thr : Nat) (payload : List Bool) : Stack → List Bool :=
  bank printerSlots W (V39WEncodedTable.final S WB m m thr payload)

theorem finished_word (W : Stack → List Bool) (S : Fin 14 → List Bool)
    (WB : V39WTablePrepare.WriterStack → List Bool) (m thr : Nat) (payload : List Bool) :
    finished W S WB m thr payload outputPort=encodeInstance ⟨m,m,thr,payload⟩ :=
  V39WEncodedTable.embedded_final_word printerSlots W S WB m m thr payload

theorem header_threshold (WB : V39WTablePrepare.WriterStack → List Bool)
    (m thr : Nat) (payload : List Bool) :
    V39WHeaderExact.finalBank WB m m thr payload [] HeaderJoin.thrM=
      List.replicate thr true := by
  rw [V39WHeaderExact.finalBank,bank_outside HeaderJoin.ιH _ _ _ (by
    rintro ⟨x,hx⟩
    change HeaderJoin.ιHf x=HeaderJoin.thrM at hx
    unfold HeaderJoin.ιHf at hx
    split_ifs at hx <;> simp [HeaderJoin.wOut,HeaderJoin.thrM,HeaderJoin.hb] at hx)]
  rw [CopyAll.done_off _ _ _ (by
    intro j; fin_cases j <;> simp [HeaderJoin.cpH,HeaderJoin.cp3,HeaderJoin.hb,HeaderJoin.thrM]) 3]
  rfl

theorem finished_source (W : Stack → List Bool) (S : Fin 14 → List Bool)
    (WB : V39WTablePrepare.WriterStack → List Bool) (m thr : Nat) (payload : List Bool)
    (i : Fin 14) : finished W S WB m thr payload (sourceSlots i)=S i := by
  change bank printerSlots W _ (printerSlots (.inl i)) = _
  rw [bank_at]
  rfl

theorem finished_threshold (W : Stack → List Bool) (S : Fin 14 → List Bool)
    (WB : V39WTablePrepare.WriterStack → List Bool) (m thr : Nat) (payload : List Bool) :
    finished W S WB m thr payload (.inl rawThreshold)=List.replicate thr true := by
  change bank printerSlots W _ (printerSlots V39WEncodedTable.thresholdPort) = _
  rw [bank_at]
  exact header_threshold WB m thr payload

theorem finished_raw (W : Stack → List Bool) (S : Fin 14 → List Bool)
    (WB : V39WTablePrepare.WriterStack → List Bool) (m thr : Nat) (payload : List Bool)
    (hS : ∀ i, W (sourceSlots i)=S i)
    (hB : W (.inl rawThreshold)=List.replicate thr true) (r : Raw) :
    finished W S WB m thr payload (.inl r)=W (.inl r) := by
  by_cases h : ∃ x, printerSlots x=Sum.inl r
  · obtain ⟨x,hx⟩ := h
    rw [← hx]
    rcases x with i | ((w | (a | f)) | p)
    · exact (finished_source W S WB m thr payload i).trans (hS i).symm
    · cases hx
    · cases hx
    · fin_cases f
      · exact (finished_threshold W S WB m thr payload).trans hB.symm
      · cases hx
    · cases hx
  · exact bank_outside printerSlots W _ _ h

#print axioms finished_word
#print axioms finished_threshold
#print axioms finished_raw
end
end CurrentAdditive.V39WRaw
