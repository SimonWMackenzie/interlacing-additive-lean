import Paper2.CappedTicketStatus

namespace Paper2.TicketStatus

open Turing
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineComposition


def fullProgram := BitMachineRawSequence.program TicketWordScratch.drawLift program Label.first
  (TicketWordScratch.drawInitial, ()) (none : Option Bool)

theorem compose (S T U : Fin 10 → List Bool) (acc finalAcc : List Bool)
    (ta te : Nat) (flag : Bool)
    (ha : ((advance CappedLoop.Cleanup.readyProgram)^[ta])
      (⟨some TicketWordScratch.drawStart, TicketWordScratch.drawInitial, S⟩ : TM2.Cfg (fun _ : Fin 10 => Bool)
        TicketWordScratch.DrawLabel TicketWordScratch.DrawControl) = ⟨none, TicketWordScratch.drawInitial, T⟩)
    (he : ((advance program)^[te]) (cfg (some .first) none T acc) =
      cfg none (some flag) U finalAcc) :
    ∃ t ≤ ta + te + 1,
      ((advance fullProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel (.inl TicketWordScratch.drawStart)),
          ((TicketWordScratch.drawInitial, ()), none), bank S acc⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, ((TicketWordScratch.drawInitial, ()), some flag), bank U finalAcc⟩ := by
  have hh : (((advance CappedLoop.Cleanup.readyProgram)^[ta])
      (⟨some TicketWordScratch.drawStart, TicketWordScratch.drawInitial, S⟩ : TM2.Cfg (fun _ : Fin 10 => Bool)
        TicketWordScratch.DrawLabel TicketWordScratch.DrawControl)).l = none := by rw [ha]
  obtain ⟨td, htd, hd⟩ := BitMachineSubroutine.lift_outputs
    CappedLoop.Cleanup.readyProgram TicketWordScratch.drawLift none (by intro l; rfl)
    () (fun _ : Fin 1 => acc)
    (⟨some TicketWordScratch.drawStart, TicketWordScratch.drawInitial, S⟩ : TM2.Cfg (fun _ : Fin 10 => Bool)
      TicketWordScratch.DrawLabel TicketWordScratch.DrawControl) ta hh
  have hdraw : ((advance TicketWordScratch.drawLift)^[td])
      (⟨some (.inl TicketWordScratch.drawStart), (TicketWordScratch.drawInitial, ()), bank S acc⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, (TicketWordScratch.drawInitial, ()), bank T acc⟩ := by
    simpa [BitMachineComposition.liftCfg, bank, ha] using hd
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs TicketWordScratch.drawLift program
    (.inl TicketWordScratch.drawStart) Label.first (TicketWordScratch.drawInitial, ()) (TicketWordScratch.drawInitial, ())
    none (some flag) (bank S acc) (bank T acc) (bank U finalAcc)
    td te hdraw he
  exact ⟨t, by omega, hr⟩

theorem erase_result (suffix out : List Bool) :
    Function.update (CappedLoop.Comparator.bank suffix [] [] [] [] [] [] [] [] out)
      9 [] = TicketWordScratch.emptyBank suffix := by
  funext k
  fin_cases k <;> simp [CappedLoop.Comparator.bank, TicketWordScratch.emptyBank, Function.update]

/-- The flag is an actual finite control value, not a semantic witness that
must be reconstructed from the accumulator. -/
theorem source_ticket (D B R N : Nat) (hD : 0 < D)
    (hB : Nat.clog 2 D ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1)) (acc : List Bool) :
    ∃ t ≤ TicketWordScratch.drawBound D B R + D + 2,
      ((advance fullProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel (.inl TicketWordScratch.drawStart)),
          ((TicketWordScratch.drawInitial, ()), none), bank (TicketWordScratch.sourceInitialBank D B R N tape) acc⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, ((TicketWordScratch.drawInitial, ()),
          some (CappedSampler.runWideBits D B R hB tape.1).isSome),
          bank (TicketWordScratch.emptyBank (RecursiveSamplingTape.writeTape B R N tape.2).val)
            (match CappedSampler.runWideBits D B R hB tape.1 with
              | none => acc
              | some q => (RecursiveLabelCodecScratch.finCodec D).encode q ++ acc)⟩ := by
  obtain ⟨ta, out, hta, hra, hout⟩ :=
    CappedLoop.Cleanup.source_draw_ready D B R N hD hB tape
  let T := CappedLoop.Comparator.bank
    (RecursiveSamplingTape.writeTape B R N tape.2).val [] [] [] [] [] [] [] [] out
  cases hc : CappedSampler.runWideBits D B R hB tape.1 with
  | none =>
      have ho : out = [] := by simpa [hc] using hout
      have h9 : T 9 = [] := by simp [T, CappedLoop.Comparator.bank, ho]
      obtain ⟨t, ht, hx⟩ := compose (TicketWordScratch.sourceInitialBank D B R N tape) T T
        acc acc ta 1 false hra (abort T acc h9)
      refine ⟨t, ?_, ?_⟩
      · simp [TicketWordScratch.drawBound, ho] at hta ⊢
        omega
      · simpa [T, ho, TicketWordScratch.emptyBank, hc] using hx
  | some q =>
      have ho : out = true :: List.replicate q.val true := by simpa [hc] using hout
      have h9 : T 9 = true :: List.replicate q.val true := by
        simp [T, CappedLoop.Comparator.bank, ho]
      obtain ⟨t, ht, hx⟩ := compose (TicketWordScratch.sourceInitialBank D B R N tape) T
        (Function.update T 9 []) acc (List.replicate q.val true ++ [false] ++ acc)
        ta (q.val+2) true hra (success q.val T acc h9)
      refine ⟨t, ?_, ?_⟩
      · have hq := q.isLt
        simp [TicketWordScratch.drawBound, ho] at hta ⊢
        omega
      · simpa [T, erase_result, hc, RecursiveLabelCodecScratch.finCodec] using hx

#print axioms source_ticket

end Paper2.TicketStatus
