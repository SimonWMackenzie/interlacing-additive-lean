import EthInapproximability.CurrentPaper.SourceGenericFirstRowJoin
import EthInapproximability.CurrentPaper.SourceCSPEntryBound

namespace EthInapproximability.CurrentPaper.SourceGenericRowClearSuffix

open Turing BitMachineEncoding
open scoped Classical

/-- Clear the validator-private counter with real machine steps, then run the
generic remaining-row controller. This starts after the actual first-row
callback, so its saved and count words already contain that row. -/
theorem remaining_after_first_with_clear {n m a q H : Nat}
    (rows : Fin m → SourceCSPCodec.Row n a q) (hq : 0 < q)
    (L : Nat) (hn : 0 < n) (hm : 0 < m)
    (hword : ∀ i : Fin m, ∀ j : Fin q,
      ((rows i).1 j).val.bits.length ≤ L)
    (hcapL : n - 1 ≤ L)
    (hnH : n ≤ H) (hmH : m ≤ H)
    (ht : 1 + a ^ q ≤ H) (hL : L ≤ H)
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (saved output count : List Bool)
    (hS : ∀ x, (S x).length ≤ H)
    (hrow : ∀ x, (row x).length ≤ H)
    (hsaved : saved.length ≤ H)
    (houtput : output.length ≤ H)
    (hcountWords : count.length ≤ H)
    (hheader : S SourceCSPHeaderRowBridge.count =
      List.replicate m true)
    (hcap : S SourceCSPHeaderRowBridge.capSource =
      List.replicate (n - 1) true)
    (hsource : row (.inr 0) = SourceCSPCodec.fnFields
      SourceCSPCodec.rowFields
        (SourceGenericAllRowLoop.remainingRows rows 0 (m - 1)
          (by omega)))
    (hsourceLen : (row (.inr 0)).length ≤ H) :
    let S' := Function.update S SourceCSPHeaderRowBridge.loopCount []
    let clauses := SourceGenericAllRowLoop.suffixClauses rows hq 0
      (m - 1) (by omega)
    ∃ (tclear tloop : Nat)
      (lastRow : SourceCSPRowQueryFrame.Stack q → List Bool),
      tclear ≤ H + 2 ∧
      tloop ≤ SourceGenericAllRowLoopClock.loopCoefficient a q * (H + 1) ^ 9 ∧
      ((advance (SourceCSPEntryBound.clearLoopProgram q))^[tclear])
        (⟨some 0, ((), none),
          SourceCSPNextRowBridge.callbackBank S row n 0
            saved output count⟩ :
          TM2.Cfg (fun _ : SourceGenericAllRowLoop.Stack q => Bool)
            (Fin 2) (Unit × Option Bool)) =
        ⟨none, ((), none),
          SourceCSPNextRowBridge.callbackBank S' row n 0
            saved output count⟩ ∧
      ((advance (SourceGenericAllRowLoop.program (a := a) hq))^[tloop])
        (⟨some (.copy .scan), .copy none,
          SourceCSPNextRowBridge.callbackBank S' row n 0
            saved output count⟩ :
          TM2.Cfg (fun _ : SourceGenericAllRowLoop.Stack q => Bool)
            (SourceGenericAllRowLoop.Label (a := a) hq)
            (SourceGenericAllRowLoop.Control (a := a) hq)) =
        ⟨none, .done true,
          SourceCSPNextRowBridge.callbackBank
            (SourceGenericAllRowLoop.withRemaining S' 0)
            lastRow n (m - 1)
            ((EncodedCNF.clauseFields clauses).reverse ++ saved)
            output (List.replicate clauses.length true ++ count)⟩ ∧
      lastRow (.inr 0) = [] := by
  let S' := Function.update S SourceCSPHeaderRowBridge.loopCount []
  have hS' : ∀ x, (S' x).length ≤ H := by
    intro x
    by_cases hx : x = SourceCSPHeaderRowBridge.loopCount
    · subst x
      simp [S']
    · simpa [S', Function.update_of_ne hx] using hS x
  have hheader' : S' SourceCSPHeaderRowBridge.count =
      List.replicate m true := by
    simpa [S', SourceCSPHeaderRowBridge.count,
      SourceCSPHeaderRowBridge.loopCount] using hheader
  have hcap' : S' SourceCSPHeaderRowBridge.capSource =
      List.replicate (n - 1) true := by
    simpa [S', SourceCSPHeaderRowBridge.capSource,
      SourceCSPHeaderRowBridge.loopCount] using hcap
  have hzero : S' SourceCSPHeaderRowBridge.loopCount = [] := by
    simp [S']
  obtain ⟨tl, lastRow, htl, hrun, hlast⟩ :=
    SourceGenericAllRowLoopClock.all_remaining_after_first_polynomial
      rows hq L hn hm hword hcapL hnH hmH ht hL
      S' row saved output count hS' hrow hsaved houtput
      hcountWords hheader' hzero hcap' hsource hsourceLen
  refine ⟨(S SourceCSPHeaderRowBridge.loopCount).length + 2,
    tl, lastRow, ?_, htl, ?_, hrun, hlast⟩
  · have hc := hS SourceCSPHeaderRowBridge.loopCount
    omega
  · exact SourceCSPEntryBound.clear_callback_bank_run
      S row saved output count

#print axioms remaining_after_first_with_clear

end EthInapproximability.CurrentPaper.SourceGenericRowClearSuffix
