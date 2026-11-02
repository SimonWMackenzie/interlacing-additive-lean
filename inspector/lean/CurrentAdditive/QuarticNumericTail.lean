import CurrentAdditive.QuarticInstallRun
import CurrentAdditive.QuarticTMValues
import CurrentAdditive.QuarticInstallValues

namespace Paper2.CurrentAdditive.QuarticNumericFront.Tail27

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open BitMachineRawSequence (leftLabel)

abbrev Stack := Packet27.Stack
def progBC := BitMachineRawSequence.program
  (CopyAll.prog TM27.copies) TM27.tmProgram TMFront.tmStart
  (none : Option Bool) TMFront.tmCtl
def ctlBC := ((none : Option Bool), TMFront.tmCtl)

theorem runBC (g : EncodedGraph.Graph) (hg : g.Valid)
    (k : ℕ) (word : List Bool) (p s q₂ w Q L : ℕ)
    (FLold : LProducer.LK → List Bool) (FQold : QProducer.QK → List Bool)
    (FLnew : LProducer.LK → List Bool) (FQnew : QProducer.QK → List Bool)
    (hv : ∀ i, Packet27.exitBank g hg k word FLold FQold FLnew FQnew
      (TM27.copies i 0) = List.replicate (![k,p,s,q₂,w,Q,L] i) true) :
    ∃ t ≤ (7 * (2 * (k+p+s+q₂+w+Q+L) + 3) + 1) +
      TMFront.tmBd k ![p,s,q₂,w,Q] L + 1,
      ∃ vc, ∃ FT : TMFront.TK → List Bool,
      ∃ FM : TMFront.MK → List Bool,
      ((advance progBC)^[t])
        (⟨some (leftLabel (.inl ⟨0, by omega⟩)), ctlBC,
          Packet27.exitBank g hg k word FLold FQold FLnew FQnew⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, ((none : Option Bool), vc),
          TM27.afterTM g hg k word FLold FQold FLnew FQnew FT FM⟩ ∧
      TMFront.TFacts k ![p,s,q₂,w,Q] FT ∧
      TMFront.MFacts (TMFront.thrVal k ![p,s,q₂,w,Q]) k L FM := by
  obtain ⟨tb, htb, vb, hb⟩ := TM27.runCopies g hg k word p s q₂ w Q L
    FLold FQold FLnew FQnew hv
  obtain ⟨tc, htc, vc, FT, FM, hc, hTF, hMF⟩ :=
    TM27.runTM g hg k word ![p,s,q₂,w,Q] L FLold FQold FLnew FQnew
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (CopyAll.prog TM27.copies) TM27.tmProgram
    (.inl ⟨0, by omega⟩) TMFront.tmStart
    (none : Option Bool) vb TMFront.tmCtl vc
    (Packet27.exitBank g hg k word FLold FQold FLnew FQnew)
    (TM27.afterCopies g hg k word ![p,s,q₂,w,Q] L
      FLold FQold FLnew FQnew)
    (TM27.afterTM g hg k word FLold FQold FLnew FQnew FT FM)
    tb tc hb hc
  refine ⟨t, by omega, vc, FT, FM, ?_, hTF, hMF⟩
  exact hr

end
end Paper2.CurrentAdditive.QuarticNumericFront.Tail27

#print axioms Paper2.CurrentAdditive.QuarticNumericFront.Tail27.runBC
