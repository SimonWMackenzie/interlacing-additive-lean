import CurrentAdditive.QuarticInstallFront

/-! Run the final eleven physical copies from the generic table-machine exit. -/

namespace Paper2.CurrentAdditive.QuarticNumericFront.Install27

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

theorem runCopies (g : EncodedGraph.Graph) (hg : g.Valid)
    (k : ℕ) (word : List Bool)
    (FLold : LProducer.LK → List Bool) (FQold : QProducer.QK → List Bool)
    (FLnew : LProducer.LK → List Bool) (FQnew : QProducer.QK → List Bool)
    (FT : TMFront.TK → List Bool) (FM : TMFront.MK → List Bool)
    (n p s q₁ q₂ w Q mX mY : ℕ)
    (hv : ∀ i, TM27.afterTM g hg k word FLold FQold FLnew FQnew FT FM
      (copies i 0) =
        ![List.replicate q₂ true, List.replicate q₁ true,
          List.replicate s true, List.replicate n true,
          List.replicate w true, List.replicate Q true,
          List.replicate p true, List.replicate k true,
          List.replicate mX true, List.replicate mY true, word] i) :
    ∃ t ≤ 11 * (2 * (q₂+q₁+s+n+w+Q+p+k+mX+mY+word.length) + 3) + 1,
      ∃ vc,
      ((advance (CopyAll.prog copies))^[t])
        (⟨some (.inl ⟨0, by omega⟩), none,
          TM27.afterTM g hg k word FLold FQold FLnew FQnew FT FM⟩ :
          TM2.Cfg (fun _ : Stack => Bool) (CopyAll.Lab 11) (Option Bool)) =
        ⟨none, vc, afterInstall g hg k word FLold FQold FLnew FQnew FT FM
          n p s q₁ q₂ w Q mX mY⟩ := by
  obtain ⟨t, ht, vc, hr⟩ := CopyAll.all_run copies src_ne_dst scratch_ne_dst
    dst_injective (TM27.afterTM g hg k word FLold FQold FLnew FQnew FT FM)
    (fun _ => rfl) (q₂+q₁+s+n+w+Q+p+k+mX+mY+word.length)
    (fun i => by
      rw [hv i]
      fin_cases i <;> simp <;> omega) none
  refine ⟨t, ht, vc, ?_⟩
  rw [doneC g hg k word FLold FQold FLnew FQnew FT FM
    n p s q₁ q₂ w Q mX mY hv] at hr
  exact hr

end
end Paper2.CurrentAdditive.QuarticNumericFront.Install27

#print axioms Paper2.CurrentAdditive.QuarticNumericFront.Install27.runCopies
