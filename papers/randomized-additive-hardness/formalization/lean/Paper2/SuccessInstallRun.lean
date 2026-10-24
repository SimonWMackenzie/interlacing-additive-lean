import Paper2.SuccessInstall

/-! Unit 3, segments (5) and (6): the install run and the whole success branch as ONE fixed
program `SuccessInstall.fullProg = install ; SuccessRun.succProg`, started from the admitted
success start bank beside the parameter-free writer bank `SuccessInstall.preJH0`. -/

set_option maxHeartbeats 64000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.SuccessInstall

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open GeneratorCode GeneratorSerialization GeneratorSource GeneratorFullSample
open RecursiveSamplingProgram RecursiveSamplingLaws RecursiveLabelCodecScratch
open RecursiveEntries RecursiveSampling RecursiveRequestCodeShape
open SourceProfileParameters SourceRecursiveNoSampling TotalFiniteConstructorScratch
open Paper2.HeaderJoin (JH hjIn hjProg wOut thrM scrH)
open Paper2.SuccessXfer (OS JT wAux xLmax)
open Paper2.SuccessRun (preJH auxPre hCtl succProg)

/-- Explicit clock of the install program. -/
def instBd (s q₁ Q p w k : ℕ) : ℕ := 8 * (2 * (s + q₁ + Q + p + w + k) + 3) + 1 + 1 + 1

variable {p s q₁ q₂ w Q : ℕ} [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q] [NeZero s]

theorem src_val (n k mX mY : ℕ) (word : List Bool) (i : Fin 9) :
    SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word (srcC i) =
      DrawCoefficients.initialBank s q₁ q₂ w Q p k mX mY ⟨i.val, by omega⟩ :=
  SamplerParameterJoin.nrSrc_value n p s q₁ q₂ w Q k mX mY word i

theorem dst_val (g : EncodedGraph.Graph) (r K thr : ℕ) (output : List Bool) :
    let W := preJH (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r K thr output
    W (dstsI 0) = List.replicate s true ∧ W (dstsI 1) = true :: List.replicate s true ∧
      W (dstsI 2) = List.replicate q₁ true ∧ W (dstsI 3) = List.replicate s true ∧
      W (dstsI 4) = List.replicate Q true ∧ W (dstsI 5) = List.replicate p true ∧
      W (dstsI 6) = List.replicate w true ∧ W (dstsI 7) = List.replicate K true := by
  intro W
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (change auxPre (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r K
        (WEntry.eqv.symm (WEntry.eqv _)) = _
     rw [Equiv.symm_apply_apply]
     rfl)

theorem install_run (n k mX mY : ℕ) (word : List Bool) (g : EncodedGraph.Graph)
    (r thr : ℕ) (output : List Bool) :
    ∃ t ≤ instBd s q₁ Q p w k,
      ((advance install)^[t])
          (⟨some (BitMachineRawSequence.leftLabel (.inl ⟨0, by omega⟩)),
            ((none : Option Bool), (none : Option Bool)),
            Sum.elim (SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word)
              (Sum.elim (preJH0 g r thr output) (fun _ => []))⟩ :
            TM2.Cfg (fun _ : JT => Bool) _ _) =
        ⟨none, ((none : Option Bool), (none : Option Bool)),
          Sum.elim (SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word)
            (Sum.elim (preJH (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
              g r k thr output) (fun _ => []))⟩ := by
  let SB := SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word
  let W := preJH (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r k thr output
  let T0 : JT → List Bool := Sum.elim SB (Sum.elim (blankI W) (fun _ => []))
  have hT0 : Sum.elim SB (Sum.elim (preJH0 g r thr output) (fun _ => [])) = T0 := by
    rw [pre0_eq (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r k thr output]
  rw [hT0]
  have hs0 : SB (srcC 0) = List.replicate s true := by
    show SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word (srcC 0) = _
    rw [src_val]; rfl
  have hs1 : SB (srcC 1) = List.replicate q₁ true := by
    show SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word (srcC 1) = _
    rw [src_val]; rfl
  have hs3 : SB (srcC 3) = List.replicate w true := by
    show SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word (srcC 3) = _
    rw [src_val]; rfl
  have hs4 : SB (srcC 4) = List.replicate Q true := by
    show SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word (srcC 4) = _
    rw [src_val]; rfl
  have hs5 : SB (srcC 5) = List.replicate p true := by
    show SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word (srcC 5) = _
    rw [src_val]; rfl
  have hs6 : SB (srcC 6) = List.replicate k true := by
    show SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word (srcC 6) = _
    rw [src_val]; rfl
  have hv := dst_val (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r k thr output
  have hsd : ∀ i j, cpsI i 0 ≠ cpsI j 1 := by
    intro i j h
    rw [cpsI_src, cpsI_dst] at h
    cases h
  have hzd : ∀ i j, cpsI i 2 ≠ cpsI j 1 := by
    intro i j h
    rw [cpsI_scr, cpsI_dst] at h
    cases h
  have hdd : ∀ i j, cpsI i 1 = cpsI j 1 → i = j := by
    intro i j h
    rw [cpsI_dst, cpsI_dst] at h
    exact dstsI_inj i j (Sum.inl_injective (Sum.inr_injective h))
  have hz : ∀ i, T0 (cpsI i 2) = [] := fun i => rfl
  have hL : ∀ i, (T0 (cpsI i 0)).length ≤ s + q₁ + Q + p + w + k := by
    intro i
    rw [cpsI_src]
    change (SB (srcsI i)).length ≤ _
    fin_cases i
    · change (SB (srcC 0)).length ≤ _
      rw [hs0, List.length_replicate]; omega
    · change (SB (srcC 0)).length ≤ _
      rw [hs0, List.length_replicate]; omega
    · change (SB (srcC 1)).length ≤ _
      rw [hs1, List.length_replicate]; omega
    · change (SB (srcC 0)).length ≤ _
      rw [hs0, List.length_replicate]; omega
    · change (SB (srcC 4)).length ≤ _
      rw [hs4, List.length_replicate]; omega
    · change (SB (srcC 5)).length ≤ _
      rw [hs5, List.length_replicate]; omega
    · change (SB (srcC 3)).length ≤ _
      rw [hs3, List.length_replicate]; omega
    · change (SB (srcC 6)).length ≤ _
      rw [hs6, List.length_replicate]; omega
  obtain ⟨t, ht, v', hr⟩ := CopyAll.all_run cpsI hsd hzd hdd T0 hz
    (s + q₁ + Q + p + w + k) hL none
  have hp := push_run (CopyAll.done cpsI 8 T0) none
  have hdst : ∀ j : Fin 8, CopyAll.done cpsI 8 T0 (cpsI j 1) = SB (srcsI j) := by
    intro j
    rw [CopyAll.done_dst cpsI hdd T0 j, cpsI_src, cpsI_dst]
    change SB (srcsI j) ++ blankI W (dstsI j) = _
    rw [blankI_dst, List.append_nil]
  have hfin : Function.update (CopyAll.done cpsI 8 T0) myT
      (true :: CopyAll.done cpsI 8 T0 myT) = Sum.elim SB (Sum.elim W (fun _ => [])) := by
    funext x
    by_cases hx : x = myT
    · subst hx
      rw [Function.update_self]
      change true :: CopyAll.done cpsI 8 T0 (cpsI 1 1) = W (dstsI 1)
      rw [hdst 1]
      change true :: SB (srcC 0) = _
      rw [hs0]
      exact hv.2.1.symm
    · rw [Function.update_of_ne hx]
      by_cases hd : ∃ j, cpsI j 1 = x
      · obtain ⟨j, rfl⟩ := hd
        rw [hdst j, cpsI_dst]
        change SB (srcsI j) = W (dstsI j)
        fin_cases j
        · change SB (srcC 0) = _
          rw [hs0]; exact hv.1.symm
        · exact absurd rfl hx
        · change SB (srcC 1) = _
          rw [hs1]; exact hv.2.2.1.symm
        · change SB (srcC 0) = _
          rw [hs0]; exact hv.2.2.2.1.symm
        · change SB (srcC 4) = _
          rw [hs4]; exact hv.2.2.2.2.1.symm
        · change SB (srcC 5) = _
          rw [hs5]; exact hv.2.2.2.2.2.1.symm
        · change SB (srcC 3) = _
          rw [hs3]; exact hv.2.2.2.2.2.2.1.symm
        · change SB (srcC 6) = _
          rw [hs6]; exact hv.2.2.2.2.2.2.2.symm
      · rw [CopyAll.done_off cpsI T0 x (fun j h => hd ⟨j, h⟩)]
        rcases x with x | x | x
        · rfl
        · change blankI W x = W x
          apply blankI_off
          rintro ⟨i, hi⟩
          exact hd ⟨i, by rw [cpsI_dst, hi]⟩
        · rfl
  rw [hfin] at hp
  obtain ⟨u, hu, ru⟩ := BitMachineRawSequence.runs (CopyAll.prog cpsI) pushP
    (.inl ⟨0, by omega⟩) () (none : Option Bool) v' (none : Option Bool) (none : Option Bool)
    T0 (CopyAll.done cpsI 8 T0) (Sum.elim SB (Sum.elim W (fun _ => []))) t 1 hr hp
  refine ⟨u, ?_, ru⟩
  unfold instBd
  omega

end

#print axioms src_val
#print axioms dst_val
#print axioms install_run

end Paper2.SuccessInstall
