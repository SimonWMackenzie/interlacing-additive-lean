import CurrentAdditive.RatioCallbackPolynomial

set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 100
set_option maxRecDepth 10000

/-! A single polynomial bounds the complete concrete ratio scan in the length
of its prepared list packet. The accumulator never grows by successive
arithmetic: it is either retained or replaced by one quotient of a listed
pair. Header/unary-fuel initialization is a separate producer boundary. -/

namespace CurrentAdditive.RatioScanPolynomial

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open MinimumRatioCallbackLayout RatioCallbackPolynomial CurrentAdditive.GaussListContext
open EntryClockPoly

theorem step_length (best word : List Bool) (B : Nat)
    (hbest : best.length ≤ B)
    (hquot : 1+(RationalCanonicalCallback.quotientResult word).length ≤ B) :
    (MinimumRatioStepSpec.step best word).length ≤ B := by
  unfold MinimumRatioStepSpec.step
  split
  · dsimp only
    split
    · simp only [List.length_cons]; omega
    · split
      · simp only [List.length_cons]; omega
      · exact hbest
  · exact hbest

theorem fold_length (xs : List (List Bool)) (L : Nat)
    (hwords : ∀ w ∈ xs, w.length ≤ L) (best : List Bool)
    (hbest : best.length ≤ 1+quotientCap L) :
    (xs.foldl MinimumRatioStepSpec.step best).length ≤ 1+quotientCap L := by
  induction xs generalizing best with
  | nil => exact hbest
  | cons w xs ih =>
      have hw := hwords w (by simp)
      have hq := quotient_length w L hw
      apply ih
      · intro a ha; exact hwords a (by simp [ha])
      · exact step_length best w _ hbest (by omega)

theorem cut_lengths (xs pre : List (List Bool)) (word : List Bool)
    (tail : List (List Bool)) (hsplit : pre ++ word :: tail = xs) :
    let L := (SourceListEncoding.encode xs).length
    word.length ≤ L ∧
    (pre.foldl MinimumRatioStepSpec.step []).length ≤ 1+quotientCap L ∧
    (SourceListEncoding.fields tail).length ≤ L := by
  dsimp only
  have hf : (SourceListEncoding.fields xs).length ≤
      (SourceListEncoding.encode xs).length := by simp [SourceListEncoding.encode]
  constructor
  · exact (IndexedV2Clock.fields_item_length_le xs word
      (by rw [← hsplit]; simp)).trans hf
  constructor
  · apply fold_length
    · intro w hw
      exact (IndexedV2Clock.fields_item_length_le xs w
        (by rw [← hsplit]; simp [hw])).trans hf
    · simp
  · have he : SourceListEncoding.fields xs =
        SourceListEncoding.fields pre ++
          (EncodedCommunication.natField word.length ++ word ++
            SourceListEncoding.fields tail) := by
      rw [← hsplit,IndexedV2Clock.fields_append]
      rfl
    rw [he] at hf
    simp only [List.length_append] at hf
    omega

theorem cut_scratch (context : List Bool) (pre : List (List Bool))
    (word : List Bool) (tail : List (List Bool)) :
    (∑ i : Fin 10,
      (((RatioPhysicalFold.contract context).state pre word tail)
        (StatefulListScheduler.cleanBank i)).length) =
      (SourceListEncoding.fields tail).length+2*word.length := by
  have he (i : Fin 10) :
      (((RatioPhysicalFold.contract context).state pre word tail)
        (StatefulListScheduler.cleanBank i)).length =
      if i=0 then (SourceListEncoding.fields tail).length
      else if i=5 ∨ i=6 then word.length else 0 := by
    change (Function.update
      (RatioPhysicalFold.selected
        (SourceListEncoding.encode (pre ++ word :: tail))
        (SourceListEncoding.fields tail) word
        (pre.foldl MinimumRatioStepSpec.step []) context pre.length tail.length)
      (low 9) (MinimumRatioStepSpec.step
        (pre.foldl MinimumRatioStepSpec.step []) word)
      (StatefulListScheduler.cleanBank i)).length = _
    fin_cases i <;>
      simp [RatioPhysicalFold.selected,RatioPhysicalFold.boundary,
        RatioPhysicalFold.blank,StatefulListScheduler.initialBank,
        StatefulListScheduler.cleanBank,LargeContextListScheduler.cleanBank,
        Function.update_apply,Fin.ext_iff,low,Fin.ofNat]
  calc
    _ = ∑ i : Fin 10,
        ((if i=0 then (SourceListEncoding.fields tail).length else 0) +
          (if i=5 then word.length else 0) +
          (if i=6 then word.length else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [he]
      fin_cases i <;> simp
    _ = _ := by simp [Finset.sum_add_distrib]; omega

noncomputable def callbackCap (L : Nat) : Nat :=
  (1+17*growth)*itemCap L (1+quotientCap L)+20

theorem callbackCap_poly : PolyIn (fun n : Nat => n) callbackCap := by
  exact ((PolyIn.const (1+17*growth)).mul
    (itemCap_poly PolyIn.self
      ((PolyIn.const 1).add (quotientCap_poly PolyIn.self)))).add
        (PolyIn.const 20)

theorem cut_time_le (context : List Bool) (xs pre : List (List Bool))
    (word : List Bool) (tail : List (List Bool)) (hsplit : pre ++ word :: tail = xs) :
    (RatioPhysicalFold.contract context).time pre word tail ≤
      callbackCap (SourceListEncoding.encode xs).length := by
  have hl := cut_lengths xs pre word tail hsplit
  have ht := RatioPhysicalFold.cutTime_le context pre word tail
  have hc := callbackBound_le (RatioPhysicalFold.selectedCut context pre word tail)
    word (pre.foldl MinimumRatioStepSpec.step []) _ _
    (RatioPhysicalFold.selected_six _ _ _ _ _ _ _)
    (RatioPhysicalFold.selected_nine _ _ _ _ _ _ _)
    (RatioPhysicalFold.selected_scratch _ _ _ _ _ _ _)
    hl.1 hl.2.1
  exact ht.trans hc

/-- Absolute constants precede all list packets and caller contexts. This is
the complete concrete loop, including all item lookups, arithmetic, cleanup
and index increments, from its explicit prepared initial bank. -/
theorem uniform_scan_polynomial : ∃ C d : Nat,
    ∀ (xs : List (List Bool)) (context : List Bool),
    ∃ t ≤ C*((SourceListEncoding.encode xs).length+1)^d,
      ∃ v,
      ((advance RatioPhysicalFold.program)^[t])
        (⟨some (.inr (.inr .check)),
          StatefulListScheduler.getterControl MinimumRatioCallbackPhysical.control
            (CurrentAdditive.CylinderContextScanStep.copyControl ((),none)),
          RatioPhysicalFold.boundary (SourceListEncoding.encode xs) []
            context 0 xs.length⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,v,RatioPhysicalFold.boundary (SourceListEncoding.encode xs)
          (xs.foldl MinimumRatioStepSpec.step []) context xs.length 0⟩ := by
  classical
  obtain ⟨Q,dQ,hQ⟩ := callbackCap_poly
  have hpoly : PolyIn (fun n : Nat => n)
      (fun n => (n+1)*(50*(n+1)^3+Q*(n+1)^dQ+3*(n+1)^1+15)) := by
    have hn : PolyIn (fun n : Nat => n) (fun n => n+1) :=
      PolyIn.self.add (PolyIn.const 1)
    exact hn.mul (((((PolyIn.const 50).mul (hn.pow 3)).add
      ((PolyIn.const Q).mul (hn.pow dQ))).add
        ((PolyIn.const 3).mul (hn.pow 1))).add (PolyIn.const 15))
  obtain ⟨C,d,hC⟩ := hpoly
  refine ⟨C,d,?_⟩
  intro xs context
  have hcb : ∀ pre word tail, pre ++ word :: tail = xs →
      (RatioPhysicalFold.contract context).time pre word tail ≤
        Q*((SourceListEncoding.encode xs).length+1)^dQ := by
    intro pre word tail hsplit
    exact (cut_time_le context xs pre word tail hsplit).trans (hQ _)
  have hs : ∀ pre word tail, pre ++ word :: tail = xs →
      (∑ i : Fin 10,
        (((RatioPhysicalFold.contract context).state pre word tail)
          (StatefulListScheduler.cleanBank i)).length) ≤
        3*((SourceListEncoding.encode xs).length+1)^1 := by
    intro pre word tail hsplit
    have hl := cut_lengths xs pre word tail hsplit
    rw [cut_scratch]
    simp only [pow_one]
    omega
  obtain ⟨t,ht,v,hr⟩ := StatefulListScheduler.run_with_callback_polynomial_cap
    MinimumRatioCallbackPhysical.program MinimumRatioCallbackPhysical.start
    MinimumRatioCallbackPhysical.control MinimumRatioStepSpec.step [] context
    (RatioPhysicalFold.contract context) xs Q 3 dQ 1 hcb hs
    (StatefulListScheduler.getterControl MinimumRatioCallbackPhysical.control
      (CurrentAdditive.CylinderContextScanStep.copyControl ((),none)))
  have hn : xs.length ≤ (SourceListEncoding.encode xs).length :=
    (IndexedV2Clock.fields_length_ge_count xs).trans
      (by simp [SourceListEncoding.encode])
  have htot := ht.trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right hn 1))
  refine ⟨t,htot.trans (hC _),v,?_⟩
  simpa only [RatioPhysicalFold.program,StatefulListScheduler.run,
    RatioPhysicalFold.contract,RatioPhysicalFold.frame_initial] using hr

#print axioms uniform_scan_polynomial

end CurrentAdditive.RatioScanPolynomial
