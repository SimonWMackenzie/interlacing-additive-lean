import EthInapproximability.CurrentPaper.SourceOriginalListPacketizerStep
import EthInapproximability.CurrentPaper.SourceOriginalListPacketizerSemantics

/-! Binary-count traversal of every canonical sparsified branch. -/

namespace EthInapproximability.CurrentPaper.SourceOriginalListPacketizer

open Turing TM2.Stmt BitMachineEncoding EncodedCommunication

noncomputable section

def itemTimeWidth (n width : ℕ) (word : List Bool) : ℕ :=
  (4*width+5) + 1 +
  20*(word.length+1)*(word.length.bits.length+1) + 1 +
  SourceOriginalPacketFraming.totalTime n word +
  1 + (SourceOriginalPacketFraming.answer n word).length+1 +
  (word.length+1) + outerCleanupBound n word

theorem itemTimeBound_eq_width (n : ℕ) (q word : List Bool) :
    itemTimeBound n q word = itemTimeWidth n q.length word := rfl

def listWork (n width : ℕ) : List (List Bool) → ℕ
  | [] => 0
  | word :: words => itemTimeWidth n width word + listWork n width words

theorem canonical_list_run (n : ℕ) (words : List (List Bool))
    (suffix q acc : List Bool) (hvalue : bitsValue q = words.length) :
    ∃ t ≤ listWork n q.length words, ∃ q' : List Bool,
      run t (loopCfg (readyBank n
        (SourceListEncoding.fields words ++ suffix) q acc)) =
        loopCfg (readyBank n suffix q'
          ((joined n words).reverse ++ acc)) ∧
      bitsValue q' = 0 ∧ q'.length = q.length := by
  induction words generalizing q acc with
  | nil =>
      refine ⟨0, by simp [listWork], q, ?_, by simpa using hvalue, rfl⟩
      simp [SourceListEncoding.fields, joined, run]
  | cons word words ih =>
      have hpositive : bitsValue q ≠ 0 := by
        rw [hvalue]
        simp
      cases hdec : ProtocolBinaryCounter.subOne q with
      | none =>
          have hz := ProtocolBinaryCounter.subOne_spec q
          simp only [hdec] at hz
          exact (hpositive hz).elim
      | some q' =>
          have hspec := ProtocolBinaryCounter.subOne_spec q
          simp only [hdec] at hspec
          have hval' : bitsValue q' = words.length := by
            rw [hvalue] at hspec
            simp at hspec
            omega
          obtain ⟨a, ha, hstep⟩ := canonical_item_step n word
            (SourceListEncoding.fields words ++ suffix) q q' acc hdec
          obtain ⟨b, hb, q'', htail, hzero, hlen⟩ :=
            ih (q := q') (acc :=
              (SourceOriginalPacketFraming.answer n word).reverse ++ acc) hval'
          have hsource : SourceListEncoding.fields (word :: words) ++ suffix =
              natField word.length ++
                (word ++ (SourceListEncoding.fields words ++ suffix)) := by
            simp [SourceListEncoding.fields, List.append_assoc]
          have hacc : (joined n (word :: words)).reverse ++ acc =
              (joined n words).reverse ++
                ((SourceOriginalPacketFraming.answer n word).reverse ++ acc) := by
            simp [joined, SourceOriginalPacketFraming.answer,
              SourceOriginalListPacketizer.answer, List.reverse_append,
              List.append_assoc]
            rfl
          refine ⟨a+b, ?_, q'', ?_, hzero, by omega⟩
          · rw [listWork]
            rw [itemTimeBound_eq_width] at ha
            rw [hspec.2] at hb
            omega
          · rw [hsource, hacc]
            exact (run_add hstep b).trans htail

end

end EthInapproximability.CurrentPaper.SourceOriginalListPacketizer
