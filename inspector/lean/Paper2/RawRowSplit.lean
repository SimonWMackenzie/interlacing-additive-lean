import Paper2.OuterLocate
import Paper2.FullSupport

/-! Segment 2, item (2), template case: splitting the captured raw-row word
`rawRowCodec.encode (.inl (p, z)) = [false] ++ unary p ++ templateWord`
into the unary outer index `p` (fresh cell) and the template word, by one
fixed program (pop the sum bit, read one terminated unary field).
Generic in the ambient bank. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.RawRowSplit

noncomputable section

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open GeneratorCode GeneratorSerialization GeneratorSource
open RecursiveLabelCodecScratch RecursiveEntries

variable {J : Type*} [DecidableEq J]

def readU (src cnt : J) : Unit → TM2.Stmt (fun _ : J => Bool) Unit (Option Bool) :=
  fun _ => pop src (fun _ b => b)
    (branch (fun v => v.getD false) (push cnt (fun _ => true) (goto (fun _ => ()))) halt)

theorem readU_run (src cnt : J) (hne : src ≠ cnt) :
    ∀ (j : ℕ) (rest C : List Bool) (S : J → List Bool) (v : Option Bool),
      S src = List.replicate j true ++ false :: rest → S cnt = C →
      ((advance (readU src cnt))^[j + 1]) (⟨some (), v, S⟩ :
          TM2.Cfg (fun _ : J => Bool) Unit (Option Bool)) =
        ⟨none, some false,
          Function.update (Function.update S src rest) cnt (List.replicate j true ++ C)⟩
  | 0, rest, C, S, v, hS, hC => by
      rw [Function.iterate_one]
      have hc : Function.update S src rest cnt = C := by
        rw [Function.update_of_ne (Ne.symm hne), hC]
      have hS' : S src = false :: rest := by simpa using hS
      simp only [List.replicate_zero, List.nil_append]
      rw [← hc, Function.update_eq_self]
      simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, readU, hS']
  | j + 1, rest, C, S, v, hS, hC => by
      rw [Function.iterate_succ_apply]
      have h1 : Function.update S src (List.replicate j true ++ false :: rest) cnt = S cnt :=
        Function.update_of_ne (Ne.symm hne) _ _
      have e : advance (readU src cnt) (⟨some (), v, S⟩ :
          TM2.Cfg (fun _ : J => Bool) Unit (Option Bool)) =
          ⟨some (), some true, Function.update (Function.update S src
            (List.replicate j true ++ false :: rest)) cnt (true :: S cnt)⟩ := by
        have hS' : S src = true :: (List.replicate j true ++ false :: rest) := by
          rw [hS, List.replicate_succ, List.cons_append]
        simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, readU, hS', h1]
      rw [e, readU_run src cnt hne j rest (true :: C) _ (some true)
        (by rw [Function.update_of_ne hne, Function.update_self])
        (by rw [Function.update_self, hC])]
      congr 1
      funext k
      by_cases h1 : k = cnt
      · subst h1
        simp only [Function.update_self]
        rw [List.replicate_succ', List.append_assoc, List.singleton_append]
      · rw [Function.update_of_ne h1, Function.update_of_ne h1]
        by_cases h2 : k = src
        · subst h2
          simp only [Function.update_self]
        · rw [Function.update_of_ne h2, Function.update_of_ne h1, Function.update_of_ne h2,
            Function.update_of_ne h2]

def splitProgram (src cnt : J) :=
  BitMachineRawSequence.program (OuterLocate.popBits src 1) (readU src cnt) () ()
    (none : Option Bool)

theorem split_run (src cnt : J) (hne : src ≠ cnt) (pp : ℕ) (T : List Bool)
    (W : J → List Bool) (hW : W src = [false] ++ (List.replicate pp true ++ false :: T))
    (hc : W cnt = []) :
    ∃ t ≤ 2 + (pp + 1) + 1,
      ((advance (splitProgram src cnt))^[t])
        (⟨some (BitMachineRawSequence.leftLabel ⟨0, by omega⟩), ((), none), W⟩ :
          TM2.Cfg (fun _ : J => Bool) _ _) =
        ⟨none, ((), some false),
          Function.update (Function.update W src T) cnt (List.replicate pp true)⟩ := by
  have p1 := OuterLocate.popBits_run src 1 0 (by omega) [false] rfl _ W hW
  have p2 := readU_run src cnt hne pp T [] (Function.update W src
    (List.replicate pp true ++ false :: T)) none (by rw [Function.update_self])
    (by rw [Function.update_of_ne (Ne.symm hne), hc])
  rw [Function.update_idem, List.append_nil] at p2
  obtain ⟨t, ht, q⟩ := BitMachineRawSequence.runs (OuterLocate.popBits src 1) (readU src cnt)
    ⟨0, by omega⟩ () () () none (some false) _ _ _ _ _ p1 p2
  exact ⟨t, by omega, q⟩

/-- Actual template-case raw row: the split leaves the encoded template and
the unary outer index. -/
theorem split_actual {n p s q₁ q₂ w Q : ℕ} (k : ℕ) (pp : Fin s)
    (z : SourceMatrix.Template q₁ q₂
      (Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k))
    (src cnt : J) (hne : src ≠ cnt) (W : J → List Bool)
    (hW : W src = (rawRowCodec q₁ q₂ s (defaultCarrierCodecs n p s q₁ q₂ w Q k).1
      (defaultItemCodec n s)).encode (.inl (pp, z)))
    (hc : W cnt = []) :
    ∃ t ≤ 2 + (pp.val + 1) + 1,
      ((advance (splitProgram src cnt))^[t])
        (⟨some (BitMachineRawSequence.leftLabel ⟨0, by omega⟩), ((), none), W⟩ :
          TM2.Cfg (fun _ : J => Bool) _ _) =
        ⟨none, ((), some false),
          Function.update (Function.update W src
            ((piCodec (prodCodec (finCodec q₁) (defaultCarrierCodecs n p s q₁ q₂ w Q k).1) q₂).encode z))
            cnt (List.replicate pp.val true)⟩ := by
  apply split_run src cnt hne pp.val _ W _ hc
  rw [hW]
  change false :: ((finCodec s).encode pp ++ _) = _
  simp [finCodec]

end

#print axioms readU_run
#print axioms split_run
#print axioms split_actual

end Paper2.RawRowSplit
