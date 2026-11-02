import EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalAll
import EthInapproximability.CurrentPaper.SourceCSPRowCodecConverse

/-!
# All-input row-loop acceptance agrees with the source codec

The physical parser/range predicate is identified with recursive decoding
by the canonical source codec. This is a semantic equivalence, not a machine
oracle: both directions use the separately proved literal parser-bank bridge.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalCodec

open Turing BitMachineEncoding

def ReadRowsGood (n a q : Nat) : Nat → List Bool → Prop
  | 0, input => input = []
  | m + 1, input =>
      ∃ row : SourceCSPCodec.Row n a q,
        ∃ suffix : List Bool,
          SourceCSPCodec.readRow n a q input = some (row, suffix) ∧
          ReadRowsGood n a q m suffix

theorem goodRows_iff_readRowsGood (n a q m : Nat) (input : List Bool)
    (hn : 0 < n) :
    SourceCSPRowLoopTotalAll.GoodRows q (a ^ q)
      (List.replicate (n - 1) true) m input ↔
      ReadRowsGood n a q m input := by
  induction m generalizing input with
  | zero => rfl
  | succ m ih =>
      constructor
      · rintro ⟨bank, rest, hparse, htable, hrange, htail⟩
        have hrange' : ∀ j : Fin q,
            EncodedCommunication.bitsValue (bank j) < n := by
          intro j
          have h := hrange j
          simp only [List.length_replicate] at h
          omega
        obtain ⟨row, hrow⟩ := SourceCSPRowCodecParser.parse_range_to_readRow
          input bank rest hparse hrange' htable
        exact ⟨row, rest.drop (a ^ q), hrow, (ih _).mp htail⟩
      · rintro ⟨row, suffix, hread, htail⟩
        obtain ⟨rest, hparse, htable, hsuffix, hrange⟩ :=
          SourceCSPRowCodecConverse.readRow_to_parse input suffix row hread
        refine ⟨(fun j => (row.1 j).val.bits), rest, hparse, htable, ?_, ?_⟩
        · intro j
          have h := hrange j
          simp only [List.length_replicate]
          omega
        · rw [hsuffix]
          exact (ih _).mpr htail

theorem readRowsGood_iff_readFn (n a q m : Nat) (input : List Bool) :
    ReadRowsGood n a q m input ↔
      ∃ rows : Fin m → SourceCSPCodec.Row n a q,
        SourceCSPCodec.readFn (SourceCSPCodec.readRow n a q) m input =
          some (rows, []) := by
  induction m generalizing input with
  | zero =>
      constructor
      · intro h
        refine ⟨Fin.elim0, ?_⟩
        change input = [] at h
        simp [SourceCSPCodec.readFn, h]
      · rintro ⟨rows, h⟩
        have h' : input = [] := by
          have hs : (Fin.elim0, input) = (rows, []) := by
            exact Option.some.inj (by simpa only [SourceCSPCodec.readFn] using h)
          exact congrArg Prod.snd hs
        exact h'
  | succ m ih =>
      constructor
      · rintro ⟨row, suffix, hrow, htail⟩
        obtain ⟨rows, hrows⟩ := (ih suffix).mp htail
        refine ⟨Fin.cases row rows, ?_⟩
        simp [SourceCSPCodec.readFn, hrow, hrows]
      · rintro ⟨rows, h⟩
        cases hrow : SourceCSPCodec.readRow n a q input with
        | none => simp [SourceCSPCodec.readFn, hrow] at h
        | some pair =>
            obtain ⟨row, suffix⟩ := pair
            cases htail : SourceCSPCodec.readFn
                (SourceCSPCodec.readRow n a q) m suffix with
            | none => simp [SourceCSPCodec.readFn, hrow, htail] at h
            | some pair' =>
                obtain ⟨tailRows, finalSuffix⟩ := pair'
                have hfinal : finalSuffix = [] := by
                  have hs : (Fin.cases row tailRows, finalSuffix) = (rows, []) := by
                    exact Option.some.inj
                      (by simpa [SourceCSPCodec.readFn, hrow, htail] using h)
                  exact congrArg Prod.snd hs
                subst finalSuffix
                exact ⟨row, suffix, hrow,
                  (ih suffix).mpr ⟨tailRows, htail⟩⟩

/-- For any raw suffix, the corrected physical controller accepts exactly when
the source codec reads the requested number of rows and reaches literal EOF. -/
theorem rows_total_codec (n a q m : Nat) (input : List Bool)
    (E : Fin 4 → List Bool) (hn : 0 < n)
    (hcount : E 0 = List.replicate m true)
    (hcap : E 1 = List.replicate (n - 1) true)
    (hscratch : E 3 = []) :
    ∃ t S v b,
      t ≤ m * SourceCSPRowLoopTotalUniformOne.oneBound q (a ^ q)
        input (List.replicate (n - 1) true) + 3 ∧
      ((advance (SourceCSPRowLoopTotalController.program q (a ^ q)))^[t])
        (⟨some (SourceCSPRowLoopController.adminLabel .check),
          SourceCSPRowLoopController.initialControl,
          Sum.elim (SourceCSPRowQueryFrame.initial input
            (List.replicate (n - 1) true)) E⟩ :
            SourceCSPRowLoopController.Config q (a ^ q)) =
        ⟨none, (v, some b), S⟩ ∧
      (b = true ↔ ∃ rows : Fin m → SourceCSPCodec.Row n a q,
        SourceCSPCodec.readFn (SourceCSPCodec.readRow n a q) m input =
          some (rows, [])) := by
  obtain ⟨t, S, v, b, ht, hrun, hsem⟩ :=
    SourceCSPRowLoopTotalAll.rows_total q (a ^ q) m input
      (List.replicate (n - 1) true) E hcount hcap hscratch
  exact ⟨t, S, v, b, ht, hrun,
    hsem.trans ((goodRows_iff_readRowsGood n a q m input hn).trans
      (readRowsGood_iff_readFn n a q m input))⟩

end EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalCodec
