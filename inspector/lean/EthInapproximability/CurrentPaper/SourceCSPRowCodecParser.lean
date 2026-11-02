import EthInapproximability.CurrentPaper.SourceCSPRowControllerTotal
import EthInapproximability.CurrentPaper.SourceCSPRowCodecReadFn

/-!
# Canonical-source factorization of the actual row query parser

For a fresh future bank, every successful physical query parse factors the
original bitstream into canonical natural-number fields and the exact unread
suffix. The proof follows the controller's recursive parser, not a decoder
oracle.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPRowCodecParser

open EncodedCommunication SourceCSPRowController

def Post {q : Nat} (i : Nat) (input : List Bool) (bank : Bank q) :
    Option (Bank q × List Bool) → Prop
  | none => True
  | some (finalBank, rest) =>
      input = queriesFrom i (fun j => bitsValue (finalBank j)) ++ rest ∧
      (∀ j : Fin q, j.val < i → finalBank j = bank j) ∧
      (∀ j : Fin q, i ≤ j.val →
        finalBank j = (bitsValue (finalBank j)).bits)

theorem parse_sound {q : Nat} (i : Nat) (input : List Bool)
    (bank : Bank q)
    (hfuture : ∀ j : Fin q, i ≤ j.val → bank j = []) :
    Post i input bank (readQueriesFrom i input bank) := by
  revert hfuture
  fun_induction readQueriesFrom i input bank with
  | case1 i input bank hi ih =>
      intro hfuture
      cases hread : readNat input with
      | none => trivial
      | some pair =>
          obtain ⟨n, rest⟩ := pair
          let k : Fin q := ⟨i, hi⟩
          let nextBank := Function.update bank k (n.bits ++ bank k)
          have hnext : ∀ j : Fin q, i + 1 ≤ j.val → nextBank j = [] := by
            intro j hj
            have hne : j ≠ k := by
              intro he
              have hv := congrArg Fin.val he
              simp only [k] at hv
              omega
            dsimp only [nextBank]
            rw [Function.update_of_ne hne]
            exact hfuture j (by omega)
          have hrec := ih n rest hnext
          cases htail : readQueriesFrom (i + 1) rest nextBank with
          | none =>
              change Post i input bank
                (readQueriesFrom (i + 1) rest nextBank)
              rw [htail]
              trivial
          | some p =>
              obtain ⟨finalBank, suffix⟩ := p
              rw [htail] at hrec
              change Post (i + 1) rest nextBank
                (some (finalBank, suffix)) at hrec
              obtain ⟨hrest, hpast, hcanon⟩ := hrec
              have hiBank : finalBank k = n.bits := by
                rw [hpast k (by simp [k])]
                dsimp only [nextBank]
                rw [Function.update_self,
                  hfuture k (by simp [k]), List.append_nil]
              have hvalue : bitsValue (finalBank k) = n := by
                rw [hiBank, bitsValue_bits]
              have hsource : input =
                  queriesFrom i (fun j => bitsValue (finalBank j)) ++ suffix := by
                have hn := readNat_sound hread
                calc
                  input = natField n ++ rest := hn.symm
                  _ = natField n ++
                      (queriesFrom (i + 1)
                        (fun j => bitsValue (finalBank j)) ++ suffix) := by rw [hrest]
                  _ = queriesFrom i (fun j => bitsValue (finalBank j)) ++
                        suffix := by
                    have hq : queriesFrom i (fun j => bitsValue (finalBank j)) =
                        natField (bitsValue (finalBank k)) ++
                          queriesFrom (i + 1)
                            (fun j => bitsValue (finalBank j)) := by
                      rw [queriesFrom.eq_1, dif_pos hi]
                    rw [hq, hvalue, List.append_assoc]
              have hpast' : ∀ j : Fin q, j.val < i → finalBank j = bank j := by
                intro j hj
                rw [hpast j (by omega)]
                dsimp only [nextBank]
                rw [Function.update_of_ne (by
                  intro he
                  have hv := congrArg Fin.val he
                  simp only [k] at hv
                  omega)]
              have hcanon' : ∀ j : Fin q, i ≤ j.val →
                  finalBank j = (bitsValue (finalBank j)).bits := by
                intro j hj
                by_cases hji : j.val = i
                · have he : j = k := Fin.ext hji
                  subst j
                  simp [hiBank]
                · exact hcanon j (by omega)
              change Post i input bank
                (readQueriesFrom (i + 1) rest nextBank)
              rw [htail]
              exact ⟨hsource, hpast', hcanon'⟩
  | case2 i input bank hi =>
      intro _
      simpa [readQueriesFrom.eq_1, hi, Post, queriesFrom] using
        (show input = input ∧
          (∀ j : Fin q, j.val < i → bank j = bank j) ∧
          (∀ j : Fin q, i ≤ j.val →
            bank j = (bitsValue (bank j)).bits) from by
            refine ⟨rfl, ?_, ?_⟩
            · intro j _; rfl
            · intro j hj; exact False.elim (hi (by omega)))

theorem parse_zero_sound {q : Nat} (input : List Bool)
    (finalBank : Bank q) (rest : List Bool)
    (hparse : readQueriesFrom (q := q) 0 input (fun _ => []) =
      some (finalBank, rest)) :
    input = queriesFrom 0 (fun j => bitsValue (finalBank j)) ++ rest ∧
      (∀ j : Fin q, finalBank j = (bitsValue (finalBank j)).bits) := by
  have hp := parse_sound 0 input (fun _ : Fin q => []) (by
    intro j _; rfl)
  rw [hparse] at hp
  exact ⟨hp.1, fun j => hp.2.2 j (by omega)⟩

/-- A successful physical query parse with all coordinates in range and a
sufficient remaining truth-table suffix is a successful codec `readRow`.
This direction is what prevents an accepting raw controller from accepting
a noncanonical or out-of-range source row. -/
theorem parse_range_to_readRow {n a q : Nat} (input : List Bool)
    (bank : Bank q) (rest : List Bool)
    (hparse : readQueriesFrom (q := q) 0 input (fun _ => []) =
      some (bank, rest))
    (hrange : ∀ j : Fin q, bitsValue (bank j) < n)
    (htable : a ^ q ≤ rest.length) :
    ∃ row : SourceCSPCodec.Row n a q,
      SourceCSPCodec.readRow n a q input =
        some (row, rest.drop (a ^ q)) := by
  obtain ⟨hsource, hcanonical⟩ := parse_zero_sound input bank rest hparse
  let query : Fin q → Fin n := fun j => ⟨bitsValue (bank j), hrange j⟩
  obtain ⟨table, htableRead⟩ :=
    SourceCSPRowCodecReadFn.read_bits_total (a ^ q) rest htable
  have hqueryFields : queriesFrom 0 (fun j => bitsValue (bank j)) =
      SourceCSPCodec.fnFields (fun v : Fin n => natField v.val) query := by
    rw [queriesFrom_eq_drop]
    simp only [List.drop_zero, SourceCSPCodec.fnFields, query]
  have hqueryRead : SourceCSPCodec.readFn (SourceCSPCodec.readIndex n) q input =
      some (query, rest) := by
    rw [hsource, hqueryFields]
    exact SourceCSPCodec.readFn_append
      (fun v : Fin n => natField v.val)
      (SourceCSPCodec.readIndex n)
      (SourceCSPCodec.readIndex_append n) q query rest
  refine ⟨(query, table), ?_⟩
  simp only [SourceCSPCodec.readRow, hqueryRead,
    htableRead, Bind.bind, Option.bind, pure]

end EthInapproximability.CurrentPaper.SourceCSPRowCodecParser
