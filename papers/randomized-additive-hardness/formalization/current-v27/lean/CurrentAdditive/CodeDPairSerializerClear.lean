import EthInapproximability.CurrentPaper.BitMachineBankSerialize

/-! The two-word serializer consumes both input cells.  This strengthens
the inherited existential final-bank theorem for the exact two-field request
used in Code D, allowing a fixed input-size callback clock. -/

namespace CurrentAdditive.CodeDPairSerializerClear

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineBankSerialize
open Turing BitMachineEncoding EncodedCommunication

def words (x y : List Bool) : Bank 2 :=
  fun i => if i = 0 then x else y

def cleared (S : Bank 2) : Bank 2 :=
  Function.update (Function.update S 0 []) 1 []

theorem cleared_zero (S : Bank 2) : cleared S 0 = [] := by simp [cleared]
theorem cleared_one (S : Bank 2) : cleared S 1 = [] := by simp [cleared]

theorem serialized_words (x y : List Bool) :
    encode (List.ofFn (words x y)) = field x ++ field y := by
  simp [words, encode, List.ofFn_succ]

theorem emit_two (x y : List Bool) :
    run (x.length + 1 + (y.length + 1))
      (cfg (some (.emit 0)) none (words x y) [] [] []) =
      cfg (some (.emit 2)) none (cleared (words x y)) []
        ((field x ++ field y).reverse) [] := by
  have hx := emit_word (i := (0 : Fin 2)) none (words x y)
    x [] [] [] (by rfl)
  have hx' : run (x.length + 1)
      (cfg (some (.emit 0)) none (words x y) [] [] []) =
      cfg (some (.emit 1)) none
        (Function.update (words x y) 0 []) [] (field x).reverse [] := by
    simpa only [List.append_nil] using hx
  have hy : (Function.update (words x y) 0 []) 1 = y := by
    simp [words]
  have hy' := emit_word (i := (1 : Fin 2)) none
    (Function.update (words x y) 0 []) y [] (field x).reverse [] hy
  have hy'' : run (y.length + 1)
      (cfg (some (.emit 1)) none
        (Function.update (words x y) 0 []) [] (field x).reverse []) =
      cfg (some (.emit 2)) none (cleared (words x y)) []
        (field x ++ field y).reverse [] := by
    simpa [cleared, List.reverse_append] using hy'
  rw [run_add, hx']
  exact hy''

theorem serialize_cleared (x y : List Bool) :
    run (x.length + 1 + (y.length + 1) +
        ((field x ++ field y).length + 2))
      (cfg (some (.emit 0)) none (words x y) [] [] []) =
      cfg none none (cleared (words x y)) [] []
        (field x ++ field y) := by
  rw [run_add, emit_two]
  rw [show (field x ++ field y).length + 2 =
      1 + (((field x ++ field y).reverse).length + 1) by simp; omega]
  rw [run_add]
  have he := emit_end (cleared (words x y)) []
    ((field x ++ field y).reverse) []
  have he' : advance (program 2) (cfg (some (.emit 2)) none
      (cleared (words x y)) [] ((field x ++ field y).reverse) []) =
      cfg (some .finish) none (cleared (words x y)) []
        ((field x ++ field y).reverse) [] := by
    simpa using he
  change run (((field x ++ field y).reverse).length + 1)
    (advance (program 2) (cfg (some (.emit 2)) none
      (cleared (words x y)) []
      ((field x ++ field y).reverse) [])) = _
  rw [he']
  simpa using finish_run none (cleared (words x y)) []
    ((field x ++ field y).reverse) []

#print axioms serialize_cleared

end CurrentAdditive.CodeDPairSerializerClear
