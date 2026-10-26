import CurrentAdditive.CanonicalPhysicalEntryLift
import EthInapproximability.CurrentPaper.MatrixTableWriter

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalTable

open Paper2.YaoLookup Paper2.YaoSourceCodec Paper2.UnaryFieldListParserScratch
open EthInapproximability.CurrentPaper

abbrev CanonicalCell := MatrixTableWriter.CellStack 60

/-- Shared ABI for the writer callback. Writer cells `inr 0,1,2` are row,
column, answer; static cells 0..6 hold the seven prepared constants/data
and static cells 7..53 are workspace. -/
def canonicalWriterBank {v e : ℕ} (b t d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v) : Fin 60 → List Bool :=
  fun k => if h : k.val < 7 then
    (![List.replicate ((2 ^ b) ^ (2 ^ (t - 1))) true,
       List.replicate ((2 ^ d) ^ 2) true,
       List.replicate (2 ^ b) true,
       tokens (List.ofFn (flatten edges)),
       List.replicate (2 ^ t * 2 ^ t) true,
       packedFieldBits d modulus (2 ^ b * (2 ^ t * 2 ^ t + 1)),
       List.replicate (2 ^ b * (2 ^ t * 2 ^ t + 1)) true] :
       Fin 7 → List Bool) ⟨k.val, h⟩
  else []

def canonicalIndexPlace : Fin 14 ↪ CanonicalCell :=
  ⟨![.inr 0, .inr 1, .inl 0, .inl 1, .inl 2,
      .inl 13, .inl 14, .inl 15, .inl 7, .inl 8,
      .inl 9, .inl 10, .inl 11, .inl 16], by decide⟩

def canonicalCoordPlace : Fin 40 ↪ CanonicalCell :=
  ⟨fun k => if h : k.val < 8 then
      (![.inl 8, .inl 9, .inl 2, .inl 10,
         .inl 7, .inl 3, .inl 4, .inl 12] : Fin 8 → CanonicalCell)
        ⟨k.val, h⟩
      else .inl ⟨k.val + 9, by omega⟩,
    by decide⟩

def canonicalLookupPlace : MatrixTableLookup.Stack ↪ CanonicalCell :=
  ⟨![.inl 11, .inl 6, .inl 12, .inl 49, .inl 50,
      .inl 51, .inl 5, .inr 2, .inl 52, .inl 53], by decide⟩

def canonicalReady {v e : ℕ} (b t d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (x y : ℕ) : CanonicalCell → List Bool :=
  Sum.elim (canonicalWriterBank b t d modulus edges)
    (![List.replicate x true, List.replicate y true, []] : Fin 3 → List Bool)

theorem canonicalReady_eq_cellCfg {v e : ℕ} (b t d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (x y : ℕ) {L V : Type*} (l : Option L) (control : V) :
    (MatrixTableWriter.cellCfg l control
      (canonicalWriterBank b t d modulus edges) x y []).stk =
      canonicalReady b t d modulus edges x y := rfl

/-- The writer's ordinary row/column cells and the prepared static bank
satisfy the exact initial conditions of the inherited physical decoder. -/
theorem canonicalReady_index_inputs {v e : ℕ} (b t d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (x y : ℕ) :
    let S := canonicalReady b t d modulus edges x y
    S (canonicalIndexPlace 0) = List.replicate x true ∧
    S (canonicalIndexPlace 1) = List.replicate y true ∧
    S (canonicalIndexPlace 2) =
      List.replicate ((2 ^ b) ^ (2 ^ (t - 1))) true ∧
    S (canonicalIndexPlace 3) = List.replicate ((2 ^ d) ^ 2) true ∧
    S (canonicalIndexPlace 4) = List.replicate (2 ^ b) true ∧
    (∀ k : Fin 14, 5 ≤ k.val → S (canonicalIndexPlace k) = []) := by
  dsimp only
  refine ⟨by simp [canonicalReady, canonicalIndexPlace],
    by simp [canonicalReady, canonicalIndexPlace],
    by simp [canonicalReady, canonicalIndexPlace, canonicalWriterBank],
    by simp [canonicalReady, canonicalIndexPlace, canonicalWriterBank],
    by simp [canonicalReady, canonicalIndexPlace, canonicalWriterBank], ?_⟩
  intro k hk
  fin_cases k <;> simp_all [canonicalReady, canonicalIndexPlace,
    canonicalWriterBank]

theorem canonicalWriterBank_scratch {v e : ℕ} (b t d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (k : Fin 60) (hk : 7 ≤ k.val) :
    canonicalWriterBank b t d modulus edges k = [] := by
  simp [canonicalWriterBank, show ¬ k.val < 7 by omega]

#print axioms canonicalWriterBank_scratch
#print axioms canonicalReady_index_inputs

end CurrentAdditive.FiniteFieldConstructor.CanonicalTable
