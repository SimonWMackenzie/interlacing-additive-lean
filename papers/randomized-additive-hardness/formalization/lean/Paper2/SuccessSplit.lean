import Paper2.FetchIndexed

/-! The successful columns-first word splits into exactly `mY` column labels
followed by `mX` row labels, each a word its code can actually produce.
This is the input contract of `FetchIndexed.col_fetch` / `row_fetch`. -/

namespace Paper2.SuccessSplit

open GeneratorCode GeneratorSerialization
open RecursiveRequestCodeShape
open RecursiveSamplingProgram

theorem split_produced (col row : Code) (mX mY : Nat) (bytes : List Bool)
    (h : Produces (meaning (.append (copies mY col) (copies mX row))) bytes) :
    ∃ cs rs : List (List Bool), cs.length = mY ∧ rs.length = mX ∧
      (∀ c ∈ cs, Produces (meaning col) c) ∧ (∀ r ∈ rs, Produces (meaning row) r) ∧
      bytes = cs.flatten ++ rs.flatten := by
  obtain ⟨x, y, hx, hy, rfl⟩ := OutputSkipper.produces_append h
  obtain ⟨cs, hcl, hca, rfl⟩ := OutputSkipper.produces_copies col mY x hx
  obtain ⟨rs, hrl, hra, rfl⟩ := OutputSkipper.produces_copies row mX y hy
  exact ⟨cs, rs, hcl, hrl, hca, hra, rfl⟩

theorem split_success {M : Nat} (B R : Nat) (hMB : Nat.clog 2 M ≤ B) (N : Nat)
    (col row : Code) (mX mY : Nat)
    (hM : (meaning (.append (copies mY col) (copies mX row))).maxAlphabet ≤ M)
    (t : CappedSampler.Adaptive.Tape B R N) (bytes : List Bool)
    (hr : GeneratorCode.run B R hMB N
      (GeneratorStateSize.initialBounded (.append (copies mY col) (copies mX row)) hM) t =
        some bytes) :
    ∃ cs rs : List (List Bool), cs.length = mY ∧ rs.length = mX ∧
      (∀ c ∈ cs, Produces (meaning col) c) ∧ (∀ r ∈ rs, Produces (meaning row) r) ∧
      bytes = cs.flatten ++ rs.flatten :=
  split_produced col row mX mY bytes
    (OutputSkipper.run_produces B R hMB N _ hM t bytes hr)

#print axioms split_success

end Paper2.SuccessSplit
