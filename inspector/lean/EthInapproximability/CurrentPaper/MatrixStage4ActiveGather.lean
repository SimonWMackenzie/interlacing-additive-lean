import EthInapproximability.CurrentPaper.MatrixStage4ActiveCount

/-!
# Gathering the strict-predecessor graph bits

The existing generic stride-gather machine reads the first `i` entries of
the selected vector column from its literal row-major serialization. Those
bits, in reverse order, are the input to the variable-bin unary rank counter.
-/

namespace EthInapproximability.CurrentPaper.MatrixStage4ActiveGather

open MatrixStrideGather MatrixMaterialization MatrixSourceColumnMachine

theorem word_prefix_eq_before {n q : ℕ}
    (vectors : Fin n → Fin q → Bool) (i : Fin n) (α : Fin q) :
    word q α.val i.val (rowMajor vectors) = beforeColumn vectors i α := by
  rw [word_eq_ofFn]
  apply congrArg List.ofFn
  funext j
  let r : Fin n := ⟨j.val, j.isLt.trans i.isLt⟩
  have h := rowMajor_entry vectors r α
  simpa only [r, Nat.add_comm α.val] using
    congrArg (fun z : Option Bool => z.getD false) h

theorem gather_before_run {n q : ℕ}
    (vectors : Fin n → Fin q → Bool) (i : Fin n) (α : Fin q) :
    ∃ t ≤ i.val *
        (3*(α.val+i.val*q)+3*(n*q)+2*q+12)+1,
      run t (cfg (some (.inr .test)) false
        (List.replicate α.val true) (rowMajor vectors) []
        (List.replicate i.val true) (List.replicate q true) []) =
      cfg none false (List.replicate (α.val+i.val*q) true)
        (rowMajor vectors) (beforeColumn vectors i α).reverse
        [] (List.replicate q true) [] := by
  obtain ⟨t,ht,he⟩ := gather_run i.val α.val q false
    (rowMajor vectors) []
  refine ⟨t, ?_, ?_⟩
  · simpa only [rowMajor_length] using ht
  · simpa only [word_prefix_eq_before, List.append_nil] using he

end EthInapproximability.CurrentPaper.MatrixStage4ActiveGather
