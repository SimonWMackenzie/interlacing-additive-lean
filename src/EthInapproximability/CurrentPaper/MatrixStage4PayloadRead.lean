import EthInapproximability.CurrentPaper.MatrixStage4TupleMachine
import EthInapproximability.CurrentPaper.MatrixTableLookup

/-!
# Source and graph-vector payload reads for variable-bin Stage--4

The table bits are literal row-major input stacks. These theorems invoke
the fixed address-and-read controller; neither the address nor answer is
supplied. Reading a whole matrix known only by an abstract accessor is not
claimed to be free: its concrete serialized bits are input data.
-/

namespace EthInapproximability.CurrentPaper.MatrixStage4PayloadRead

open MatrixMaterialization MatrixTableLookup

theorem payload_run {rows cols : ℕ} (f : Fin rows → Fin cols → Bool)
    (r : Fin rows) (c : Fin cols) (out : List Bool) :
    ∃ t ≤ 32*(r.val+cols+c.val+rows*cols+1)^2,
      run t (cfg (some start) initial
        (List.replicate r.val true) (List.replicate cols true)
        (List.replicate c.val true) [] (rowMajor f) out) =
      cfg none initial (List.replicate r.val true)
        (List.replicate cols true) (List.replicate c.val true)
        [] (rowMajor f) (f r c :: out) := by
  obtain ⟨t,ht,he⟩ := lookup_run r.val cols c.val (rowMajor f) out
  refine ⟨t, ?_, ?_⟩
  · simpa only [rowMajor_length] using ht
  · simpa only [rowMajor_entry, Option.getD_some] using he

theorem source_run {rx cy : ℕ} (R : Fin rx → Fin cy → Bool)
    (x : Fin rx) (y : Fin cy) (out : List Bool) :
    ∃ t ≤ 32*(x.val+cy+y.val+rx*cy+1)^2,
      run t (cfg (some start) initial
        (List.replicate x.val true) (List.replicate cy true)
        (List.replicate y.val true) [] (rowMajor R) out) =
      cfg none initial (List.replicate x.val true)
        (List.replicate cy true) (List.replicate y.val true)
        [] (rowMajor R) (R x y :: out) := payload_run R x y out

theorem vector_run {n q : ℕ} (vectors : Fin n → Fin q → Bool)
    (i : Fin n) (α : Fin q) (out : List Bool) :
    ∃ t ≤ 32*(i.val+q+α.val+n*q+1)^2,
      run t (cfg (some start) initial
        (List.replicate i.val true) (List.replicate q true)
        (List.replicate α.val true) [] (rowMajor vectors) out) =
      cfg none initial (List.replicate i.val true)
        (List.replicate q true) (List.replicate α.val true)
        [] (rowMajor vectors) (vectors i α :: out) := payload_run vectors i α out

end EthInapproximability.CurrentPaper.MatrixStage4PayloadRead
