import EthInapproximability.CurrentPaper.SourceClausePrefixGateReady

/-! A charged physical clear of every non-core cell in the shared prefix bank. -/

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixSharedClear

open Turing BitMachineEncoding
open scoped Classical

abbrev Stack := PrefixSharedCore.Stack

noncomputable instance : Fintype Stack := Fintype.ofFinite _
noncomputable instance : DecidableEq Stack := Classical.decEq _

noncomputable def keep : Finset Stack :=
  Finset.univ.image (Sum.inl : PrefixSharedCore.Core → Stack)

theorem mem_keep (x : Stack) :
    x ∈ keep ↔ ∃ i : PrefixSharedCore.Core, x = .inl i := by
  simp [keep, Finset.mem_image, eq_comm]

noncomputable def program := SourceClauseClearExcept.program keep

noncomputable def cost (S : Stack → List Bool) : ℕ :=
  (∑ i : Fin (SourceClauseClearExcept.workCount keep),
    (S (SourceClauseClearExcept.workBank keep i)).length) +
    SourceClauseClearExcept.workCount keep + 2

theorem run (S : Stack → List Bool) :
    ((advance program)^[cost S])
      (⟨some (.clear 0), ((), none), S⟩ :
        TM2.Cfg (fun _ : Stack => Bool)
          (SourceClauseClearExcept.Label
            (SourceClauseClearExcept.workCount keep))
          (Unit × Option Bool)) =
      ⟨none, ((), none), SourceClauseClearExcept.result keep S⟩ := by
  exact SourceClauseClearExcept.run keep S

theorem result_eq_blank (S : Stack → List Bool)
    (n v : ℕ) (saved output count : List Bool)
    (hcore : ∀ i : PrefixSharedCore.Core,
      S (.inl i) = PrefixGateReady.coreWords n v saved output count i) :
    SourceClauseClearExcept.result keep S =
      PrefixGateReady.blank n v saved output count := by
  funext x
  rcases x with i | z
  · simp [SourceClauseClearExcept.result, mem_keep, PrefixGateReady.blank,
      hcore i]
  · simp [SourceClauseClearExcept.result, mem_keep, PrefixGateReady.blank]

end EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixSharedClear
