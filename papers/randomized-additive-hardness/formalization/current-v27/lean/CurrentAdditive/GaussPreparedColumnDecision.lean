import EthInapproximability.CurrentPaper.BitMachineRawSequence
import EthInapproximability.CurrentPaper.EntryUnaryCompare

/-! A fixed two-comparison TM2 subroutine on prepared unary banks.  The
controller supplies two copies of the current column and free column.  The
subroutine writes both `j<f` and `j=f` verdicts and consumes those copies. -/

namespace CurrentAdditive.GaussPreparedColumnDecision

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

abbrev Bank := Fin 6 → List Bool
abbrev Label := BitMachineRawSequence.Label
  EntryUnaryCompare.CL EntryUnaryCompare.CL
abbrev Control := BitMachineRawSequence.Control
  EntryUnaryCompare.CV EntryUnaryCompare.CV

def A₀ : Fin 6 := 0
def B₀ : Fin 6 := 1
def O₀ : Fin 6 := 2
def A₁ : Fin 6 := 3
def B₁ : Fin 6 := 4
def O₁ : Fin 6 := 5

def initial (j f : Nat) : Bank :=
  ![List.replicate j true, List.replicate f true, [],
    List.replicate j true, List.replicate f true, []]

def program : Label → TM2.Stmt (fun _ : Fin 6 => Bool) Label Control :=
  BitMachineRawSequence.program
    (EntryUnaryCompare.program A₀ B₀ O₀ true false false)
    (EntryUnaryCompare.program A₁ B₁ O₁ false true false)
    .loop (none, none) (none, none)

theorem local_run (j f : Nat) :
    ∃ t ≤ 2 * (max j f + 2) + 1, ∃ v,
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel EntryUnaryCompare.CL.loop),
          ((none, none), (none, none)), initial j f⟩ :
          TM2.Cfg (fun _ : Fin 6 => Bool) Label Control) =
        ⟨none, v,
          Function.update
            (Function.update
              (Function.update
                (Function.update
                  (Function.update
                    (Function.update (initial j f) A₀ []) B₀ [])
                      O₀ [decide (j < f)]) A₁ []) B₁ [])
              O₁ [decide (j = f)]⟩ := by
  obtain ⟨ta, hta, va, ha⟩ := EntryUnaryCompare.compare_run
    A₀ B₀ O₀ (by decide) (by decide) (by decide)
    true false false (initial j f) (none, none) j f
    (by simp [initial, A₀]) (by simp [initial, B₀])
  let T := Function.update
    (Function.update (Function.update (initial j f) A₀ []) B₀ [])
      O₀ (EntryUnaryCompare.verdict true false false j f :: (initial j f) O₀)
  have hT₁ : T A₁ = List.replicate j true := by
    simp [T, initial, A₀, B₀, O₀, A₁]
  have hT₂ : T B₁ = List.replicate f true := by
    simp [T, initial, A₀, B₀, O₀, B₁]
  obtain ⟨tb, htb, vb, hb⟩ := EntryUnaryCompare.compare_run
    A₁ B₁ O₁ (by decide) (by decide) (by decide)
    false true false T (none, none) j f hT₁ hT₂
  have hlt : EntryUnaryCompare.verdict true false false j f =
      decide (j < f) := by
    by_cases h : j < f <;> simp [EntryUnaryCompare.verdict, h]
  have heq : EntryUnaryCompare.verdict false true false j f =
      decide (j = f) := by
    by_cases h : j = f
    · subst f; simp [EntryUnaryCompare.verdict]
    · by_cases hlt' : j < f <;>
        simp [EntryUnaryCompare.verdict, h, hlt']
  have hraw := BitMachineRawSequence.runs
    (EntryUnaryCompare.program A₀ B₀ O₀ true false false)
    (EntryUnaryCompare.program A₁ B₁ O₁ false true false)
    EntryUnaryCompare.CL.loop EntryUnaryCompare.CL.loop
    (none, none) va (none, none) vb
    (initial j f) T
    (Function.update (Function.update (Function.update T A₁ []) B₁ [])
      O₁ (EntryUnaryCompare.verdict false true false j f :: T O₁))
    ta tb ha hb
  obtain ⟨t, ht, hr⟩ := hraw
  refine ⟨t, by omega, ((none, none), vb), ?_⟩
  change ((advance program)^[t]) _ = _ at hr
  simpa [T, hlt, heq, initial, A₀, B₀, O₀, A₁, B₁, O₁,
    Function.update_of_ne] using hr

#print axioms local_run

end CurrentAdditive.GaussPreparedColumnDecision
