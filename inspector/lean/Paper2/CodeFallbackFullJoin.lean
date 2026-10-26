import Paper2.CodeFallbackEntryJoin

/-! One fixed controller: public-count syntax construction and physically
loaded fallback dimensions, followed directly by the status-preserving
interpreter/fallback program. The handoff occurs before interpretation. -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

namespace Paper2.CodeFallbackFullJoin

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.CodeFallbackEntryBank

abbrev Stack := CodeFallbackEntryJoin.Stack

noncomputable def fallbackProgram := fun l =>
  stackStmt fallbackSlots (CodeTableFallback.program l)

noncomputable def fallbackStart : CodeTableFallback.Label :=
  (CodeTableFallback.initial (GeneratorCode.initial .bit)
    [] 0 0 0 0).l.getD (.inr (.inl .route))
noncomputable def fallbackControl : CodeTableFallback.Control :=
  (CodeTableFallback.initial (GeneratorCode.initial .bit)
    [] 0 0 0 0).var
def prepControl :=
  ((CodeFallbackEntryJoin.sourceControl,
      CodeFallbackEntryJoin.copyControl),
    CodeFallbackEntryJoin.copyControl)

noncomputable def program :=
  BitMachineRawSequence.program CodeFallbackEntryJoin.program fallbackProgram
    fallbackStart prepControl fallbackControl

theorem fallback_initial_fixed (root : Code) (tape : List Bool)
    (B R mX mY : Nat) :
    (CodeTableFallback.initial (GeneratorCode.initial root)
      tape B R mX mY).l = some fallbackStart ∧
    (CodeTableFallback.initial (GeneratorCode.initial root)
      tape B R mX mY).var = fallbackControl := by
  constructor <;> rfl

theorem prepared_eq_embedded (n s q₁ q₂ w Q k mX mY : Nat)
    (row col : Code) (tape : List Bool) (B R : Nat) :
    let root : Code := .append (copies mY col) (copies mX row)
    let S := CodeFallbackEntryJoin.finalBank n s q₁ q₂ w Q k mX mY
      row col tape B R
    bank fallbackSlots S
      (CodeTableFallback.initial (GeneratorCode.initial root)
        tape B R mX mY).stk = S := by
  let root : Code := .append (copies mY col) (copies mX row)
  let S := CodeFallbackEntryJoin.finalBank n s q₁ q₂ w Q k mX mY
    row col tape B R
  apply bank_eq_self
  intro j
  exact (congrFun (CodeFallbackEntryBank.prepared_fallback_bank
    n s q₁ q₂ w Q k mX mY row col tape B R) j).symm

theorem fallback_run (n s q₁ q₂ w Q k mX mY : Nat)
    (row col : Code) (tape : List Bool) (B R t : Nat)
    (d : CodeTableFallback.Config)
    (hd : CodeTableFallback.run t
      (CodeTableFallback.initial
        (GeneratorCode.initial
          (.append (copies mY col) (copies mX row)))
        tape B R mX mY) = d) :
    let S := CodeFallbackEntryJoin.finalBank n s q₁ q₂ w Q k mX mY
      row col tape B R
    ((advance fallbackProgram)^[t])
      (⟨some fallbackStart,fallbackControl,S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨d.l,d.var,bank fallbackSlots S d.stk⟩ := by
  let root : Code := .append (copies mY col) (copies mX row)
  let S := CodeFallbackEntryJoin.finalBank n s q₁ q₂ w Q k mX mY
    row col tape B R
  let c := CodeTableFallback.initial (GeneratorCode.initial root)
    tape B R mX mY
  have h := BitMachineStackRun.run fallbackSlots S
    CodeTableFallback.program c t
  change ((advance CodeTableFallback.program)^[t]) c = d at hd
  rw [hd] at h
  obtain ⟨hl,hv⟩ := fallback_initial_fixed root tape B R mX mY
  have hb : bank fallbackSlots S c.stk = S :=
    prepared_eq_embedded n s q₁ q₂ w Q k mX mY row col tape B R
  simpa only [fallbackProgram, stackCfg, hl, hv, hb]
    using h

theorem run_from_fallback (n p s q₁ q₂ w Q k mX mY : Nat)
    (tape : List Bool) (B R : Nat) (hs : 3 ≤ s)
    (t : Nat) (d : CodeTableFallback.Config)
    (hd :
      let c := GeneratorSource.seedRecursiveCodes n p s q₁ q₂ w Q k
      let root : Code := .append (copies mY c.2) (copies mX c.1)
      CodeTableFallback.run t
        (CodeTableFallback.initial (GeneratorCode.initial root)
          tape B R mX mY) = d)
    (hh : d.l = none) :
    ∃ u ≤ CodeFallbackEntryJoin.clock n p s q₁ q₂ w Q k mX mY + t + 1,
      ((advance program)^[u])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel
                  (BitMachineRawSequence.leftLabel
                    (BitMachineRawSequence.leftLabel
                      CodeGeneratorSampleJoin.compilerStart)))))),
          (prepControl,fallbackControl),
          CodeFallbackEntryJoin.initial n p s q₁ q₂ w Q k mX mY
            tape B R⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,(prepControl,d.var),
          bank fallbackSlots
            (CodeFallbackEntryJoin.finalBank n s q₁ q₂ w Q k mX mY
              (GeneratorSource.seedRecursiveCodes n p s q₁ q₂ w Q k).1
              (GeneratorSource.seedRecursiveCodes n p s q₁ q₂ w Q k).2
              tape B R) d.stk⟩ := by
  let c := GeneratorSource.seedRecursiveCodes n p s q₁ q₂ w Q k
  let root : Code := .append (copies mY c.2) (copies mX c.1)
  let S := CodeFallbackEntryJoin.finalBank n s q₁ q₂ w Q k mX mY
    c.1 c.2 tape B R
  obtain ⟨tp,htp,hp⟩ := CodeFallbackEntryJoin.run
    n p s q₁ q₂ w Q k mX mY tape B R hs
  have hf := fallback_run n s q₁ q₂ w Q k mX mY
    c.1 c.2 tape B R t d hd
  have hf' : ((advance fallbackProgram)^[t])
      (⟨some fallbackStart,fallbackControl,S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none,d.var,bank fallbackSlots S d.stk⟩ := by
    simpa only [hh] using hf
  obtain ⟨u,hu,hr⟩ := BitMachineRawSequence.runs
    CodeFallbackEntryJoin.program fallbackProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              CodeGeneratorSampleJoin.compilerStart))))) fallbackStart
    prepControl prepControl fallbackControl d.var
    (CodeFallbackEntryJoin.initial n p s q₁ q₂ w Q k mX mY tape B R)
    S (bank fallbackSlots S d.stk)
    tp t hp hf'
  exact ⟨u,by omega,by simpa only [program, c, S, hh] using hr⟩

#print axioms fallback_run
#print axioms run_from_fallback

end Paper2.CodeFallbackFullJoin
