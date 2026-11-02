import CurrentAdditive.V38DegreePhysical
import CurrentAdditive.CanonicalAmbientSourceDegree

noncomputable section
namespace CurrentAdditive.V38SourceDegree

open Turing EthInapproximability.CurrentPaper
open BitMachineEncoding BitMachineStackEmbedding
open CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
open CurrentAdditive.FiniteFieldConstructor.CanonicalSourcePrelude
open Paper2.YaoMachine Paper2.YaoLookup Paper2.YaoSourceCodec

def place (t : ℕ) : Fin 6 ↪ Cell t 16 :=
  ⟨![.degree 0, .degree 8, .degree 9, .degree 3, .degree 10, .degree 11], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all⟩

def degreeStage (t : ℕ) :=
  fun l => stackStmt (place t) (CurrentAdditive.V38DegreePhysical.program t l)

def inputBank {t : ℕ} (x : YaoSource t) : Cell t 16 → List Bool :=
  degreeInputBank (by decide) x

def outputBank {t : ℕ} (x : YaoSource t) : Cell t 16 → List Bool :=
  bank (place t) (inputBank x)
    (CurrentAdditive.V38DegreePhysical.final (paddedEdgeBits x.2.1) t)

theorem input_restrict {t : ℕ} (x : YaoSource t) :
    (fun k => inputBank x (place t k)) =
      CurrentAdditive.V38DegreePhysical.initial (paddedEdgeBits x.2.1) := by
  funext k
  fin_cases k <;>
    simp [inputBank, place, CurrentAdditive.V38DegreePhysical.initial,
      degreeInputBank, sourceBank_degree]

theorem degree_run (t : ℕ) (x : YaoSource t) :
    ∃ steps ≤ CurrentAdditive.V38DegreePhysical.clock (paddedEdgeBits x.2.1) t,
      ((advance (degreeStage t))^[steps])
        (⟨some (BitMachineRawSequence.leftLabel
            (0 : SourceClauseFixedUnary.Label 5)),
          ((), ((), false)), inputBank x⟩ :
          TM2.Cfg (fun _ : Cell t 16 => Bool) _ _) =
        ⟨none, ((), ((), false)), outputBank x⟩ := by
  obtain ⟨steps, hs, hr⟩ :=
    CurrentAdditive.V38DegreePhysical.run (paddedEdgeBits x.2.1) t
  have hl := BitMachineStackRun.run (place t) (inputBank x)
    (CurrentAdditive.V38DegreePhysical.program t)
    (⟨some (BitMachineRawSequence.leftLabel
        (0 : SourceClauseFixedUnary.Label 5)),
      ((), ((), false)), CurrentAdditive.V38DegreePhysical.initial
        (paddedEdgeBits x.2.1)⟩ : TM2.Cfg (fun _ : Fin 6 => Bool) _ _) steps
  rw [hr] at hl
  have hbank : bank (place t) (inputBank x)
      (CurrentAdditive.V38DegreePhysical.initial (paddedEdgeBits x.2.1)) =
      inputBank x := by
    rw [← input_restrict]
    exact bank_restrict _ _
  exact ⟨steps, hs, by
    simpa only [degreeStage, outputBank, stackCfg, hbank] using hl⟩

def program (t : ℕ) :=
  BitMachineRawSequence.program (sourceToDegreeInputs t 16 (by decide))
    (degreeStage t)
    (BitMachineRawSequence.leftLabel (0 : SourceClauseFixedUnary.Label 5))
    (initialControl t, (none, (none, none))) ((), ((), false))

theorem output_degree {t : ℕ} (x : YaoSource t) :
    outputBank x (.degree 3) =
      List.replicate (5 * paddedEdgeBits x.2.1 + 14*t) true := by
  have h := bank_at (place t) (inputBank x)
    (CurrentAdditive.V38DegreePhysical.final (paddedEdgeBits x.2.1) t) 3
  exact h

theorem output_foreign {t : ℕ} (x : YaoSource t) (j : Cell t 16)
    (hj : ∀ k : Fin 16, Cell.degree k ≠ j) :
    outputBank x j = sourceBank x j := by
  have hp : ¬ ∃ k, place t k = j := by
    rintro ⟨k, hk⟩
    fin_cases k <;> exact hj _ hk
  rw [outputBank, bank_outside (place t) _ _ j hp]
  have h0 : j ≠ .degree 0 := fun h => hj 0 h.symm
  have h1 : j ≠ .degree 1 := fun h => hj 1 h.symm
  have h2 : j ≠ .degree 2 := fun h => hj 2 h.symm
  simp [inputBank, degreeInputBank, h0, h1, h2]

theorem output_source {t : ℕ} (x : YaoSource t) (j : WStack t 0) :
    outputBank x (.source j) = sourceReady x j := by
  rw [output_foreign x (.source j) (by intro k h; cases h)]
  exact sourceBank_source x j

theorem output_blank {t : ℕ} (x : YaoSource t) (j : Cell t 16)
    (hd : ∀ k : Fin 16, Cell.degree k ≠ j)
    (hs : ∀ k : WStack t 0, Cell.source k ≠ j) :
    outputBank x j = [] := by
  rw [output_foreign x j hd]
  exact bank_outside (sourceEmbed t 16) (blank t 16) (sourceReady x) j
    (by rintro ⟨k, hk⟩; exact hs k hk)

def clock {t : ℕ} (x : YaoSource t) : ℕ :=
  sourceClock x +
    ((2*paddedEdgeBits x.2.1+2) + (2*paddedEdgeCount x.2.1+2) +
      (2*arity t+2) + 2) + 1 +
    CurrentAdditive.V38DegreePhysical.clock (paddedEdgeBits x.2.1) t + 1

theorem source_run (t : ℕ) (ht : 1 ≤ t) (x : YaoSource t) :
    ∃ steps ≤ clock x,
      ((advance (program t))^[steps])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel Paper2.YaoHeaderParser.startLabel))),
          ((initialControl t, (none, (none, none))), ((), ((), false))),
          bank (sourceEmbed t 16) (blank t 16) (initBank 0 x [])⟩ :
            TM2.Cfg (fun _ : Cell t 16 => Bool) _ _) =
        ⟨none, ((initialControl t, (none, (none, none))), ((), ((), false))),
          outputBank x⟩ := by
  obtain ⟨s, hs, hr⟩ := physical_source_to_degree_inputs t 16 ht (by decide) x
  obtain ⟨u, hu, hd⟩ := degree_run t x
  obtain ⟨v, hv, hc⟩ := BitMachineRawSequence.runs
    (sourceToDegreeInputs t 16 (by decide)) (degreeStage t)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel Paper2.YaoHeaderParser.startLabel))
    (BitMachineRawSequence.leftLabel (0 : SourceClauseFixedUnary.Label 5))
    (initialControl t, (none, (none, none)))
    (initialControl t, (none, (none, none)))
    ((), ((), false)) ((), ((), false))
    (bank (sourceEmbed t 16) (blank t 16) (initBank 0 x []))
    (inputBank x) (outputBank x) s u
    (by simpa [inputBank, degreeInputBank] using hr) hd
  exact ⟨v, by unfold clock; omega, by simpa [program] using hc⟩

#print axioms degree_run
#print axioms output_degree
#print axioms output_foreign
#print axioms output_source
#print axioms output_blank
#print axioms source_run
end CurrentAdditive.V38SourceDegree
