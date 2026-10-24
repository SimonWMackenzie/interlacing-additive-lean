import CurrentAdditive.CanonicalEntryLookupClock

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalTable

open Turing CurrentAdditive.SmallBias
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding

noncomputable def canonicalLookupProgramOn {J : Type*} [DecidableEq J]
    (ι : MatrixTableLookup.Stack ↪ J) :=
  fun l => stackStmt ι (MatrixTableLookup.program l)

/-- The fixed packed-array lookup runs inside any larger writer bank.
Only the answer cell changes; the pair label, width, coordinate, packed
array, and every foreign bank cell are preserved. -/
theorem physical_canonical_entry_lift {J : Type*} [DecidableEq J]
    (ι : MatrixTableLookup.Stack ↪ J) (S : J → List Bool)
    {v e : ℕ} (b t d modulus : ℕ) (he : e ≤ 2 ^ b)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (i : Fin (rowCount v b t)) (j : Fin (columnCount b t d))
    (h0 : S (ι 0) = List.replicate (((columnIndex b t d).symm j).2.2).val true)
    (h1 : S (ι 1) = List.replicate (2 ^ b * (2 ^ t * 2 ^ t + 1)) true)
    (h2 : S (ι 2) = List.replicate
      (numericPayloadCoord b t d he edges i j).val true)
    (h6 : S (ι 6) = packedFieldBits d modulus
      (2 ^ b * (2 ^ t * 2 ^ t + 1)))
    (hempty : ∀ k : Fin 10, k ≠ 0 → k ≠ 1 → k ≠ 2 → k ≠ 6 →
      S (ι k) = []) :
    ∃ steps ≤ canonicalLookupClock b t d,
      ((advance (canonicalLookupProgramOn ι))^[steps])
        (⟨some MatrixTableLookup.start, MatrixTableLookup.initial, S⟩ :
          TM2.Cfg (fun _ : J => Bool) _ _) =
        ⟨none, MatrixTableLookup.initial,
          Function.update S (ι 7)
            [numericEntry b t d modulus he edges i j]⟩ := by
  let localS : MatrixTableLookup.Stack → List Bool := fun k => S (ι k)
  have hstart : localS =
      (MatrixTableLookup.cfg (some MatrixTableLookup.start)
        MatrixTableLookup.initial
        (List.replicate (((columnIndex b t d).symm j).2.2).val true)
        (List.replicate (2 ^ b * (2 ^ t * 2 ^ t + 1)) true)
        (List.replicate (numericPayloadCoord b t d he edges i j).val true)
        [] (packedFieldBits d modulus
          (2 ^ b * (2 ^ t * 2 ^ t + 1))) []).stk := by
    funext k
    fin_cases k <;> simp [localS, MatrixTableLookup.cfg,
      h0, h1, h2, h6,
      hempty 3 (by decide) (by decide) (by decide) (by decide),
      hempty 4 (by decide) (by decide) (by decide) (by decide),
      hempty 5 (by decide) (by decide) (by decide) (by decide),
      hempty 7 (by decide) (by decide) (by decide) (by decide),
      hempty 8 (by decide) (by decide) (by decide) (by decide),
      hempty 9 (by decide) (by decide) (by decide) (by decide)]
  obtain ⟨steps, hsteps, hrun⟩ := physical_canonical_entry_bit
    b t d modulus he edges i j []
  have huniform := physical_entry_lookup_clock_uniform
    b t d modulus he edges i j
  have hfinish :
      (MatrixTableLookup.cfg none MatrixTableLookup.initial
        (List.replicate (((columnIndex b t d).symm j).2.2).val true)
        (List.replicate (2 ^ b * (2 ^ t * 2 ^ t + 1)) true)
        (List.replicate (numericPayloadCoord b t d he edges i j).val true)
        [] (packedFieldBits d modulus
          (2 ^ b * (2 ^ t * 2 ^ t + 1)))
        [numericEntry b t d modulus he edges i j]).stk =
      Function.update localS 7 [numericEntry b t d modulus he edges i j] := by
    funext k
    fin_cases k <;> simp [MatrixTableLookup.cfg, hstart]
  have hrun' : ((advance MatrixTableLookup.program)^[steps])
      (⟨some MatrixTableLookup.start, MatrixTableLookup.initial, localS⟩ :
        TM2.Cfg (fun _ : MatrixTableLookup.Stack => Bool) _ _) =
      ⟨none, MatrixTableLookup.initial,
        Function.update localS 7 [numericEntry b t d modulus he edges i j]⟩ := by
    have hsCfg :
        (⟨some MatrixTableLookup.start, MatrixTableLookup.initial, localS⟩ :
          TM2.Cfg (fun _ : MatrixTableLookup.Stack => Bool) _ _) =
        MatrixTableLookup.cfg (some MatrixTableLookup.start)
          MatrixTableLookup.initial
          (List.replicate (((columnIndex b t d).symm j).2.2).val true)
          (List.replicate (2 ^ b * (2 ^ t * 2 ^ t + 1)) true)
          (List.replicate (numericPayloadCoord b t d he edges i j).val true)
          [] (packedFieldBits d modulus
            (2 ^ b * (2 ^ t * 2 ^ t + 1))) [] := by
      simpa only [MatrixTableLookup.cfg] using
        congrArg (fun stk : MatrixTableLookup.Stack → List Bool =>
          (⟨some MatrixTableLookup.start,
            MatrixTableLookup.initial, stk⟩ : MatrixTableLookup.Config)) hstart
    have hfCfg :
        MatrixTableLookup.cfg none MatrixTableLookup.initial
          (List.replicate (((columnIndex b t d).symm j).2.2).val true)
          (List.replicate (2 ^ b * (2 ^ t * 2 ^ t + 1)) true)
          (List.replicate (numericPayloadCoord b t d he edges i j).val true)
          [] (packedFieldBits d modulus
            (2 ^ b * (2 ^ t * 2 ^ t + 1)))
          [numericEntry b t d modulus he edges i j] =
        (⟨none, MatrixTableLookup.initial,
          Function.update localS 7 [numericEntry b t d modulus he edges i j]⟩ :
          TM2.Cfg (fun _ : MatrixTableLookup.Stack => Bool) _ _) := by
      simpa only [MatrixTableLookup.cfg] using
        congrArg (fun stk : MatrixTableLookup.Stack → List Bool =>
          (⟨none, MatrixTableLookup.initial, stk⟩ : MatrixTableLookup.Config))
          hfinish
    rw [hsCfg, ← hfCfg]
    exact hrun
  have hlift := BitMachineStackRun.run ι S MatrixTableLookup.program
    (⟨some MatrixTableLookup.start, MatrixTableLookup.initial, localS⟩ :
      TM2.Cfg (fun _ : MatrixTableLookup.Stack => Bool) _ _) steps
  rw [hrun'] at hlift
  refine ⟨steps, hsteps.trans huniform, ?_⟩
  have hbank : bank ι S localS = S := by
    simpa only [localS] using bank_restrict ι S
  simpa only [canonicalLookupProgramOn, stackCfg, hbank,
    bank_update] using hlift

#print axioms physical_canonical_entry_lift

end CurrentAdditive.FiniteFieldConstructor.CanonicalTable
