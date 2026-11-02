import CurrentAdditive.GaussWorkListSuffix
import EthInapproximability.CurrentPaper.FuelLoop

/-! The literal descending unary-fuel loop repeatedly executes the checked
reusable physical item round.  After k iterations its accumulator is the
ordered V2 field sequence for all k columns; the final count header is a
separate physical stage. -/

namespace CurrentAdditive.GaussWorkListFuel

open Turing Turing.TM2 EthInapproximability.CurrentPaper BitMachineEncoding

abbrev Bank := GaussWorkItemRoundComplete.Bank

noncomputable def maxRoundClock {m k : Nat}
    (B : Fin m → Fin k → ℚ) (f : Fin k) : Nat :=
  Finset.univ.sup (GaussWorkItemRoundComplete.roundClock B f)

noncomputable def stateAt {m k : Nat}
    (S : Bank → List Bool) (B : Fin m → Fin k → ℚ)
    (f : Fin k) (q : Nat) : Bank → List Bool :=
  Function.update
    (Function.update S ⟨5, by omega⟩ (List.replicate (k - q) true))
    ⟨24, by omega⟩ (GaussWorkListSuffix.fieldsAt B f (k - q))

theorem stateAt_fuel {m k : Nat}
    (S : Bank → List Bool) (B : Fin m → Fin k → ℚ)
    (f : Fin k) (q : Nat) :
    stateAt S B f q ⟨5, by omega⟩ = List.replicate (k - q) true := by
  simp [stateAt]

theorem stateAt_output {m k : Nat}
    (S : Bank → List Bool) (B : Fin m → Fin k → ℚ)
    (f : Fin k) (q : Nat) :
    stateAt S B f q ⟨24, by omega⟩ =
      GaussWorkListSuffix.fieldsAt B f (k - q) := by
  simp [stateAt]

theorem stateAt_other {m k : Nat}
    (S : Bank → List Bool) (B : Fin m → Fin k → ℚ)
    (f : Fin k) (q : Nat) (z : Bank)
    (h5 : z ≠ ⟨5, by omega⟩) (h24 : z ≠ ⟨24, by omega⟩) :
    stateAt S B f q z = S z := by
  simp [stateAt, h5, h24]

theorem stateAt_zero {m k : Nat}
    (S : Bank → List Bool) (B : Fin m → Fin k → ℚ)
    (f : Fin k)
    (h5 : S ⟨5, by omega⟩ = List.replicate k true)
    (h24 : S ⟨24, by omega⟩ = []) :
    stateAt S B f 0 = S := by
  funext z
  by_cases hz5 : z = (⟨5, by omega⟩ : Bank)
  · subst z; simp [stateAt_fuel, h5]
  by_cases hz24 : z = (⟨24, by omega⟩ : Bank)
  · subst z
    simp [stateAt_output, GaussWorkListSuffix.fields_at_width, h24]
  exact stateAt_other S B f 0 z hz5 hz24

noncomputable def program := FuelLoop.program
  GaussWorkItemRoundComplete.program
  GaussWorkItemRoundComplete.start
  GaussWorkItemRoundComplete.control (⟨5, by omega⟩ : Bank)

theorem physical_fields {m k : Nat}
    (B : Fin m → Fin k → ℚ) (f : Fin k)
    (S : Bank → List Bool)
    (hmat : S ⟨4, by omega⟩ = GaussPhysical.encodeTypedMatrix B)
    (hf : S ⟨1, by omega⟩ = List.replicate f.val true)
    (h5 : S ⟨5, by omega⟩ = List.replicate k true)
    (h6 : S ⟨6, by omega⟩ = [])
    (h7 : S ⟨7, by omega⟩ = [])
    (h8 : S ⟨8, by omega⟩ = [])
    (h9 : S ⟨9, by omega⟩ = [])
    (h10 : S ⟨10, by omega⟩ = [])
    (h11 : S ⟨11, by omega⟩ = [])
    (h12 : S ⟨12, by omega⟩ = [])
    (h13 : S ⟨13, by omega⟩ = [])
    (h14 : S ⟨14, by omega⟩ = [])
    (h15 : S ⟨15, by omega⟩ = [])
    (h24 : S ⟨24, by omega⟩ = [])
    (hblank : ∀ i, S (GaussWorkItemFrameContext.slots.machine i) = []) :
    ∃ t ≤ k * (maxRoundClock B f + 1) + 1,
      ((advance program)^[t])
        (⟨some (.inl ()),
          (none, GaussWorkItemRoundComplete.control), S⟩ :
          TM2.Cfg (fun _ : Bank => Bool) _ _) =
        ⟨none, (none, GaussWorkItemRoundComplete.control), stateAt S B f k⟩ := by
  let Q := stateAt S B f
  have hne : ∀ q < k, Q q ⟨5, by omega⟩ ≠ [] := by
    intro q hq
    rw [show Q q ⟨5, by omega⟩ = List.replicate (k - q) true by
      exact stateAt_fuel S B f q]
    intro he
    have := congrArg List.length he
    simp at this
    omega
  have hend : Q k ⟨5, by omega⟩ = [] := by
    simp [Q, stateAt_fuel]
  have hbody : ∀ q < k, ∃ t ≤ maxRoundClock B f,
      ((advance GaussWorkItemRoundComplete.program)^[t])
        (⟨some GaussWorkItemRoundComplete.start,
          GaussWorkItemRoundComplete.control,
          Function.update (Q q) ⟨5, by omega⟩
            (Q q ⟨5, by omega⟩).tail⟩ :
          TM2.Cfg (fun _ : Bank => Bool) _ _) =
        ⟨none, GaussWorkItemRoundComplete.control, Q (q + 1)⟩ := by
    intro q hq
    let jn := k - (q + 1)
    have hjlt : jn < k := by dsimp [jn]; omega
    let j : Fin k := ⟨jn, hjlt⟩
    let P := Function.update (Q q) ⟨5, by omega⟩
      (Q q ⟨5, by omega⟩).tail
    have hfuel : P ⟨5, by omega⟩ = List.replicate j.val true := by
      have hsub : k - q = jn + 1 := by dsimp [jn]; omega
      change P ⟨5, by omega⟩ = List.replicate jn true
      simp only [P, Function.update_self, Q, stateAt_fuel, hsub]
      simp [List.tail_replicate]
    have hother : ∀ z : Bank, z ≠ ⟨5, by omega⟩ →
        z ≠ ⟨24, by omega⟩ → P z = S z := by
      intro z hz5 hz24
      change Function.update (Q q) ⟨5, by omega⟩
        (Q q ⟨5, by omega⟩).tail z = S z
      rw [Function.update_of_ne hz5]
      exact stateAt_other S B f q z hz5 hz24
    have hfixed (z : Bank) (hz5 : z.val ≠ 5) (hz24 : z.val ≠ 24) :
        P z = S z := by
      apply hother z
      · intro h; exact hz5 (congrArg Fin.val h)
      · intro h; exact hz24 (congrArg Fin.val h)
    have hP24 : P ⟨24, by omega⟩ =
        GaussWorkListSuffix.fieldsAt B f (jn + 1) := by
      have hsub : k - q = jn + 1 := by dsimp [jn]; omega
      simp [P, Q, stateAt_output, hsub]
    have hPb : ∀ i, P (GaussWorkItemFrameContext.slots.machine i) = [] := by
      intro i
      have hz5 : GaussWorkItemFrameContext.slots.machine i ≠
          (⟨5, by omega⟩ : Bank) := by
        intro he
        have hv := congrArg Fin.val he
        change 16 + i.val = 5 at hv
        omega
      have hz24 : GaussWorkItemFrameContext.slots.machine i ≠
          (⟨24, by omega⟩ : Bank) := by
        intro he
        have hv := congrArg Fin.val he
        have hi : i.val < 8 := by
          simpa only [show (SourceListMachineWriter.framingMachine true).stackCount = 8
            from rfl] using i.isLt
        change 16 + i.val = 24 at hv
        omega
      rw [hother _ hz5 hz24]
      exact hblank i
    obtain ⟨u, hu, hr⟩ := GaussWorkItemRoundComplete.physical_round B f j P
      (GaussWorkListSuffix.fieldsAt B f (jn + 1))
      ((hfixed ⟨4, by omega⟩ (by norm_num) (by norm_num)).trans hmat)
      ((hfixed ⟨1, by omega⟩ (by norm_num) (by norm_num)).trans hf)
      hfuel
      ((hfixed ⟨6, by omega⟩ (by norm_num) (by norm_num)).trans h6)
      ((hfixed ⟨7, by omega⟩ (by norm_num) (by norm_num)).trans h7)
      ((hfixed ⟨8, by omega⟩ (by norm_num) (by norm_num)).trans h8)
      ((hfixed ⟨9, by omega⟩ (by norm_num) (by norm_num)).trans h9)
      ((hfixed ⟨10, by omega⟩ (by norm_num) (by norm_num)).trans h10)
      ((hfixed ⟨11, by omega⟩ (by norm_num) (by norm_num)).trans h11)
      ((hfixed ⟨12, by omega⟩ (by norm_num) (by norm_num)).trans h12)
      ((hfixed ⟨13, by omega⟩ (by norm_num) (by norm_num)).trans h13)
      ((hfixed ⟨14, by omega⟩ (by norm_num) (by norm_num)).trans h14)
      ((hfixed ⟨15, by omega⟩ (by norm_num) (by norm_num)).trans h15)
      hP24 hPb
    have hnext : Function.update P ⟨24, by omega⟩
        (SourceListMachineWriter.result true
            (GaussWorkItemContextSerialize.workPacket B f j) ++
          GaussWorkListSuffix.fieldsAt B f (jn + 1)) = Q (q + 1) := by
      funext z
      by_cases hz24 : z = (⟨24, by omega⟩ : Bank)
      · subst z
        simpa only [Function.update_self, stateAt_output] using
          (GaussWorkListSuffix.fields_step B f jn hjlt).symm
      by_cases hz5 : z = (⟨5, by omega⟩ : Bank)
      · subst z
        have hneq : (⟨5, by omega⟩ : Bank) ≠ ⟨24, by omega⟩ := by
          intro h
          have hv := congrArg Fin.val h
          norm_num at hv
        rw [Function.update_of_ne hneq]
        rw [hfuel]
        change List.replicate jn true = Q (q + 1) ⟨5, by omega⟩
        rw [show Q (q + 1) ⟨5, by omega⟩ =
          List.replicate (k - (q + 1)) true from stateAt_fuel S B f (q + 1)]
      rw [Function.update_of_ne hz24, hother z hz5 hz24]
      exact (stateAt_other S B f (q + 1) z hz5 hz24).symm
    have hround : GaussWorkItemRoundComplete.roundClock B f j ≤
        maxRoundClock B f := by
      exact Finset.le_sup (f := GaussWorkItemRoundComplete.roundClock B f)
        (Finset.mem_univ j)
    refine ⟨u, hu.trans hround, ?_⟩
    simpa [GaussWorkItemRoundComplete.start,
      GaussWorkItemRoundComplete.control, hnext] using hr
  obtain ⟨t, ht, hr⟩ := FuelLoop.loop_run
    GaussWorkItemRoundComplete.program
    GaussWorkItemRoundComplete.start GaussWorkItemRoundComplete.control
    (⟨5, by omega⟩ : Bank) (maxRoundClock B f) k Q hne hend hbody
  refine ⟨t, ht, ?_⟩
  simpa [program, Q, stateAt_zero S B f h5 h24] using hr

#print axioms physical_fields

end CurrentAdditive.GaussWorkListFuel
