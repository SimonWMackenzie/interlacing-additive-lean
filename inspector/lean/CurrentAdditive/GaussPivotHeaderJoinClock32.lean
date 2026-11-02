import CurrentAdditive.GaussPivotJoinClock32
import CurrentAdditive.GaussPivotHeaderPreservesRow32

/-! Compose the physical unary count-header writer, list join, and exact
Bank4 state assembler in the same fixed Fin32 controller. -/

namespace CurrentAdditive.GaussPivotHeaderJoinClock32

noncomputable section

open EthInapproximability.CurrentPaper
open CurrentAdditive.GaussStepFields32

private noncomputable abbrev W :=
  SourceListMachineWriter.framingMachine false

def headerPhaseBound (n : Nat) : Nat :=
  (2*n+3)+
  (UnaryBinaryEncoding.coefficient+7)*(n+1)^2+1+
  (2*(SourceListMachineWriter.result false
    (List.replicate n true)).length+3)+1

def clock {m k : Nat} (B' : Fin m → Fin k → ℚ) (c : Nat)
    (ps : List (Fin m × Fin k)) (S : Stack → List Bool)
    (charge : Nat) : Nat :=
  headerPhaseBound ps.length + 1 +
  GaussPivotJoinClock32.clock B' ps.length c ps S
    (charge + GaussPivotClockGrowth32.pushConstant *
      (headerPhaseBound ps.length + 1))

def uniformClock {m k : Nat} (B' : Fin m → Fin k → ℚ)
    (c : Nat) (ps : List (Fin m × Fin k))
    (charge : Nat) : Nat :=
  headerPhaseBound ps.length + 1 +
  GaussPivotJoinClock32.uniformClock B' ps.length c ps
    (charge + GaussPivotClockGrowth32.pushConstant *
      (headerPhaseBound ps.length + 1))

theorem clock_le_uniform {m k : Nat} (B' : Fin m → Fin k → ℚ)
    (c : Nat) (ps : List (Fin m × Fin k))
    (S : Stack → List Bool) (charge : Nat)
    (h7 : (S 7).length ≤ charge) :
    clock B' c ps S charge ≤ uniformClock B' c ps charge := by
  unfold clock uniformClock
  apply Nat.add_le_add_left
  exact GaussPivotJoinClock32.clock_le_uniform
    B' ps.length c ps S _ (h7.trans (Nat.le_add_right _ _))

theorem header_join_finish_bound {m k : Nat}
    (B' : Fin m → Fin k → ℚ) (c : Nat)
    (ps : List (Fin m × Fin k))
    (S : Stack → List Bool)
    (h4 : S 4 = GaussPhysical.encodeTypedMatrix B')
    (h5 : S 5 = List.replicate ps.length true)
    (h6 : S 6 = List.replicate c true)
    (h27 : S 27 = SourceListEncoding.fields
      (ps.map GaussControlTrace.pivotPacket))
    (h24 : S 24 = []) (h30 : S 30 = []) (h31 : S 31 = [])
    (hempty : ∀ j : Fin W.stackCount,
      S (GaussPivotFraming32.locate j) = [])
    (charge : Nat) (hcharge : ∀ j : Stack, (S j).length ≤ charge) :
    ∃ t ≤ clock B' c ps S charge,
      (run t ⟨some (.header (.copyIn .scan)),
        eHeader (((),none),W.initial),S⟩).l = some .done ∧
      (run t ⟨some (.header (.copyIn .scan)),
        eHeader (((),none),W.initial),S⟩).stk 14 =
        GaussControlTrace.statePacket
          (⟨B',ps.length,c,ps⟩ : GaussControlTrace.State m k) := by
  let start : Config := ⟨some (.header (.copyIn .scan)),
    eHeader (((),none),W.initial),S⟩
  obtain ⟨a,ha,w,hrun⟩ :=
    GaussStepPivotHeaderExactRun32.header_exact
      (List.replicate ps.length true) S h5 h31 h30 hempty
  let C := GaussStepPivotHeaderExactRun32.result
    (List.replicate ps.length true) S w
  have hrun' : run a start = C := hrun
  have h4' : C.stk 4 = GaussPhysical.encodeTypedMatrix B' :=
    (GaussStepPivotHeaderExactRun32.result_preserves _ S w 4
      (Or.inl (by decide)) (by decide) (by decide) (by decide)).trans h4
  have h5' : C.stk 5 = List.replicate ps.length true :=
    GaussPivotHeaderPreservesRow32.result5 _ S w
  have h6' : C.stk 6 = List.replicate c true :=
    (GaussStepPivotHeaderExactRun32.result_preserves _ S w 6
      (Or.inl (by decide)) (by decide) (by decide) (by decide)).trans h6
  have h24' : C.stk 24 = [] :=
    (GaussStepPivotHeaderExactRun32.result_preserves _ S w 24
      (Or.inr (by decide)) (by decide) (by decide) (by decide)).trans h24
  have h27' : C.stk 27 = SourceListEncoding.fields
      (ps.map GaussControlTrace.pivotPacket) :=
    (GaussStepPivotHeaderExactRun32.result_preserves _ S w 27
      (Or.inr (by decide)) (by decide) (by decide) (by decide)).trans h27
  have h30' : C.stk 30 =
      EthInapproximability.CurrentPaper.EncodedCommunication.natField
        ps.length := by
    rw [show C.stk 30 = SourceListMachineWriter.result false
      (List.replicate ps.length true) from
      GaussStepPivotHeaderExactRun32.result30 _ S w h30]
    simp [SourceListMachineWriter.result]
  have h31' : C.stk 31 = [] :=
    GaussStepPivotHeaderExactRun32.result31 _ S w
  have h7' : C.stk 7 = S 7 :=
    GaussStepPivotHeaderExactRun32.result_preserves _ S w 7
      (Or.inl (by decide)) (by decide) (by decide) (by decide)
  have ha' : a ≤ headerPhaseBound ps.length := by
    simpa [headerPhaseBound] using ha
  have hcharge' : ∀ j : Stack,
      (C.stk j).length ≤
        charge + GaussPivotClockGrowth32.pushConstant *
          (headerPhaseBound ps.length+1) := by
    intro j
    have hg := GaussPivotClockGrowth32.bank_growth_from_charge
      start a charge (by simpa [start] using hcharge) j
    rw [hrun'] at hg
    have hm := Nat.mul_le_mul_left
      GaussPivotClockGrowth32.pushConstant
      (show a ≤ headerPhaseBound ps.length+1 by omega)
    omega
  have hnext : run 1 C =
      ⟨some (.join .clear7),eJoin ((),none),C.stk⟩ := by
    change run 1 (GaussStepPivotHeaderExactRun32.result _ S w) = _
    rfl
  obtain ⟨b,hb,hend,hpacket⟩ :=
    GaussPivotJoinClock32.pivot_join_finish_bound
      B' ps.length c ps C.stk h4' h5' h6' h30' h27' h24' h31'
      (charge + GaussPivotClockGrowth32.pushConstant *
        (headerPhaseBound ps.length+1)) hcharge'
  have hb' : b ≤ GaussPivotJoinClock32.clock
      B' ps.length c ps S
      (charge + GaussPivotClockGrowth32.pushConstant *
        (headerPhaseBound ps.length+1)) := by
    simpa [GaussPivotJoinClock32.clock,
      GaussPivotJoinClock32.joinPhaseBound,h7'] using hb
  refine ⟨a+1+b, by dsimp [clock]; omega, ?_, ?_⟩
  · rw [show a+1+b = a+(1+b) by omega,
      run_add hrun' (1+b),run_add hnext b]
    exact hend
  · rw [show a+1+b = a+(1+b) by omega,
      run_add hrun' (1+b),run_add hnext b]
    exact hpacket

theorem header_join_finish_uniform {m k : Nat}
    (B' : Fin m → Fin k → ℚ) (c : Nat)
    (ps : List (Fin m × Fin k))
    (S : Stack → List Bool)
    (h4 : S 4 = GaussPhysical.encodeTypedMatrix B')
    (h5 : S 5 = List.replicate ps.length true)
    (h6 : S 6 = List.replicate c true)
    (h27 : S 27 = SourceListEncoding.fields
      (ps.map GaussControlTrace.pivotPacket))
    (h24 : S 24 = []) (h30 : S 30 = []) (h31 : S 31 = [])
    (hempty : ∀ j : Fin W.stackCount,
      S (GaussPivotFraming32.locate j) = [])
    (charge : Nat) (hcharge : ∀ j : Stack, (S j).length ≤ charge) :
    ∃ t ≤ uniformClock B' c ps charge,
      (run t ⟨some (.header (.copyIn .scan)),
        eHeader (((),none),W.initial),S⟩).l = some .done ∧
      (run t ⟨some (.header (.copyIn .scan)),
        eHeader (((),none),W.initial),S⟩).stk 14 =
        GaussControlTrace.statePacket
          (⟨B',ps.length,c,ps⟩ : GaussControlTrace.State m k) := by
  obtain ⟨t,ht,he,hp⟩ := header_join_finish_bound
    B' c ps S h4 h5 h6 h27 h24 h30 h31 hempty charge hcharge
  exact ⟨t,ht.trans (clock_le_uniform B' c ps S charge (hcharge 7)),he,hp⟩

#print axioms header_join_finish_bound
#print axioms header_join_finish_uniform

end
end CurrentAdditive.GaussPivotHeaderJoinClock32
