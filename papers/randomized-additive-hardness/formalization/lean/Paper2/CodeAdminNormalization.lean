import Paper2.CodeAdminMachine
import Paper2.GeneratorPositive

namespace Paper2.CodeAdminNormalization

open Turing
open EthInapproximability.CurrentPaper.BitMachineEncoding
open GeneratorCode GeneratorSerialization GeneratorStateSize GeneratorPositive

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def todoWord (cs : List Code) : List Bool := cs.flatMap encodeCode

def stateCfg (s : State) : CodeAdminMachine.Config :=
  CodeAdminMachine.ready (todoWord s.todo) s.output.reverse

def stepClock (s : State) : Nat :=
  match s.todo with
  | .emit bits :: _ => 6*bits.length+18
  | .append _ _ :: _ => 13
  | _ => 0

theorem admin_run (s t : State) (hp : PositiveState s)
    (h : admin s = some t) :
    ∃ u ≤ stepClock s, ((advance CodeAdminMachine.program)^[u]) (stateCfg s) = stateCfg t := by
  rcases admin_positive_cases s t hp h with ⟨bits,cs,hs,rfl⟩ | ⟨a,b,cs,hs,rfl⟩
  · have hr := CodeAdminMachine.emit_operation bits (todoWord cs) s.output.reverse
    simpa only [stateCfg, stepClock, hs, todoWord, List.flatMap_cons,
      List.reverse_append] using hr
  · have hr := CodeAdminMachine.append_operation a b (todoWord cs) s.output.reverse
    simpa only [stateCfg, stepClock, hs, todoWord, List.flatMap_cons,
      List.append_assoc] using hr

def normalizationClock (s : State) : Nat :=
  match h : admin s with
  | none => 0
  | some t => stepClock s + normalizationClock t
termination_by weight s
decreasing_by exact admin_weight_lt s t h

theorem normalization_run (s : State) (hp : PositiveState s) :
    ∃ u ≤ normalizationClock s,
      ((advance CodeAdminMachine.program)^[u]) (stateCfg s) =
        stateCfg (GeneratorCode.normalize s) := by
  induction s using GeneratorCode.normalize.induct with
  | case1 s h =>
      refine ⟨0, Nat.zero_le _, ?_⟩
      rw [GeneratorCode.normalize]
      split <;> simp_all
  | case2 s t h ih =>
      obtain ⟨a,ha,har⟩ := admin_run s t hp h
      obtain ⟨b,hb,hbr⟩ := ih (admin_positive s t hp h)
      refine ⟨b+a, ?_, ?_⟩
      · rw [normalizationClock]
        split
        · simp_all
        · rename_i t' ht
          have he : t'=t := Option.some.inj (ht.symm.trans h)
          subst t'
          omega
      · have hn : GeneratorCode.normalize s = GeneratorCode.normalize t := by
          conv_lhs => rw [GeneratorCode.normalize]
          split
          · simp_all
          · rename_i t' ht
            have he : t'=t := Option.some.inj (ht.symm.trans h)
            subst t'
            rfl
        rw [Function.iterate_add_apply, har, hbr, hn]

theorem stepClock_le (s : State) : stepClock s ≤ 6*potential s+18 := by
  rcases s with ⟨todo,output⟩
  cases todo with
  | nil => simp [stepClock]
  | cons c cs =>
      cases c <;> simp [stepClock, potential, codesSize, codeSize] <;> omega

theorem normalizationClock_le (s : State) :
    normalizationClock s ≤ (6*potential s+18)*weight s := by
  induction s using GeneratorCode.normalize.induct with
  | case1 s h =>
      rw [normalizationClock]
      split <;> simp_all
  | case2 s t h ih =>
      have hp := admin_potential_le s t h
      have hw := admin_weight_lt s t h
      have hs := stepClock_le s
      have hb : normalizationClock t ≤ (6*potential s+18)*weight t :=
        ih.trans (Nat.mul_le_mul_right (weight t) (by omega))
      have hz : stepClock s + normalizationClock t ≤ (6*potential s+18)*weight s := by
        calc
          _ ≤ (6*potential s+18) + (6*potential s+18)*weight t := Nat.add_le_add hs hb
          _ = (6*potential s+18)*(weight t+1) := by ring
          _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
      rw [normalizationClock]
      split
      · simp_all
      · rename_i t' ht
        have he : t'=t := Option.some.inj (ht.symm.trans h)
        subst t'
        exact hz

theorem physical_normalize (s : State) (hp : PositiveState s) :
    ∃ u ≤ (6*potential s+18)*weight s,
      ((advance CodeAdminMachine.program)^[u]) (stateCfg s) =
        stateCfg (GeneratorCode.normalize s) := by
  obtain ⟨u,hu,hr⟩ := normalization_run s hp
  exact ⟨u,hu.trans (normalizationClock_le s),hr⟩

#print axioms admin_run
#print axioms physical_normalize

theorem physical_normalize_trace (c : Code) (s : State)
    (hp : PositiveState s) (ht : Trace c s) :
    ∃ u ≤ 12*(codeSize c+3)^2,
      ((advance CodeAdminMachine.program)^[u]) (stateCfg s) =
        stateCfg (GeneratorCode.normalize s) := by
  obtain ⟨u,hu,hr⟩ := physical_normalize s hp
  have hpot := trace_potential_le c s ht
  have hw := GeneratorSize.state_weight_le_stateSize s
  have hsize := stateSize_le_potential s
  have hweight : weight s ≤ 2*codeSize c+2 := by omega
  have hfac : 6*potential s+18 ≤ 6*codeSize c+18 := by omega
  have hmul := Nat.mul_le_mul hfac hweight
  refine ⟨u,hu.trans (hmul.trans ?_),hr⟩
  nlinarith

/-- Every actual pre-request state on every tape has a charged physical
administrative run. Rejection and padding remain tasks for the draw loop. -/
theorem physical_normalize_visited {M : Nat} (B R : Nat)
    (hMB : Nat.clog 2 M ≤ B) (N : Nat) (c : Code)
    (hc : (meaning c).maxAlphabet ≤ M) (hp : Positive c)
    (t : CappedSampler.Adaptive.Tape B R N) (v : State)
    (hv : v ∈ visited B R hMB N (initialBounded c hc) t) :
    ∃ u ≤ 12*(codeSize c+3)^2,
      ((advance CodeAdminMachine.program)^[u]) (stateCfg v) =
        stateCfg (GeneratorCode.normalize v) := by
  have hpos := visited_positive B R hMB N (initialBounded c hc)
    (positive_initial c hp) t v hv
  have htrace := visited_trace B R hMB N c (initialBounded c hc) Trace.initial t v hv
  exact physical_normalize_trace c v hpos htrace

#print axioms physical_normalize_visited

end Paper2.CodeAdminNormalization
