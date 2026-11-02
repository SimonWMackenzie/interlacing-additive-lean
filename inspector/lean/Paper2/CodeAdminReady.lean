import Paper2.CodeAdminNormalization

namespace Paper2.CodeAdminReady

open Turing
open EthInapproximability.CurrentPaper.BitMachineEncoding
open GeneratorCode GeneratorSerialization GeneratorStateSize GeneratorPositive
open CodeAdminNormalization

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- The actual natural halt of the administrative machine on a ready state.
The draw case retains its finite constructor tag and physically read operands. -/
def stopped (s : State) : CodeAdminMachine.Config :=
  match s.todo with
  | [] => CodeAdminMachine.cfg none ((none,none),none)
      [] [] [] [] [] [] [] s.output.reverse
  | c :: cs => CodeAdminMachine.cfg none
      ((none,some (CodeHeaderMachine.headerKind c)),none)
      (CodeHeaderMachine.headerTail c (todoWord cs))
      (CodeHeaderMachine.headerN c) (CodeHeaderMachine.headerA c)
      (CodeHeaderMachine.headerB c) [] (CodeHeaderMachine.headerWord c)
      [] s.output.reverse

def readyClock (s : State) : Nat :=
  match s.todo with
  | [] => 1
  | c :: _ => CodeHeaderMachine.headerCost c + 2

theorem draw_kind (c : Code) (h : DrawHead c) :
    CodeHeaderMachine.headerKind c ≠ .emit ∧
      CodeHeaderMachine.headerKind c ≠ .append := by
  cases c <;> simp_all [DrawHead, CodeHeaderMachine.headerKind]

theorem ready_halts (s : State) (hp : PositiveState s)
    (hr : admin s = none) :
    ∃ u ≤ readyClock s,
      ((advance CodeAdminMachine.program)^[u]) (stateCfg s) = stopped s := by
  by_cases hnil : s.todo = []
  · refine ⟨1, by simp [readyClock, hnil], ?_⟩
    simpa [stateCfg, todoWord, stopped, hnil] using
      CodeAdminMachine.start_empty s.output.reverse
  · obtain ⟨c,cs,hcs,hc⟩ := ready_positive_draw s hp hr hnil
    obtain ⟨he,ha⟩ := draw_kind c hc
    obtain ⟨u,hu,hur⟩ := CodeAdminMachine.draw_header c (todoWord cs)
      s.output.reverse he ha
    refine ⟨u, by simpa [readyClock,hcs] using hu, ?_⟩
    simpa [stateCfg,todoWord,stopped,hcs] using hur

theorem stopped_halted (s : State) : (stopped s).l = none := by
  cases hs : s.todo <;> simp [stopped, hs, CodeAdminMachine.cfg]

theorem draw_header_cost_le (c : Code) (h : DrawHead c) :
    CodeHeaderMachine.headerCost c ≤ codeSize c + 1 := by
  cases c <;> simp_all [DrawHead, CodeHeaderMachine.headerCost, codeSize] <;> omega

theorem readyClock_le (s : State) (hp : PositiveState s)
    (hr : admin s = none) : readyClock s ≤ potential s + 3 := by
  by_cases hnil : s.todo = []
  · simp [readyClock, hnil]
  · obtain ⟨c,cs,hcs,hc⟩ := ready_positive_draw s hp hr hnil
    have hh := draw_header_cost_le c hc
    simp only [readyClock,hcs]
    simp only [potential,hcs,codesSize]
    omega

/-- Unlike the preceding live normalization endpoint, this is an actual halt
of the same fixed machine. It executes no draw and leaves the actual header
available for the next physically composed subprogram. -/
theorem physical_ready_trace (c : Code) (s : State)
    (hp : PositiveState s) (ht : Trace c s) :
    ∃ u ≤ 13*(codeSize c+3)^2,
      ((advance CodeAdminMachine.program)^[u]) (stateCfg s) =
        stopped (GeneratorCode.normalize s) := by
  obtain ⟨a,ha,har⟩ := physical_normalize_trace c s hp ht
  have hpos := normalize_positive s hp
  have hready := GeneratorCode.normalize_ready s
  obtain ⟨b,hb,hbr⟩ := ready_halts (GeneratorCode.normalize s) hpos hready
  have hc := readyClock_le (GeneratorCode.normalize s) hpos hready
  have hn := normalize_potential_le s
  have hs := trace_potential_le c s ht
  refine ⟨b+a,?_,?_⟩
  · have hb' : b ≤ codeSize c+3 := by omega
    nlinarith [Nat.zero_le (codeSize c)]
  · rw [Function.iterate_add_apply, har, hbr]

theorem physical_ready_visited {M : Nat} (B R : Nat)
    (hMB : Nat.clog 2 M ≤ B) (N : Nat) (c : Code)
    (hc : (meaning c).maxAlphabet ≤ M) (hp : Positive c)
    (t : CappedSampler.Adaptive.Tape B R N) (v : State)
    (hv : v ∈ visited B R hMB N (initialBounded c hc) t) :
    ∃ u ≤ 13*(codeSize c+3)^2,
      ((advance CodeAdminMachine.program)^[u]) (stateCfg v) =
        stopped (GeneratorCode.normalize v) := by
  have hpos := visited_positive B R hMB N (initialBounded c hc)
    (positive_initial c hp) t v hv
  have htrace := visited_trace B R hMB N c (initialBounded c hc) Trace.initial t v hv
  exact physical_ready_trace c v hpos htrace

#print axioms ready_halts
#print axioms physical_ready_trace
#print axioms physical_ready_visited

end Paper2.CodeAdminReady
