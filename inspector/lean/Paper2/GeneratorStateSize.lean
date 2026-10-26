import Paper2.GeneratorSize
import Paper2.GeneratorResult
import Mathlib.Tactic

/-! Concrete storage potential for the actual first-order generator stack. -/

namespace Paper2.GeneratorStateSize

open Paper2.GeneratorCode Paper2.GeneratorSerialization
  Paper2.GeneratorSize

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def potential (s : State) : Nat := codesSize s.todo + s.output.length

theorem admin_potential_le (s t : State) (h : admin s = some t) :
    potential t ≤ potential s := by
  rcases s with ⟨todo, out⟩
  cases todo with
  | nil => simp [admin] at h
  | cons c cs =>
      cases c with
      | emit bits =>
          simp only [admin, Option.some.injEq] at h
          subst t
          simp [potential, codesSize, codeSize, List.length_append]
          omega
      | ticket n =>
          cases n with
          | zero =>
              simp only [admin, Option.some.injEq] at h
              subst t
              simp [potential, codesSize, codeSize]
          | succ n => simp [admin] at h
      | bit => simp [admin] at h
      | append left right =>
          simp only [admin, Option.some.injEq] at h
          subst t
          simp [potential, codesSize, codeSize]
          omega
      | branch3 n a b first second third =>
          cases n with
          | zero =>
              simp only [admin, Option.some.injEq] at h
              subst t
              simp [potential, codesSize, codeSize]
          | succ n => simp [admin] at h

theorem normalize_potential_le (s : State) :
    potential (GeneratorCode.normalize s) ≤ potential s := by
  induction s using GeneratorCode.normalize.induct with
  | case1 s h => rw [GeneratorCode.normalize]; split <;> simp_all
  | case2 s t h ih =>
      rw [GeneratorCode.normalize]
      split
      · simp_all
      · rename_i t' ht
        have he : t' = t := Option.some.inj (ht.symm.trans h)
        subst t'
        exact ih.trans (admin_potential_le s t h)

theorem advance_potential_le (s : State) (hr : admin s = none)
    (i : Fin (request s)) : potential (advance s i.val) ≤ potential s := by
  rcases s with ⟨todo, out⟩
  cases todo with
  | nil => simp [advance, potential]
  | cons c cs =>
      cases c with
      | emit bits => simp [admin] at hr
      | append left right => simp [admin] at hr
      | ticket n =>
          cases n with
          | zero => simp [admin] at hr
          | succ n =>
              have hi : i.val < n+1 := by simpa [request] using i.isLt
              simp [advance, potential, codesSize, codeSize,
                List.length_append, List.length_replicate]
              omega
      | bit =>
          simp [advance, potential, codesSize, codeSize,
            List.length_append]
          omega
      | branch3 n a b first second third =>
          cases n with
          | zero => simp [admin] at hr
          | succ n =>
              by_cases h₁ : i.val < a
              · simp [advance, potential, codesSize, codeSize, h₁]
                omega
              · by_cases h₂ : i.val < b
                · simp [advance, potential, codesSize, codeSize, h₁, h₂]
                  omega
                · simp [advance, potential, codesSize, codeSize, h₁, h₂]

theorem nextRaw_potential_le {M : Nat} (s : BoundedState M)
    (i : Fin (den s)) : potential (nextRaw s i) ≤ potential s.val := by
  exact (advance_potential_le (normalize s.val) (normalize_ready s.val) i).trans
    (normalize_potential_le s.val)

theorem next_potential_le {M : Nat} (s : BoundedState M)
    (i : Fin (den s)) : potential (next s i).val ≤ potential s.val :=
  nextRaw_potential_le s i

theorem list_length_le_codesSize (cs : List Code) : cs.length ≤ codesSize cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp only [List.length_cons, codesSize]
      have hnode := nodes_pos c
      have hsize := nodes_le_codeSize c
      omega

theorem stateSize_le_potential (s : State) :
    stateSize s ≤ 2*potential s + 2 := by
  have hl := list_length_le_codesSize s.todo
  simp only [stateSize, potential]
  omega

theorem initial_potential (c : Code) : potential (initial c) = codeSize c := by
  simp [initial, potential, codesSize]

/-- This relation is generated only by the actual administrative update and
accepted finite ticket update of the first-order interpreter. -/
inductive Trace (c : Code) : State → Prop where
  | initial : Trace c (GeneratorCode.initial c)
  | admin {s t : State} (hs : Trace c s) (h : GeneratorCode.admin s = some t) :
      Trace c t
  | accepted {s : State} (hs : Trace c s) (hr : GeneratorCode.admin s = none)
      (i : Fin (GeneratorCode.request s)) : Trace c (GeneratorCode.advance s i.val)

theorem trace_potential_le (c : Code) (s : State) (h : Trace c s) :
    potential s ≤ codeSize c := by
  induction h with
  | initial => rw [initial_potential]
  | admin hs ht ih => exact (admin_potential_le _ _ ht).trans ih
  | accepted hs hr i ih => exact (advance_potential_le _ hr i).trans ih

theorem trace_output_length_le (c : Code) (s : State) (h : Trace c s) :
    s.output.length ≤ codeSize c := by
  have hp := trace_potential_le c s h
  dsimp [potential] at hp
  omega

theorem codeSize_ge_three (c : Code) : 3 ≤ codeSize c := by
  cases c <;> simp [codeSize] <;> omega

theorem trace_stateSize_le (c : Code) (s : State) (h : Trace c s) :
    (encodeState s).length ≤ 3*codeSize c := by
  have hp := trace_potential_le c s h
  have hs := stateSize_le_potential s
  have hc := codeSize_ge_three c
  rw [encodeState_length]
  omega

theorem trace_normalize (c : Code) (s : State) (h : Trace c s) :
    Trace c (GeneratorCode.normalize s) := by
  induction s using GeneratorCode.normalize.induct with
  | case1 s hs =>
      rw [GeneratorCode.normalize]
      split <;> simp_all
  | case2 s t hs ih =>
      rw [GeneratorCode.normalize]
      split
      · simp_all
      · rename_i t' ht
        have he : t' = t := Option.some.inj (ht.symm.trans hs)
        subst t'
        exact ih (Trace.admin h hs)

theorem trace_nextRaw {M : Nat} (c : Code) (s : BoundedState M)
    (h : Trace c s.val) (i : Fin (den s)) : Trace c (nextRaw s i) := by
  exact Trace.accepted (trace_normalize c s.val h)
    (normalize_ready s.val) i

def initialBounded {M : Nat} (c : Code)
    (hc : (meaning c).maxAlphabet ≤ M) : BoundedState M :=
  ⟨initial c, by simpa only [initial_meaning] using hc⟩

inductive Reachable {M : Nat} (s₀ : BoundedState M) : BoundedState M → Prop where
  | refl : Reachable s₀ s₀
  | step {s : BoundedState M} (hs : Reachable s₀ s)
      (i : Fin (den s)) : Reachable s₀ (GeneratorCode.next s i)

theorem reachable_potential_le {M : Nat} (s₀ s : BoundedState M)
    (h : Reachable s₀ s) : potential s.val ≤ potential s₀.val := by
  induction h with
  | refl => exact le_refl _
  | step hs i ih => exact (next_potential_le _ i).trans ih

theorem reachable_initial_stateSize_le {M : Nat} (c : Code)
    (hc : (meaning c).maxAlphabet ≤ M) (s : BoundedState M)
    (h : Reachable (initialBounded c hc) s) :
    (encodeState s.val).length ≤ 2*codeSize c+2 := by
  have hp := reachable_potential_le (initialBounded c hc) s h
  have hs := stateSize_le_potential s.val
  rw [encodeState_length]
  dsimp [initialBounded] at hp
  rw [initial_potential] at hp
  omega

theorem capped_potential_le {M : Nat} (B R : Nat)
    (hMB : Nat.clog 2 M ≤ B) (N : Nat)
    (s : BoundedState M) (t : CappedSampler.Adaptive.Tape B R N)
    (u : BoundedState M) (hu : capped B R hMB N s t = some u) :
    potential u.val ≤ potential s.val := by
  induction N generalizing s u with
  | zero =>
      simp only [capped, CappedSampler.Adaptive.run, Option.some.injEq] at hu
      subst u
      exact le_refl _
  | succ N ih =>
      change (CappedSampler.runWideBits (den s) B R (den_width hMB s) t.1).bind
        (fun i => capped B R hMB N (GeneratorCode.next s i) t.2) = some u at hu
      cases hd : CappedSampler.runWideBits (den s) B R (den_width hMB s) t.1 with
      | none => simp [hd] at hu
      | some i =>
          simp only [hd, Option.bind_some] at hu
          exact (ih (GeneratorCode.next s i) t.2 u hu).trans
            (next_potential_le s i)

theorem capped_initial_stateSize_le {M : Nat} (B R : Nat)
    (hMB : Nat.clog 2 M ≤ B) (N : Nat) (c : Code)
    (hc : (meaning c).maxAlphabet ≤ M)
    (t : CappedSampler.Adaptive.Tape B R N) (u : BoundedState M)
    (hu : capped B R hMB N (initialBounded c hc) t = some u) :
    (encodeState u.val).length ≤ 2*codeSize c+2 := by
  have hp := capped_potential_le B R hMB N (initialBounded c hc) t u hu
  have hs := stateSize_le_potential u.val
  rw [encodeState_length]
  dsimp [initialBounded] at hp
  rw [initial_potential] at hp
  omega

theorem capped_initial_trace {M : Nat} (B R : Nat)
    (hMB : Nat.clog 2 M ≤ B) (N : Nat) (c : Code)
    (hc : (meaning c).maxAlphabet ≤ M)
    (t : CappedSampler.Adaptive.Tape B R N) (u : BoundedState M)
    (hu : capped B R hMB N (initialBounded c hc) t = some u) :
    Trace c u.val := by
  have main {s : BoundedState M} (hs : Trace c s.val)
      (N : Nat) (t : CappedSampler.Adaptive.Tape B R N)
      (u : BoundedState M) (hu : capped B R hMB N s t = some u) :
      Trace c u.val := by
    induction N generalizing s u with
    | zero =>
        simp only [capped, CappedSampler.Adaptive.run, Option.some.injEq] at hu
        subst u
        exact hs
    | succ N ih =>
        change (CappedSampler.runWideBits (den s) B R (den_width hMB s) t.1).bind
          (fun i => capped B R hMB N (GeneratorCode.next s i) t.2) = some u at hu
        cases hd : CappedSampler.runWideBits (den s) B R (den_width hMB s) t.1 with
        | none => simp [hd] at hu
        | some i =>
            simp only [hd, Option.bind_some] at hu
            exact ih (trace_nextRaw c s hs i) t.2 u hu
  exact main Trace.initial N t u hu

theorem capped_initial_stateSize_le_three {M : Nat} (B R : Nat)
    (hMB : Nat.clog 2 M ≤ B) (N : Nat) (c : Code)
    (hc : (meaning c).maxAlphabet ≤ M)
    (t : CappedSampler.Adaptive.Tape B R N) (u : BoundedState M)
    (hu : capped B R hMB N (initialBounded c hc) t = some u) :
    (encodeState u.val).length ≤ 3*codeSize c :=
  trace_stateSize_le c u.val
    (capped_initial_trace B R hMB N c hc t u hu)

/-- Instrumentation of the actual capped recursion: record the state before
each finite-alphabet request, including the state where rejection aborts. -/
def visited {M : Nat} (B R : Nat) (hMB : Nat.clog 2 M ≤ B) :
    (N : Nat) → BoundedState M → CappedSampler.Adaptive.Tape B R N → List State
  | 0, s, _ => [s.val]
  | N+1, s, t =>
      s.val ::
        match CappedSampler.runWideBits (den s) B R (den_width hMB s) t.1 with
        | none => []
        | some i => visited B R hMB N (GeneratorCode.next s i) t.2

theorem visited_trace {M : Nat} (B R : Nat) (hMB : Nat.clog 2 M ≤ B)
    (N : Nat) (c : Code) (s : BoundedState M)
    (hs : Trace c s.val) (t : CappedSampler.Adaptive.Tape B R N)
    (v : State) (hv : v ∈ visited B R hMB N s t) : Trace c v := by
  induction N generalizing s with
  | zero =>
      simp only [visited, List.mem_singleton] at hv
      subst v
      exact hs
  | succ N ih =>
      simp only [visited, List.mem_cons] at hv
      rcases hv with hfirst | htail
      · simpa [hfirst] using hs
      · cases hd : CappedSampler.runWideBits (den s) B R (den_width hMB s) t.1 with
        | none => simp [hd] at htail
        | some i =>
            simp only [hd] at htail
            exact ih (GeneratorCode.next s i) (trace_nextRaw c s hs i) t.2 htail

theorem visited_initial_stateSize_le_three {M : Nat} (B R : Nat)
    (hMB : Nat.clog 2 M ≤ B) (N : Nat) (c : Code)
    (hc : (meaning c).maxAlphabet ≤ M)
    (t : CappedSampler.Adaptive.Tape B R N)
    (v : State)
    (hv : v ∈ visited B R hMB N (initialBounded c hc) t) :
    (encodeState v).length ≤ 3*codeSize c :=
  trace_stateSize_le c v
    (visited_trace B R hMB N c (initialBounded c hc) Trace.initial t v hv)

theorem read_length_le (s : State) (bits : List Bool)
    (h : GeneratorCode.read s = some bits) : bits.length ≤ potential s := by
  have hn := normalize_potential_le s
  unfold GeneratorCode.read at h
  cases ht : (GeneratorCode.normalize s).todo with
  | nil =>
      have hb : (GeneratorCode.normalize s).output = bits := by
        simpa [readReady, ht] using h
      have hlen : bits.length ≤ potential (GeneratorCode.normalize s) := by
        simp [potential, ht, hb, codesSize]
      exact hlen.trans hn
  | cons c cs => simp [readReady, ht] at h

theorem run_output_length_le {M : Nat} (B R : Nat)
    (hMB : Nat.clog 2 M ≤ B) (N : Nat)
    (s : BoundedState M) (t : CappedSampler.Adaptive.Tape B R N)
    (bits : List Bool) (h : run B R hMB N s t = some bits) :
    bits.length ≤ potential s.val := by
  unfold run at h
  cases hu : capped B R hMB N s t with
  | none => simp [hu] at h
  | some u =>
      simp only [hu, Option.bind_some] at h
      exact (read_length_le u.val bits h).trans
        (capped_potential_le B R hMB N s t u hu)

theorem run_initial_output_le_codeSize {M : Nat} (B R : Nat)
    (hMB : Nat.clog 2 M ≤ B) (N : Nat) (c : Code)
    (hc : (meaning c).maxAlphabet ≤ M)
    (t : CappedSampler.Adaptive.Tape B R N)
    (bits : List Bool)
    (h : run B R hMB N (initialBounded c hc) t = some bits) :
    bits.length ≤ codeSize c := by
  have hp := run_output_length_le B R hMB N (initialBounded c hc) t bits h
  dsimp [initialBounded] at hp
  simpa only [initial_potential] using hp

#print axioms admin_potential_le
#print axioms normalize_potential_le
#print axioms advance_potential_le
#print axioms next_potential_le
#print axioms stateSize_le_potential
#print axioms reachable_initial_stateSize_le
#print axioms trace_stateSize_le
#print axioms trace_output_length_le
#print axioms trace_normalize
#print axioms capped_initial_trace
#print axioms capped_initial_stateSize_le
#print axioms capped_initial_stateSize_le_three
#print axioms visited_initial_stateSize_le_three
#print axioms run_initial_output_le_codeSize

end Paper2.GeneratorStateSize
