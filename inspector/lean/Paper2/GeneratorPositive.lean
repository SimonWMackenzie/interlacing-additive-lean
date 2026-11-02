import Paper2.GeneratorFullSample
import Paper2.GeneratorStateSize
import Mathlib.Tactic

/-! Structural positivity for the exact first-order scheduled generators. -/

namespace Paper2.GeneratorPositive

open Paper2.GeneratorCode Paper2.GeneratorSource
  Paper2.GeneratorFullSample

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def Positive : Code → Prop
  | .emit _ => True
  | .ticket n => 0 < n
  | .bit => True
  | .append a b => Positive a ∧ Positive b
  | .branch3 n _ _ a b c => 0 < n ∧ Positive a ∧ Positive b ∧ Positive c

theorem positive_copies (n : Nat) (c : Code) (hc : Positive c) :
    Positive (copies n c) := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨hc, ih⟩

theorem positive_outer (q₁ q₂ s : Nat) (c : Code)
    (hq₂ : 0 < q₂) (hc : Positive c) :
    Positive (outerCode q₁ q₂ s c) := by
  exact ⟨hq₂, positive_copies _ c hc⟩

theorem positive_raw (q₁ q₂ s : Nat) (c : Code)
    (hq₂ : 0 < q₂) (hc : Positive c) :
    Positive (rawCode q₁ q₂ s c) := by
  exact ⟨positive_copies _ c hc,
    positive_copies _ _ (positive_outer q₁ q₂ s c hq₂ hc)⟩

theorem positive_fixedTail (q₁ q₂ s : Nat) (c : Code)
    (hq₂ : 0 < q₂) (hc : Positive c) :
    Positive (fixedTailCode q₁ q₂ s c) :=
  positive_copies _ _ (positive_outer q₁ q₂ s c hq₂ hc)

theorem positive_tagged (q₁ q₂ s : Nat) (c : Code)
    (hq₂ : 0 < q₂) (hc : Positive c) :
    Positive (taggedCode q₁ q₂ s c) := by
  exact ⟨by decide,
    ⟨trivial, positive_raw q₁ q₂ s c hq₂ hc⟩,
    ⟨trivial, positive_fixedTail q₁ q₂ s c hq₂ hc⟩,
    ⟨trivial, positive_outer q₁ q₂ s c hq₂ hc⟩⟩

theorem positive_template (q₁ q₂ : Nat) (c : Code)
    (hq₁ : 0 < q₁) (hc : Positive c) :
    Positive (templateCode q₁ q₂ c) := by
  exact positive_copies _ _ ⟨hq₁, hc⟩

theorem positive_templateRow (q₁ q₂ s : Nat) (c : Code)
    (hq₁ : 0 < q₁) (hs : 0 < s) (hc : Positive c) :
    Positive (templateRowCode q₁ q₂ s c) := by
  exact ⟨hs, positive_template q₁ q₂ c hq₁ hc⟩

theorem positive_vertices (n s : Nat) (hn : 0 < n) (hs : 0 < s) :
    Positive (vertexLabelsCode (V := Fin n) s) := by
  simp [vertexLabelsCode, Positive, Fintype.card_fin]
  omega

theorem positive_auxiliaries (s : Nat) (hs : 4 ≤ s) :
    Positive (auxiliaryLabelsCode s) := by
  simp [auxiliaryLabelsCode, Positive]
  omega

theorem positive_rows (n q₁ q₂ s : Nat) (c : Code)
    (hn : 0 < n) (hq₁ : 0 < q₁) (hs : 4 ≤ s)
    (hc : Positive c) :
    Positive (graphRowsCode (V := Fin n) q₁ q₂ s c) := by
  exact ⟨by decide,
    ⟨trivial, positive_templateRow q₁ q₂ s c hq₁ (by omega) hc⟩,
    ⟨trivial, ⟨positive_vertices n s hn (by omega), hc⟩⟩,
    ⟨trivial, ⟨positive_auxiliaries s hs, hc⟩⟩⟩

theorem positive_recursiveCodes (n s q₁ q₂ w Q : Nat)
    (row₀ col₀ : Code) (k : Nat)
    (hn : 0 < n) (hs : 4 ≤ s) (hq₁ : 0 < q₁)
    (hq₂ : 0 < q₂) (hw : 0 < w) (hQ : 0 < Q)
    (hr₀ : Positive row₀) (hc₀ : Positive col₀) :
    let pair := recursiveCodes n s q₁ q₂ w Q row₀ col₀ k
    Positive pair.1 ∧ Positive pair.2 := by
  induction k with
  | zero => exact ⟨hr₀, hc₀⟩
  | succ k ih =>
      change Positive (copies Q (.append (.ticket w)
          (taggedCode q₁ q₂ s
            (recursiveCodes n s q₁ q₂ w Q row₀ col₀ k).2))) ∧
        Positive (.append (.ticket Q)
          (copies w (graphRowsCode (V := Fin n) q₁ q₂ s
            (recursiveCodes n s q₁ q₂ w Q row₀ col₀ k).1)))
      exact ⟨positive_copies _ _ ⟨hw, positive_tagged q₁ q₂ s _ hq₂ ih.2⟩,
        ⟨hQ, positive_copies _ _
          (positive_rows n q₁ q₂ s _ hn hq₁ hs ih.1)⟩⟩

theorem positive_seedRecursiveCodes (n p s q₁ q₂ w Q k : Nat)
    (hn : 0 < n) (hp : 0 < p) (hs : 4 ≤ s)
    (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hw : 0 < w) (hQ : 0 < Q) :
    let pair := seedRecursiveCodes n p s q₁ q₂ w Q k
    Positive pair.1 ∧ Positive pair.2 := by
  exact positive_recursiveCodes n s q₁ q₂ w Q
    (copies p .bit) (.ticket p) k hn hs hq₁ hq₂ hw hQ
    (positive_copies p .bit trivial) hp

theorem positive_scheduledCodes {n m : Nat} [NeZero n]
    (L Δ : Nat) (γ : ℚ) (k : Nat) :
    let pair := scheduledCodes n m L Δ γ k
    Positive pair.1 ∧ Positive pair.2 := by
  have hp : 0 < LookupSeed.width L := by unfold LookupSeed.width; positivity
  have hs : 4 ≤ SourceProfileParameters.width L := by
    have h := SourceProfileParameters.width_admissible L
    omega
  have hq₁ : 0 < SourceProfileParameters.width L - 2 := by omega
  have hq₂ : 0 < SourceProfileParameters.outerWidth L := by
    unfold SourceProfileParameters.outerWidth
    positivity
  have hw : 0 < ParameterizedCanonicalSource.restorationWidth L := by
    unfold ParameterizedCanonicalSource.restorationWidth
      RestorationWidthScheduleScratch.width
    positivity
  have hQ : 0 < ParameterizedCanonicalSource.coverWidth n m L Δ γ := by
    rw [show ParameterizedCanonicalSource.coverWidth n m L Δ γ =
      2 ^ ParameterizedCanonicalSource.coverDepth n m L Δ γ from
        Paper2.SourceOverheadBounds.actualQ_pow
          (V := Fin n) (E := Fin m) L γ Δ]
    positivity
  exact positive_seedRecursiveCodes n (LookupSeed.width L)
    (SourceProfileParameters.width L) (SourceProfileParameters.width L - 2)
    (SourceProfileParameters.outerWidth L)
    (ParameterizedCanonicalSource.restorationWidth L)
    (ParameterizedCanonicalSource.coverWidth n m L Δ γ)
    k (NeZero.pos n) hp hs hq₁ hq₂ hw hQ

theorem positive_scheduledSampleCode {n m : Nat} [NeZero n]
    (L Δ : Nat) (γ : ℚ) (k mX mY : Nat) :
    Positive (scheduledSampleCode n m L Δ γ k mX mY) := by
  have hp := positive_scheduledCodes (n := n) (m := m) L Δ γ k
  rw [scheduledSampleCode_columns_first]
  exact ⟨positive_copies mY _ hp.2, positive_copies mX _ hp.1⟩

def PositiveState (s : State) : Prop := ∀ c ∈ s.todo, Positive c

theorem positive_initial (c : Code) (hc : Positive c) :
    PositiveState (initial c) := by
  simpa [PositiveState, initial] using hc

theorem admin_positive_cases (s t : State) (hp : PositiveState s)
    (h : admin s = some t) :
    (∃ bits cs, s.todo = .emit bits :: cs ∧
      t = ⟨cs, s.output ++ bits⟩) ∨
    (∃ left right cs, s.todo = .append left right :: cs ∧
      t = ⟨left :: right :: cs, s.output⟩) := by
  rcases s with ⟨todo, out⟩
  cases todo with
  | nil => simp [admin] at h
  | cons c cs =>
      have hc : Positive c := hp c (by simp)
      cases c with
      | emit bits =>
          left
          have ht : t = ⟨cs, out ++ bits⟩ := by simpa [admin] using h.symm
          exact ⟨bits, cs, rfl, ht⟩
      | append left right =>
          right
          have ht : t = ⟨left :: right :: cs, out⟩ := by
            simpa [admin] using h.symm
          exact ⟨left, right, cs, rfl, ht⟩
      | ticket n =>
          cases n with
          | zero => simp [Positive] at hc
          | succ n => simp [admin] at h
      | bit => simp [admin] at h
      | branch3 n a b first second third =>
          cases n with
          | zero => simp [Positive] at hc
          | succ n => simp [admin] at h

theorem admin_positive (s t : State) (hp : PositiveState s)
    (h : admin s = some t) : PositiveState t := by
  rcases s with ⟨todo, out⟩
  cases todo with
  | nil => simp [admin] at h
  | cons c cs =>
      have hc : Positive c := hp c (by simp)
      have hcs : ∀ d ∈ cs, Positive d := by
        intro d hd
        exact hp d (by simp [hd])
      cases c with
      | emit bits =>
          simp only [admin, Option.some.injEq] at h
          subst t
          exact hcs
      | append left right =>
          simp only [admin, Option.some.injEq] at h
          subst t
          intro d hd
          simp only [List.mem_cons] at hd
          rcases hd with rfl | rfl | hd
          · exact hc.1
          · exact hc.2
          · exact hcs d hd
      | ticket n =>
          cases n with
          | zero => simp [Positive] at hc
          | succ n => simp [admin] at h
      | bit => simp [admin] at h
      | branch3 n a b first second third =>
          cases n with
          | zero => simp [Positive] at hc
          | succ n => simp [admin] at h

theorem normalize_positive (s : State) (hp : PositiveState s) :
    PositiveState (GeneratorCode.normalize s) := by
  induction s using GeneratorCode.normalize.induct with
  | case1 s h => rw [GeneratorCode.normalize]; split <;> simp_all
  | case2 s t h ih =>
      rw [GeneratorCode.normalize]
      split
      · simp_all
      · rename_i t' ht
        have he : t' = t := Option.some.inj (ht.symm.trans h)
        subst t'
        exact ih (admin_positive s t hp h)

def DrawHead : Code → Prop
  | .ticket (_n+1) => True
  | .bit => True
  | .branch3 (_n+1) _ _ _ _ _ => True
  | _ => False

theorem ready_positive_draw (s : State) (hp : PositiveState s)
    (hr : admin s = none) (hne : s.todo ≠ []) :
    ∃ c cs, s.todo = c :: cs ∧ DrawHead c := by
  rcases s with ⟨todo, out⟩
  cases todo with
  | nil => contradiction
  | cons c cs =>
      refine ⟨c, cs, rfl, ?_⟩
      have hc : Positive c := hp c (by simp)
      cases c with
      | emit bits => simp [admin] at hr
      | append left right => simp [admin] at hr
      | ticket n =>
          cases n with
          | zero => simp [Positive] at hc
          | succ n => trivial
      | bit => trivial
      | branch3 n a b first second third =>
          cases n with
          | zero => simp [Positive] at hc
          | succ n => trivial

theorem advance_positive (s : State) (hp : PositiveState s)
    (hr : admin s = none) (i : Fin (request s)) :
    PositiveState (advance s i.val) := by
  rcases s with ⟨todo, out⟩
  cases todo with
  | nil => simpa [advance] using hp
  | cons c cs =>
      have hc : Positive c := hp c (by simp)
      have hcs : ∀ d ∈ cs, Positive d := by
        intro d hd
        exact hp d (by simp [hd])
      cases c with
      | emit bits => simp [admin] at hr
      | append left right => simp [admin] at hr
      | ticket n =>
          cases n with
          | zero => simp [Positive] at hc
          | succ n => simpa [advance, PositiveState] using hcs
      | bit => simpa [advance, PositiveState] using hcs
      | branch3 n a b first second third =>
          cases n with
          | zero => simp [Positive] at hc
          | succ n =>
              by_cases h₁ : i.val < a
              · simpa [advance, PositiveState, h₁] using
                  (show ∀ d ∈ first :: cs, Positive d from by
                    intro d hd
                    simp only [List.mem_cons] at hd
                    rcases hd with rfl | hd
                    · exact hc.2.1
                    · exact hcs d hd)
              · by_cases h₂ : i.val < b
                · simpa [advance, PositiveState, h₁, h₂] using
                    (show ∀ d ∈ second :: cs, Positive d from by
                      intro d hd
                      simp only [List.mem_cons] at hd
                      rcases hd with rfl | hd
                      · exact hc.2.2.1
                      · exact hcs d hd)
                · simpa [advance, PositiveState, h₁, h₂] using
                    (show ∀ d ∈ third :: cs, Positive d from by
                      intro d hd
                      simp only [List.mem_cons] at hd
                      rcases hd with rfl | hd
                      · exact hc.2.2.2
                      · exact hcs d hd)

theorem nextRaw_positive {M : Nat} (s : BoundedState M)
    (hp : PositiveState s.val) (i : Fin (den s)) :
    PositiveState (nextRaw s i) := by
  exact advance_positive (GeneratorCode.normalize s.val)
    (normalize_positive s.val hp) (normalize_ready s.val) i

theorem next_positive {M : Nat} (s : BoundedState M)
    (hp : PositiveState s.val) (i : Fin (den s)) :
    PositiveState (GeneratorCode.next s i).val := nextRaw_positive s hp i

theorem capped_positive {M : Nat} (B R : Nat)
    (hMB : Nat.clog 2 M ≤ B) (N : Nat)
    (s : BoundedState M) (hp : PositiveState s.val)
    (t : CappedSampler.Adaptive.Tape B R N) (u : BoundedState M)
    (hu : capped B R hMB N s t = some u) : PositiveState u.val := by
  induction N generalizing s u with
  | zero =>
      simp only [capped, CappedSampler.Adaptive.run, Option.some.injEq] at hu
      subst u
      exact hp
  | succ N ih =>
      change (CappedSampler.runWideBits (den s) B R (den_width hMB s) t.1).bind
        (fun i => capped B R hMB N (GeneratorCode.next s i) t.2) = some u at hu
      cases hd : CappedSampler.runWideBits (den s) B R (den_width hMB s) t.1 with
      | none => simp [hd] at hu
      | some i =>
          simp only [hd, Option.bind_some] at hu
          exact ih (GeneratorCode.next s i) (next_positive s hp i) t.2 u hu

theorem visited_positive {M : Nat} (B R : Nat)
    (hMB : Nat.clog 2 M ≤ B) (N : Nat)
    (s : BoundedState M) (hp : PositiveState s.val)
    (t : CappedSampler.Adaptive.Tape B R N) (v : State)
    (hv : v ∈ Paper2.GeneratorStateSize.visited B R hMB N s t) :
    PositiveState v := by
  induction N generalizing s with
  | zero =>
      simp only [Paper2.GeneratorStateSize.visited, List.mem_singleton] at hv
      subst v
      exact hp
  | succ N ih =>
      simp only [Paper2.GeneratorStateSize.visited, List.mem_cons] at hv
      rcases hv with hfirst | htail
      · simpa [hfirst] using hp
      · cases hd : CappedSampler.runWideBits (den s) B R (den_width hMB s) t.1 with
        | none => simp [hd] at htail
        | some i =>
            simp only [hd] at htail
            exact ih (GeneratorCode.next s i) (next_positive s hp i) t.2 htail

theorem scheduledSample_initial_positive {n m : Nat} [NeZero n]
    (L Δ : Nat) (γ : ℚ) (k mX mY : Nat) :
    PositiveState (initial (scheduledSampleCode n m L Δ γ k mX mY)) :=
  positive_initial _ (positive_scheduledSampleCode L Δ γ k mX mY)

#print axioms positive_recursiveCodes
#print axioms positive_scheduledCodes
#print axioms positive_scheduledSampleCode
#print axioms admin_positive_cases
#print axioms normalize_positive
#print axioms ready_positive_draw
#print axioms next_positive
#print axioms capped_positive
#print axioms visited_positive
#print axioms scheduledSample_initial_positive

end Paper2.GeneratorPositive
