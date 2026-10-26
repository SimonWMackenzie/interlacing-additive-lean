import EthInapproximability.CurrentPaper.EncodedGraphMachineCorrectness
import EthInapproximability.CurrentPaper.EncodedGraphMachineLoops

/-! # Total graph validation by the literal finite controller

Source: frozen v8 explicit graph encoding and bit-machine convention. This
module composes the previously checked field, storage and comparison runs.
-/

namespace EthInapproximability.CurrentPaper.EncodedGraphMachineTotal

open Turing BitMachineEncoding EncodedGraphMachine
open EncodedGraphMachineCorrectness EncodedGraphMachineLoops

theorem field_run (f : Field) (v : Control) (hf : field v = f)
    (d : Data) (n L : Nat)
    (hinput : d.input.length ≤ L) (hn : n ≤ L) (hcap : d.cap.length ≤ L) :
    ∃ t ≤ 22 * (L + 1)^2, ∃ c,
      run t (cfg (some (.inl .scan)) ((none, none), v.2)
        {entryData v d n with value := []}) = c ∧
      match EncodedCommunication.readNat d.input with
      | none => RejectFrame d c
      | some (k, rest) => if Fits v d n k then
          ∃ w : Control, field w = field (storeControl f v) ∧
            (f = .left → w.1 = (none, none)) ∧
            c = cfg (some (storeNext f)) w
              (EncodedGraphMachineLoops.storeData f k
                (EncodedGraphMachineCorrectness.storeData {d with input := rest} n k))
        else RejectFrame d c := by
  obtain ⟨t, ht, c, he, hp⟩ := field_to_store v d n L hinput hn hcap
  cases hr : EncodedCommunication.readNat d.input with
  | none => exact ⟨t, by omega, c, he, by simpa [hr] using hp⟩
  | some p =>
    obtain ⟨k, rest⟩ := p
    by_cases hok : Fits v d n k
    · simp only [hr, hok, ↓reduceIte] at hp
      obtain ⟨w, hw, hc⟩ := hp
      rw [hc] at he
      have hwf : field w = f := hw.trans hf
      have hs := store_run f (List.replicate k true) w hwf
        (EncodedGraphMachineCorrectness.storeData {d with input := rest} n k)
      simp only [List.length_replicate] at hs
      have hk : k ≤ L := by
        by_cases hfc : field v = .count
        · have hh : k ≤ d.cap.length := by simpa [Fits, hfc] using hok
          exact hh.trans hcap
        · have hh : k < n := by simpa [Fits, hfc] using hok
          omega
      refine ⟨t + (k + 1), by nlinarith [Nat.zero_le (L^2)], _,
        (run_add he _).trans hs, ?_⟩
      simp only [hr, hok, ↓reduceIte]
      refine ⟨storeControl f w, ?_, ?_, rfl⟩
      · cases f <;> simpa [storeControl, field, setPop] using hw
      · intro hh
        rw [hh]
        rfl
    · exact ⟨t, by omega, c, he, by simpa [hr, hok] using hp⟩

def edgeData (bits original : List Bool) (n count left : Nat := 0) : Data :=
  {input := bits, original := original, vertices := List.replicate n true,
    edges := List.replicate count true, left := List.replicate left true}

theorem readNat_length {bits rest : List Bool} {n : Nat}
    (h : EncodedCommunication.readNat bits = some (n, rest)) : rest.length ≤ bits.length := by
  have he := congrArg List.length (EncodedCommunication.readNat_sound h)
  simp only [List.length_append] at he
  omega

theorem left_run (v : Control) (hf : field v = .left)
    (bits original : List Bool) (n count L : Nat)
    (hinput : bits.length ≤ L) (hn : n ≤ L) :
    ∃ t ≤ 22 * (L + 1)^2, ∃ c,
      run t (cfg (some (.inl .scan)) ((none, none), v.2)
        (edgeData bits original n count)) = c ∧
      match EncodedCommunication.readNat bits with
      | none => RejectFrame (edgeData bits original n count) c
      | some (k, rest) => if k < n then
          ∃ w : Control, field w = .right ∧ w.1 = (none, none) ∧
            c = cfg (some (.inl .scan)) w (edgeData rest original n count k)
        else RejectFrame (edgeData bits original n count) c := by
  have hh := field_run .left v hf (edgeData bits original n count) n L hinput hn
    (by simp [edgeData])
  have hi : {entryData v (edgeData bits original n count) n with value := []} =
      edgeData bits original n count := by
    simp [entryData, edgeData]
  rw [hi] at hh
  have hf' : v.2.2.1 = .left := hf
  simpa [Fits, hf, EncodedGraphMachineLoops.storeData,
    EncodedGraphMachineCorrectness.storeData, storeControl, storeNext, edgeData,
    field, hf', List.replicate_zero] using hh

theorem right_run (v : Control) (hf : field v = .right)
    (bits original : List Bool) (n count u L : Nat)
    (hinput : bits.length ≤ L) (hn : n ≤ L) :
    ∃ t ≤ 22 * (L + 1)^2, ∃ c,
      run t (cfg (some (.inl .scan)) ((none, none), v.2)
        (edgeData bits original n count u)) = c ∧
      match EncodedCommunication.readNat bits with
      | none => RejectFrame (edgeData bits original n count u) c
      | some (k, rest) => if k < n then
          ∃ w : Control, field w = .right ∧
            c = cfg (some (outer .compare)) w
              {edgeData rest original n count u with right := List.replicate k true}
        else RejectFrame (edgeData bits original n count u) c := by
  have hh := field_run .right v hf (edgeData bits original n count u) n L hinput hn
    (by simp [edgeData])
  have hi : {entryData v (edgeData bits original n count u) n with value := []} =
      edgeData bits original n count u := by
    simp [entryData, edgeData]
  rw [hi] at hh
  have hf' : v.2.2.1 = .right := hf
  simpa [Fits, hf, EncodedGraphMachineLoops.storeData,
    EncodedGraphMachineCorrectness.storeData, storeControl, storeNext, edgeData,
    field, hf', List.replicate_zero, setPop] using hh

theorem edge_loop (v : Control) (bits original : List Bool) (n count L : Nat)
    (hinput : bits.length ≤ L) (hn : n ≤ L) :
    ∃ t ≤ (count + 1) * (50 * (L + 1)^2), ∃ c,
      run t (cfg (some (outer .edges)) v (edgeData bits original n count)) = c ∧
      match EncodedGraphBounded.readCheckedEdges n count bits with
      | none => RejectFrame (edgeData bits original n count) c
      | some (_, rest) => ∃ w : Control,
          c = cfg (some (outer .finalCheck)) w (edgeData rest original n 0) := by
  induction count generalizing v bits with
  | zero =>
      refine ⟨1, by nlinarith [Nat.zero_le (L^2)],
        cfg (some (outer .finalCheck)) (setPop v none) (edgeData bits original n 0), ?_, ?_⟩
      · simpa [edgeData] using run_succ (edges_nil v (edgeData bits original n 0)) 0
      · exact ⟨setPop v none, rfl⟩
  | succ count ih =>
      let vl : Control := ((none, none), v.2.1, .left, some true, v.2.2.2.2)
      have hs : advance program
          (cfg (some (outer .edges)) v (edgeData bits original n (count + 1))) =
          cfg (some (.inl .scan)) vl (edgeData bits original n count) := by
        simpa [edgeData, List.replicate_succ] using
          edges_cons true (List.replicate count true) v (edgeData bits original n count)
      obtain ⟨t₁, ht₁, c₁, he₁, hp₁⟩ := left_run vl rfl bits original n count L hinput hn
      have he₁' : run (t₁ + 1)
          (cfg (some (outer .edges)) v (edgeData bits original n (count + 1))) = c₁ :=
        (run_succ hs t₁).trans he₁
      cases h₁ : EncodedCommunication.readNat bits with
      | none =>
          refine ⟨t₁ + 1, ?_, c₁, he₁', ?_⟩
          · nlinarith [Nat.zero_le (L^2), Nat.zero_le (count * (50 * (L + 1)^2))]
          · simpa [EncodedGraphBounded.readCheckedEdges, h₁, RejectFrame, edgeData] using hp₁
      | some pair₁ =>
        obtain ⟨a, tail₁⟩ := pair₁
        by_cases ha : a < n
        · simp only [h₁, ha, ↓reduceIte] at hp₁
          obtain ⟨w₁, hw₁, hw₁header, hc₁⟩ := hp₁
          rw [hc₁] at he₁'
          have hw₁eq : ((none, none), w₁.2) = w₁ := by
            rw [← hw₁header]
          obtain ⟨t₂, ht₂, c₂, he₂, hp₂⟩ := right_run w₁ hw₁ tail₁ original
            n count a L ((readNat_length h₁).trans hinput) hn
          rw [hw₁eq] at he₂
          have he₂' := (run_add he₁' t₂).trans he₂
          cases h₂ : EncodedCommunication.readNat tail₁ with
          | none =>
              refine ⟨t₁ + 1 + t₂, ?_, c₂, he₂', ?_⟩
              · nlinarith [Nat.zero_le (L^2), Nat.zero_le (count * (50 * (L + 1)^2))]
              · simpa [EncodedGraphBounded.readCheckedEdges, h₁, h₂, ha,
                  RejectFrame, edgeData] using hp₂
          | some pair₂ =>
            obtain ⟨b, tail₂⟩ := pair₂
            by_cases hb : b < n
            · simp only [h₂, hb, ↓reduceIte] at hp₂
              obtain ⟨w₂, hw₂, hc₂⟩ := hp₂
              rw [hc₂] at he₂'
              by_cases hab : a = b
              · subst b
                have hc := compare_eq a w₂ (edgeData tail₂ original n count)
                have hc' : run (a + 1)
                    (cfg (some (outer .compare)) w₂
                      {edgeData tail₂ original n count a with right := List.replicate a true}) =
                    cfg (some (outer .reject)) (setPop₂ (setPop w₂ none) none)
                      (edgeData tail₂ original n count) := by
                  simpa [edgeData] using hc
                refine ⟨t₁ + 1 + t₂ + (a + 1), ?_, _,
                  (run_add he₂' _).trans hc', ?_⟩
                · nlinarith [Nat.zero_le (L^2), Nat.zero_le (count * (50 * (L + 1)^2))]
                · simp [EncodedGraphBounded.readCheckedEdges, h₁, h₂, ha, RejectFrame,
                    cfg, Data.stacks, edgeData]
              · have hcompare : ∃ tc ≤ L + 1, ∃ wc : Control,
                    run tc (cfg (some (outer .compare)) w₂
                      {edgeData tail₂ original n count a with right := List.replicate b true}) =
                      cfg (some (outer .edges)) wc (edgeData tail₂ original n count) := by
                  rcases lt_or_gt_of_ne hab with hlt | hgt
                  · refine ⟨b + 1, by omega, setPop₂ (setPop w₂ none) (some true), ?_⟩
                    simpa [edgeData] using compare_lt a b hlt w₂ (edgeData tail₂ original n count)
                  · refine ⟨a + 1, by omega, setPop₂ (setPop w₂ none) none, ?_⟩
                    simpa [edgeData] using compare_gt a b hgt w₂ (edgeData tail₂ original n count)
                obtain ⟨tc, htc, wc, hec⟩ := hcompare
                have hec' := (run_add he₂' tc).trans hec
                obtain ⟨ti, hti, ci, hei, hpi⟩ := ih wc tail₂
                  ((readNat_length h₂).trans ((readNat_length h₁).trans hinput))
                refine ⟨t₁ + 1 + t₂ + tc + ti, ?_, ci,
                  (run_add hec' ti).trans hei, ?_⟩
                · nlinarith [Nat.zero_le (L^2)]
                · cases hr : EncodedGraphBounded.readCheckedEdges n count tail₂ with
                  | none =>
                    simpa [EncodedGraphBounded.readCheckedEdges, h₁, h₂, ha, hb, hab,
                      hr, RejectFrame, edgeData] using hpi
                  | some p =>
                    simpa [EncodedGraphBounded.readCheckedEdges, h₁, h₂, ha, hb, hab,
                      hr] using hpi
            · refine ⟨t₁ + 1 + t₂, ?_, c₂, he₂', ?_⟩
              · nlinarith [Nat.zero_le (L^2), Nat.zero_le (count * (50 * (L + 1)^2))]
              · simpa [EncodedGraphBounded.readCheckedEdges, h₁, h₂, ha, hb,
                  RejectFrame, edgeData] using hp₂
        · refine ⟨t₁ + 1, ?_, c₁, he₁', ?_⟩
          · nlinarith [Nat.zero_le (L^2), Nat.zero_le (count * (50 * (L + 1)^2))]
          · simpa [EncodedGraphBounded.readCheckedEdges, h₁, ha, RejectFrame, edgeData] using hp₁

end EthInapproximability.CurrentPaper.EncodedGraphMachineTotal
