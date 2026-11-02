import EthInapproximability.CurrentPaper.CNFValidatorSteps
import EthInapproximability.CurrentPaper.EncodedGraphMachineCorrectness

/-! # Composition of the CNF validator's field-reading blocks (unit 4, B4-S1)

The admitted `EncodedGraphMachineCorrectness` block compositions, restated for
the literal `CNFValidator` controller: canonical field read, strict budget
check (`count ≤ |input|` for the clause count, `index < n` for a literal) and
bounded conversion to unary. The machine-independent header length lemma is
reused by exact name.
-/

namespace EthInapproximability.CurrentPaper.CNFValidator.Correctness

open Turing BitMachineEncoding EthInapproximability.CurrentPaper.CNFValidator
open EthInapproximability.CurrentPaper.CNFValidator.Steps

/-- A reached rejection label, with the saved input and output bank intact. -/
def RejectFrame (d : Data) (c : Config) : Prop :=
  c.l = some (outer .reject) ∧ c.stk 6 = d.original ∧ c.stk 13 = d.output

theorem rejected_cfg (v : Control) (d : Data) :
    RejectFrame d (cfg (some (outer .reject)) v d) := ⟨rfl, rfl, rfl⟩

def conversionBudget (q cap : List Bool) : Nat :=
  (cap.length + 1) * (4 * q.length + 5) + q.length + cap.length + 4

/-- The bounded conversion and explicit cleanup produce exactly the unary
field value when it fits. Oversized fields reach the rejection label within
the same quadratic bound, without iterating the represented number. -/
theorem conversion (v : Control) (d : Data) :
    ∃ t ≤ conversionBudget d.value d.cap, ∃ c,
      run t (cfg (some (.inr (.inl .zeroScan))) (v.1, (none, false), v.2.2)
        {d with work := [], unary := []}) = c ∧
      if EncodedCommunication.bitsValue d.value ≤ d.cap.length then
        ∃ u : ProtocolBoundedUnary.Control,
          c = cfg (some (outer .store)) (setPop (v.1, u, v.2.2) none)
            {d with value := [], cap := [], work := [],
                    unary := List.replicate (EncodedCommunication.bitsValue d.value) true}
      else RejectFrame d c := by
  obtain ⟨t, ht, c, he, hout, hv, hw, hb⟩ := bounded_run v d
  let vd : Control := (v.1, c.var, v.2.2)
  let dd := boundData d c
  have hu : dd.unary = ProtocolBoundedUnary.result d.value d.cap [] := hout
  have hl : dd.value.length = d.value.length := hv
  have hc : dd.cap.length ≤ d.cap.length := hb
  have hz : dd.work = [] := hw
  by_cases hok : EncodedCommunication.bitsValue d.value ≤ d.cap.length
  · have hu' : dd.unary = true :: List.replicate (EncodedCommunication.bitsValue d.value) true := by
      simpa [ProtocolBoundedUnary.result, hok, Nat.min_eq_left hok] using hu
    have hed : dd = {dd with unary := true :: List.replicate (EncodedCommunication.bitsValue d.value) true} := by
      rw [← hu']
    have hstep := afterBound_good vd dd (List.replicate (EncodedCommunication.bitsValue d.value) true)
    rw [← hed] at hstep
    let clean : Data := {dd with unary := List.replicate (EncodedCommunication.bitsValue d.value) true}
    have hrun := (run_add he 1).trans (run_succ hstep 0)
    have hclean := cleanup_run (setPop vd (some true)) clean
    refine ⟨t + 1 + (dd.value.length + dd.cap.length + dd.work.length + 3), ?_, _,
      (run_add hrun _).trans hclean, ?_⟩
    · simp only [conversionBudget, hl, hz, List.length_nil]
      omega
    · simp only [hok, ↓reduceIte]
      refine ⟨c.var, ?_⟩
      rfl
  · have hu' : dd.unary = false :: List.replicate d.cap.length true := by
      simpa [ProtocolBoundedUnary.result, hok, Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge hok))] using hu
    have hed : dd = {dd with unary := false :: List.replicate d.cap.length true} := by
      rw [← hu']
    have hstep := afterBound_bad vd dd (List.replicate d.cap.length true)
    rw [← hed] at hstep
    refine ⟨t + 1, ?_, _, (run_add he 1).trans (run_succ hstep 0), ?_⟩
    · unfold conversionBudget
      omega
    · simp only [hok, ↓reduceIte]
      exact ⟨rfl, rfl, rfl⟩

theorem conversionBudget_bound {q cap : List Bool} {L : Nat}
    (hq : q.length ≤ L) (hc : cap.length ≤ L) :
    conversionBudget q cap ≤ 12 * (L + 1)^2 := by
  unfold conversionBudget
  have hp := Nat.mul_le_mul (Nat.add_le_add_right hc 1)
    (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hq) 5)
  nlinarith

def headerDestination (v : Control) (d : Data) : Config :=
  if field v = .count then
    cfg (some (.inr (.inl .zeroScan))) (v.1, (none, false), (setPop v (some true)).2.2) d
  else cfg (some (outer .copyVertices)) (setPop v (some true)) d

theorem read_header (v : Control) (d : Data) :
    ∃ t ≤ 2 * d.input.length + 3, ∃ c,
      run t (cfg (some (.inl .scan)) ((none, none), v.2) {d with saved := [], value := []}) = c ∧
      match ProtocolBinaryHeader.readChecked none d.input with
      | none => RejectFrame d c
      | some (bs, rest) => ∃ u : ProtocolBinaryHeader.Control,
          c = headerDestination (u, v.2) {d with input := rest, saved := [], value := bs} := by
  obtain ⟨t, ht, c, he, hp⟩ := header_run v d
  let vd : Control := (c.var, v.2)
  let dd := headerData d c
  cases hr : ProtocolBinaryHeader.readChecked none d.input with
  | none =>
      have hv : dd.value = [false] := by
        simpa [ProtocolBinaryHeader.Post, hr, dd, headerData] using hp.2
      have hd : dd = {dd with value := false :: []} := by rw [← hv]
      have hs := afterHeader_bad vd dd []
      rw [← hd] at hs
      refine ⟨t + 1, by omega, _, (run_add he 1).trans (run_succ hs 0), ?_⟩
      exact ⟨rfl, rfl, rfl⟩
  | some p =>
      obtain ⟨bs, rest⟩ := p
      have hh : c.stk 0 = rest ∧ c.stk 1 = [] ∧ c.stk 2 = true :: bs := by
        simpa [ProtocolBinaryHeader.Post, hr] using hp.2
      have hd : dd = {d with input := rest, saved := [], value := true :: bs} := by
        simp [dd, headerData, hh.1, hh.2.1, hh.2.2]
      have hs := afterHeader_good vd {d with input := rest, saved := []} bs
      have hs' : advance program (cfg (some (outer .afterHeader)) vd dd) =
          headerDestination vd {d with input := rest, saved := [], value := bs} := by
        rw [hd]
        exact hs
      refine ⟨t + 1, by omega, _, (run_add he 1).trans (run_succ hs' 0), c.var, rfl⟩

/-- For a literal index, the budget is exactly one less than the variable
count. The zero-variable case rejects before starting binary conversion. -/
theorem endpoint_budget (n : Nat) (v : Control) (d : Data) :
    ∃ t ≤ 2 * n + 3, ∃ c,
      run t (cfg (some (outer .copyVertices)) v
        {d with vertices := List.replicate n true, scratch := [], cap := []}) = c ∧
      if n = 0 then RejectFrame d c else
        c = cfg (some (.inr (.inl .zeroScan)))
          (v.1, (none, false), (setPop v (some true)).2.2)
          {d with vertices := List.replicate n true, scratch := [], cap := List.replicate (n - 1) true} := by
  have hc := copy_budget_run n v d
  cases n with
  | zero =>
      have hs := endpointCap_nil (setPop v none) {d with vertices := [], scratch := []}
      refine ⟨3, le_rfl, _, (run_add hc 1).trans (run_succ hs 0), ?_⟩
      simp only [↓reduceIte]
      exact ⟨rfl, rfl, rfl⟩
  | succ n =>
      have hs := endpointCap_cons true (List.replicate n true) (setPop v none)
        {d with vertices := List.replicate (n + 1) true, scratch := []}
      refine ⟨2 * (n + 1) + 2 + 1, by omega, _,
        (run_add hc 1).trans (run_succ hs 0), ?_⟩
      simp only [Nat.add_eq_zero_iff, Nat.succ_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
      rfl

def entryData (v : Control) (d : Data) (n : Nat) : Data :=
  {d with saved := [], cap := if field v = .count then d.cap else [], work := [],
          unary := [], vertices := List.replicate n true, scratch := []}

def storeData (d : Data) (n k : Nat) : Data :=
  {d with saved := [], value := [], cap := [], work := [],
          unary := List.replicate k true, vertices := List.replicate n true, scratch := []}

def Fits (v : Control) (d : Data) (n k : Nat) : Prop :=
  if field v = .count then k ≤ d.cap.length else k < n

instance (v : Control) (d : Data) (n k : Nat) : Decidable (Fits v d n k) := by
  unfold Fits
  infer_instance

def StoreFrame (v : Control) (d : Data) (n k : Nat) (c : Config) : Prop :=
  ∃ w : Control, field w = field v ∧ c = cfg (some (outer .store)) w (storeData d n k)

theorem prepared_conversion (v : Control) (d : Data) (n L : Nat)
    (hq : d.value.length ≤ L) (hn : n ≤ L) (hcap : d.cap.length ≤ L) :
    ∃ t ≤ 16 * (L + 1)^2, ∃ c,
      run t (headerDestination v (entryData v d n)) = c ∧
      if Fits v d n (EncodedCommunication.bitsValue d.value) then
        StoreFrame v d n (EncodedCommunication.bitsValue d.value) c else RejectFrame d c := by
  by_cases hf : field v = .count
  · let vd := setPop v (some true)
    let dd := entryData v d n
    obtain ⟨t, ht, c, he, hp⟩ := conversion vd dd
    have hinit : headerDestination v dd =
        cfg (some (.inr (.inl .zeroScan))) (vd.1, (none, false), vd.2.2)
          {dd with work := [], unary := []} := by
      simp only [headerDestination, hf, ↓reduceIte]
      rfl
    have hbound : conversionBudget dd.value dd.cap ≤ 12 * (L + 1)^2 := by
      apply conversionBudget_bound
      · exact hq
      · simpa [dd, entryData, hf] using hcap
    refine ⟨t, by omega, c, hinit ▸ he, ?_⟩
    simp only [Fits, hf, ↓reduceIte]
    by_cases hok : EncodedCommunication.bitsValue d.value ≤ d.cap.length
    · simp only [dd, entryData, hf, ↓reduceIte, hok] at hp
      simp only [hok, ↓reduceIte]
      obtain ⟨u, hu⟩ := hp
      exact ⟨setPop (vd.1, u, vd.2.2) none, rfl, hu⟩
    · simp only [dd, entryData, hf, ↓reduceIte, hok] at hp
      simp only [hok, ↓reduceIte]
      exact hp
  · let vd := setPop v (some true)
    let dd := entryData v d n
    obtain ⟨t, ht, c, he, hp⟩ := endpoint_budget n vd dd
    have hinit : headerDestination v dd =
        cfg (some (outer .copyVertices)) vd
          {dd with vertices := List.replicate n true, scratch := [], cap := []} := by
      simp only [headerDestination, hf, ↓reduceIte]
      simp only [dd, entryData, hf, ↓reduceIte]
      rfl
    rw [← hinit] at he
    cases n with
    | zero =>
        refine ⟨t, by nlinarith [Nat.zero_le ((L + 1)^2)], c, he, ?_⟩
        simpa [Fits, hf, RejectFrame, dd, entryData] using hp
    | succ n =>
        simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at hp
        let conv : Data := {dd with vertices := List.replicate (n + 1) true, scratch := [], cap := List.replicate n true}
        obtain ⟨u, hu, out, hrun, hpost⟩ := conversion vd conv
        have hs : c = cfg (some (.inr (.inl .zeroScan)))
            (vd.1, (none, false), vd.2.2) {conv with work := [], unary := []} := by
          rw [hp]
          rfl
        rw [hs] at he
        have hbound : conversionBudget conv.value conv.cap ≤ 12 * (L + 1)^2 := by
          apply conversionBudget_bound
          · exact hq
          · simp only [conv, List.length_replicate]
            omega
        refine ⟨t + u, by nlinarith [Nat.zero_le (L^2)], out, (run_add he u).trans hrun, ?_⟩
        have hfits : Fits v d (n + 1) (EncodedCommunication.bitsValue d.value) ↔
            EncodedCommunication.bitsValue conv.value ≤ conv.cap.length := by
          simp only [Fits, hf, ↓reduceIte, conv, dd, entryData, List.length_replicate]
          omega
        by_cases hok : Fits v d (n + 1) (EncodedCommunication.bitsValue d.value)
        · simp only [hfits.mp hok, ↓reduceIte] at hpost
          simp only [hok, ↓reduceIte]
          obtain ⟨w, hw⟩ := hpost
          refine ⟨setPop (vd.1, w, vd.2.2) none, rfl, ?_⟩
          exact hw
        · simp only [hfits.not.mp hok, ↓reduceIte] at hpost
          simp only [hok, ↓reduceIte]
          exact hpost

/-- A complete canonical field read, strict budget check, and conversion
to a unary value, stopping immediately before the field's storage loop. -/
theorem field_to_store (v : Control) (d : Data) (n L : Nat)
    (hinput : d.input.length ≤ L) (hn : n ≤ L) (hcap : d.cap.length ≤ L) :
    ∃ t ≤ 20 * (L + 1)^2, ∃ c,
      run t (cfg (some (.inl .scan)) ((none, none), v.2)
        {entryData v d n with value := []}) = c ∧
      match EncodedCommunication.readNat d.input with
      | none => RejectFrame d c
      | some (k, rest) => if Fits v d n k then
          StoreFrame v {d with input := rest} n k c else RejectFrame d c := by
  let dd := entryData v d n
  obtain ⟨t, ht, c, he, hp⟩ := read_header v dd
  have hi : {dd with saved := [], value := []} = {entryData v d n with value := []} := rfl
  rw [hi] at he
  cases hr : ProtocolBinaryHeader.readChecked none d.input with
  | none =>
      have hrn : EncodedCommunication.readNat d.input = none := by
        rw [← ProtocolBinaryHeader.readChecked_readNat, hr]
        rfl
      refine ⟨t, ?_, c, he, ?_⟩
      · change t ≤ 2 * d.input.length + 3 at ht
        nlinarith [Nat.zero_le (L^2)]
      · rw [hrn]
        simpa only [dd, entryData, hr] using hp
  | some p =>
      obtain ⟨bs, rest⟩ := p
      have hrn : EncodedCommunication.readNat d.input =
          some (EncodedCommunication.bitsValue bs, rest) := by
        rw [← ProtocolBinaryHeader.readChecked_readNat, hr]
        rfl
      have hbs : bs.length ≤ L := (Nat.le_add_right _ _).trans ((EncodedGraphMachineCorrectness.readChecked_lengths hr).trans hinput)
      have hp' : ∃ u : ProtocolBinaryHeader.Control,
          c = headerDestination (u, v.2) {dd with input := rest, saved := [], value := bs} := by
        simpa only [dd, entryData, hr] using hp
      obtain ⟨u, hu⟩ := hp'
      let ds : Data := {d with input := rest, value := bs}
      obtain ⟨t₂, ht₂, out, he₂, hp₂⟩ := prepared_conversion (u, v.2) ds n L hbs hn hcap
      have hstart : headerDestination (u, v.2) (entryData (u, v.2) ds n) =
          headerDestination (u, v.2) {dd with input := rest, saved := [], value := bs} := rfl
      rw [hstart, ← hu] at he₂
      refine ⟨t + t₂, ?_, out, (run_add he t₂).trans he₂, ?_⟩
      · change t ≤ 2 * d.input.length + 3 at ht
        nlinarith [Nat.zero_le (L^2)]
      · rw [hrn]
        exact hp₂

end EthInapproximability.CurrentPaper.CNFValidator.Correctness
