import EthInapproximability.CurrentPaper.SignedMidpointMachine
import EthInapproximability.CurrentPaper.SourceListOR

/-!
# Semantic bridge from the physical midpoint and OR programs

Source: frozen v8 `06-eth.tex`, proof of `thm:main`. The runtime clock here
is a mathematical fuel bound for already physically supplied answer and unary
cap banks. It does not manufacture either bank or claim an ordinary-input
solver. Those operational compositions remain separate obligations.
-/

namespace EthInapproximability.CurrentPaper.SignedMidpointSemantics

open EncodedETHTail SignedMidpointMachine

def fuel (answer cap : List Bool) : ℕ :=
  20 * (answer.length + 1) * (cap.length + 1) + 2

def result (answer cap : List Bool) : List Bool :=
  (SignedMidpointMachine.run (fuel answer cap)
    (SignedMidpointMachine.cfg (some (.inl .sign))
      (none, (none, false), none, none) answer cap [] [] [])).stk 4

private theorem halted_at_fuel {answer cap : List Bool} {t : ℕ}
    (ht : t ≤ fuel answer cap)
    (hh : (SignedMidpointMachine.run t
      (SignedMidpointMachine.cfg (some (.inl .sign))
        (none, (none, false), none, none) answer cap [] [] [])).l = none) :
    (SignedMidpointMachine.run (fuel answer cap)
      (SignedMidpointMachine.cfg (some (.inl .sign))
        (none, (none, false), none, none) answer cap [] [] [])).l = none := by
  obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le ht
  rw [hu, SignedMidpointMachine.run_add]
  have hs := BitMachineSubroutine.run_halted SignedMidpointMachine.program
    (SignedMidpointMachine.run t
      (SignedMidpointMachine.cfg (some (.inl .sign))
        (none, (none, false), none, none) answer cap [] [] [])) hh u
  change SignedMidpointMachine.run u
    (SignedMidpointMachine.run t
      (SignedMidpointMachine.cfg (some (.inl .sign))
        (none, (none, false), none, none) answer cap [] [] [])) = _ at hs
  rw [hs]
  exact hh

private theorem at_fuel {answer cap : List Bool} {decision : Bool}
    {t : ℕ} (ht : t ≤ fuel answer cap)
    (hh : (SignedMidpointMachine.run t
      (SignedMidpointMachine.cfg (some (.inl .sign))
        (none, (none, false), none, none) answer cap [] [] [])).l = none)
    (ho : (SignedMidpointMachine.run t
      (SignedMidpointMachine.cfg (some (.inl .sign))
        (none, (none, false), none, none) answer cap [] [] [])).stk 4 = [decision]) :
    result answer cap = [decision] := by
  obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le ht
  unfold result
  rw [hu, SignedMidpointMachine.run_add]
  have hs := BitMachineSubroutine.run_halted SignedMidpointMachine.program
    (SignedMidpointMachine.run t
      (SignedMidpointMachine.cfg (some (.inl .sign))
        (none, (none, false), none, none) answer cap [] [] [])) hh u
  change SignedMidpointMachine.run u
    (SignedMidpointMachine.run t
      (SignedMidpointMachine.cfg (some (.inl .sign))
        (none, (none, false), none, none) answer cap [] [] [])) = _ at hs
  rw [hs]
  exact ho

theorem result_encodeInteger (a : ℤ) (cap : List Bool) :
    result (encodeInteger a) cap =
      [decide (2 * a < (cap.length : ℤ))] := by
  cases a with
  | ofNat n =>
      obtain ⟨t, ht, hh, ho⟩ := SignedMidpointMachine.nonnegative_canonical n cap
      apply at_fuel (answer := encodeInteger (n : ℤ)) (cap := cap)
        (decision := decide (2 * (n : ℤ) < (cap.length : ℤ)))
        (t := t) (by unfold fuel; omega) hh ho
  | negSucc n =>
      obtain ⟨t, ht, hh, ho⟩ := SignedMidpointMachine.negative_canonical n cap
      apply at_fuel (answer := encodeInteger (Int.negSucc n)) (cap := cap)
        (decision := decide (2 * (Int.negSucc n) < (cap.length : ℤ)))
        (t := t) (by unfold fuel; omega) hh ho

theorem halt_encodeInteger (a : ℤ) (cap : List Bool) :
    (SignedMidpointMachine.run (fuel (encodeInteger a) cap)
      (SignedMidpointMachine.cfg (some (.inl .sign))
        (none, (none, false), none, none) (encodeInteger a) cap [] [] [])).l = none := by
  cases a with
  | ofNat n =>
      obtain ⟨t, ht, hh, _⟩ := SignedMidpointMachine.nonnegative_canonical n cap
      exact halted_at_fuel (answer := encodeInteger (n : ℤ)) (cap := cap)
        (t := t) (by unfold fuel; omega) hh
  | negSucc n =>
      obtain ⟨t, ht, hh, _⟩ := SignedMidpointMachine.negative_canonical n cap
      exact halted_at_fuel (answer := encodeInteger (Int.negSucc n)) (cap := cap)
        (t := t) (by unfold fuel; omega) hh

theorem branch_result (answer : List Bool → ℤ) (k : ℕ) (b : Branch) :
    result (encodeInteger (answer b.table))
      (List.replicate (2 * b.threshold + k) true) =
        [branchAccept answer k b] := by
  rw [result_encodeInteger]
  simp [branchAccept]

def branchBit (answer : List Bool → ℤ) (k : ℕ) (b : Branch) : Bool :=
  (result (encodeInteger (answer b.table))
    (List.replicate (2 * b.threshold + k) true)).headD false

theorem branchBit_correct (answer : List Bool → ℤ) (k : ℕ) (b : Branch) :
    branchBit answer k b = branchAccept answer k b := by
  simp only [branchBit, branch_result, List.headD_cons]

/-- Actual OR machine output agrees with the paper's semantic list decision
when its input is the mapper's canonical singleton encoding. No mapper runtime
or cap construction is hidden in this theorem. -/
theorem list_result_correct (input : List Bool) (branches : List Branch)
    (answer : List Bool → ℤ) (k A : ℕ)
    (herror : ∀ b ∈ branches, |answer b.table - (b.cost : ℤ)| ≤ (A : ℤ))
    (hgap : 2 * A < k)
    (hyes : input ∈ EncodedCNF.Language → ∃ b ∈ branches, b.cost ≤ b.threshold)
    (hno : input ∉ EncodedCNF.Language → ∀ b ∈ branches, b.cost = b.threshold + k) :
    SourceListOR.result
      (SourceListEncoding.encode
        ((branches.map (branchAccept answer k)).map fun bit => [bit])) =
      [satAnswer input] := by
  rw [SourceListOR.result_canonical]
  congr 1
  simpa only [List.any_map] using
    listAccept_correct input branches answer k A herror hgap hyes hno

theorem physical_bits_list_correct (input : List Bool) (branches : List Branch)
    (answer : List Bool → ℤ) (k A : ℕ)
    (herror : ∀ b ∈ branches, |answer b.table - (b.cost : ℤ)| ≤ (A : ℤ))
    (hgap : 2 * A < k)
    (hyes : input ∈ EncodedCNF.Language → ∃ b ∈ branches, b.cost ≤ b.threshold)
    (hno : input ∉ EncodedCNF.Language → ∀ b ∈ branches, b.cost = b.threshold + k) :
    SourceListOR.result
      (SourceListEncoding.encode
        ((branches.map (branchBit answer k)).map fun bit => [bit])) =
      [satAnswer input] := by
  have hf : branchBit answer k = branchAccept answer k := by
    funext b
    exact branchBit_correct answer k b
  rw [hf]
  exact list_result_correct input branches answer k A herror hgap hyes hno

end EthInapproximability.CurrentPaper.SignedMidpointSemantics
