import EthInapproximability.CurrentPaper.SourceListMachineOuterFinish

/-! Complete positive-input run of the physical framed-list controller. -/

namespace EthInapproximability.CurrentPaper.SourceListMachineOuter

open Turing TM2.Stmt BitMachine BitMachineEncoding EncodedCommunication

variable (M : Machine)

def canonicalBound (xs : List (List Bool)) (output : List Bool → List Bool)
    (bound : List Bool → Nat) : Nat :=
  5*xs.length.bits.length+7 +
  (SourceListMachineWork.work M xs output bound +
    xs.length*(4*xs.length.bits.length+7)) +
  (4*xs.length.bits.length+(natField xs.length ++ joined xs output).length+9)

theorem joined_length_le (xs : List (List Bool)) (output : List Bool → List Bool)
    (L : Nat) (h : ∀ x ∈ xs, (output x).length ≤ L) :
    (joined xs output).length ≤ xs.length*L := by
  induction xs with
  | nil => simp [joined]
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht : ∀ y ∈ xs, (output y).length ≤ L := by
        intro y hy
        exact h y (by simp [hy])
      rw [joined_cons, List.length_append, List.length_cons]
      have hi := ih ht
      rw [Nat.succ_mul]
      omega

theorem canonicalBound_le_count (xs : List (List Bool))
    (output : List Bool → List Bool) (bound : List Bool → Nat)
    (B L : Nat)
    (hitem : ∀ x ∈ xs,
      SourceListMachineWork.itemCost M x (output x) (bound x) ≤ B)
    (hout : ∀ x ∈ xs, (output x).length ≤ L) :
    canonicalBound M xs output bound ≤
      5*xs.length.bits.length+7 +
      (xs.length*B + xs.length*(4*xs.length.bits.length+7)) +
      (4*xs.length.bits.length + (natField xs.length).length + xs.length*L + 9) := by
  have hw := SourceListMachineWork.work_le_count M xs output bound B hitem
  have hl := joined_length_le xs output L hout
  unfold canonicalBound
  simp only [List.length_append]
  omega

/-- A source producer may instantiate these four *physical* envelopes using
the original SAT variable count `n`. The exponential number of branches
occurs as one multiplier, never as an argument of a polynomial. -/
theorem canonicalBound_le_source (xs : List (List Bool))
    (output : List Bool → List Bool) (bound : List Bool → Nat)
    (n : Nat) (branchCap digitCap itemEnvelope outputEnvelope : Nat → Nat)
    (hcount : xs.length ≤ branchCap n)
    (hdigits : xs.length.bits.length ≤ digitCap n)
    (hitem : ∀ x ∈ xs,
      SourceListMachineWork.itemCost M x (output x) (bound x) ≤ itemEnvelope n)
    (hout : ∀ x ∈ xs, (output x).length ≤ outputEnvelope n) :
    canonicalBound M xs output bound ≤
      branchCap n * (itemEnvelope n + 4*digitCap n+7+outputEnvelope n) +
        11*digitCap n+17 := by
  have hbase := canonicalBound_le_count M xs output bound
    (itemEnvelope n) (outputEnvelope n) hitem hout
  have hwork := Nat.mul_le_mul_right (itemEnvelope n) hcount
  have hcounter : xs.length*(4*xs.length.bits.length+7) ≤
      branchCap n*(4*digitCap n+7) :=
    Nat.mul_le_mul hcount (by omega)
  have houtlen := Nat.mul_le_mul_right (outputEnvelope n) hcount
  have hfield : (natField xs.length).length ≤ 2*digitCap n+1 := by
    simp only [natField, field_length]
    omega
  calc
    canonicalBound M xs output bound ≤
        5*xs.length.bits.length+7 +
        (xs.length*itemEnvelope n + xs.length*(4*xs.length.bits.length+7)) +
        (4*xs.length.bits.length + (natField xs.length).length +
          xs.length*outputEnvelope n + 9) := hbase
    _ ≤ branchCap n*itemEnvelope n + branchCap n*(4*digitCap n+7) +
          branchCap n*outputEnvelope n + 11*digitCap n+17 := by omega
    _ = branchCap n*(itemEnvelope n+4*digitCap n+7+outputEnvelope n) +
          11*digitCap n+17 := by ring

/-- Every physically framed positive input is processed by a single fixed
finite-stack program. The only per-branch cost is the explicit sum. -/
theorem canonical_raw_run (xs : List (List Bool))
    (output : List Bool → List Bool) (bound : List Bool → Nat)
    (hM : ∀ x ∈ xs, M.OutputsWithin x (output x) (bound x)) :
    ∃ c : Config M, ∃ t ≤ canonicalBound M xs output bound,
      run M t (rawInit (.inl (.inr 0) : Stack M) (adminLabel M .startInit)
        (initialControl M) (SourceListEncoding.encode xs)) = c ∧
      c.l = none ∧ c.stk (.inr 2) = natField xs.length ++ joined xs output := by
  let S₀ := initBanks M (SourceListEncoding.encode xs)
    {input := SourceListEncoding.fields xs, count := xs.length.bits,
      output := (natField xs.length).reverse} []
  obtain ⟨a, ha, hra⟩ := init_to_counter M xs.length (SourceListEncoding.fields xs)
  have hcount : S₀ (.inr 0) = xs.length.bits := init_count M _ _ []
  have htemp : S₀ (.inr 1) = [] := init_temp M _ _ []
  change run M a _ = counterFrame M S₀ _ at hra
  rw [counterFrame_initial M S₀ xs.length.bits hcount htemp] at hra
  change run M a (rawInit _ _ _ (SourceListEncoding.encode xs)) =
    loopCfg M S₀ at hra
  obtain ⟨T,q,t,ht,hT,hzero,hlen,hrt⟩ := loop_items M xs output bound hM
    xs.length.bits (natField xs.length).reverse S₀ (bitsValue_bits xs.length)
    (initial_invariant M xs)
  let acc := (joined xs output).reverse ++ (natField xs.length).reverse
  obtain ⟨c,u,hu,hru,hhalt,hout⟩ := zero_finish M T q acc hT hzero
  have hr := (run_add M ((run_add M hra t).trans hrt) u).trans hru
  have hword : acc.reverse = natField xs.length ++ joined xs output := by
    simp [acc, List.reverse_append]
  refine ⟨c,a+t+u,?_,hr,hhalt,?_⟩
  · unfold canonicalBound
    rw [hlen] at hu
    have hacc : acc.length = (natField xs.length ++ joined xs output).length := by
      simp [acc, List.length_append, Nat.add_comm]
    rw [hacc] at hu
    omega
  · exact hout.trans hword

theorem canonical_outputsWithin (xs : List (List Bool))
    (output : List Bool → List Bool) (bound : List Bool → Nat)
    (hM : ∀ x ∈ xs, M.OutputsWithin x (output x) (bound x)) :
    (machine M).OutputsWithin (SourceListEncoding.encode xs)
      (natField xs.length ++ joined xs output) (canonicalBound M xs output bound) := by
  obtain ⟨c,t,ht,hr,hhalt,hout⟩ := canonical_raw_run M xs output bound hM
  apply outputsWithin_of_raw_run (.inl (.inr 0) : Stack M) (.inr (2 : Fin 3))
    (adminLabel M .startInit) (initialControl M) (program M)
    (SourceListEncoding.encode xs) (natField xs.length ++ joined xs output)
    t (canonicalBound M xs output bound) ht
  · change (run M t _).l = none
    rw [hr]
    exact hhalt
  · change (run M t _).stk (.inr 2) = _
    rw [hr]
    exact hout

end EthInapproximability.CurrentPaper.SourceListMachineOuter
