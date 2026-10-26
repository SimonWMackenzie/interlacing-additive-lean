import EthInapproximability.CurrentPaper.SourceListMachineOuterStep

/-! Sum-of-item-cost induction for the physical binary-count list loop. -/

namespace EthInapproximability.CurrentPaper.SourceListMachineOuter

open Turing TM2.Stmt BitMachine BitMachineEncoding EncodedCommunication

variable (M : Machine)

def joined (xs : List (List Bool)) (output : List Bool → List Bool) : List Bool :=
  (xs.map output).flatten

theorem joined_nil (output : List Bool → List Bool) : joined [] output = [] := rfl
theorem joined_cons (x : List Bool) (xs : List (List Bool))
    (output : List Bool → List Bool) :
    joined (x::xs) output = output x ++ joined xs output := rfl

theorem loop_items (xs : List (List Bool)) (output : List Bool → List Bool)
    (bound : List Bool → Nat)
    (hM : ∀ x ∈ xs, M.OutputsWithin x (output x) (bound x))
    (q accumulator : List Bool) (S : Stack M → List Bool)
    (hvalue : bitsValue q = xs.length)
    (hstate : LoopInvariant M S (SourceListEncoding.fields xs) q accumulator) :
    ∃ T : Stack M → List Bool, ∃ q' : List Bool,
      ∃ t ≤ SourceListMachineWork.work M xs output bound +
        xs.length * (4*q.length+7),
      LoopInvariant M T [] q' ((joined xs output).reverse ++ accumulator) ∧
      bitsValue q' = 0 ∧ q'.length = q.length ∧
      run M t (loopCfg M S) = loopCfg M T := by
  induction xs generalizing q accumulator S with
  | nil =>
      refine ⟨S,q,0,?_,?_,?_,rfl,rfl⟩
      · simp [SourceListMachineWork.work]
      · simpa only [joined_nil, List.reverse_nil, List.nil_append] using hstate
      · simpa using hvalue
  | cons x xs ih =>
      have hx := hM x (by simp)
      have htail : ∀ y ∈ xs, M.OutputsWithin y (output y) (bound y) := by
        intro y hy
        exact hM y (by simp [hy])
      cases hs : ProtocolBinaryCounter.subOne q with
      | none =>
          have hz := ProtocolBinaryCounter.subOne_spec q
          simp only [hs] at hz
          simp only [List.length_cons] at hvalue
          omega
      | some q₁ =>
          have hspec := ProtocolBinaryCounter.subOne_spec q
          simp only [hs] at hspec
          have hv : bitsValue q₁ = xs.length := by
            simp only [List.length_cons] at hvalue
            omega
          have hlength : q₁.length = q.length := hspec.2
          obtain ⟨T₁,t₁,ht₁,hst₁,hr₁⟩ := positive_step M S x (output x)
            (SourceListEncoding.fields xs) q q₁ accumulator (bound x)
            (by simpa only [SourceListEncoding.fields, List.append_assoc] using hstate) hs hx
          obtain ⟨T₂,q₂,t₂,ht₂,hst₂,hzero,hlen,hr₂⟩ :=
            ih htail q₁ ((output x).reverse ++ accumulator) T₁ hv hst₁
          refine ⟨T₂,q₂,t₁+t₂,?_,?_,hzero,?_,?_⟩
          · rw [hlength] at ht₂
            calc
              t₁+t₂ ≤ (4*q.length+7+SourceListMachineWork.itemCost M x
                (output x) (bound x)) +
                (SourceListMachineWork.work M xs output bound +
                  xs.length*(4*q.length+7)) := Nat.add_le_add ht₁ ht₂
              _ = SourceListMachineWork.work M (x::xs) output bound +
                    (x::xs).length*(4*q.length+7) := by
                  rw [SourceListMachineWork.work_cons, List.length_cons]
                  ring
          · simpa only [joined_cons, List.reverse_append, List.append_assoc]
              using hst₂
          · omega
          · exact (run_add M hr₁ t₂).trans hr₂

end EthInapproximability.CurrentPaper.SourceListMachineOuter
