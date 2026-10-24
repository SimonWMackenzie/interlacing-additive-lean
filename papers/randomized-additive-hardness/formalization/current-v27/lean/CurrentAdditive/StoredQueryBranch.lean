import CurrentAdditive.StoredQuery
import CurrentAdditive.OrdinaryBitBranch
import CurrentAdditive.GaussCellPolynomialClock

/-! A literal one-bit dispatch uses only the selected child's execution.
The other child is allowed to diverge on this request. The common clock is
a fixed polynomial chosen before any request or bit. -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace CurrentAdditive.StoredQuery
open EthInapproximability.CurrentPaper GaussCellPolynomialClock
noncomputable section

def singletonBit : List Bool → Option Bool
  | [b] => some b
  | _ => none

def branchResult (G A B : Query) (x : List Bool) : Option (List Bool) :=
  (G.result x).bind (fun bs => (singletonBit bs).bind
    (fun b => (if b then B else A).result x))

def invocation (A : Query) (n : Nat) :=
  OrdinaryBitBranch.invocationBound A.machine n (A.coefficient*(n+1)^A.degree)

theorem invocation_polynomial (A : Query) : PolynomialBound (fun _ n => invocation A n) := by
  exact uniform_invocation A.machine second
    (mul (constant A.coefficient) (power (GaussCellPolynomialClock.add second (constant 1)) A.degree))

def branchBudget (G A B : Query) (n : Nat) :=
  invocation G n+invocation A n+invocation B n+1

theorem branchBudget_polynomial (G A B : Query) : PolynomialBound (fun _ n => branchBudget G A B n) :=
  GaussCellPolynomialClock.add
    (GaussCellPolynomialClock.add (GaussCellPolynomialClock.add (invocation_polynomial G) (invocation_polynomial A))
    (invocation_polynomial B)) (constant 1)

def branchCoefficient (G A B : Query) := Classical.choose (branchBudget_polynomial G A B)
def branchDegree (G A B : Query) := Classical.choose (Classical.choose_spec (branchBudget_polynomial G A B))

theorem branch_outputs (G A B : Query) (x y : List Bool) (b : Bool)
    (hg : G.result x=some [b]) (hp : (if b then B else A).result x=some y) :
    (OrdinaryBitBranch.machine G.machine A.machine B.machine).OutputsWithin x y
      (branchCoefficient G A B*(x.length+1)^branchDegree G A B) := by
  let P := if b then B else A
  have hP := P.outputs x y hp
  have hselected : P.machine=OrdinaryBitBranch.selected A.machine B.machine b := by
    cases b <;> rfl
  have h := OrdinaryBitBranch.outputsWithin G.machine A.machine B.machine x y b
    (G.coefficient*(x.length+1)^G.degree) (P.coefficient*(x.length+1)^P.degree)
    (G.outputs x [b] hg) (by simpa only [hselected] using hP)
  apply BitMachine.outputsWithin_mono _ h
  have hcap := Classical.choose_spec (Classical.choose_spec (branchBudget_polynomial G A B)) 0 x.length
  have hmono : OrdinaryBitBranch.invocationBound G.machine x.length
      (G.coefficient*(x.length+1)^G.degree)+
      OrdinaryBitBranch.invocationBound (OrdinaryBitBranch.selected A.machine B.machine b)
        x.length (P.coefficient*(x.length+1)^P.degree)+1 ≤ branchBudget G A B x.length := by
    cases b <;> simp [P,branchBudget,invocation,OrdinaryBitBranch.selected] <;> omega
  exact hmono.trans (by simpa [branchCoefficient,branchDegree] using hcap)

def branch (G A B : Query) : Query where
  result := branchResult G A B
  machine := OrdinaryBitBranch.machine G.machine A.machine B.machine
  coefficient := branchCoefficient G A B
  degree := branchDegree G A B
  outputs x y h := by
    unfold branchResult at h
    cases hg : G.result x with
    | none => simp [hg] at h
    | some bs =>
      cases bs with
      | nil => simp [hg,singletonBit] at h
      | cons b rest =>
        cases rest with
        | nil =>
          have hp : (if b then B else A).result x=some y := by
            simpa [hg,singletonBit] using h
          exact branch_outputs G A B x y b hg hp
        | cons c rest => simp [hg,singletonBit] at h

theorem branch_result (G A B : Query) (x y : List Bool) (b : Bool)
    (hg : G.result x=some [b]) (hp : (if b then B else A).result x=some y) :
    (branch G A B).result x=some y := by
  simp only [branch,branchResult,hg,Option.bind_some,singletonBit]
  exact hp

end
end CurrentAdditive.StoredQuery

#print axioms CurrentAdditive.StoredQuery.branch
#print axioms CurrentAdditive.StoredQuery.branch_outputs
