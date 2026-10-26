import CurrentAdditive.GaussFourOperands64
import EthInapproximability.CurrentPaper.BitMachine

/-! A uniform clock from the initial bank for the actual four-fetch circuit.
The replay below retains the real intermediate configurations, rather than
placing arbitrary banks in the clock formula. -/

namespace CurrentAdditive.GaussFourFetchEnvelope64

noncomputable section

set_option maxRecDepth 2048
set_option maxHeartbeats 1800000

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.GaussFourOperands64

abbrev Bank := Fin 64

def rawPushBound {K L V : Type*} [Fintype L]
    (P : L → TM2.Stmt (fun _ : K => Bool) L V) : Nat :=
  ∑ l : L, BitMachine.pushBound (P l)

theorem advance_length {K L V : Type*} [DecidableEq K] [Fintype L]
    (P : L → TM2.Stmt (fun _ : K => Bool) L V)
    (c : TM2.Cfg (fun _ : K => Bool) L V) (j : K) :
    (((advance P) c).stk j).length ≤ (c.stk j).length + rawPushBound P := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => simp [advance,TM2.step]
  | some l =>
      have h := BitMachine.stepAux_length (P l) v S j
      have hb : BitMachine.pushBound (P l) ≤ rawPushBound P := by
        unfold rawPushBound
        exact Finset.single_le_sum (f := fun l => BitMachine.pushBound (P l))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
      exact (show (((advance P) ⟨some l,v,S⟩).stk j).length ≤
        (S j).length + BitMachine.pushBound (P l) from by
          simpa [advance,TM2.step] using h).trans (Nat.add_le_add_left hb _)

theorem run_length {K L V : Type*} [DecidableEq K] [Fintype L]
    (P : L → TM2.Stmt (fun _ : K => Bool) L V)
    (c : TM2.Cfg (fun _ : K => Bool) L V) (j : K) (t : Nat) :
    ((((advance P)^[t]) c).stk j).length ≤
      (c.stk j).length + t * rawPushBound P := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Function.iterate_succ_apply']
      have h := advance_length P (((advance P)^[t]) c) j
      nlinarith

def stagePush (r c : Fin 2) (target : Bank) : Nat :=
  rawPushBound (GaussFetchFromBackups64.program r c target)

def pushes : Nat :=
  stagePush 0 0 24 + stagePush 0 1 25 + stagePush 1 0 26 + stagePush 1 1 27

def stageTime (B n : Nat) : Nat :=
  23*B + 52*n + 49 + 140*(n+1)^3

def nextBankBound (B n : Nat) : Nat := B + stageTime B n * pushes

def fourBound (B n : Nat) : Nat :=
  stageTime B n + stageTime (nextBankBound B n) n +
    stageTime (nextBankBound (nextBankBound B n) n) n +
    stageTime (nextBankBound (nextBankBound (nextBankBound B n) n) n) n + 3

private theorem broadcast_length {K : Type*} [DecidableEq K]
    (source temp : K) (targets : List K) (bits : List Bool)
    (S : K → List Bool) (B n : Nat)
    (hS : ∀ j, (S j).length ≤ B) (hbits : bits.length ≤ n) (j : K) :
    (SourceClausePreservingBroadcast.result source temp targets bits S j).length ≤ B+n := by
  unfold SourceClausePreservingBroadcast.result
  by_cases ht : j = temp
  · subst j; simp
  · rw [Function.update_of_ne ht]
    unfold BitMachineBroadcast.prepend
    split_ifs with hm
    · simp only [List.length_append]
      by_cases hs : j = source
      · subst j; simp; omega
      · rw [Function.update_of_ne hs]
        have h := hS j
        omega
    · by_cases hs : j = source
      · subst j; simp
      · rw [Function.update_of_ne hs]
        have h := hS j
        omega

private theorem afterColumn_length (r c : Fin 2)
    (S : Bank → List Bool) (row col B n : Nat)
    (hS : ∀ j, (S j).length ≤ B) (hr : row ≤ n) (hc : col ≤ n) :
    ∀ j, (GaussLoadIndices64.afterColumn r c row col S j).length ≤ B+2*n := by
  have hclear : ∀ j, (GaussActiveIndexReset64.cleared S j).length ≤ B := by
    intro j
    unfold GaussActiveIndexReset64.cleared BitMachineClearBank.cleared
    split_ifs <;> first | simp | exact hS j
  have hrow : ∀ j, (GaussLoadIndices64.afterRow r row S j).length ≤ B+n := by
    intro j
    exact broadcast_length _ _ _ _ _ B n hclear (by simpa using hr) j
  intro j
  have h := broadcast_length (GaussLoadIndices64.columnBank c) (63 : Bank) [16]
    (List.replicate col true) (GaussLoadIndices64.afterRow r row S)
    (B+n) n hrow (by simpa using hc) j
  simpa [GaussLoadIndices64.afterColumn,Nat.add_assoc,Nat.two_mul] using h

theorem fetch_clock_le (r c : Fin 2) (S : Bank → List Bool)
    (row col B n : Nat) (matrix cell : List Bool)
    (hS : ∀ j, (S j).length ≤ B) (hr : row ≤ n) (hc : col ≤ n)
    (hm : matrix.length ≤ n) (he : cell.length ≤ n) :
    GaussFetchFromBackups64.clock r c S row col matrix cell ≤ stageTime B n := by
  have h15 := hS 15
  have h16 := hS 16
  have hcol := afterColumn_length r c S row col B n hS hr hc
  have hsum : (∑ i : Fin 21,
      (GaussLoadIndices64.afterColumn r c row col S
        (GaussGetterReset64.resetBank i)).length) ≤ 21*(B+2*n) := by
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 21)))
      (fun i _ => hcol (GaussGetterReset64.resetBank i))
    simpa using h
  have hpow := Nat.pow_le_pow_left (Nat.add_le_add_right hm 1) 3
  unfold GaussFetchFromBackups64.clock GaussLoadIndices64.clock
    GaussLoadIndices64.resetClock GaussLoadIndices64.copyClock
    GaussOneFetchProgram64.preparationClock GaussOneFetchProgram64.resetClock
    GaussOneFetchProgram64.copyClock stageTime
  nlinarith

theorem stage_growth (r c : Fin 2) (target : Bank)
    (S : Bank → List Bool) (t B n : Nat)
    (hS : ∀ j, (S j).length ≤ B) (ht : t ≤ stageTime B n)
    (hp : stagePush r c target ≤ pushes) :
    ∀ j, ((GaussFetchFromBackups64.run r c target t
      (GaussFetchFromBackups64.initial S)).stk j).length ≤ nextBankBound B n := by
  intro j
  have h := run_length (GaussFetchFromBackups64.program r c target)
    (GaussFetchFromBackups64.initial S) j t
  have hmul := Nat.mul_le_mul ht hp
  change ((GaussFetchFromBackups64.run r c target t
    (GaussFetchFromBackups64.initial S)).stk j).length ≤
      (S j).length + t * stagePush r c target at h
  have hSj := hS j
  unfold nextBankBound
  omega

#print axioms fetch_clock_le
#print axioms stage_growth

end
end CurrentAdditive.GaussFourFetchEnvelope64
