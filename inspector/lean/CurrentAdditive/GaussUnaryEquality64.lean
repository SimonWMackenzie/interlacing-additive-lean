import CurrentAdditive.GaussGetterCopy64
import EthInapproximability.CurrentPaper.EntryUnaryCompare

set_option maxHeartbeats 1000000

/-! A fixed source-preserving unary equality circuit, used to select the
swapped source row without reading an address in finite control. -/
namespace CurrentAdditive.GaussUnaryEquality64
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
abbrev Stack := Fin 64

def copied (S : Stack → List Bool) (a b : Nat) : Stack → List Bool :=
  Function.update (Function.update S 15 (List.replicate a true))
    16 (List.replicate b true)

def copyPair (A B : Stack) := BitMachineRawSequence.program
  (GaussGetterCopy64.program A 15) (GaussGetterCopy64.program B 16)
  .scan ((),none) ((),none)

def compare (O : Stack) := EntryUnaryCompare.program (15 : Stack) 16 O false true false

def program (A B O : Stack) := BitMachineRawSequence.program
  (copyPair A B) (compare O) .loop (((),none),((),none)) (none,none)

abbrev Label := BitMachineRawSequence.Label
  (BitMachineRawSequence.Label GaussGetterCopy64.Label GaussGetterCopy64.Label)
  EntryUnaryCompare.CL
abbrev Control := BitMachineRawSequence.Control
  (BitMachineRawSequence.Control GaussGetterCopy64.Control GaussGetterCopy64.Control)
  EntryUnaryCompare.CV
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def initial (S : Stack → List Bool) : Config :=
  ⟨some (BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel .scan)),
    ((((),none),((),none)),(none,none)),S⟩

theorem copy_result (A target : Stack)
    (hA : A ≠ 63) (htA : target ≠ A) (ht63 : target ≠ 63)
    (S : Stack → List Bool) (word : List Bool)
    (hword : S A = word) (htemp : S 63 = []) (htarget : S target = []) :
    SourceClausePreservingBroadcast.result A 63 [target] word S =
      Function.update S target word := by
  funext z
  by_cases hzt : z = target
  · subst z
    simpa [htarget] using SourceClausePreservingBroadcast.target_written
      A 63 [target] (by simp [Ne.symm ht63]) (by simp [Ne.symm htA])
      hA word S target (by simp)
  by_cases hzA : z = A
  · subst z
    rw [Function.update_of_ne (Ne.symm htA)]
    simpa [hword] using SourceClausePreservingBroadcast.source_restored
      A 63 [target] hA word S
  by_cases hz63 : z = 63
  · subst z
    rw [Function.update_of_ne (Ne.symm ht63)]
    simpa [htemp] using SourceClausePreservingBroadcast.temp_empty A 63 [target] word S
  rw [Function.update_of_ne hzt]
  exact GaussGetterCopy64.copy_preserves_other A target z word S hzA hz63 hzt

theorem run_equal (A B O : Stack)
    (hA15 : A ≠ 15) (hA16 : A ≠ 16) (hA63 : A ≠ 63)
    (hB15 : B ≠ 15) (hB16 : B ≠ 16) (hB63 : B ≠ 63)
    (hO15 : O ≠ 15) (hO16 : O ≠ 16) (hO63 : O ≠ 63)
    (S : Stack → List Bool) (a b : Nat)
    (hA : S A = List.replicate a true) (hB : S B = List.replicate b true)
    (h15 : S 15 = []) (h16 : S 16 = []) (h63 : S 63 = []) :
    ∃ t ≤ 2*a+2*b+max a b+10, ∃ v,
      ((advance (program A B O))^[t]) (initial S) =
        ⟨none,v,Function.update S O (decide (a=b) :: S O)⟩ := by
  let S1 := Function.update S 15 (List.replicate a true)
  have hcopyA := (GaussGetterCopy64.copy_word A 15 hA63
    (Ne.symm hA15) (by decide) (List.replicate a true) S hA h63 h15).1
  rw [copy_result A 15 hA63 (Ne.symm hA15) (by decide) S _ hA h63 h15] at hcopyA
  have hB1 : S1 B = List.replicate b true := by simp [S1,hB15,hB]
  have h631 : S1 63 = [] := by simp [S1,h63]
  have h161 : S1 16 = [] := by simp [S1,h16]
  have hcopyB := (GaussGetterCopy64.copy_word B 16 hB63
    (Ne.symm hB16) (by decide) (List.replicate b true) S1 hB1 h631 h161).1
  rw [copy_result B 16 hB63 (Ne.symm hB16) (by decide) S1 _ hB1 h631 h161] at hcopyB
  have hpairInitA : GaussGetterCopy64.run A 15 (2*a+3)
      ⟨some .scan,((),none),S⟩ = ⟨none,((),none),S1⟩ := by
    simpa only [List.length_replicate] using hcopyA
  have hpairInitB : GaussGetterCopy64.run B 16 (2*b+3)
      ⟨some .scan,((),none),S1⟩ = ⟨none,((),none),copied S a b⟩ := by
    simpa only [List.length_replicate,copied,S1] using hcopyB
  obtain ⟨u,hu,hpair⟩ := BitMachineRawSequence.runs
    (GaussGetterCopy64.program A 15) (GaussGetterCopy64.program B 16)
    .scan .scan ((),none) ((),none) ((),none) ((),none)
    S S1 (copied S a b) (2*a+3) (2*b+3) hpairInitA hpairInitB
  obtain ⟨v,hv,w,hcompare⟩ := EntryUnaryCompare.compare_run (15 : Stack) 16 O
    (by decide) (Ne.symm hO15) (Ne.symm hO16) false true false
    (copied S a b) (none,none) a b
    (by simp [copied]) (by simp [copied])
  have hverdict : EntryUnaryCompare.verdict false true false a b = decide (a=b) := by
    by_cases he : a=b
    · simp [EntryUnaryCompare.verdict,he]
    · by_cases hl : a<b <;> simp [EntryUnaryCompare.verdict,he,hl]
  have hbank : Function.update
      (Function.update (Function.update (copied S a b) 15 []) 16 [])
      O (EntryUnaryCompare.verdict false true false a b :: copied S a b O) =
      Function.update S O (decide (a=b) :: S O) := by
    funext z
    by_cases hzO : z=O
    · subst z; simp [copied,hverdict,hO15,hO16]
    by_cases hz15 : z=15
    · subst z; simp [copied,hzO,h15]
    by_cases hz16 : z=16
    · subst z; simp [copied,hzO,h16]
    simp [copied,hzO,hz15,hz16]
  rw [hbank] at hcompare
  obtain ⟨t,ht,hall⟩ := BitMachineRawSequence.runs
    (copyPair A B) (compare O) (BitMachineRawSequence.leftLabel .scan) .loop
    (((),none),((),none)) (((),none),((),none)) (none,none) w
    S (copied S a b) (Function.update S O (decide (a=b)::S O))
    u v hpair hcompare
  exact ⟨t,by omega,((((),none),((),none)),w),hall⟩

#print axioms run_equal
end CurrentAdditive.GaussUnaryEquality64
