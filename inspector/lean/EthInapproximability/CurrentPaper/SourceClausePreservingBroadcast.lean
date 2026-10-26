import EthInapproximability.CurrentPaper.BitMachineBroadcast

/-!
# Charged source-preserving unary fanout

The converter repeatedly needs the same unary vertex count or row ordinal in
distinct arithmetic work banks. A destructive broadcast would lose its only
validated copy. This program restores the source during the reverse pass and
simultaneously writes the chosen finite target list. Targets are program
syntax, not an uncharged input word.
-/

namespace EthInapproximability.CurrentPaper.SourceClausePreservingBroadcast

open Turing BitMachineEncoding

variable {K : Type*} [DecidableEq K]

inductive Label where
  | scan | restore | finish
  deriving DecidableEq, Fintype

def program (source temp : K) (targets : List K) :
    Label → TM2.Stmt (fun _ : K => Bool) Label (Unit × Option Bool)
  | .scan => BitMachineBroadcast.scanStep source temp .scan .restore
  | .restore => BitMachineBroadcast.restoreStep temp (source :: targets)
      .restore .finish
  | .finish => .halt

def result (source temp : K) (targets : List K) (bits : List Bool)
    (S : K → List Bool) : K → List Bool :=
  Function.update
    (BitMachineBroadcast.prepend (source :: targets) bits
      (Function.update S source [])) temp []

theorem run (source temp : K) (targets : List K)
    (hst : source ≠ temp) (hnodup : targets.Nodup)
    (hsource : source ∉ targets) (htemp : temp ∉ targets)
    (bits : List Bool) (S : K → List Bool)
    (hbits : S source = bits) (hscratch : S temp = []) :
    ((advance (program source temp targets))^[2 * bits.length + 2])
      (⟨some .scan, ((), none), S⟩ :
        TM2.Cfg (fun _ : K => Bool) Label (Unit × Option Bool)) =
      ⟨some .finish, ((), none), result source temp targets bits S⟩ := by
  have hs := BitMachineBroadcast.scan_run
    (program source temp targets) source temp hst .scan .restore
    (by rfl) () none bits [] S
  have hi : BitMachineBroadcast.contents source temp S bits [] = S := by
    simp [BitMachineBroadcast.contents, ← hbits, ← hscratch]
  rw [hi] at hs
  simp only [List.append_nil] at hs
  have hr := BitMachineBroadcast.restore_run
    (program source temp targets) temp (source :: targets)
    (by simpa [hsource] using hnodup)
    (by simp [Ne.symm hst, htemp])
    .restore .finish (by rfl) () none bits.reverse
    (Function.update S source [])
  simp only [List.length_reverse, List.reverse_reverse] at hr
  have he := (BitMachineBroadcast.run_add _ hs (bits.length + 1)).trans hr
  simpa only [BitMachineBroadcast.run, Nat.two_mul,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, result] using he

theorem run_halt (source temp : K) (targets : List K)
    (hst : source ≠ temp) (hnodup : targets.Nodup)
    (hsource : source ∉ targets) (htemp : temp ∉ targets)
    (bits : List Bool) (S : K → List Bool)
    (hbits : S source = bits) (hscratch : S temp = []) :
    ((advance (program source temp targets))^[2 * bits.length + 3])
      (⟨some .scan, ((), none), S⟩ :
        TM2.Cfg (fun _ : K => Bool) Label (Unit × Option Bool)) =
      ⟨none, ((), none), result source temp targets bits S⟩ := by
  rw [show 2 * bits.length + 3 = (2 * bits.length + 2) + 1 by omega,
    Function.iterate_succ_apply']
  rw [run source temp targets hst hnodup hsource htemp bits S hbits hscratch]
  rfl

theorem source_restored (source temp : K) (targets : List K)
    (h : source ≠ temp) (bits : List Bool) (S : K → List Bool) :
    result source temp targets bits S source = bits := by
  simp [result, BitMachineBroadcast.prepend, h, Ne.symm h]

theorem target_written (source temp : K) (targets : List K)
    (htemp : temp ∉ targets) (hsource : source ∉ targets)
    (h : source ≠ temp) (bits : List Bool) (S : K → List Bool)
    (x : K) (hx : x ∈ targets) :
    result source temp targets bits S x = bits ++ S x := by
  have hxs : x ≠ source := fun he => hsource (he ▸ hx)
  have hxt : x ≠ temp := fun he => htemp (he ▸ hx)
  simp [result, BitMachineBroadcast.prepend, hx, hxs, hxt,
    Function.update_of_ne]

theorem other_preserved (source temp : K) (targets : List K)
    (bits : List Bool) (S : K → List Bool) (x : K)
    (hs : x ≠ source) (ht : x ≠ temp) (hx : x ∉ targets) :
    result source temp targets bits S x = S x := by
  simp [result, BitMachineBroadcast.prepend, hs, ht, hx,
    Function.update_of_ne]

theorem temp_empty (source temp : K) (targets : List K)
    (bits : List Bool) (S : K → List Bool) :
    result source temp targets bits S temp = [] := by
  simp [result]

end EthInapproximability.CurrentPaper.SourceClausePreservingBroadcast
