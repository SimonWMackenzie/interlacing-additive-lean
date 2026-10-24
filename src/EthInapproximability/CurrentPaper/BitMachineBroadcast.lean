import EthInapproximability.CurrentPaper.BitMachineEncoding
import Mathlib.Tactic

/-!
# Broadcasting one stack to a fixed list of destination stacks

Source: frozen v8 `03-exact-hardness.tex`, concrete verifier implementation,
and `B-effectivity-details.tex`, charged Boolean-stack data transfers.
The destination list is fixed program syntax, not a machine register.
-/

namespace EthInapproximability.CurrentPaper.BitMachineBroadcast

open Turing TM2.Stmt BitMachineEncoding

variable {K L V : Type*} [DecidableEq K]

def pushTargets (targets : List K)
    (next : TM2.Stmt (fun _ : K => Bool) L (V × Option Bool)) :
    TM2.Stmt (fun _ : K => Bool) L (V × Option Bool) :=
  match targets with
  | [] => next
  | k :: ks => push k (fun v => v.2.getD false) (pushTargets ks next)

def scanStep (source temp : K) (scan restore : L) :
    TM2.Stmt (fun _ : K => Bool) L (V × Option Bool) :=
  pop source (fun v b => (v.1, b))
    (branch (fun v => v.2.isSome)
      (push temp (fun v => v.2.getD false) (goto (fun _ => scan)))
      (goto (fun _ => restore)))

def restoreStep (temp : K) (targets : List K) (restore next : L) :
    TM2.Stmt (fun _ : K => Bool) L (V × Option Bool) :=
  pop temp (fun v b => (v.1, b))
    (branch (fun v => v.2.isSome)
      (pushTargets targets (goto (fun _ => restore)))
      (goto (fun _ => next)))

def prepend (targets : List K) (bits : List Bool) (bank : K → List Bool) : K → List Bool :=
  fun k => if k ∈ targets then bits ++ bank k else bank k

def copied (source temp : K) (targets : List K) (bits : List Bool)
    (bank : K → List Bool) : K → List Bool :=
  fun k => if k = source ∨ k = temp then [] else if k ∈ targets then bits ++ bank k else bank k

@[simp] theorem copied_source (source temp : K) (targets : List K) (bits : List Bool)
    (bank : K → List Bool) : copied source temp targets bits bank source = [] := by
  simp [copied]

@[simp] theorem copied_temp (source temp : K) (targets : List K) (bits : List Bool)
    (bank : K → List Bool) : copied source temp targets bits bank temp = [] := by
  simp [copied]

theorem copied_target (source temp : K) (targets : List K) (bits : List Bool)
    (bank : K → List Bool) (hsource : source ∉ targets) (htemp : temp ∉ targets)
    (k : K) (hk : k ∈ targets) : copied source temp targets bits bank k = bits ++ bank k := by
  have hs : k ≠ source := fun h => hsource (h ▸ hk)
  have ht : k ≠ temp := fun h => htemp (h ▸ hk)
  simp [copied, hs, ht, hk]

theorem copied_other (source temp : K) (targets : List K) (bits : List Bool)
    (bank : K → List Bool) (k : K) (hs : k ≠ source) (ht : k ≠ temp)
    (hk : k ∉ targets) : copied source temp targets bits bank k = bank k := by
  simp [copied, hs, ht, hk]

def run (P : L → TM2.Stmt (fun _ : K => Bool) L (V × Option Bool))
    (n : Nat) (c : TM2.Cfg (fun _ : K => Bool) L (V × Option Bool)) :=
  ((advance P)^[n]) c

theorem prepend_cons (a : K) (targets : List K) (h : a ∉ targets)
    (b : Bool) (bank : K → List Bool) :
    prepend targets [b] (Function.update bank a (b :: bank a)) =
      prepend (a :: targets) [b] bank := by
  funext k
  by_cases hk : k = a
  · subst k
    simp [prepend, h]
  · simp [prepend, hk, Function.update_of_ne hk]

theorem pushTargets_step (targets : List K) (h : targets.Nodup)
    (next : TM2.Stmt (fun _ : K => Bool) L (V × Option Bool))
    (v : V × Option Bool) (bank : K → List Bool) :
    TM2.stepAux (pushTargets targets next) v bank =
      TM2.stepAux next v (prepend targets [v.2.getD false] bank) := by
  induction targets generalizing bank with
  | nil => rfl
  | cons a targets ih =>
      simp only [List.nodup_cons] at h
      simp only [pushTargets, TM2.stepAux]
      rw [ih h.2, prepend_cons a targets h.1]

theorem prepend_update (targets : List K) (bits : List Bool) (bank : K → List Bool)
    (temp : K) (htemp : temp ∉ targets) (saved : List Bool) :
    prepend targets bits (Function.update bank temp saved) =
      Function.update (prepend targets bits bank) temp saved := by
  funext k
  by_cases hk : k = temp
  · subst k
    simp [prepend, htemp]
  · simp [prepend, Function.update_of_ne hk]

theorem prepend_prepend (targets : List K) (a b : List Bool) (bank : K → List Bool) :
    prepend targets a (prepend targets b bank) = prepend targets (a ++ b) bank := by
  funext k
  by_cases hk : k ∈ targets <;> simp [prepend, hk, List.append_assoc]

theorem prepend_nil (targets : List K) (bank : K → List Bool) :
    prepend targets [] bank = bank := by
  funext k
  simp [prepend]

theorem run_succ (P : L → TM2.Stmt (fun _ : K => Bool) L (V × Option Bool))
    {c c' : TM2.Cfg (fun _ : K => Bool) L (V × Option Bool)}
    (h : advance P c = c') (n : Nat) : run P (n + 1) c = run P n c' := by
  exact (Function.iterate_succ_apply _ _ _).trans (congrArg (run P n) h)

theorem run_add (P : L → TM2.Stmt (fun _ : K => Bool) L (V × Option Bool))
    {c c' : TM2.Cfg (fun _ : K => Bool) L (V × Option Bool)}
    {n : Nat} (h : run P n c = c') (m : Nat) : run P (n + m) c = run P m c' := by
  rw [Nat.add_comm, run, Function.iterate_add_apply]
  exact congrArg (run P m) h

def contents (source temp : K) (bank : K → List Bool) (bits saved : List Bool) :
    K → List Bool := Function.update (Function.update bank source bits) temp saved

theorem scan_cons (P : L → TM2.Stmt (fun _ : K => Bool) L (V × Option Bool))
    (source temp : K) (hst : source ≠ temp) (scan restore : L)
    (hp : P scan = scanStep source temp scan restore)
    (v : V) (popped : Option Bool) (b : Bool) (bits saved : List Bool)
    (bank : K → List Bool) :
    advance P ⟨some scan, (v, popped), contents source temp bank (b :: bits) saved⟩ =
      ⟨some scan, (v, some b), contents source temp bank bits (b :: saved)⟩ := by
  simp [advance, TM2.step, hp, scanStep, TM2.stepAux, contents,
    Function.update_of_ne hst, Function.update_of_ne (Ne.symm hst)]
  funext k
  by_cases hs : k = source <;> by_cases ht : k = temp <;>
    simp_all [Function.update_apply]

theorem scan_nil (P : L → TM2.Stmt (fun _ : K => Bool) L (V × Option Bool))
    (source temp : K) (hst : source ≠ temp) (scan restore : L)
    (hp : P scan = scanStep source temp scan restore)
    (v : V) (popped : Option Bool) (saved : List Bool) (bank : K → List Bool) :
    advance P ⟨some scan, (v, popped), contents source temp bank [] saved⟩ =
      ⟨some restore, (v, none), contents source temp bank [] saved⟩ := by
  simp [advance, TM2.step, hp, scanStep, TM2.stepAux, contents,
    Function.update_of_ne hst]

theorem scan_run (P : L → TM2.Stmt (fun _ : K => Bool) L (V × Option Bool))
    (source temp : K) (hst : source ≠ temp) (scan restore : L)
    (hp : P scan = scanStep source temp scan restore)
    (v : V) (popped : Option Bool) (bits saved : List Bool) (bank : K → List Bool) :
    run P (bits.length + 1)
      ⟨some scan, (v, popped), contents source temp bank bits saved⟩ =
      ⟨some restore, (v, none), contents source temp bank [] (bits.reverse ++ saved)⟩ := by
  induction bits generalizing popped saved with
  | nil => simpa [run] using run_succ P (scan_nil P source temp hst scan restore hp v popped saved bank) 0
  | cons b bits ih =>
      rw [List.length_cons, run_succ P (scan_cons P source temp hst scan restore hp v popped b bits saved bank)]
      simpa [List.reverse_cons, List.append_assoc] using ih (some b) (b :: saved)

theorem restore_cons (P : L → TM2.Stmt (fun _ : K => Bool) L (V × Option Bool))
    (temp : K) (targets : List K) (hnodup : targets.Nodup) (htemp : temp ∉ targets)
    (restore next : L) (hp : P restore = restoreStep temp targets restore next)
    (v : V) (popped : Option Bool) (b : Bool) (saved : List Bool) (bank : K → List Bool) :
    advance P ⟨some restore, (v, popped), Function.update bank temp (b :: saved)⟩ =
      ⟨some restore, (v, some b), Function.update (prepend targets [b] bank) temp saved⟩ := by
  simp only [advance, TM2.step, hp, restoreStep, TM2.stepAux, Function.update_self,
    List.head?, List.tail, Option.isSome, cond_true]
  rw [pushTargets_step targets hnodup]
  simp only [Option.getD_some, TM2.stepAux, Option.getD_some, Function.update_idem]
  rw [prepend_update targets [b] bank temp htemp saved]

theorem restore_nil (P : L → TM2.Stmt (fun _ : K => Bool) L (V × Option Bool))
    (temp : K) (targets : List K) (restore next : L)
    (hp : P restore = restoreStep temp targets restore next)
    (v : V) (popped : Option Bool) (bank : K → List Bool) :
    advance P ⟨some restore, (v, popped), Function.update bank temp []⟩ =
      ⟨some next, (v, none), Function.update bank temp []⟩ := by
  simp [advance, TM2.step, hp, restoreStep, TM2.stepAux]

theorem restore_run (P : L → TM2.Stmt (fun _ : K => Bool) L (V × Option Bool))
    (temp : K) (targets : List K) (hnodup : targets.Nodup) (htemp : temp ∉ targets)
    (restore next : L) (hp : P restore = restoreStep temp targets restore next)
    (v : V) (popped : Option Bool) (saved : List Bool) (bank : K → List Bool) :
    run P (saved.length + 1)
      ⟨some restore, (v, popped), Function.update bank temp saved⟩ =
      ⟨some next, (v, none), Function.update (prepend targets saved.reverse bank) temp []⟩ := by
  induction saved generalizing popped bank with
  | nil =>
      simpa only [List.length_nil, List.reverse_nil, prepend_nil, run,
        Function.iterate_zero_apply] using
        run_succ P (restore_nil P temp targets restore next hp v popped bank) 0
  | cons b saved ih =>
      rw [List.length_cons, run_succ P (restore_cons P temp targets hnodup htemp restore next hp v popped b saved bank), ih]
      rw [prepend_prepend]
      simp [List.reverse_cons]

/-- One destructive source pass followed by one restoring broadcast pass.
The source and temporary stack are empty afterward; every target receives
an order-preserving copy before its previous contents. All other stacks and
the entire `V` part of finite control are unchanged. -/
theorem broadcast_run (P : L → TM2.Stmt (fun _ : K => Bool) L (V × Option Bool))
    (source temp : K) (hst : source ≠ temp) (targets : List K)
    (hnodup : targets.Nodup) (hsource : source ∉ targets) (htemp : temp ∉ targets)
    (scan restore next : L)
    (hscan : P scan = scanStep source temp scan restore)
    (hrestore : P restore = restoreStep temp targets restore next)
    (v : V) (popped : Option Bool) (bits : List Bool) (bank : K → List Bool)
    (hbits : bank source = bits) (hsaved : bank temp = []) :
    run P (2 * bits.length + 2) ⟨some scan, (v, popped), bank⟩ =
      ⟨some next, (v, none), copied source temp targets bits bank⟩ := by
  have hs := scan_run P source temp hst scan restore hscan v popped bits [] bank
  have hi : contents source temp bank bits [] = bank := by
    simp [contents, ← hbits, ← hsaved]
  rw [hi] at hs
  simp only [List.append_nil] at hs
  have hr := restore_run P temp targets hnodup htemp restore next hrestore v none
    bits.reverse (Function.update bank source [])
  simp only [List.length_reverse, List.reverse_reverse] at hr
  have he := (run_add P hs (bits.length + 1)).trans hr
  have hfinal : Function.update (prepend targets bits (Function.update bank source [])) temp [] =
      copied source temp targets bits bank := by
    funext k
    by_cases ht : k = temp
    · subst k
      simp [copied]
    · by_cases hs : k = source
      · subst k
        simp [copied, prepend, hsource, Function.update_of_ne ht]
      · simp [copied, prepend, ht, hs, Function.update_of_ne ht, Function.update_of_ne hs]
  rw [hfinal] at he
  simpa only [Nat.two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he

end EthInapproximability.CurrentPaper.BitMachineBroadcast
