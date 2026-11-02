import EthInapproximability.CurrentPaper.BitMachineBankCodec

/-!
# Initial packet and fuel for the bounded clock iteration

Source: frozen v8 `05-iteration.tex`, implementation of the prefix clock.
The fixed parameter `K` is the number of empty transient fields. The input
word itself supplies unary iteration fuel. Three stacks suffice: the source
is restored as fuel while its bits are written into the framed budget field.
The packet begins with active=[true], the input budget, and an empty counter.
-/

namespace EthInapproximability.CurrentPaper.ClockIterationInput

open Turing TM2.Stmt BitMachineEncoding EncodedCommunication

def payload : List Bool → List Bool
  | [] => []
  | b::bits => true::b::payload bits

theorem payload_append (a b : List Bool) : payload (a++b) = payload a++payload b := by
  induction a with
  | nil => rfl
  | cons x a ih => simp only [List.cons_append,payload,ih]

theorem field_payload (bits : List Bool) : field bits = payload bits++[false] := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp only [field,payload,List.cons_append,ih]

def packet (K : ℕ) (budget : List Bool) :=
  field [true] ++ field budget ++ List.replicate (K+1) false

def initialBank (K : ℕ) (budget : List Bool) : Fin (K+3) → List Bool :=
  Fin.cons [true] (Fin.cons budget (fun _ : Fin (K+1) => []))

@[simp] theorem initialBank_zero (K : ℕ) (budget : List Bool) :
    initialBank K budget 0 = [true] := rfl

@[simp] theorem initialBank_one (K : ℕ) (budget : List Bool) :
    initialBank K budget 1 = budget := rfl

@[simp] theorem initialBank_tail (K : ℕ) (budget : List Bool) (i : Fin (K+1)) :
    initialBank K budget i.succ.succ = [] := rfl

theorem empty_fields (K : ℕ) :
    (List.replicate K ([] : List Bool)).flatMap field = List.replicate K false := by
  induction K with
  | zero => rfl
  | succ K ih => simp only [List.replicate_succ,List.flatMap_cons,field,
      List.singleton_append,ih]

theorem packet_eq_encode (K : ℕ) (budget : List Bool) :
    packet K budget = BitMachineBankCodec.encode (initialBank K budget) := by
  rw [BitMachineBankCodec.encode_eq_list]
  simp only [initialBank,List.ofFn_cons,List.ofFn_const,List.flatMap_cons,
    empty_fields,packet,List.append_assoc]

theorem packet_decodes (K : ℕ) (budget : List Bool) :
    BitMachineBankCodec.decode (K+3) (packet K budget) = some (initialBank K budget) := by
  rw [packet_eq_encode,BitMachineBankCodec.decode_encode]

theorem packet_length (K : ℕ) (budget : List Bool) :
    (packet K budget).length = 2*budget.length+K+5 := by
  simp only [packet,List.length_append,field_length,List.length_cons,List.length_nil,
    List.length_replicate]
  omega

inductive Label (K : ℕ) where
  | suffix : Fin (K+3) → Label K
  | scan | restore
  deriving DecidableEq, Fintype

def program (K : ℕ) : Label K → TM2.Stmt (fun _ : Fin 3 => Bool) (Label K) (Option Bool)
  | .suffix i => if h : i.val < K+2 then
      push 2 (fun _ => false) (goto (fun _ => .suffix ⟨i.val+1,by omega⟩))
    else goto (fun _ => .scan)
  | .scan => pop 0 (fun _ b => b)
      (branch Option.isSome
        (push 1 (fun b => b.getD false) (goto (fun _ => .scan)))
        (goto (fun _ => .restore)))
  | .restore => pop 1 (fun _ b => b)
      (branch Option.isSome
        (push 0 (fun b => b.getD false)
          (push 2 (fun b => b.getD false) (push 2 (fun _ => true) (goto (fun _ => .restore)))))
        (push 2 (fun _ => false) (push 2 (fun _ => true) (push 2 (fun _ => true)
          (load (fun _ => none) halt)))))

abbrev Config (K : ℕ) := TM2.Cfg (fun _ : Fin 3 => Bool) (Label K) (Option Bool)

def cfg {K : ℕ} (l : Option (Label K)) (v : Option Bool) (source saved out : List Bool) : Config K :=
  ⟨l,v,![source,saved,out]⟩

def run {K : ℕ} (t : ℕ) (c : Config K) := ((advance (program K))^[t]) c

theorem run_add {K : ℕ} (t u : ℕ) (c : Config K) : run (t+u) c = run u (run t c) := by
  simpa only [run,Nat.add_comm] using Function.iterate_add_apply (advance (program K)) u t c

theorem suffix_push (K i : ℕ) (hi : i < K+2) (source saved out : List Bool) :
    advance (program K) (cfg (some (.suffix ⟨i,by omega⟩)) none source saved out) =
      cfg (some (.suffix ⟨i+1,by omega⟩)) none source saved (false::out) := by
  simp [advance,program,cfg,TM2.step,TM2.stepAux,hi]
  funext j
  fin_cases j <;> rfl

theorem suffix_end (K : ℕ) (source saved out : List Bool) :
    advance (program K) (cfg (some (.suffix ⟨K+2,by omega⟩)) none source saved out) =
      cfg (some .scan) none source saved out := by
  simp [advance,program,cfg,TM2.step,TM2.stepAux]

theorem suffix_run (K left : ℕ) (i : ℕ) (hi : i+left = K+2)
    (source saved out : List Bool) :
    run (K := K) (left+1) (cfg (some (.suffix ⟨i,by omega⟩)) none source saved out) =
      cfg (some .scan) none source saved (List.replicate left false++out) := by
  induction left generalizing i out with
  | zero =>
      have he : i=K+2 := by omega
      subst i
      simpa only [run,Function.iterate_one,List.replicate_zero,List.nil_append]
        using suffix_end K source saved out
  | succ left ih =>
      have hlt : i < K+2 := by omega
      simp only [run,Function.iterate_succ_apply,suffix_push K i hlt]
      have h := ih (i+1) (by omega) (false::out)
      simpa only [run,List.replicate_succ',List.append_assoc,List.singleton_append] using h

theorem scan_cons (K : ℕ) (v : Option Bool) (b : Bool) (source saved out : List Bool) :
    advance (program K) (cfg (some .scan) v (b::source) saved out) =
      cfg (some .scan) (some b) source (b::saved) out := by
  simp [advance,program,cfg,TM2.step,TM2.stepAux]
  funext j
  fin_cases j <;> rfl

theorem scan_nil (K : ℕ) (v : Option Bool) (saved out : List Bool) :
    advance (program K) (cfg (some .scan) v [] saved out) =
      cfg (some .restore) none [] saved out := by
  simp [advance,program,cfg,TM2.step,TM2.stepAux]

theorem scan_run (K : ℕ) (v : Option Bool) (source saved out : List Bool) :
    run (K := K) (source.length+1) (cfg (some .scan) v source saved out) =
      cfg (some .restore) none [] (source.reverse++saved) out := by
  induction source generalizing v saved with
  | nil => simpa only [run,Function.iterate_one,List.length_nil,zero_add,
      List.reverse_nil,List.nil_append] using scan_nil K v saved out
  | cons b source ih =>
      simp only [List.length_cons,run,Function.iterate_succ_apply,scan_cons]
      simpa only [run,List.reverse_cons,List.append_assoc,List.singleton_append]
        using ih (some b) (b::saved)

theorem restore_cons (K : ℕ) (v : Option Bool) (b : Bool) (source saved out : List Bool) :
    advance (program K) (cfg (some .restore) v source (b::saved) out) =
      cfg (some .restore) (some b) (b::source) saved (true::b::out) := by
  simp [advance,program,cfg,TM2.step,TM2.stepAux]
  funext j
  fin_cases j <;> rfl

theorem restore_nil (K : ℕ) (v : Option Bool) (source out : List Bool) :
    advance (program K) (cfg (some .restore) v source [] out) =
      cfg none none source [] (field [true]++out) := by
  simp [advance,program,cfg,TM2.step,TM2.stepAux,field]
  funext j
  fin_cases j <;> rfl

theorem restore_run (K : ℕ) (v : Option Bool) (source saved out : List Bool) :
    run (K := K) (saved.length+1) (cfg (some .restore) v source saved out) =
      cfg none none (saved.reverse++source) [] (field [true]++payload saved.reverse++out) := by
  induction saved generalizing v source out with
  | nil => simpa only [run,Function.iterate_one,List.length_nil,zero_add,
      List.reverse_nil,List.nil_append,payload,List.append_nil]
        using restore_nil K v source out
  | cons b saved ih =>
      simp only [List.length_cons,run,Function.iterate_succ_apply,restore_cons]
      simpa only [run,List.reverse_cons,List.append_assoc,List.singleton_append,
        payload_append,payload,List.cons_append,List.nil_append]
        using ih (some b) (b::source) (true::b::out)

/-- The source word is restored as iteration fuel, and the complete initial
state packet is physically emitted in the other designated stack. -/
theorem run_correct (K : ℕ) (input : List Bool) :
    run (K := K) (2*input.length+K+5)
      (cfg (some (.suffix 0)) none input [] []) =
      cfg none none input [] (packet K input) := by
  have h1 := suffix_run K (K+2) 0 (by omega) input [] []
  simp only [List.append_nil] at h1
  have hz : (⟨0,by omega⟩ : Fin (K+3)) = 0 := by ext; simp
  rw [hz] at h1
  have h2 := scan_run K none input [] (List.replicate (K+2) false)
  simp only [List.append_nil] at h2
  have h3 := restore_run K none [] input.reverse (List.replicate (K+2) false)
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at h3
  rw [show 2*input.length+K+5 = (K+3)+(input.length+1)+(input.length+1) by omega,
    run_add _ (input.length+1),run_add (K+3) (input.length+1),h1,h2,h3]
  congr 1
  simp only [packet,field_payload,List.replicate_succ,List.singleton_append,
    List.append_assoc,List.cons_append,List.nil_append]

noncomputable def machine (K : ℕ) : BitMachine.Machine :=
  ofFinite (0 : Fin 3) 2 (.suffix 0 : Label K) (none : Option Bool) (program K)

theorem outputs_all (K : ℕ) (input : List Bool) :
    (machine K).OutputsWithin input (packet K input) (2*input.length+K+5) := by
  apply outputsWithin_of_raw_run (0 : Fin 3) 2 (.suffix 0 : Label K)
    (none : Option Bool) (program K) input (packet K input)
    (2*input.length+K+5) _ le_rfl
  all_goals
    have hi : rawInit (0 : Fin 3) (.suffix 0 : Label K) (none : Option Bool) input =
        cfg (some (.suffix 0)) none input [] [] := by
      unfold rawInit cfg
      congr 1
      funext j
      fin_cases j <;> simp
    rw [hi]
  · change (run (2*input.length+K+5) _).l = none
    rw [run_correct]
    rfl
  · change (run (2*input.length+K+5) _).stk 2 = packet K input
    rw [run_correct]
    rfl

theorem packet_polytime (K : ℕ) : BitMachine.Polytime (packet K) := by
  refine ⟨machine K,K+5,1,fun input => ?_⟩
  apply BitMachine.outputsWithin_mono _ (outputs_all K input)
  simp only [pow_one]
  nlinarith

end EthInapproximability.CurrentPaper.ClockIterationInput
