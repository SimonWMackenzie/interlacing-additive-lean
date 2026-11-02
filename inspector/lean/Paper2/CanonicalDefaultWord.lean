import Paper2.CanonicalDefaultSource
import Paper2.RecursiveLabelCodec
import EthInapproximability.CurrentPaper.SourceNormalizationMachineRepeatStream
import EthInapproximability.CurrentPaper.BitMachineCopy
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding
import Mathlib.Tactic

/-! Scratch: exact canonical words and a physically charged repeated-stream segment.
No production module imports this file. -/

namespace Paper2.CanonicalDefaultWordScratch

open RecursiveLabelCodecScratch RecursiveEntries

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def repeatWord (n : Nat) (word : List Bool) : List Bool :=
  (List.replicate n word).flatten

theorem repeatWord_zero (word : List Bool) : repeatWord 0 word = [] := rfl

theorem repeatWord_succ (n : Nat) (word : List Bool) :
    repeatWord (n + 1) word = word ++ repeatWord n word := by
  simp [repeatWord, List.replicate_succ]

theorem piCodec_const {α : Type} (ca : PrefixCodec α) (n : Nat) (x : α) :
    (piCodec ca n).encode (fun _ => x) = repeatWord n (ca.encode x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have htail : Fin.tail (fun _ : Fin (n+1) => x) =
          (fun _ : Fin n => x) := rfl
      simp [piCodec, transportCodec, prodCodec, repeatWord_succ, htail, ih]

def words (p s q₁ q₂ w Q : Nat) : Nat → List Bool × List Bool
  | 0 => (List.replicate p false, [false])
  | k + 1 =>
      let prev := words p s q₁ q₂ w Q k
      (repeatWord Q ([false,true,true,false] ++
        repeatWord (q₁+s+1) prev.2),
       [false] ++ repeatWord w ([true,false,false,false] ++ prev.1))

theorem seed_words (p s q₁ q₂ w Q : Nat) :
    words p s q₁ q₂ w Q 0 = (List.replicate p false, [false]) := rfl

theorem successor_words (p s q₁ q₂ w Q k : Nat) :
    words p s q₁ q₂ w Q (k+1) =
      (repeatWord Q ([false,true,true,false] ++
        repeatWord (q₁+s+1) (words p s q₁ q₂ w Q k).2),
       [false] ++ repeatWord w ([true,false,false,false] ++
        (words p s q₁ q₂ w Q k).1)) := rfl

theorem repeatWord_singleton (n : Nat) (b : Bool) :
    repeatWord n [b] = List.replicate n b := by
  induction n with
  | zero => rfl
  | succ n ih => simp [repeatWord_succ, ih, List.replicate_succ]

theorem default_item_zero (n s : Nat) (hn : 0 < n)
    (hs : 0 < 4*s) :
    (defaultItemCodec n s).encode
      ((⟨0,hs⟩, .inl ⟨0,hn⟩) :
        SourceConstruction.Items s (Fin n)) = [false,false,false] := rfl

/-- Exact words for the semantic public default, without choosing carriers. -/
theorem defaultLabels_encoded (n p s q₁ q₂ w Q : Nat)
    (hn : 0 < n) (hp : 0 < p) (hs : 0 < 4*s)
    (hq₂ : 0 < q₂) (hw : 0 < w) (hQ : 0 < Q) (k : Nat) :
    let label := RecursiveEntries.defaultLabels
      (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
      (fun _ : Fin p => false) (⟨0,hp⟩ : Fin p)
      ((⟨0,hs⟩, .inl ⟨0,hn⟩) :
        SourceConstruction.Items s (Fin n)) hq₂ hw hQ k
    ((defaultCarrierCodecs n p s q₁ q₂ w Q k).1.encode label.1,
      (defaultCarrierCodecs n p s q₁ q₂ w Q k).2.encode label.2) =
      words p s q₁ q₂ w Q k := by
  induction k with
  | zero =>
      simp [defaultLabels, defaultCarrierCodecs, carrierCodecs,
        piCodec_const, repeatWord_singleton, words, finCodec, boolCodec]
  | succ k ih =>
      have hr :
          (defaultCarrierCodecs n p s q₁ q₂ w Q k).1.encode
            (defaultLabels (fun _ : Fin p => false) (⟨0,hp⟩ : Fin p)
              ((⟨0,hs⟩, .inl ⟨0,hn⟩) :
                SourceConstruction.Items s (Fin n)) hq₂ hw hQ k).1 =
          (words p s q₁ q₂ w Q k).1 := by
        simpa only [Prod.fst] using congrArg Prod.fst ih
      have hc :
          (defaultCarrierCodecs n p s q₁ q₂ w Q k).2.encode
            (defaultLabels (fun _ : Fin p => false) (⟨0,hp⟩ : Fin p)
              ((⟨0,hs⟩, .inl ⟨0,hn⟩) :
                SourceConstruction.Items s (Fin n)) hq₂ hw hQ k).2 =
          (words p s q₁ q₂ w Q k).2 := by
        simpa only [Prod.snd] using congrArg Prod.snd ih
      have hr' := hr
      have hc' := hc
      simp only [defaultCarrierCodecs] at hr' hc'
      simp [defaultLabels, defaultCarrierCodecs, carrierCodecs,
        words, piCodec_const, prodCodec, taggedColumnCodec,
        transportCodec, taggedEquiv, sumCodec, outerColumnCodec,
        rawRowCodec,
        show (finCodec w).encode (⟨0,hw⟩ : Fin w) = [false] from rfl,
        show (finCodec q₂).encode (⟨0,hq₂⟩ : Fin q₂) = [false] from rfl,
        show (finCodec Q).encode (⟨0,hQ⟩ : Fin Q) = [false] from rfl,
        default_item_zero n s hn hs]
      constructor
      · exact congrArg (fun z => repeatWord Q
          ([false,true,true,false] ++ repeatWord (q₁+s+1) z)) hc'
      · exact congrArg (fun z => repeatWord w
          ([true,false,false,false] ++ z)) hr'

theorem canonical_tail_encoded (L n w Q : Nat)
    (hn : 0 < n) (hw : 0 < w) (hQ : 0 < Q)
    (k : Nat) (i : Fin (SourceProfileParameters.width L + 1)) :
    (defaultCarrierCodecs n (LookupSeed.width L)
      (SourceProfileParameters.width L)
      (SourceProfileParameters.width L - 2)
      (SourceProfileParameters.outerWidth L) w Q k).2.encode
      (CanonicalDefaultSource.canonicalDefaultTails
        L n w Q hn hw hQ k i) =
    (words (LookupSeed.width L) (SourceProfileParameters.width L)
      (SourceProfileParameters.width L - 2)
      (SourceProfileParameters.outerWidth L) w Q k).2 := by
  have hp : 0 < LookupSeed.width L := by
    unfold LookupSeed.width; positivity
  have hs : 0 < 4 * SourceProfileParameters.width L := by
    unfold SourceProfileParameters.width; positivity
  have hq₂ : 0 < SourceProfileParameters.outerWidth L := by
    unfold SourceProfileParameters.outerWidth; positivity
  have h := defaultLabels_encoded n (LookupSeed.width L)
    (SourceProfileParameters.width L)
    (SourceProfileParameters.width L - 2)
    (SourceProfileParameters.outerWidth L) w Q
    hn hp hs hq₂ hw hQ k
  have hc := congrArg Prod.snd h
  simp only [CanonicalDefaultSource.canonicalDefaultTails,
    RecursiveEntries.defaultTails] at *
  exact hc

theorem repeatWord_commute (n : Nat) (word : List Bool) :
    repeatWord n word ++ word = word ++ repeatWord n word := by
  induction n with
  | zero => simp [repeatWord]
  | succ n ih => simp [repeatWord_succ, List.append_assoc, ih]

theorem repeated_eq_repeatWord (word : List Bool) (n : Nat) :
    EthInapproximability.CurrentPaper.SourceNormalizationMachineRepeatStream.repeated
      word n = repeatWord n word := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [EthInapproximability.CurrentPaper.SourceNormalizationMachineRepeatStream.repeated,
        ih, repeatWord_succ, repeatWord_commute]

theorem repeatWord_length (n : Nat) (word : List Bool) :
    (repeatWord n word).length = n * word.length := by
  induction n with
  | zero => simp [repeatWord]
  | succ n ih => simp [repeatWord_succ, ih, Nat.succ_mul, Nat.add_comm]

theorem physical_repeat (word front payload : List Bool) (n : Nat) :
    EthInapproximability.CurrentPaper.SourceNormalizationMachineRepeatStream.run
      (n * (2 * word.length + 3) + 1)
      (EthInapproximability.CurrentPaper.SourceNormalizationMachineRepeatStream.cfg
        (some .next) none word [] (List.replicate n true) front payload) =
    EthInapproximability.CurrentPaper.SourceNormalizationMachineRepeatStream.cfg
      none none word [] [] (repeatWord n word ++ front) payload := by
  simpa only [repeated_eq_repeatWord] using
    (EthInapproximability.CurrentPaper.SourceNormalizationMachineRepeatStream.repeat_run
      word front payload n none)

/-- The physical primitive starts from a literal false bit and a unary p bank,
constructing exactly the canonical seed row. The unrelated payload is retained. -/
theorem physical_seed_row (p : Nat) (front payload : List Bool) :
    EthInapproximability.CurrentPaper.SourceNormalizationMachineRepeatStream.run
      (p*5+1)
      (EthInapproximability.CurrentPaper.SourceNormalizationMachineRepeatStream.cfg
        (some .next) none [false] [] (List.replicate p true) front payload) =
    EthInapproximability.CurrentPaper.SourceNormalizationMachineRepeatStream.cfg
      none none [false] [] [] (List.replicate p false ++ front) payload := by
  simpa only [List.length_singleton, Nat.reduceMul, repeatWord_singleton] using
    physical_repeat [false] front payload p

theorem physical_repeat_output_sensitive (n : Nat) (word : List Bool) :
    n * (2 * word.length + 3) + 1 =
      2 * (repeatWord n word).length + 3*n + 1 := by
  rw [repeatWord_length]
  ring

#print axioms defaultLabels_encoded
#print axioms canonical_tail_encoded
#print axioms physical_repeat
#print axioms physical_seed_row

end Paper2.CanonicalDefaultWordScratch

namespace Paper2.CanonicalDefaultWordScratch.RowMachine

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

abbrev Stack := Fin 10
abbrev Control := Option Bool
abbrev RepeatPhase :=
  EthInapproximability.CurrentPaper.SourceNormalizationMachineRepeatStream.Phase

inductive Label where
  | copyQ1 (l : BitMachineCopy.Label)
  | repeatQ1 (l : RepeatPhase)
  | copyS (l : BitMachineCopy.Label)
  | repeatS (l : RepeatPhase)
  | mark
  | repeatOne (l : RepeatPhase)
  | header
  | copyQ (l : BitMachineCopy.Label)
  | repeatQ (l : RepeatPhase)
  | done
  deriving DecidableEq, Fintype

def copyQ1Index : Fin 3 ↪ Stack where
  toFun i := ![0,4,8] i
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all

def copySIndex : Fin 3 ↪ Stack where
  toFun i := ![1,4,8] i
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all

def copyQIndex : Fin 3 ↪ Stack where
  toFun i := ![2,4,8] i
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all

def innerIndex : Fin 5 ↪ Stack where
  toFun i := ![3,5,4,6,9] i
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all

def outerIndex : Fin 5 ↪ Stack where
  toFun i := ![6,5,4,7,9] i
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all

/-- This table is independent of q1,s,Q and the previous column word.
They are data in literal Boolean stacks. -/
noncomputable def program : Label →
    TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .copyQ1 l => BitMachineStackEmbedding.stmt copyQ1Index
      Label.copyQ1 id id (some (.repeatQ1 .next)) (BitMachineCopy.program l)
  | .repeatQ1 l => BitMachineStackEmbedding.stmt innerIndex
      Label.repeatQ1 id id (some (.copyS .scan))
        (SourceNormalizationMachineRepeatStream.program l)
  | .copyS l => BitMachineStackEmbedding.stmt copySIndex
      Label.copyS id id (some (.repeatS .next)) (BitMachineCopy.program l)
  | .repeatS l => BitMachineStackEmbedding.stmt innerIndex
      Label.repeatS id id (some .mark)
        (SourceNormalizationMachineRepeatStream.program l)
  | .mark => push 4 (fun _ => true) (goto (fun _ => .repeatOne .next))
  | .repeatOne l => BitMachineStackEmbedding.stmt innerIndex
      Label.repeatOne id id (some .header)
        (SourceNormalizationMachineRepeatStream.program l)
  | .header =>
      push 6 (fun _ => false) (push 6 (fun _ => true)
        (push 6 (fun _ => true) (push 6 (fun _ => false)
          (goto (fun _ => .copyQ .scan)))))
  | .copyQ l => BitMachineStackEmbedding.stmt copyQIndex
      Label.copyQ id id (some (.repeatQ .next)) (BitMachineCopy.program l)
  | .repeatQ l => BitMachineStackEmbedding.stmt outerIndex
      Label.repeatQ id id (some .done)
        (SourceNormalizationMachineRepeatStream.program l)
  | .done => halt

def initial (q₁ s Q : Nat) (column payload : List Bool) :
    TM2.Cfg (fun _ : Stack => Bool) Label Control :=
  ⟨some (.copyQ1 .scan),none,
    ![List.replicate q₁ true, List.replicate s true,
      List.replicate Q true, column, [], [], [], [], [], payload]⟩

def bank0 (q₁ s Q : Nat) (column payload : List Bool) : Stack → List Bool :=
  (initial q₁ s Q column payload).stk

def bank1 (q₁ s Q : Nat) (column payload : List Bool) : Stack → List Bool :=
  Function.update (bank0 q₁ s Q column payload) 4 (List.replicate q₁ true)

noncomputable def run (t : Nat) (c : TM2.Cfg (fun _ : Stack => Bool) Label Control) :=
  ((advance program)^[t]) c

theorem copy_phase (index : Fin 3 ↪ Stack)
    (wrap : BitMachineCopy.Label → Label) (next : Label)
    (hprog : ∀ l, program (wrap l) =
      BitMachineStackEmbedding.stmt index wrap id id (some next)
        (BitMachineCopy.program l))
    (S : Stack → List Bool) (source target : List Bool)
    (hsource : S (index 0) = source)
    (htarget : S (index 1) = target)
    (hscratch : S (index 2) = []) :
    ∃ t ≤ 2*source.length+2,
      run t ⟨some (wrap .scan),none,S⟩ =
        ⟨some next,none,
          BitMachineStackEmbedding.bank index S
            (BitMachineCopy.cfg none none source
              (source ++ target) []).stk⟩ := by
  let c := BitMachineCopy.cfg (some .scan) none source target []
  have hi : BitMachineStackEmbedding.bank index S c.stk = S := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro i
    fin_cases i <;> simp [c, BitMachineCopy.cfg,
      BitMachineCopy.stackContents, hsource, htarget, hscratch]
  have hraw : ((advance BitMachineCopy.program)^[2*source.length+2]) c =
      BitMachineCopy.cfg none none source (source ++ target) [] :=
    BitMachineCopy.run_correct none source target
  have hhalt : (((advance BitMachineCopy.program)^[2*source.length+2]) c).l =
      none := by rw [hraw]; rfl
  obtain ⟨t,ht,hr⟩ := BitMachineStackEmbedding.outputs
    index S wrap id id (by intro; rfl) (some next)
    BitMachineCopy.program program hprog c
    (2*source.length+2) hhalt
  refine ⟨t,ht,?_⟩
  rw [hraw] at hr
  simpa only [run, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    hi, Option.map_some, Option.map_none] using hr

theorem repeat_phase (index : Fin 5 ↪ Stack)
    (wrap : RepeatPhase → Label) (next : Label)
    (hprog : ∀ l, program (wrap l) =
      BitMachineStackEmbedding.stmt index wrap id id (some next)
        (SourceNormalizationMachineRepeatStream.program l))
    (S : Stack → List Bool) (source front payload : List Bool) (n : Nat)
    (hsource : S (index 0) = source)
    (hscratch : S (index 1) = [])
    (hcount : S (index 2) = List.replicate n true)
    (hfront : S (index 3) = front)
    (hpayload : S (index 4) = payload) :
    ∃ t ≤ n*(2*source.length+3)+1,
      run t ⟨some (wrap .next),none,S⟩ =
        ⟨some next,none,
          BitMachineStackEmbedding.bank index S
            (SourceNormalizationMachineRepeatStream.cfg none none
              source [] [] (repeatWord n source ++ front) payload).stk⟩ := by
  let c := SourceNormalizationMachineRepeatStream.cfg (some .next) none
    source [] (List.replicate n true) front payload
  have hi : BitMachineStackEmbedding.bank index S c.stk = S := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro i
    fin_cases i <;> simp [c, SourceNormalizationMachineRepeatStream.cfg,
      hsource, hscratch, hcount, hfront, hpayload]
  have hraw : ((advance SourceNormalizationMachineRepeatStream.program)^[n*(2*source.length+3)+1]) c =
      SourceNormalizationMachineRepeatStream.cfg none none source [] []
        (repeatWord n source ++ front) payload :=
    physical_repeat source front payload n
  have hhalt : (((advance SourceNormalizationMachineRepeatStream.program)^[n*(2*source.length+3)+1]) c).l = none := by rw [hraw]; rfl
  obtain ⟨t,ht,hr⟩ := BitMachineStackEmbedding.outputs
    index S wrap id id (by intro; rfl) (some next)
    SourceNormalizationMachineRepeatStream.program program hprog c
    (n*(2*source.length+3)+1) hhalt
  refine ⟨t,ht,?_⟩
  rw [hraw] at hr
  simpa only [run, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    hi, Option.map_some, Option.map_none] using hr

theorem copy_phase_update (index : Fin 3 ↪ Stack)
    (wrap : BitMachineCopy.Label → Label) (next : Label)
    (hprog : ∀ l, program (wrap l) =
      BitMachineStackEmbedding.stmt index wrap id id (some next)
        (BitMachineCopy.program l))
    (S : Stack → List Bool) (source target : List Bool)
    (hsource : S (index 0) = source)
    (htarget : S (index 1) = target)
    (hscratch : S (index 2) = []) :
    ∃ t ≤ 2*source.length+2,
      run t ⟨some (wrap .scan),none,S⟩ =
        ⟨some next,none,
          Function.update S (index 1) (source ++ target)⟩ := by
  obtain ⟨t,ht,hr⟩ := copy_phase index wrap next hprog S source target
    hsource htarget hscratch
  refine ⟨t,ht,?_⟩
  rw [hr]
  congr 1
  have hbase : BitMachineStackEmbedding.bank index S
      (BitMachineCopy.cfg (some .scan) none source target []).stk = S := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro i
    fin_cases i <;> simp [BitMachineCopy.cfg,
      BitMachineCopy.stackContents, hsource, htarget, hscratch]
  have hupdate :
      (BitMachineCopy.cfg none none source (source ++ target) []).stk =
      Function.update
        (BitMachineCopy.cfg (some .scan) none source target []).stk
        (1 : Fin 3) (source ++ target) := by
    funext i
    fin_cases i <;> rfl
  rw [hupdate, BitMachineStackEmbedding.bank_update, hbase]

theorem repeat_phase_update (index : Fin 5 ↪ Stack)
    (wrap : RepeatPhase → Label) (next : Label)
    (hprog : ∀ l, program (wrap l) =
      BitMachineStackEmbedding.stmt index wrap id id (some next)
        (SourceNormalizationMachineRepeatStream.program l))
    (S : Stack → List Bool) (source front payload : List Bool) (n : Nat)
    (hsource : S (index 0) = source)
    (hscratch : S (index 1) = [])
    (hcount : S (index 2) = List.replicate n true)
    (hfront : S (index 3) = front)
    (hpayload : S (index 4) = payload) :
    ∃ t ≤ n*(2*source.length+3)+1,
      run t ⟨some (wrap .next),none,S⟩ =
        ⟨some next,none,
          Function.update (Function.update S (index 2) [])
            (index 3) (repeatWord n source ++ front)⟩ := by
  obtain ⟨t,ht,hr⟩ := repeat_phase index wrap next hprog S source front payload n
    hsource hscratch hcount hfront hpayload
  refine ⟨t,ht,?_⟩
  rw [hr]
  congr 1
  have hbase : BitMachineStackEmbedding.bank index S
      (SourceNormalizationMachineRepeatStream.cfg (some .next) none
        source [] (List.replicate n true) front payload).stk = S := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro i
    fin_cases i <;> simp [SourceNormalizationMachineRepeatStream.cfg,
      hsource, hscratch, hcount, hfront, hpayload]
  have hupdate :
      (SourceNormalizationMachineRepeatStream.cfg none none source [] []
        (repeatWord n source ++ front) payload).stk =
      Function.update
        (Function.update
          (SourceNormalizationMachineRepeatStream.cfg (some .next) none
            source [] (List.replicate n true) front payload).stk
          (2 : Fin 5) [])
        (3 : Fin 5) (repeatWord n source ++ front) := by
    funext i
    fin_cases i <;> rfl
  rw [hupdate, BitMachineStackEmbedding.bank_update,
    BitMachineStackEmbedding.bank_update, hbase]

#print axioms copy_phase
#print axioms repeat_phase
#print axioms copy_phase_update
#print axioms repeat_phase_update

theorem copy_q1_run (q₁ s Q : Nat) (column payload : List Bool) :
    ∃ t ≤ 2*q₁+2,
      run t (initial q₁ s Q column payload) =
        ⟨some (.repeatQ1 .next),none,bank1 q₁ s Q column payload⟩ := by
  have h := copy_phase_update copyQ1Index Label.copyQ1
    (.repeatQ1 .next) (by intro l; rfl)
    (bank0 q₁ s Q column payload)
    (List.replicate q₁ true) [] (by rfl) (by rfl) (by rfl)
  simpa only [bank0, bank1, initial, List.length_replicate,
    List.append_nil] using h

#print axioms copy_q1_run

end Paper2.CanonicalDefaultWordScratch.RowMachine
