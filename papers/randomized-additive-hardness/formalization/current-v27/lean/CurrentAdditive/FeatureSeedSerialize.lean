import CurrentAdditive.FeatureSeedPrepare
import EthInapproximability.CurrentPaper.BitMachineBankSerialize
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

namespace CurrentAdditive.FeatureSeedSerialize
noncomputable section
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open FeatureSeedPrepare
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

def serializeProgram {J : Type} [DecidableEq J] {K : Nat} (loc : (Fin K ⊕ Fin 3) ↪ J)
    (l : BitMachineBankSerialize.Label K) :=
  BitMachineStackEmbedding.stmt loc id id id none (BitMachineBankSerialize.program K l)

def finish {J : Type} [DecidableEq J] {K : Nat} (loc : (Fin K ⊕ Fin 3) ↪ J)
    (S : J → List Bool) (sf : Fin K → List Bool) (packet : List Bool) :=
  BitMachineStackEmbedding.bank loc S (BitMachineBankSerialize.contents sf [] [] packet)

theorem serialize {J : Type} [DecidableEq J] {K : Nat} (loc : (Fin K ⊕ Fin 3) ↪ J)
    (S : J → List Bool) (haux : ∀ i, S (loc (.inr i)) = []) :
    let words := fun i => S (loc (.inl i))
    let packet := BitMachineBankCodec.encode words
    ∃ t ≤ 2 * packet.length + 2, ∃ sf : Fin K → List Bool,
      ((advance (serializeProgram loc))^[t])
        (⟨some (.emit 0),none,S⟩ : TM2.Cfg (fun _ : J => Bool) _ _) =
      ⟨none,none,finish loc S sf packet⟩ := by
  let words := fun i => S (loc (.inl i))
  let packet := BitMachineBankCodec.encode words
  obtain ⟨t,sf,ht,hr⟩ := BitMachineBankSerialize.serialize words [] []
  let c := BitMachineBankSerialize.cfg (some (.emit 0)) none words [] [] []
  have hh : (((advance (BitMachineBankSerialize.program K))^[t]) c).l = none := by
    change (BitMachineBankSerialize.run t c).l = none
    rw [hr]
    rfl
  obtain ⟨u,hu,he⟩ := BitMachineStackEmbedding.outputs loc S id id id
    (by intro v; rfl) none (BitMachineBankSerialize.program K) (serializeProgram loc)
    (by intro l; rfl) c t hh
  have hstart : BitMachineStackEmbedding.cfg loc S id id none c =
      (⟨some (.emit 0),none,S⟩ : TM2.Cfg (fun _ : J => Bool) _ _) := by
    have hb : BitMachineStackEmbedding.bank loc S c.stk = S := by
      apply BitMachineStackEmbedding.bank_eq_self
      intro j
      cases j with
      | inl j => rfl
      | inr j => fin_cases j <;>
          simp [c,BitMachineBankSerialize.cfg,BitMachineBankSerialize.contents,haux]
    simpa [BitMachineStackEmbedding.cfg,BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg,c,BitMachineBankSerialize.cfg] using
      congrArg (fun bank => (⟨some (.emit 0),none,bank⟩ :
        TM2.Cfg (fun _ : J => Bool) (BitMachineBankSerialize.Label K) (Option Bool))) hb
  have hp : BitMachineBankSerialize.encode (List.ofFn words) = packet := by
    simp [packet,BitMachineBankCodec.encode_eq_list,BitMachineBankSerialize.encode]
  rw [hstart] at he
  change ((advance (serializeProgram loc))^[u]) _ =
    BitMachineStackEmbedding.cfg loc S id id none (BitMachineBankSerialize.run t c) at he
  have hr' : BitMachineBankSerialize.run t c =
      BitMachineBankSerialize.cfg none none sf [] [] packet := by
    simpa only [c,List.append_nil,hp] using hr
  rw [hr'] at he
  refine ⟨u,hu.trans ?_,sf,he⟩
  simpa only [hp] using ht

def loc96 : (Fin 96 ⊕ Fin 3) ↪ Bank := ⟨Sum.elim
  (fun i => cell ⟨i.val,by omega⟩) (![cell 100,cell 101,cell 102]),by
  intro i j h
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          apply congrArg Sum.inl
          apply Fin.ext
          exact congrArg (fun b : Bank => b.val) h
      | inr j => fin_cases j <;> have hv := congrArg (fun b : Bank => b.val) h <;>
                  dsimp [cell] at hv <;> have hi := i.isLt <;> omega
  | inr i =>
      cases j with
      | inl j => fin_cases i <;> have hv := congrArg (fun b : Bank => b.val) h <;>
                  dsimp [cell] at hv <;> have hj := j.isLt <;> omega
      | inr j => fin_cases i <;> fin_cases j <;> simp_all⟩

def loc2 : (Fin 2 ⊕ Fin 3) ↪ Bank := ⟨Sum.elim
  (![cell 102,cell 97]) (![cell 103,cell 104,cell 105]),by
  intro i j h
  cases i <;> cases j <;> rename_i i j <;>
    fin_cases i <;> fin_cases j <;> simp_all⟩

theorem loc96_outside (i : Fin 128) (h : 96 ≤ i.val) (hne : i.val ≠ 100)
    (hne' : i.val ≠ 101) (hne'' : i.val ≠ 102) :
    ¬ ∃ k,loc96 k = cell i := by
  rintro ⟨k,hk⟩
  cases k with
  | inl k =>
      have hv := congrArg (fun b : Bank => b.val) hk
      change k.val=i.val at hv
      have hh := k.isLt
      omega
  | inr k => fin_cases k <;> have hv := congrArg (fun b : Bank => b.val) hk <;>
              dsimp [loc96,cell] at hv <;> omega

def prepared (raw : List Bool) (q : Nat) (ys : List Nat) : Bank → List Bool :=
  seeded (afterCopy raw (List.replicate q true)
    (SourceListEncoding.encode (FeatureInnerAlphabetRun64.labelWords ys))
    (List.replicate ys.length true))

theorem prepared_low (raw : List Bool) (q : Nat) (ys : List Nat) :
    (fun i => prepared raw q ys (loc96 (.inl i))) = FeatureSeedLayout.bank raw ys := by
  funext i
  simp only [prepared,seeded,afterCopy,afterC,afterA,afterQ,rawBank,loc96,
    Function.Embedding.coeFn_mk,Sum.elim_inl,Function.update_apply,cell_eq]
  simp only [FeatureSeedLayout.bank]
  split_ifs <;> simp_all only [Fin.ext_iff] <;> omega

theorem prepared_aux (raw : List Bool) (q : Nat) (ys : List Nat) (i : Fin 3) :
    prepared raw q ys (loc96 (.inr i)) = [] := by
  fin_cases i <;> simp [prepared,seeded,afterCopy,afterC,afterA,afterQ,rawBank,loc96]

theorem prepared_at (raw : List Bool) (q : Nat) (ys : List Nat) :
    prepared raw q ys (cell 97)=List.replicate q true ∧
    prepared raw q ys (cell 96)=raw ∧
    prepared raw q ys (cell 103)=[] ∧ prepared raw q ys (cell 104)=[] ∧
    prepared raw q ys (cell 105)=[] := by
  simp [prepared,seeded,afterCopy,afterC,afterA,afterQ,rawBank]

def bank96 (raw : List Bool) (q : Nat) (ys : List Nat) (sf : Fin 96 → List Bool) :=
  finish loc96 (prepared raw q ys) sf (BitMachineBankCodec.encode (FeatureSeedLayout.bank raw ys))

theorem bank96_at (raw : List Bool) (q : Nat) (ys : List Nat) (sf : Fin 96 → List Bool) :
    bank96 raw q ys sf (cell 102)=BitMachineBankCodec.encode (FeatureSeedLayout.bank raw ys) ∧
    bank96 raw q ys sf (cell 97)=List.replicate q true ∧
    bank96 raw q ys sf (cell 96)=raw ∧
    bank96 raw q ys sf (cell 103)=[] ∧ bank96 raw q ys sf (cell 104)=[] ∧
    bank96 raw q ys sf (cell 105)=[] := by
  constructor
  · exact BitMachineStackEmbedding.bank_at loc96 _ _ (.inr 2)
  · simp only [bank96,finish]
    rw [BitMachineStackEmbedding.bank_outside loc96 _ _ (cell 97) (loc96_outside 97 (by decide) (by decide) (by decide) (by decide)),
      BitMachineStackEmbedding.bank_outside loc96 _ _ (cell 96) (loc96_outside 96 (by decide) (by decide) (by decide) (by decide)),
      BitMachineStackEmbedding.bank_outside loc96 _ _ (cell 103) (loc96_outside 103 (by decide) (by decide) (by decide) (by decide)),
      BitMachineStackEmbedding.bank_outside loc96 _ _ (cell 104) (loc96_outside 104 (by decide) (by decide) (by decide) (by decide)),
      BitMachineStackEmbedding.bank_outside loc96 _ _ (cell 105) (loc96_outside 105 (by decide) (by decide) (by decide) (by decide))]
    exact prepared_at raw q ys

#print axioms serialize
#print axioms prepared_low
#print axioms bank96_at
end
end CurrentAdditive.FeatureSeedSerialize
