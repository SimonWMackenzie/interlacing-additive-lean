import EthInapproximability.CurrentPaper.SourcePrefixRawFrame
import EthInapproximability.CurrentPaper.BitMachineCopy

namespace EthInapproximability.CurrentPaper.SourcePrefixRawCopy

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.CurrentPaper.SourcePrefixRawFrame
open scoped Classical

def slots {q : Nat} (src dst : Stack q) (hs : src ≠ dst)
    (hx : src ≠ scratch) (hy : dst ≠ scratch) : Fin 3 ↪ Stack q where
  toFun k := if k = 0 then src else if k = 1 then dst else scratch
  inj' := by intro x y h; fin_cases x <;> fin_cases y <;> simp_all

def program {q : Nat} (src dst : Stack q) (hs : src ≠ dst)
    (hx : src ≠ scratch) (hy : dst ≠ scratch)
    (l : BitMachineCopy.Label) :
    TM2.Stmt (fun _ : Stack q => Bool) BitMachineCopy.Label (Option Bool) :=
  stmt (slots src dst hs hx hy) id id id none (BitMachineCopy.program l)

theorem framed {q : Nat} (src dst : Stack q) (hs : src ≠ dst)
    (hx : src ≠ scratch) (hy : dst ≠ scratch)
    (before : Stack q → List Bool) (word : List Bool)
    (hsrc : before src = word) (hdst : before dst = [])
    (hscratch : before scratch = []) :
    ∃ t S, t ≤ 2 * word.length + 2 ∧
      ((advance (program src dst hs hx hy))^[t])
        (⟨some .scan, none, before⟩ :
          TM2.Cfg (fun _ : Stack q => Bool)
            BitMachineCopy.Label (Option Bool)) =
        ⟨none, none, S⟩ ∧
      S src = word ∧ S dst = word ∧ S scratch = [] ∧
      (∀ k, k ≠ src → k ≠ dst → k ≠ scratch → S k = before k) := by
  let ι := slots src dst hs hx hy
  let localCfg := BitMachineCopy.cfg (some .scan) none word [] []
  have hhalt : (((advance BitMachineCopy.program)^[2 * word.length + 2])
      localCfg).l = none := by
    rw [show ((advance BitMachineCopy.program)^[2 * word.length + 2])
      localCfg = BitMachineCopy.cfg none none word word [] from by
      simpa only [BitMachineCopy.run, localCfg, List.append_nil] using
        BitMachineCopy.run_correct none word []]
    rfl
  obtain ⟨t, ht, hr⟩ := outputs ι before id id id (fun _ => rfl)
    none BitMachineCopy.program (program src dst hs hx hy)
    (fun _ => rfl) localCfg (2 * word.length + 2) hhalt
  have hstart : cfg ι before id id none localCfg =
      (⟨some .scan, none, before⟩ :
        TM2.Cfg (fun _ : Stack q => Bool)
          BitMachineCopy.Label (Option Bool)) := by
    simp only [cfg, stackCfg, BitMachineInline.cfg, localCfg,
      BitMachineCopy.cfg, id_eq]
    congr 1
    apply bank_eq_self
    intro k
    fin_cases k <;> simp [ι, slots, BitMachineCopy.stackContents,
      hsrc, hdst, hscratch]
  have hlocal : ((advance BitMachineCopy.program)^[2 * word.length + 2])
      localCfg = BitMachineCopy.cfg none none word word [] :=
    by simpa only [BitMachineCopy.run, localCfg, List.append_nil] using
      BitMachineCopy.run_correct none word []
  rw [hstart, hlocal] at hr
  let S := bank ι before (BitMachineCopy.stackContents word word [])
  refine ⟨t, S, ht, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [program, S, cfg, stackCfg, BitMachineInline.cfg,
      BitMachineCopy.cfg, id_eq, Option.map_none] using hr
  · change bank ι before _ (ι 0) = _
    rw [bank_at]
    rfl
  · change bank ι before _ (ι 1) = _
    rw [bank_at]
    rfl
  · change bank ι before _ (ι 2) = _
    rw [bank_at]
    rfl
  · intro k hk hl hm
    change bank ι before _ k = before k
    rw [bank_outside]
    rintro ⟨i, hi⟩
    fin_cases i
    · exact hk (by simpa [ι, slots] using hi.symm)
    · exact hl (by simpa [ι, slots] using hi.symm)
    · exact hm (by simpa [ι, slots] using hi.symm)

theorem framed_update {q : Nat} (src dst : Stack q) (hs : src ≠ dst)
    (hx : src ≠ scratch) (hy : dst ≠ scratch)
    (before : Stack q → List Bool) (word : List Bool)
    (hsrc : before src = word) (hdst : before dst = [])
    (hscratch : before scratch = []) :
    ∃ t ≤ 2 * word.length + 2,
      ((advance (program src dst hs hx hy))^[t])
        (⟨some .scan, none, before⟩ :
          TM2.Cfg (fun _ : Stack q => Bool)
            BitMachineCopy.Label (Option Bool)) =
        ⟨none, none, Function.update before dst word⟩ := by
  obtain ⟨t, S, ht, hr, hs, hd, hw, hf⟩ :=
    framed src dst hs hx hy before word hsrc hdst hscratch
  have hS : S = Function.update before dst word := by
    funext k
    by_cases hk : k = dst
    · subst k
      simpa only [Function.update_self] using hd
    · rw [Function.update_of_ne hk]
      by_cases hks : k = src
      · subst k
        exact hs.trans hsrc.symm
      · by_cases hkw : k = scratch
        · subst k
          exact hw.trans hscratch.symm
        · exact hf k hks hk hkw
  exact ⟨t, ht, hS ▸ hr⟩

end EthInapproximability.CurrentPaper.SourcePrefixRawCopy
