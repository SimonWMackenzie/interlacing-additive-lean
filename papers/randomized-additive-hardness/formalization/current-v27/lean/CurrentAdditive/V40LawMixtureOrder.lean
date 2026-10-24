import CurrentAdditive.V40LawMixtureRows
import CurrentAdditive.V40LawJobOrder

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

namespace CurrentAdditive.V40LawMixtureOrder
open EthInapproximability.CurrentPaper
open Paper2 V40LawJobsClock V40LawJobOrder
noncomputable section

def pairs {m n : ℕ} (μ : PositiveRationalLaw (Fin m))
    (ν : PositiveRationalLaw (Fin n)) : List (List Bool × List Bool) :=
  (List.ofFn (fun i : Fin m =>
    (V40LawProductEntry.input i.val ((255 : ℚ)/256) (μ.weight i),
      V40LawPacket.packet [false] i.val.bits))) ++
  (List.ofFn (fun j : Fin n =>
    (V40LawProductEntry.input (m+j.val) ((1 : ℚ)/256) (ν.weight j),
      V40LawPacket.packet [true] j.val.bits)))

def leftRecords {m : ℕ} (μ : PositiveRationalLaw (Fin m)) : List (List Bool) :=
  List.ofFn (fun i : Fin m => LawMixtureFormatter.output false 0 i.val (μ.weight i))

def rightRecords {m n : ℕ} (_μ : PositiveRationalLaw (Fin m))
    (ν : PositiveRationalLaw (Fin n)) : List (List Bool) :=
  List.ofFn (fun j : Fin n => LawMixtureFormatter.output true m j.val (ν.weight j))

def records {m n : ℕ} (μ : PositiveRationalLaw (Fin m))
    (ν : PositiveRationalLaw (Fin n)) : List (List Bool) := leftRecords μ ++ rightRecords μ ν

theorem records_pairs {m n : ℕ} (μ : PositiveRationalLaw (Fin m))
    (ν : PositiveRationalLaw (Fin n)) :
    records μ ν=(pairs μ ν).map (fun p => V40LawPacket.packet p.1 p.2) := by
  simp [records,leftRecords,rightRecords,pairs,List.map_ofFn,Function.comp_def,
    LawMixtureFormatter.output,LawMixtureFormatter.mass,packet_eq]

theorem sum_inverse_left {m n : ℕ} (h : m ≤ m+n) (i : Fin m) :
    finSumFinEquiv.symm (Fin.castLE h i)=Sum.inl i := by
  have he : Fin.castLE h i=Fin.castAdd n i := Fin.ext rfl
  rw [he,finSumFinEquiv_symm_apply_castAdd]

theorem jobs {m n : ℕ} (μ : PositiveRationalLaw (Fin m))
    (ν : PositiveRationalLaw (Fin n)) :
    (pairs μ ν).map Prod.fst=
      V40LawProductList.inputItems (V40LawActualProduct.mixtureJobs μ ν) := by
  simp [pairs,V40LawProductList.inputItems,V40LawActualProduct.mixtureJobs,
    List.map_ofFn,List.ofFn_add,Function.comp_def,
    sum_inverse_left,finSumFinEquiv_symm_apply_natAdd]

def companions {m n : ℕ} (μ : PositiveRationalLaw (Fin m))
    (ν : PositiveRationalLaw (Fin n)) : List Bool :=
  SourceListEncoding.encode ((pairs μ ν).map Prod.snd)

theorem companions_exact {m n : ℕ} (μ : PositiveRationalLaw (Fin m))
    (ν : PositiveRationalLaw (Fin n)) : companions μ ν=
      SourceListEncoding.encode
        ((List.ofFn (fun i : Fin m => BitMachineBankCodec.encode
          (![[false],i.val.bits] : Fin 2 → List Bool))) ++
         (List.ofFn (fun j : Fin n => BitMachineBankCodec.encode
          (![[true],j.val.bits] : Fin 2 → List Bool)))) := by
  simp [companions,pairs,List.map_ofFn,packet_eq,Function.comp_def]

theorem records_length {m n : ℕ} (μ : PositiveRationalLaw (Fin m))
    (ν : PositiveRationalLaw (Fin n)) : (records μ ν).length=m+n := by
  simp [records,leftRecords,rightRecords]

theorem left_rows {m : ℕ} (μ : PositiveRationalLaw (Fin m)) :
    V40LawMixtureRows.output false ((0 : ℕ).bits,entries μ)=
      SourceListEncoding.fields (leftRecords μ) := by
  simpa only [List.map_ofFn,entries,leftRecords,Function.comp_def] using
    V40LawMixtureRows.output_typed false 0
      (List.ofFn (fun i : Fin m => (i.val,μ.weight i)))

theorem right_rows {m n : ℕ} (μ : PositiveRationalLaw (Fin m))
    (ν : PositiveRationalLaw (Fin n)) :
    V40LawMixtureRows.output true (m.bits,entries ν)=
      SourceListEncoding.fields (rightRecords μ ν) := by
  simpa only [List.map_ofFn,entries,rightRecords,Function.comp_def] using
    V40LawMixtureRows.output_typed true m
      (List.ofFn (fun j : Fin n => (j.val,ν.weight j)))

#print axioms records_pairs
#print axioms jobs
#print axioms companions_exact
end
end CurrentAdditive.V40LawMixtureOrder
