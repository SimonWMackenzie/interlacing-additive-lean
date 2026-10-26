import CurrentAdditive.V40LawActualProduct
import CurrentAdditive.LawProductFormatter
import CurrentAdditive.V40LawJobsClock
import CurrentAdditive.V40LawCartesianRows
import Mathlib.Data.List.OfFn

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

namespace CurrentAdditive.V40LawJobOrder
open EthInapproximability.CurrentPaper V40LawJobsClock
open Paper2 V39GeneratedConstruction
noncomputable section

def entries {m : ℕ} (μ : PositiveRationalLaw (Fin m)) : List (List Bool) :=
  List.ofFn (fun i => CodeDTargetV2.alphabetEntry (i.val,μ.weight i))

theorem lawBytes_entries {m : ℕ} (μ : PositiveRationalLaw (Fin m)) :
    CodeDTargetV2.alphabetBytes (IndexedLaw.indexedAlphabet μ.weight)=
      SourceListEncoding.encode (entries μ) := by
  simp [CodeDTargetV2.alphabetBytes,CodeDCodecV2.encodeItems,
    IndexedLaw.indexedAlphabet,entries,List.map_ofFn,Function.comp_def]

def pairs {m n : ℕ} (μ : PositiveRationalLaw (Fin m))
    (ν : PositiveRationalLaw (Fin n)) : List (List Bool × List Bool) :=
  List.ofFn (fun k : Fin (m*n) =>
    let ij := finProdFinEquiv.symm k
    (V40LawProductEntry.input k.val (μ.weight ij.1) (ν.weight ij.2),
      V40LawPacket.packet ij.1.val.bits ij.2.val.bits))

def nestedRecords {m n : ℕ} (μ : PositiveRationalLaw (Fin m))
    (ν : PositiveRationalLaw (Fin n)) : List (List Bool) :=
  (List.ofFn (fun i : Fin m => (i.val,μ.weight i))).flatMap
    (fun a => (List.ofFn (fun j : Fin n => (j.val,ν.weight j))).map
      (fun b => LawProductFormatter.output n a.1 b.1 a.2 b.2))

theorem prod_inverse {m n : ℕ} (i : Fin m) (j : Fin n) :
    finProdFinEquiv.symm (⟨i.val*n+j.val,by
      calc
        i.val*n+j.val < (i.val+1)*n :=
          (Nat.add_lt_add_left j.isLt _).trans_eq (by ring)
        _ ≤ m*n := Nat.mul_le_mul_right n i.isLt⟩ : Fin (m*n)) = (i,j) := by
  have he : (⟨i.val*n+j.val,by
      calc
        i.val*n+j.val < (i.val+1)*n :=
          (Nat.add_lt_add_left j.isLt _).trans_eq (by ring)
        _ ≤ m*n := Nat.mul_le_mul_right n i.isLt⟩ : Fin (m*n)) = finProdFinEquiv (i,j) := by
    apply Fin.ext
    simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
  rw [he,Equiv.symm_apply_apply]

theorem nestedRecords_pairs {m n : ℕ} (μ : PositiveRationalLaw (Fin m))
    (ν : PositiveRationalLaw (Fin n)) :
    nestedRecords μ ν=(pairs μ ν).map (fun p => V40LawPacket.packet p.1 p.2) := by
  simp only [nestedRecords,List.flatMap_def,List.map_ofFn,pairs,Function.comp_def]
  rw [List.ofFn_mul]
  congr 1
  apply congrArg List.ofFn
  funext i
  simp only [List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  rw [prod_inverse]
  simp [LawProductFormatter.output,packet_eq]

theorem jobs {m n : ℕ} (μ : PositiveRationalLaw (Fin m))
    (ν : PositiveRationalLaw (Fin n)) :
    (pairs μ ν).map Prod.fst=
      V40LawProductList.inputItems (V40LawActualProduct.productJobs μ ν) := by
  simp [pairs,V40LawProductList.inputItems,V40LawActualProduct.productJobs,
    List.map_ofFn,Function.comp_def]

def companions {m n : ℕ} (μ : PositiveRationalLaw (Fin m))
    (ν : PositiveRationalLaw (Fin n)) : List Bool :=
  SourceListEncoding.encode ((pairs μ ν).map Prod.snd)

theorem companions_exact {m n : ℕ} (μ : PositiveRationalLaw (Fin m))
    (ν : PositiveRationalLaw (Fin n)) :
    companions μ ν = SourceListEncoding.encode (List.ofFn (fun k : Fin (m*n) =>
      let ij := finProdFinEquiv.symm k
      BitMachineBankCodec.encode (![ij.1.val.bits,ij.2.val.bits] : Fin 2 → List Bool))) := by
  simp [companions,pairs,List.map_ofFn,packet_eq,Function.comp_def]

theorem positions {m n : ℕ} (μ : PositiveRationalLaw (Fin m))
    (ν : PositiveRationalLaw (Fin n)) : (pairs μ ν).length=m*n := by simp [pairs]

theorem physical_rows {m n : ℕ} (μ : PositiveRationalLaw (Fin m))
    (ν : PositiveRationalLaw (Fin n)) :
    V40LawCartesianRows.output (n.bits,entries μ,entries ν)=
      SourceListEncoding.fields (nestedRecords μ ν) := by
  simpa only [List.map_ofFn,entries,nestedRecords,Function.comp_def] using
    V40LawCartesianRows.output_typed n
      (List.ofFn (fun i : Fin m => (i.val,μ.weight i)))
      (List.ofFn (fun j : Fin n => (j.val,ν.weight j)))

#print axioms nestedRecords_pairs
#print axioms jobs
#print axioms companions_exact
end
end CurrentAdditive.V40LawJobOrder
