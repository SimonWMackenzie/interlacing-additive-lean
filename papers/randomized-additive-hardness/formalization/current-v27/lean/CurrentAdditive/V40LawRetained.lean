import CurrentAdditive.V40UniformLawJobs

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

namespace CurrentAdditive.V40LawRetained
open EthInapproximability.CurrentPaper V40LawJobsClock
noncomputable section

def product : BitMachine.Machine := V40LawBankMap.liftMachine V40StoredLawOperations.productWithCompanion
def mixture : BitMachine.Machine := V40LawBankMap.liftMachine V40StoredLawOperations.mixtureWithCompanion
def uniform (branch : Bool) : BitMachine.Machine := V40LawBankMap.liftMachine (V40UniformLawJobs.machine branch)

theorem product_realizes : Realizes product
    (fun a : List Bool × V40StoredLawOperations.Data =>
      V40LawPacket.packet a.1 (V40StoredLawOperations.input a.2))
    (fun a => V40LawPacket.packet a.1 (V40StoredLawOperations.productOutput a.2)) := by
  have h : Realizes V40StoredLawOperations.productWithCompanion
      (fun a : List Bool × V40StoredLawOperations.Data => V40StoredLawOperations.input a.2)
      (fun a => V40StoredLawOperations.productOutput a.2) := by
    obtain ⟨C,d,h⟩ := V40StoredLawOperations.product_realizes
    exact ⟨C,d,fun a => h a.2⟩
  exact bank_map _ Prod.fst _ _ h

theorem mixture_realizes : Realizes mixture
    (fun a : List Bool × V40StoredLawOperations.Data =>
      V40LawPacket.packet a.1 (V40StoredLawOperations.input a.2))
    (fun a => V40LawPacket.packet a.1 (V40StoredLawOperations.mixtureOutput a.2)) := by
  have h : Realizes V40StoredLawOperations.mixtureWithCompanion
      (fun a : List Bool × V40StoredLawOperations.Data => V40StoredLawOperations.input a.2)
      (fun a => V40StoredLawOperations.mixtureOutput a.2) := by
    obtain ⟨C,d,h⟩ := V40StoredLawOperations.mixture_realizes
    exact ⟨C,d,fun a => h a.2⟩
  exact bank_map _ Prod.fst _ _ h

theorem uniform_realizes (branch : Bool) : Realizes (uniform branch)
    (fun a : List Bool × V40UniformLawJobs.Data =>
      V40LawPacket.packet a.1 (V40UniformLawJobs.input a.2))
    (fun a => V40LawPacket.packet a.1 (V40UniformLawJobs.output branch a.2)) := by
  have h : Realizes (V40UniformLawJobs.machine branch)
      (fun a : List Bool × V40UniformLawJobs.Data => V40UniformLawJobs.input a.2)
      (fun a => V40UniformLawJobs.output branch a.2) := by
    obtain ⟨C,d,h⟩ := V40UniformLawJobs.realizes branch
    exact ⟨C,d,fun a => h a.2⟩
  exact bank_map _ Prod.fst _ _ h

/-- The context is an arbitrary literal word, so it may contain every
previous source packet and the complete caller state. It is restored by the
same physical packet lift, with its copy/serialization cost charged. -/
theorem retained_context (branch : Bool) : ∃ C d : ℕ,
    ∀ (context : List Bool) (a : V40UniformLawJobs.Data),
    (uniform branch).OutputsWithin
      (V40LawPacket.packet context (V40UniformLawJobs.input a))
      (V40LawPacket.packet context (V40UniformLawJobs.output branch a))
      (C*((V40LawPacket.packet context (V40UniformLawJobs.input a)).length+1)^d) := by
  obtain ⟨C,d,h⟩ := uniform_realizes branch
  exact ⟨C,d,fun context a => h (context,a)⟩

#print axioms product_realizes
#print axioms mixture_realizes
#print axioms retained_context
end
end CurrentAdditive.V40LawRetained
