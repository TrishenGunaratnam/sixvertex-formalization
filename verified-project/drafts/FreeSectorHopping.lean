import SixVertex.FreePhysicalHopping
import SixVertex.GroundStateTransferLine

namespace SixVertex
noncomputable section

/-- Extend a vector on one actual particle sector by zero. -/
def physicalSectorExtension {L particles : ℕ} (v : ParticleConfigurations L particles → ℂ)
    (q : RowSpins L) : ℂ := if h : minusCount L q=particles then v ⟨q,h⟩ else 0

theorem physicalSectorExtension_apply {L particles : ℕ} (v : ParticleConfigurations L particles → ℂ)
    (q : ParticleConfigurations L particles) : physicalSectorExtension v q.val=v q := by
  simp [physicalSectorExtension,q.property]

/-- The exact restricted Hamiltonian is the full physical Hamiltonian
applied to the zero extension,with its output evaluated in the sector. -/
theorem complexSectorHamiltonian_mulVec_eq_full (lam eta : ℝ) (n particles : ℕ)
    (v : ParticleConfigurations (n+2) particles → ℂ) (q : ParticleConfigurations (n+2) particles) :
    (complexSectorHamiltonian lam eta n particles).mulVec v q=
      (homogeneousLinkHamiltonian lam eta (n+1)).mulVec (physicalSectorExtension v) q.val := by
  classical
  let P := fun r : RowSpins (n+2) => minusCount (n+2) r=particles
  let f := fun r : RowSpins (n+2) => homogeneousLinkHamiltonian lam eta (n+1) q.val r*
    physicalSectorExtension v r
  have hf (r : RowSpins (n+2)) (hr : ¬P r) : f r=0 := by
    simp [f,physicalSectorExtension,show minusCount (n+2) r≠particles from hr]
  have hs := sum_subtype_eq_full_of_zero_outside P f hf
  change (∑ r : ParticleConfigurations (n+2) particles,
    homogeneousLinkHamiltonian lam eta (n+1) q.val r.val*v r)=∑ r : RowSpins (n+2),f r
  rw [← hs]
  apply Finset.sum_congr rfl
  intro r _
  exact congrArg (fun z : ℂ => homogeneousLinkHamiltonian lam eta (n+1) q.val r.val*z)
    (physicalSectorExtension_apply v r).symm

/-- One actual physical bond exchange,as a map on the exact particle sector. -/
def physicalSectorBondExchange (n particles k : ℕ) (q : ParticleConfigurations (n+2) particles) :
    ParticleConfigurations (n+2) particles :=
  ⟨physicalBondExchange n k q.val,(physicalBondExchange_minusCount n k q.val).trans q.property⟩

/-- Exact periodic-exchange action of the ACTUAL complex sector Hamiltonian.
No coordinate-Hamiltonian or eigenvector identity is assumed. -/
theorem complexSectorHamiltonian_freeFermion_mulVec (n particles : ℕ)
    (v : ParticleConfigurations (n+2) particles → ℂ) (q : ParticleConfigurations (n+2) particles) :
    (complexSectorHamiltonian (Real.pi/2) (1/2) n particles).mulVec v q=
      ∑ k : Fin (n+2),if (physicalBondRotation n k.val q.val).1≠(physicalBondRotation n k.val q.val).2.1
        then -(1/2 : ℂ)*v (physicalSectorBondExchange n particles k.val q) else 0 := by
  rw [complexSectorHamiltonian_mulVec_eq_full,homogeneousLinkHamiltonian_freeFermion_mulVec]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs
  · exact congrArg (fun z : ℂ => -(1/2 : ℂ)*z)
      (physicalSectorExtension_apply v (physicalSectorBondExchange n particles k.val q))
  · rfl

end
end SixVertex
