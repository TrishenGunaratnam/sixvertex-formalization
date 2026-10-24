import SixVertex.PhysicalTransferPrimitive
import SixVertex.WeightedPerronBound

namespace SixVertex
noncomputable section

/-- Genuine finite-sector Perron data for the actual transfer row,
using the actual positive simple ground-state line. Every field is
proved by the construction below;none is an external assumption. -/
structure PhysicalSectorPerronData (lam eta : ℝ) (n particles : ℕ) (mu tau : ℝ)
    (v : ParticleConfigurations (n+2) particles → ℝ) : Prop where
  positive : ∀ q,0<v q
  ground_eigen : (complexSectorHamiltonian lam eta n particles).mulVec (fun q => (v q : ℂ))=
    (mu : ℂ) • (fun q => (v q : ℂ))
  ground_lower : ∀ w : ParticleConfigurations (n+2) particles → ℂ,
    mu*(∑ q,‖w q‖^2)≤complexMatrixRealEnergy (complexSectorHamiltonian lam eta n particles) w
  root_positive : 0<tau
  transfer_eigen : (complexSectorTransfer lam n particles ((lam : ℂ)/2)).mulVec (fun q => (v q : ℂ))=
    (tau : ℂ) • (fun q => (v q : ℂ))
  spectral_bound : ∀ (z : ℂ) (w : ParticleConfigurations (n+2) particles → ℂ),w≠0 →
    (complexSectorTransfer lam n particles ((lam : ℂ)/2)).mulVec w=z • w → ‖z‖≤tau
  simple : ∀ w : ParticleConfigurations (n+2) particles → ℂ,
    (complexSectorTransfer lam n particles ((lam : ℂ)/2)).mulVec w=(tau : ℂ) • w →
      ∃ c : ℂ,w=c • (fun q => (v q : ℂ))
  primitive : ∃ N : ℕ,0<N ∧ ∀ q r : ParticleConfigurations (n+2) particles,
    0<(((complexSectorTransfer lam n particles ((lam : ℂ)/2))^N) q r).re

/-- The actual positive simple Hamiltonian minimum is the actual
physical transfer Perron line in every valid particle sector. This
constructs the canonical line;identifying the Bethe vector with it is
still a separate mathematical obligation. -/
theorem exists_physical_sector_perron_data (lam eta : ℝ) (h0 : 0<lam)
    (hpi : lam<Real.pi) (heta : 0<eta) (n particles : ℕ) (hp : particles≤n+2) :
    ∃ (mu tau : ℝ) (v : ParticleConfigurations (n+2) particles → ℝ),
      PhysicalSectorPerronData lam eta n particles mu tau v := by
  obtain ⟨q,hq⟩ := exists_minusCount_eq (n+2) particles hp
  letI : Nonempty (ParticleConfigurations (n+2) particles) := ⟨⟨q,hq⟩⟩
  obtain ⟨mu,v,hpos,hground,hlower,hcommon⟩ := physical_positive_ground_state_common_transfer_line
    lam eta h0 hpi heta n particles hp
  obtain ⟨tau,htau⟩ := hcommon ((lam : ℂ)/2)
  let B := realPositiveSectorTransfer lam n particles
  have hmap := complexSectorTransfer_midpoint_eq_real_map lam h0 hpi n particles
  have hcomplex : (B.map Complex.ofReal).mulVec (fun q => (v q : ℂ))=
      tau • (fun q => (v q : ℂ)) := by rw [← hmap];exact htau
  have hreal := (positive_real_eigenvector_complex_root_real B v hpos tau hcomplex).2
  have hB := realPositiveSectorTransfer_nonnegative lam h0 hpi n particles
  have hd := realPositiveSectorTransfer_diagonal_pos lam h0 hpi n particles
  have hroot := positive_eigenvalue_of_nonnegative_diagonal B hB hd v hpos tau.re hreal
  have hsimple : ∀ w : ParticleConfigurations (n+2) particles → ℝ,
      B.mulVec w=tau.re • w → ∃ c : ℝ,w=c • v := by
    intro w hw
    exact positive_eigenvector_nonnegative_eigenspace_simple B hB
      (physicalPositiveTransferGraph lam n particles)
      (physicalPositiveTransferGraph_preconnected lam h0 hpi n particles)
      (fun _ _ h => h.2.1) v hpos tau.re hreal w hw
  refine ⟨mu,tau.re,v,⟨hpos,hground,hlower,hroot,?_,?_,?_,?_⟩⟩
  · rw [hmap]
    exact real_eigenvector_complexify B tau.re v hreal
  · intro z w hw he
    rw [hmap] at he
    exact positive_eigenvector_bounds_complex_eigenvalues B hB v hpos tau.re hreal z w hw he
  · intro w he
    rw [hmap] at he
    exact real_simple_eigenspace_complexify B tau.re v hsimple w he
  · exact physical_positive_transfer_sector_primitive lam h0 hpi n particles

end
end SixVertex
