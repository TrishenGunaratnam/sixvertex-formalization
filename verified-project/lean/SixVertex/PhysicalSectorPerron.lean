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
constructs the canonical line. The continued Bethe vector is identified with
it at the free point and on a relative neighborhood of that endpoint; global
identification along the full physical interval remains separate. -/
theorem exists_physical_sector_perron_data (lam eta : ℝ) (h0 : 0<lam)
    (hpi : lam<Real.pi) (heta : 0<eta) (n particles : ℕ) (hp : particles≤n+2) :
    ∃ (mu tau : ℝ) (v : ParticleConfigurations (n+2) particles → ℝ),
      PhysicalSectorPerronData lam eta n particles mu tau v := by
  obtain ⟨q₀,hq₀⟩ := exists_minusCount_eq (n+2) particles hp
  let qInst : ParticleConfigurations (n+2) particles := ⟨q₀,hq₀⟩
  letI : Nonempty (ParticleConfigurations (n+2) particles) := ⟨qInst⟩
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

/-- Every strictly positive real eigenvector of the actual midpoint transfer
matrix belongs to the canonical Perron line. The proof compares its eigenvalue
with the positive ground-line eigenvector in both directions using the
weighted-coordinate bound; it does not assume Perron maximality. -/
theorem positive_real_transfer_vector_is_perron_line (lam eta : ℝ)
    (h0 : 0<lam) (hpi : lam<Real.pi) (heta : 0<eta)
    (n particles : ℕ) (hp : particles≤n+2)
    (w : ParticleConfigurations (n+2) particles → ℝ) (hwpos : ∀ q,0<w q)
    (rho : ℝ)
    (hwe : (realPositiveSectorTransfer lam n particles).mulVec w=rho • w) :
    ∃ (mu tau : ℝ) (v : ParticleConfigurations (n+2) particles → ℝ),
      PhysicalSectorPerronData lam eta n particles mu tau v ∧
      ∃ c : ℝ,w=c • v := by
  classical
  obtain ⟨q₀,hq₀⟩ := exists_minusCount_eq (n+2) particles hp
  let qInst : ParticleConfigurations (n+2) particles := ⟨q₀,hq₀⟩
  letI : Nonempty (ParticleConfigurations (n+2) particles) := ⟨qInst⟩
  obtain ⟨mu,tau,v,hdata⟩ :=
    exists_physical_sector_perron_data lam eta h0 hpi heta n particles hp
  let B := realPositiveSectorTransfer lam n particles
  have hB : ∀ i j,0≤B i j := realPositiveSectorTransfer_nonnegative lam h0 hpi n particles
  have hd : ∀ i,0<B i i := realPositiveSectorTransfer_diagonal_pos lam h0 hpi n particles
  have htransferV : (B.map Complex.ofReal).mulVec (fun q => (v q : ℂ))=
      (tau : ℂ) • (fun q => (v q : ℂ)) := by
    rw [← complexSectorTransfer_midpoint_eq_real_map lam h0 hpi n particles]
    exact hdata.transfer_eigen
  have hrealV : B.mulVec v=tau • v := by
    have h := (positive_real_eigenvector_complex_root_real B v hdata.positive
      (tau : ℂ) htransferV).2
    simpa using h
  have hVne : (fun q => (v q : ℂ))≠0 := by
    intro hz
    have hzero : (v qInst : ℂ)=0 := by simpa using congrFun hz qInst
    exact (hdata.positive qInst).ne' (Complex.ofReal_eq_zero.mp hzero)
  have hwne : w≠0 := by
    intro hz
    have hzero : w qInst=0 := congrFun hz qInst
    exact (hwpos qInst).ne' hzero
  have hwcomplexne : (fun q => (w q : ℂ))≠0 := by
    intro hz
    apply hwne
    funext i
    exact Complex.ofReal_eq_zero.mp (by simpa using congrFun hz i)
  have hwcomplex : (B.map Complex.ofReal).mulVec (fun q => (w q : ℂ))=
      (rho : ℂ) • (fun q => (w q : ℂ)) :=
    real_eigenvector_complexify B rho w hwe
  have hbound₁ := positive_eigenvector_bounds_complex_eigenvalues B hB v
    hdata.positive tau hrealV (rho : ℂ) (fun q => (w q : ℂ)) hwcomplexne hwcomplex
  have hbound₂ := positive_eigenvector_bounds_complex_eigenvalues B hB w
    hwpos rho hwe (tau : ℂ) (fun q => (v q : ℂ)) hVne htransferV
  have hrho_le : rho≤tau := by
    simpa [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (positive_eigenvalue_of_nonnegative_diagonal
      B hB hd w hwpos rho hwe)] using hbound₁
  have htau_le : tau≤rho := by
    simpa [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hdata.root_positive] using hbound₂
  have hrho : rho=tau := le_antisymm hrho_le htau_le
  have hsimple := positive_eigenvector_nonnegative_eigenspace_simple B hB
    (physicalPositiveTransferGraph lam n particles)
    (physicalPositiveTransferGraph_preconnected lam h0 hpi n particles)
    (fun _ _ h => h.2.1) v hdata.positive tau hrealV w (by simpa [hrho] using hwe)
  exact ⟨mu,tau,v,hdata,hsimple⟩

end
end SixVertex
