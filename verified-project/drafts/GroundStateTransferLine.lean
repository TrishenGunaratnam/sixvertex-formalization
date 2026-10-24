import SixVertex.ComplexSectorMinimum

namespace SixVertex
noncomputable section

theorem sum_subtype_eq_full_of_zero_outside {V : Type*} [Fintype V]
    (P : V → Prop) [DecidablePred P] (f : V → ℂ) (hf : ∀ i,¬P i → f i=0) :
    (∑ i : {i // P i},f i.val)=∑ i : V,f i := by
  have h := Fintype.sum_subtype_add_sum_subtype P f
  have hz : (∑ i : {i // ¬P i},f i.val)=0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact hf i.val i.property
  rw [hz,add_zero] at h
  exact h

/-- The actual homogeneous transfer row restricted to a particle sector. -/
def complexSectorTransfer (lam : ℝ) (n particles : ℕ) (z : ℂ) :
    Matrix (ParticleConfigurations (n+2) particles) (ParticleConfigurations (n+2) particles) ℂ :=
  (homogeneousPhysicalRow lam (n+2) z).submatrix Subtype.val Subtype.val

/-- The actual sector restrictions commute,proved from the full row
commutation and the already checked Hamiltonian charge conservation. -/
theorem complexSectorHamiltonian_transfer_commute (lam eta : ℝ) (h0 : 0<lam)
    (hpi : lam<Real.pi) (n particles : ℕ) (z : ℂ) :
    complexSectorHamiltonian lam eta n particles*complexSectorTransfer lam n particles z=
      complexSectorTransfer lam n particles z*complexSectorHamiltonian lam eta n particles := by
  ext q r
  have hleft : (complexSectorHamiltonian lam eta n particles*complexSectorTransfer lam n particles z) q r=
      (homogeneousLinkHamiltonian lam eta (n+1)*homogeneousPhysicalRow lam (n+2) z) q.val r.val := by
    simp only [Matrix.mul_apply,complexSectorHamiltonian,complexSectorTransfer,Matrix.submatrix_apply]
    apply sum_subtype_eq_full_of_zero_outside (fun j : RowSpins (n+2) => minusCount (n+2) j=particles)
      (fun j => homogeneousLinkHamiltonian lam eta (n+1) q.val j*homogeneousPhysicalRow lam (n+2) z j r.val)
    intro j hj
    rw [homogeneousLinkHamiltonian_charge_zero lam eta n q.val j,zero_mul]
    intro h
    exact hj (h.symm.trans q.property)
  have hright : (complexSectorTransfer lam n particles z*complexSectorHamiltonian lam eta n particles) q r=
      (homogeneousPhysicalRow lam (n+2) z*homogeneousLinkHamiltonian lam eta (n+1)) q.val r.val := by
    simp only [Matrix.mul_apply,complexSectorHamiltonian,complexSectorTransfer,Matrix.submatrix_apply]
    apply sum_subtype_eq_full_of_zero_outside (fun j : RowSpins (n+2) => minusCount (n+2) j=particles)
      (fun j => homogeneousPhysicalRow lam (n+2) z q.val j*homogeneousLinkHamiltonian lam eta (n+1) j r.val)
    intro j hj
    rw [homogeneousLinkHamiltonian_charge_zero lam eta n j r.val,mul_zero]
    intro h
    exact hj (h.trans r.property)
  rw [hleft,hright,homogeneousLinkHamiltonian_commutes lam eta h0 hpi (n+1) z]

/-- One actual positive simple ground-state line is an eigenline for
every complex homogeneous transfer row,with the vector chosen before
all spectral coordinates. No Perron property is assumed. -/
theorem physical_positive_ground_state_common_transfer_line (lam eta : ℝ) (h0 : 0<lam)
    (hpi : lam<Real.pi) (heta : 0<eta) (n particles : ℕ) (hp : particles≤n+2) :
    ∃ (mu : ℝ) (v : ParticleConfigurations (n+2) particles → ℝ), (∀ q,0<v q) ∧
      (complexSectorHamiltonian lam eta n particles).mulVec (fun q => (v q : ℂ))=
        (mu : ℂ) • (fun q => (v q : ℂ)) ∧
      (∀ w : ParticleConfigurations (n+2) particles → ℂ,
        mu*(∑ q,‖w q‖^2)≤complexMatrixRealEnergy (complexSectorHamiltonian lam eta n particles) w) ∧
      (∀ z : ℂ,∃ tau : ℂ,(complexSectorTransfer lam n particles z).mulVec
        (fun q => (v q : ℂ))=tau • (fun q => (v q : ℂ))) := by
  obtain ⟨mu,v,hpos,heig,hlower,hsimple⟩ := physical_sector_complex_positive_simple_minimum
    lam eta h0 hpi heta n particles hp
  refine ⟨mu,v,hpos,heig,hlower,?_⟩
  intro z
  apply hsimple
  rw [Matrix.mulVec_mulVec,complexSectorHamiltonian_transfer_commute lam eta h0 hpi n particles z,
    ← Matrix.mulVec_mulVec,heig,Matrix.mulVec_smul]

end
end SixVertex
