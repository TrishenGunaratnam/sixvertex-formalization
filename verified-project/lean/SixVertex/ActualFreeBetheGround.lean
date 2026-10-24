import SixVertex.ActualFreeBetheEnergy
import SixVertex.PhysicalBetheColumn

namespace SixVertex
noncomputable section

/-- A01 and the proved positive Gaudin determinant supply the nonzero
physical Bethe vector at the free point. -/
theorem actual_free_bethe_ne_zero {particles : ℕ} (n : ℕ) (hEven : Even (n+2))
    (Y : Fin particles → ℝ)
    (hY : ConsecutiveRoots (Real.pi/2) (fun _ => 0) (n+2) Y 0)
    (hSlavnov : SlavnovIdentity (Real.pi/2) (fun _ => 0) (n+2) Y 0) :
    physicalBetheVector (Real.pi/2) (fun _ => 0) (n+2) Y≠0 := by
  have h0 : 0<Real.pi/2 := by linarith [Real.pi_pos]
  have hpi : Real.pi/2<Real.pi := by linarith [Real.pi_pos]
  exact physical_bethe_ne_zero (Real.pi/2) h0 hpi (fun _ => 0) (n+2) hEven Y hY.1.injective 0
    (consecutiveRoots_onShell (Real.pi/2) (fun _ => 0) (n+2) hEven Y 0 h0 hpi hY) hSlavnov
    (gaudinMatrix_posDef (Real.pi/2) (fun _ => 0) (n+2) (by omega) Y le_rfl hpi).det_pos.ne'

/-- The actual Hilbert Bethe vector satisfies the actual free Hamiltonian
eigenvalue equation with the Slater energy. -/
theorem actual_free_bethe_vector_energy {particles : ℕ} (n : ℕ) (hEven : Even (n+2))
    (Y : Fin particles → ℝ)
    (hY : ConsecutiveRoots (Real.pi/2) (fun _ => 0) (n+2) Y 0)
    (hSlavnov : SlavnovIdentity (Real.pi/2) (fun _ => 0) (n+2) Y 0) :
    (homogeneousLinkHamiltonian (Real.pi/2) (1/2) (n+1)).mulVec
      (fun q => physicalBetheVector (Real.pi/2) (fun _ => 0) (n+2) Y q)=
      (freeSlaterEnergy Y : ℂ) •
      (fun q => physicalBetheVector (Real.pi/2) (fun _ => 0) (n+2) Y q) := by
  have h0 : 0<Real.pi/2 := by linarith [Real.pi_pos]
  have hpi : Real.pi/2<Real.pi := by linarith [Real.pi_pos]
  have hnon := betheState_ne_zero_of_physicalBetheVector (Real.pi/2) h0 hpi (fun _ => 0) (n+2) Y
    hY.1.injective (actual_free_bethe_ne_zero n hEven Y hY hSlavnov)
  have hm := actual_free_bethe_eigenmatrix_energy n hEven Y hY.1.injective
    (consecutiveRoots_onShell (Real.pi/2) (fun _ => 0) (n+2) hEven Y 0 h0 hpi hY) hnon
  funext q
  simp_rw [physicalBetheVector_eq_betheState_column (Real.pi/2) h0 hpi (fun _ => 0) (n+2) Y hY.1.injective]
  exact congrArg (fun A : Matrix (RowSpins (n+2)) (RowSpins (n+2)) ℂ => A q (plusSpins (n+2))) hm

theorem actual_free_bethe_sector_energy {particles : ℕ} (n : ℕ) (hEven : Even (n+2))
    (Y : Fin particles → ℝ)
    (hY : ConsecutiveRoots (Real.pi/2) (fun _ => 0) (n+2) Y 0)
    (hSlavnov : SlavnovIdentity (Real.pi/2) (fun _ => 0) (n+2) Y 0) :
    (complexSectorHamiltonian (Real.pi/2) (1/2) n particles).mulVec
      (fun q : ParticleConfigurations (n+2) particles =>
        physicalBetheVector (Real.pi/2) (fun _ => 0) (n+2) Y q.val)=
      (freeSlaterEnergy Y : ℂ) •
      (fun q : ParticleConfigurations (n+2) particles =>
        physicalBetheVector (Real.pi/2) (fun _ => 0) (n+2) Y q.val) := by
  funext q
  rw [complexSectorHamiltonian_mulVec_eq_full,
    physicalSectorExtension_restriction_eq _ (physicalBetheVector_sector (Real.pi/2) (fun _ => 0) (n+2) Y)]
  exact congrFun (actual_free_bethe_vector_energy n hEven Y hY hSlavnov) q.val

/-- The manuscript's ACTUAL Bethe vector at the free point spans the
constructed simple ground-state line. The only external mathematical input
is the explicitly authorized A01 Slavnov identity, used for nonvanishing. -/
theorem actual_free_bethe_ground_line {particles : ℕ} (n : ℕ) (hEven : Even (n+2))
    (hp : particles≤n+2) (Y : Fin particles → ℝ)
    (hY : ConsecutiveRoots (Real.pi/2) (fun _ => 0) (n+2) Y 0)
    (hSlavnov : SlavnovIdentity (Real.pi/2) (fun _ => 0) (n+2) Y 0) :
    ∃ c : ℂ,c≠0 ∧
      (fun q : ParticleConfigurations (n+2) particles =>
        physicalBetheVector (Real.pi/2) (fun _ => 0) (n+2) Y q.val)=
      c • spinFreeSlaterVector (n+2) Y := by
  obtain ⟨c,hc⟩ := (actual_free_slater_ground_state n hp Y hY).2.2 _
    (actual_free_bethe_sector_energy n hEven Y hY hSlavnov)
  refine ⟨c,?_,hc⟩
  intro hz
  have hne := physical_sector_restriction_ne_zero
    (fun q => physicalBetheVector (Real.pi/2) (fun _ => 0) (n+2) Y q)
    (physicalBetheVector_sector (Real.pi/2) (fun _ => 0) (n+2) Y)
    (by
      intro hz
      apply actual_free_bethe_ne_zero n hEven Y hY hSlavnov
      exact (WithLp.ofLp_eq_zero 2).mp hz)
  rw [hc,hz,zero_smul] at hne
  exact hne rfl

end
end SixVertex
