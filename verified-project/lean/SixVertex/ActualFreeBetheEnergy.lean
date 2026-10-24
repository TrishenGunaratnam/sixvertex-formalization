import SixVertex.FreeBetheSwapRegular
import SixVertex.TransferEigenlineDerivative
import SixVertex.ActualFreeSlaterGround

namespace SixVertex
noncomputable section

/-- Exact conversion from the ABA spectral variable to the physical row
variable, at zero twist and zero inhomogeneity. -/
theorem physicalTwistedRow_swapCoordinate (lam : ℝ) (L : ℕ) (z : ℂ) :
    physicalTwistedRow lam (fun _ => 0) L 0 (betheSwapCoordinate lam z)=
      homogeneousPhysicalRow lam L z := by
  have htile : (fun j : ℕ => physicalTile lam 0 (betheSwapCoordinate lam z))=
      (fun _ => physicalR lam z) := by
    funext j
    unfold physicalTile betheSwapCoordinate
    congr 1
    ring_nf
    simp [Complex.I_sq]
  unfold physicalTwistedRow homogeneousPhysicalRow
  rw [htile]
  congr 1
  ext a b
  simp [Matrix.diagonal_apply,Matrix.one_apply]

/-- The physical parity conversion for an arbitrary explicitly even chain
length. Eliminating the length before introducing the matrix equation avoids
transporting matrices across dependent `RowSpins` index types. -/
theorem physical_eigenvector_of_standard_even (lam : ℝ)
    (ht : Complex.sinh (Complex.I*lam) ≠ 0) (b : ℕ → ℝ)
    (L : ℕ) (hEven : Even L) (twist : ℝ) (U : Finset ℂ) (x rho : ℂ)
    (hstd : twistedStandardRow (Complex.I*lam) (fun j => (b j : ℂ)) L twist x *
      betheState (Complex.I*lam) ht (fun j => (b j : ℂ)) L U =
      rho • betheState (Complex.I*lam) ht (fun j => (b j : ℂ)) L U) :
    physicalTwistedRow lam b L twist x *
      (quantumGauge L * betheState (Complex.I*lam) ht (fun j => (b j : ℂ)) L U) =
    ((-1 : ℂ)^U.card * rho) •
      (quantumGauge L * betheState (Complex.I*lam) ht (fun j => (b j : ℂ)) L U) := by
  obtain ⟨k,hk⟩ := hEven
  have hL : L = 2*k := by omega
  clear hk
  subst L
  exact physical_eigenvector_of_standard lam ht b k twist U x rho hstd

/-- The actual physical Bethe eigenmatrix at the free point has exactly
the proved Slater ground energy. Nonvanishing is an explicit finite-state
hypothesis here; its derivation from A01 is a separate result. -/
theorem actual_free_bethe_eigenmatrix_energy {particles : ℕ} (n : ℕ) (hEven : Even (n+2))
    (Y : Fin particles → ℝ) (hY : Function.Injective Y)
    (hShell : OnShell (Real.pi/2) (fun _ => 0) (n+2) Y 0)
    (hM : betheState (Complex.I*((Real.pi/2 : ℝ) : ℂ))
      (physical_deformation_ne_zero (Real.pi/2) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]))
      (fun _ => 0) (n+2) (rootSet Y)≠0) :
    homogeneousLinkHamiltonian (Real.pi/2) (1/2) (n+1)*
      (quantumGauge (n+2)*betheState (Complex.I*((Real.pi/2 : ℝ) : ℂ))
        (physical_deformation_ne_zero (Real.pi/2) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]))
        (fun _ => 0) (n+2) (rootSet Y))=
      (freeSlaterEnergy Y : ℂ) •
      (quantumGauge (n+2)*betheState (Complex.I*((Real.pi/2 : ℝ) : ℂ))
        (physical_deformation_ne_zero (Real.pi/2) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]))
        (fun _ => 0) (n+2) (rootSet Y)) := by
  have h0 : 0<Real.pi/2 := by linarith [Real.pi_pos]
  have hpi : Real.pi/2<Real.pi := by linarith [Real.pi_pos]
  let ht := physical_deformation_ne_zero (Real.pi/2) h0 hpi
  let M := betheState (Complex.I*((Real.pi/2 : ℝ) : ℂ)) ht (fun _ => 0) (n+2) (rootSet Y)
  obtain ⟨u,hu⟩ := exists_real_fresh_spectral Y
  obtain ⟨rho,hrho,heigen,hgen⟩ := balancedRoots_entire_eigenvalue _ ht
    (fun _ => 0) (n+2) 0 (rootSet Y)
    (onShell_balancedRoots (Real.pi/2) h0 hpi (fun _ => 0) (n+2) Y hY 0 hShell) hM
    u hu (real_insert_rootSet_regular (Real.pi/2) h0 hpi Y u)
  have hp (x : ℂ) : physicalTwistedRow (Real.pi/2) (fun _ => 0) (n+2) 0 x*
      (quantumGauge (n+2)*M)=((-1 : ℂ)^particles*rho x) • (quantumGauge (n+2)*M) := by
    have hh := physical_eigenvector_of_standard_even (Real.pi/2) ht (fun _ => 0)
      (n+2) hEven 0 (rootSet Y) x (rho x) (heigen x)
    simpa only [rootSet_card Y hY,M,Complex.ofReal_zero] using hh
  have hd := (free_entire_bethe_swap_hasDerivAt n Y hY rho hgen).const_mul ((-1 : ℂ)^particles)
  have he (z : ℂ) : homogeneousPhysicalRow (Real.pi/2) (n+2) z*(quantumGauge (n+2)*M)=
      ((-1 : ℂ)^particles*rho (betheSwapCoordinate (Real.pi/2) z)) • (quantumGauge (n+2)*M) := by
    rw [← physicalTwistedRow_swapCoordinate]
    exact hp _
  obtain ⟨hn,hH⟩ := homogeneous_physical_eigenline_logarithmic (Real.pi/2) (1/2) h0 hpi (n+1)
    (quantumGauge (n+2)*M) _ _ hd he (quantumGauge_mul_ne_zero (n+2) M hM)
  have hscalar : (-((1/2 : ℝ) : ℂ)*
      ((-1 : ℂ)^particles*((2*(∑ j,(Real.cos (physicalRootMomentum (Real.pi/2) (Y j)) : ℂ)))*
        rho (betheSwapCoordinate (Real.pi/2) 0))))/
      ((-1 : ℂ)^particles*rho (betheSwapCoordinate (Real.pi/2) 0))=(freeSlaterEnergy Y : ℂ) := by
    have heE : (freeSlaterEnergy Y : ℂ)=-(∑ j,(Real.cos (physicalRootMomentum (Real.pi/2) (Y j)) : ℂ)) := by
      simp [freeSlaterEnergy]
    rw [heE]
    apply (div_eq_iff hn).mpr
    push_cast
    ring
  simpa only [hscalar] using hH

end
end SixVertex
