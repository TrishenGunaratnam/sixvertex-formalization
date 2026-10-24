import SixVertex.PhysicalRowDerivative

namespace SixVertex
noncomputable section

/-- Differentiate an exact matrix eigenline entry by entry. -/
theorem matrix_eigenline_derivative {V : Type*} [Fintype V] [DecidableEq V]
    (T : ℂ → Matrix V V ℂ) (Tprime M : Matrix V V ℂ) (rho : ℂ → ℂ) (rhoprime : ℂ)
    (hT : ∀ q r,HasDerivAt (fun z => T z q r) (Tprime q r) 0)
    (hrho : HasDerivAt rho rhoprime 0) (he : ∀ z,T z*M=rho z • M) :
    Tprime*M=rhoprime • M := by
  ext q r
  have hd : HasDerivAt (fun z => (T z*M) q r) ((Tprime*M) q r) 0 := by
    change HasDerivAt (fun z => ∑ k,T z q k*M k r) (∑ k,Tprime q k*M k r) 0
    apply HasDerivAt.fun_sum
    intro k _
    exact (hT q k).mul_const (M k r)
  have hf : (fun z => (T z*M) q r)=(fun z => rho z*M q r) := by
    funext z
    exact congrArg (fun A : Matrix V V ℂ => A q r) (he z)
  rw [hf] at hd
  exact hd.unique (hrho.mul_const (M q r))

/-- The right logarithmic matrix derivative acts on a nonzero eigenline
by the exact scalar logarithmic derivative. -/
theorem matrix_logarithmic_eigenline {V : Type*} [Fintype V] [DecidableEq V]
    (Tzero Tprime Inv M : Matrix V V ℂ) (alpha beta eta : ℂ)
    (hinv : Inv*Tzero=1) (hM : M≠0) (hzero : Tzero*M=alpha • M) (hprime : Tprime*M=beta • M) :
    alpha≠0 ∧ (((-eta) • (Tprime*Inv))*M)=(-eta*beta/alpha) • M := by
  have hi := congrArg (fun A : Matrix V V ℂ => Inv*A) hzero
  rw [← mul_assoc,hinv,one_mul,mul_smul_comm] at hi
  have ha : alpha≠0 := by
    intro hz
    rw [hz,zero_smul] at hi
    exact hM hi
  have hInv : Inv*M=alpha⁻¹ • M := by
    have h := congrArg (fun A : Matrix V V ℂ => alpha⁻¹ • A) hi
    rw [smul_smul,inv_mul_cancel₀ ha,one_smul] at h
    exact h.symm
  refine ⟨ha,?_⟩
  calc
    _ = (-eta) • (Tprime*(Inv*M)) := by simp only [smul_mul_assoc,mul_assoc]
    _ = (-eta) • (alpha⁻¹ • (beta • M)) := by rw [hInv,mul_smul_comm,hprime]
    _ = _ := by rw [smul_smul,smul_smul];congr 1;ring

/-- An actual homogeneous physical transfer eigenline gives an actual
Hamiltonian eigenline,with no assumed logarithmic-derivative identity. -/
theorem homogeneous_physical_eigenline_logarithmic (lam eta : ℝ) (h0 : 0<lam)
    (hpi : lam<Real.pi) (n : ℕ) (M : Matrix (RowSpins (n+1)) (RowSpins (n+1)) ℂ)
    (rho : ℂ → ℂ) (rhoprime : ℂ) (hrho : HasDerivAt rho rhoprime 0)
    (he : ∀ z,homogeneousPhysicalRow lam (n+1) z*M=rho z • M) (hM : M≠0) :
    rho 0≠0 ∧ homogeneousLinkHamiltonian lam eta n*M=
      (-(eta : ℂ)*rhoprime/rho 0) • M := by
  have hd := matrix_eigenline_derivative (homogeneousPhysicalRow lam (n+1))
    (homogeneousPhysicalRowPrimeZero lam (n+1)) M rho rhoprime
    (fun q r => hasDerivAt_pi.mp (hasDerivAt_pi.mp
      (homogeneousPhysicalRow_hasDerivAt_zero lam h0 hpi (n+1)) q) r) hrho he
  have hinv : spinPermutation (cyclicSpinTranslation n).symm*homogeneousPhysicalRow lam (n+1) 0=1 := by
    rw [homogeneousPhysicalRow_at_zero lam h0 hpi n]
    simpa only [Equiv.symm_symm] using spinPermutation_mul_inverse (cyclicSpinTranslation n).symm
  exact matrix_logarithmic_eigenline _ _ _ M (rho 0) rhoprime (eta : ℂ) hinv hM (he 0) hd

end
end SixVertex
