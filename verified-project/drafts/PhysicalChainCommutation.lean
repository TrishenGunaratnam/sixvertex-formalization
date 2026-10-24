import SixVertex.PhysicalRowDerivative
import SixVertex.RowCommutation

namespace SixVertex
noncomputable section

/-- Actual homogeneous physical rows commute at every complex spectral
coordinate,including the swap endpoint. -/
theorem homogeneousPhysicalRows_commute (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (L : ℕ) (p s : ℂ) :
    homogeneousPhysicalRow lam L p*homogeneousPhysicalRow lam L s=
      homogeneousPhysicalRow lam L s*homogeneousPhysicalRow lam L p := by
  let w : ℂ → ℂ := fun z => -Complex.I*(z-(lam : ℂ)/2)
  have he (z : ℂ) : physicalTile lam 0 (w z)=physicalR lam z := by
    have hz : (lam : ℂ)/2+Complex.I*(w z-(0 : ℝ))=z := by
      dsimp [w]
      ring_nf
      simp only [Complex.I_sq,neg_mul,one_mul]
      ring
    unfold physicalTile
    rw [hz]
  have hs : Complex.sin (lam : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sin]
    exact Complex.ofReal_ne_zero.mpr (Real.sin_pos_of_pos_of_lt_pi h0 hpi).ne'
  have h := physical_diagonal_rows_commute lam hs (fun _ => 0) (w p) (w s) L (fun _ => 1)
  change markedRow (fun _ => physicalR lam p) L 1*markedRow (fun _ => physicalR lam s) L 1=
    markedRow (fun _ => physicalR lam s) L 1*markedRow (fun _ => physicalR lam p) L 1
  simpa only [he,Matrix.diagonal_one] using h

/-- The genuine derivative of the actual row commutes with every row. -/
theorem homogeneousPhysicalRowPrimeZero_commutes (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (L : ℕ) (z : ℂ) :
    homogeneousPhysicalRowPrimeZero lam L*homogeneousPhysicalRow lam L z=
      homogeneousPhysicalRow lam L z*homogeneousPhysicalRowPrimeZero lam L := by
  ext q r
  have hd := homogeneousPhysicalRow_hasDerivAt_zero lam h0 hpi L
  have hfun : (fun w : ℂ => (homogeneousPhysicalRow lam L w*homogeneousPhysicalRow lam L z) q r)=
      (fun w : ℂ => (homogeneousPhysicalRow lam L z*homogeneousPhysicalRow lam L w) q r) := by
    funext w
    exact congrArg (fun A : Matrix (RowSpins L) (RowSpins L) ℂ => A q r)
      (homogeneousPhysicalRows_commute lam h0 hpi L w z)
  have hleft : HasDerivAt (fun w : ℂ => (homogeneousPhysicalRow lam L w*homogeneousPhysicalRow lam L z) q r)
      ((homogeneousPhysicalRowPrimeZero lam L*homogeneousPhysicalRow lam L z) q r) (0 : ℂ) := by
    simp only [Matrix.mul_apply]
    apply HasDerivAt.fun_sum
    intro t _
    exact (hasDerivAt_pi.mp (hasDerivAt_pi.mp hd q) t).mul_const (homogeneousPhysicalRow lam L z t r)
  have hright : HasDerivAt (fun w : ℂ => (homogeneousPhysicalRow lam L z*homogeneousPhysicalRow lam L w) q r)
      ((homogeneousPhysicalRow lam L z*homogeneousPhysicalRowPrimeZero lam L) q r) (0 : ℂ) := by
    simp only [Matrix.mul_apply]
    apply HasDerivAt.fun_sum
    intro t _
    exact (hasDerivAt_pi.mp (hasDerivAt_pi.mp hd t) r).const_mul (homogeneousPhysicalRow lam L z q t)
  rw [hfun] at hleft
  exact hleft.unique hright

/-- The explicit inverse shift at the swap point commutes with the
actual row family. -/
theorem homogeneousShiftInverse_commutes (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (n : ℕ) (z : ℂ) :
    spinPermutation (cyclicSpinTranslation n).symm*homogeneousPhysicalRow lam (n+1) z=
      homogeneousPhysicalRow lam (n+1) z*spinPermutation (cyclicSpinTranslation n).symm := by
  let S := spinPermutation (cyclicSpinTranslation n)
  let I := spinPermutation (cyclicSpinTranslation n).symm
  let T := homogeneousPhysicalRow lam (n+1) z
  have hSI : S*I=1 := spinPermutation_mul_inverse _
  have hIS : I*S=1 := by
    simpa only [Equiv.symm_symm] using spinPermutation_mul_inverse (cyclicSpinTranslation n).symm
  have hc := homogeneousPhysicalRows_commute lam h0 hpi (n+1) 0 z
  rw [homogeneousPhysicalRow_at_zero lam h0 hpi n] at hc
  change S*T=T*S at hc
  change I*T=T*I
  calc
    _ = ((I*T)*S)*I := by rw [mul_assoc,hSI,mul_one]
    _ = (I*(S*T))*I := by rw [mul_assoc I T S,hc.symm]
    _ = _ := by rw [← mul_assoc I S T,hIS,one_mul]

/-- The actual logarithmic row derivative commutes with the actual
homogeneous transfer row. This does not assume a link-Hamiltonian
identity or a Perron eigenvector. -/
theorem homogeneousLinkHamiltonian_commutes (lam eta : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (n : ℕ) (z : ℂ) :
    homogeneousLinkHamiltonian lam eta n*homogeneousPhysicalRow lam (n+1) z=
      homogeneousPhysicalRow lam (n+1) z*homogeneousLinkHamiltonian lam eta n := by
  simp only [homogeneousLinkHamiltonian,smul_mul_assoc,mul_smul_comm]
  apply congrArg (fun A : Matrix (RowSpins (n+1)) (RowSpins (n+1)) ℂ => (-(eta : ℂ)) • A)
  rw [mul_assoc,homogeneousShiftInverse_commutes lam h0 hpi n z,← mul_assoc,
    homogeneousPhysicalRowPrimeZero_commutes lam h0 hpi (n+1) z,mul_assoc]

end
end SixVertex
