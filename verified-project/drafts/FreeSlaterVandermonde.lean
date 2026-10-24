import SixVertex.FreeSlaterHamiltonian
import Mathlib.LinearAlgebra.Vandermonde

namespace SixVertex
noncomputable section

/-- The site phase appearing in the actual consecutive-momentum determinant. -/
def freeSitePhase (L : ℕ) (x : ℤ) : ℂ :=
  Complex.exp (Complex.I*((-2*Real.pi*(x : ℝ)/(L : ℝ) : ℝ) : ℂ))

/-- A single period contains no repeated site phases. -/
theorem freeSitePhase_injective_period (L : ℕ) (hL : 0<L) (x y : ℤ)
    (hx0 : 0≤x) (hxL : x<(L : ℤ)) (hy0 : 0≤y) (hyL : y<(L : ℤ))
    (h : freeSitePhase L x=freeSitePhase L y) : x=y := by
  obtain ⟨k,hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  have hi := congrArg Complex.im hk
  norm_num [Complex.mul_re,Complex.mul_im] at hi
  have hL' : (L : ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hL)
  have hz : (x : ℝ)-(y : ℝ)+(k : ℝ)*(L : ℝ)=0 := by
    field_simp [hL'] at hi
    linear_combination -hi
  have hint : x-y+k*(L : ℤ)=0 := by exact_mod_cast hz
  have hk0 : k=0 := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hneg|hpos
    · have hneg' : k≤-1 := by omega
      have hm := mul_le_mul_of_nonneg_right hneg' (show (0 : ℤ)≤L by omega)
      nlinarith
    · have hpos' : 1≤k := by omega
      have hm := mul_le_mul_of_nonneg_right hpos' (show (0 : ℤ)≤L by omega)
      nlinarith
  subst k
  omega

/-- The actual consecutive-root Slater wave is a row-scaled Vandermonde
matrix,with all complex phases and their signs retained. -/
theorem freeSlaterWave_vandermonde {n : ℕ} (L : ℕ) (hL : 0<L)
    (Y : Fin n → ℝ) (hY : ConsecutiveRoots (Real.pi/2) (fun _ => 0) L Y 0) (x : Fin n → ℤ) :
    freeSlaterWave (fun j => physicalRootMomentum (Real.pi/2) (Y j)) x=
      (∏ i,Complex.exp (Complex.I*((Real.pi*((n : ℝ)-1)*(x i : ℝ)/(L : ℝ) : ℝ) : ℂ)))*
        (Matrix.vandermonde (fun i => freeSitePhase L (x i))).det := by
  have he (i j : Fin n) : freePlaneWave (physicalRootMomentum (Real.pi/2) (Y j)) (x i)=
      Complex.exp (Complex.I*((Real.pi*((n : ℝ)-1)*(x i : ℝ)/(L : ℝ) : ℝ) : ℂ))*
        freeSitePhase L (x i)^j.val := by
    rw [freePlaneWave,consecutiveRoots_freeFermion_momentum L hL Y hY j]
    unfold freeSitePhase
    rw [← Complex.exp_nat_mul,← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold freeSlaterWave slaterWave
  simp_rw [he]
  exact Matrix.det_mul_column _ (Matrix.vandermonde (fun i => freeSitePhase L (x i)))

/-- Every distinct-site configuration has a nonzero free-point Slater
amplitude. No assertion identifying it with the Bethe state is assumed. -/
theorem freeSlaterWave_consecutive_ne_zero {n : ℕ} (L : ℕ) (hL : 0<L)
    (Y : Fin n → ℝ) (hY : ConsecutiveRoots (Real.pi/2) (fun _ => 0) L Y 0)
    (x : Fin n → ℤ) (hx : Function.Injective x)
    (hx0 : ∀ i,0≤x i) (hxL : ∀ i,x i<(L : ℤ)) :
    freeSlaterWave (fun j => physicalRootMomentum (Real.pi/2) (Y j)) x≠0 := by
  rw [freeSlaterWave_vandermonde L hL Y hY x]
  apply mul_ne_zero
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => Complex.exp_ne_zero _)
  · apply (Matrix.det_vandermonde_ne_zero_iff).mpr
    intro i j hij
    exact hx (freeSitePhase_injective_period L hL (x i) (x j)
      (hx0 i) (hxL i) (hx0 j) (hxL j) hij)

end
end SixVertex
