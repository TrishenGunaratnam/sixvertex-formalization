import SixVertex.FreeBetheEigenvalueDerivative
import SixVertex.FiniteBetheEigen

namespace SixVertex
noncomputable section
open Filter Topology

theorem free_swap_half_sinh_ne_zero (y : ℝ) :
    Complex.sinh ((y : ℂ)+Complex.I*((Real.pi/2 : ℝ) : ℂ)/2)≠0 := by
  have hs : Real.sin (Real.pi/4)≠0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])).ne'
  convert sinh_real_shift_ne_zero y (Real.pi/4) hs using 1
  congr 1
  push_cast
  ring

theorem free_swap_three_half_sinh_ne_zero (y : ℝ) :
    Complex.sinh ((y : ℂ)+3*(Complex.I*((Real.pi/2 : ℝ) : ℂ))/2)≠0 := by
  have hs : Real.sin (3*Real.pi/4)≠0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])).ne'
  convert sinh_real_shift_ne_zero y (3*Real.pi/4) hs using 1
  congr 1
  push_cast
  ring

/-- The free physical swap is a genuine regular spectral point of the
meromorphic ABA formula, including its shifted numerator factors. -/
theorem free_swap_rootSet_regular {particles : ℕ} (Y : Fin particles → ℝ) :
    betheSwapCoordinate (Real.pi/2) 0 ∉ rootSet Y ∧
    BetheRegular (Complex.I*((Real.pi/2 : ℝ) : ℂ))
      (insert (betheSwapCoordinate (Real.pi/2) 0) (rootSet Y)) := by
  classical
  let t : ℂ := Complex.I*((Real.pi/2 : ℝ) : ℂ)
  let x : ℂ := betheSwapCoordinate (Real.pi/2) 0
  have hx : x=t/2 := by simp [x,t,betheSwapCoordinate]
  have hfresh : x ∉ rootSet Y := by
    intro h
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp h
    have hi := congrArg Complex.im hj
    simp only [hx,t,Complex.div_ofNat_im,Complex.mul_im,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,one_mul,zero_add] at hi
    linarith [Real.pi_pos]
  have hU := real_rootSet_regular (Real.pi/2) (by linarith [Real.pi_pos])
    (by linarith [Real.pi_pos]) Y
  have hxy (y : ℝ) : Complex.sinh (x-(y : ℂ))≠0 := by
    convert free_swap_half_sinh_ne_zero (-y) using 1
    congr 1
    rw [hx];dsimp [t];push_cast;ring
  have hyx (y : ℝ) : Complex.sinh ((y : ℂ)-x)≠0 := by
    have hn := neg_ne_zero.mpr (hxy y)
    simpa only [← Complex.sinh_neg,neg_sub] using hn
  have hxyT (y : ℝ) : Complex.sinh (x-(y : ℂ)+t)≠0 := by
    convert free_swap_three_half_sinh_ne_zero (-y) using 1
    congr 1
    rw [hx];dsimp [t];push_cast;ring
  have hyxT (y : ℝ) : Complex.sinh ((y : ℂ)-x+t)≠0 := by
    convert free_swap_half_sinh_ne_zero y using 1
    congr 1
    rw [hx];dsimp [t];ring
  refine ⟨hfresh,?_,?_⟩
  · intro p hp q hq hn
    rcases Finset.mem_insert.mp hp with rfl | hp
    · rcases Finset.mem_insert.mp hq with rfl | hq
      · exact False.elim (hn rfl)
      · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hq
        exact hxy (Y j)
    · rcases Finset.mem_insert.mp hq with rfl | hq
      · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hp
        exact hyx (Y j)
      · exact hU.1 p hp q hq hn
  · intro p hp q hq
    rcases Finset.mem_insert.mp hp with rfl | hp
    · rcases Finset.mem_insert.mp hq with rfl | hq
      · simpa only [sub_self,zero_add] using free_deformation_sinh_cosh.1.trans_ne Complex.I_ne_zero
      · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hq
        exact hxyT (Y j)
    · rcases Finset.mem_insert.mp hq with rfl | hq
      · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hp
        exact hyxT (Y j)
      · exact hU.2 p hp q hq

/-- The derivative is valid for any entire Bethe eigenvalue extension
agreeing with the actual ABA formula on its regular domain. -/
theorem free_entire_bethe_swap_hasDerivAt {particles : ℕ} (n : ℕ) (Y : Fin particles → ℝ)
    (hY : Function.Injective Y) (rho : ℂ → ℂ)
    (hgen : ∀ x,x ∉ rootSet Y →
      BetheRegular (Complex.I*((Real.pi/2 : ℝ) : ℂ)) (insert x (rootSet Y)) →
      rho x=abaEigenvalue (Complex.I*((Real.pi/2 : ℝ) : ℂ)) (fun _ => 0) (n+2) 0 (rootSet Y) x) :
    HasDerivAt (fun z => rho (betheSwapCoordinate (Real.pi/2) z))
      ((2*(∑ j,(Real.cos (physicalRootMomentum (Real.pi/2) (Y j)) : ℂ)))*
        rho (betheSwapCoordinate (Real.pi/2) 0)) 0 := by
  have hr := free_swap_rootSet_regular Y
  have hnear := regular_spectral_eventually _
    (physical_deformation_ne_zero (Real.pi/2) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]))
    (rootSet Y) (betheSwapCoordinate (Real.pi/2) 0) hr.1 hr.2
  have hcont : ContinuousAt (betheSwapCoordinate (Real.pi/2)) (0 : ℂ) := by
    unfold betheSwapCoordinate
    fun_prop
  have heq : (fun z => rho (betheSwapCoordinate (Real.pi/2) z)) =ᶠ[𝓝 (0 : ℂ)]
      (fun z => abaEigenvalue (Complex.I*((Real.pi/2 : ℝ) : ℂ)) (fun _ => 0)
        (n+2) 0 (rootSet Y) (betheSwapCoordinate (Real.pi/2) z)) := by
    filter_upwards [hcont.eventually hnear] with z hz
    exact hgen _ hz.1 hz.2
  rw [hgen _ hr.1 hr.2]
  exact (free_aba_swap_hasDerivAt n Y hY).congr_of_eventuallyEq heq

end
end SixVertex
