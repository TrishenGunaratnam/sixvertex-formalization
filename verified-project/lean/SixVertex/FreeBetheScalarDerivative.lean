import SixVertex.FreeFermionMomentum
import SixVertex.BetheAnalyticEigenvalue

namespace SixVertex
noncomputable section

/-- The physical spectral coordinate at which the row is a translation. -/
def betheSwapCoordinate (lam : ℝ) (z : ℂ) : ℂ :=
  Complex.I*(lam : ℂ)/2-Complex.I*z

theorem free_deformation_sinh_cosh :
    Complex.sinh (Complex.I*((Real.pi/2 : ℝ) : ℂ))=Complex.I ∧
    Complex.cosh (Complex.I*((Real.pi/2 : ℝ) : ℂ))=0 := by
  rw [mul_comm Complex.I,Complex.sinh_mul_I,Complex.cosh_mul_I]
  simp only [← Complex.ofReal_sin,← Complex.ofReal_cos,Real.sin_pi_div_two,
    Real.cos_pi_div_two,Complex.ofReal_one,Complex.ofReal_zero,one_mul,and_self]

/-- Exact vacuum factors in the physical spectral coordinate at the free point. -/
theorem free_vacuum_swap_factors (L : ℕ) (z : ℂ) :
    vacuumA (Complex.I*((Real.pi/2 : ℝ) : ℂ)) (fun _ => 0)
      (betheSwapCoordinate (Real.pi/2) z) L=Complex.cos z^L ∧
    vacuumL (Complex.I*((Real.pi/2 : ℝ) : ℂ)) (fun _ => 0)
      (betheSwapCoordinate (Real.pi/2) z) L=(-Complex.sin z)^L := by
  have hs := free_deformation_sinh_cosh
  have h1 : betheSwapCoordinate (Real.pi/2) z+Complex.I*((Real.pi/2 : ℝ) : ℂ)/2=
      Complex.I*((Real.pi/2 : ℝ) : ℂ)-z*Complex.I := by
    unfold betheSwapCoordinate;ring
  have h2 : betheSwapCoordinate (Real.pi/2) z-Complex.I*((Real.pi/2 : ℝ) : ℂ)/2=
      -(z*Complex.I) := by unfold betheSwapCoordinate;ring
  rw [vacuumA_product,vacuumL_product]
  simp only [sub_zero,h1,h2,Complex.sinh_sub,hs.1,hs.2,
    Complex.sinh_neg,Complex.sinh_mul_I,Complex.cosh_mul_I,zero_mul,sub_zero]
  simp [mul_div_cancel_left₀,Complex.I_ne_zero,mul_comm,neg_div]

/-- A useful product identity avoiding branch choices for complex square roots. -/
theorem sinh_shift_product (a b : ℂ) :
    2*Complex.sinh (a-b)*Complex.sinh (a+b)=Complex.cosh (2*a)-Complex.cosh (2*b) := by
  rw [Complex.sinh_sub,Complex.sinh_add,Complex.cosh_two_mul,Complex.cosh_two_mul]
  linear_combination
    (Complex.sinh a^2+Complex.cosh a^2)*(Complex.cosh_sq_sub_sinh_sq b)-
    (Complex.sinh b^2+Complex.cosh b^2)*(Complex.cosh_sq_sub_sinh_sq a)

/-- Differentiating one Bethe factor in the physical coordinate gives its
logarithmic derivative times the factor, with the physical sign fixed. -/
theorem bethe_factor_swap_hasDerivAt (t y : ℂ)
    (hd : Complex.sinh (y-t/2)≠0) :
    HasDerivAt (fun z : ℂ => betheF t (y-(t/2-Complex.I*z)))
      ((-Complex.I*Complex.sinh t)/Complex.sinh (y-t/2)^2) 0 := by
  have ha : HasDerivAt (fun z : ℂ => y+t/2+Complex.I*z) Complex.I 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_mul Complex.I |>.const_add (y+t/2)
  have hb : HasDerivAt (fun z : ℂ => y-t/2+Complex.I*z) Complex.I 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_mul Complex.I |>.const_add (y-t/2)
  have hh := ha.csinh.div hb.csinh (by simpa using hd)
  have hf : (fun z : ℂ => betheF t (y-(t/2-Complex.I*z)))=
      (fun z => Complex.sinh (y+t/2+Complex.I*z)/Complex.sinh (y-t/2+Complex.I*z)) := by
    funext z
    unfold betheF
    congr 2 <;> ring
  rw [hf]
  convert hh using 1
  simp only [mul_zero,add_zero]
  have he : (y-t/2)-(y+t/2)=-t := by ring
  have heq := Complex.sinh_sub (y-t/2) (y+t/2)
  rw [he,Complex.sinh_neg] at heq
  congr 1
  linear_combination Complex.I*heq

/-- At the free point the logarithmic derivative is twice the positive
one-particle cosine dispersion. -/
theorem free_bethe_factor_swap_hasDerivAt (y : ℝ) :
    HasDerivAt (fun z : ℂ => betheF (Complex.I*((Real.pi/2 : ℝ) : ℂ))
      ((y : ℂ)-betheSwapCoordinate (Real.pi/2) z))
      (2*(Real.cos (physicalRootMomentum (Real.pi/2) y) : ℂ)*
        betheF (Complex.I*((Real.pi/2 : ℝ) : ℂ))
          ((y : ℂ)-betheSwapCoordinate (Real.pi/2) 0)) 0 := by
  let t : ℂ := Complex.I*((Real.pi/2 : ℝ) : ℂ)
  have hd : Complex.sinh ((y : ℂ)-t/2)≠0 := by
    have hs : Real.sin (-Real.pi/4)≠0 := by
      have hh := Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos] : 0<Real.pi/4)
        (by linarith [Real.pi_pos] : Real.pi/4<Real.pi)
      simpa only [neg_div,Real.sin_neg,neg_ne_zero] using hh.ne'
    convert sinh_real_shift_ne_zero y (-Real.pi/4) hs using 1
    congr 1
    dsimp [t];push_cast;ring
  have hp : 2*Complex.sinh ((y : ℂ)-t/2)*Complex.sinh ((y : ℂ)+t/2)=
      (Real.cosh (2*y) : ℂ) := by
    have h := sinh_shift_product (y : ℂ) (t/2)
    rw [show 2*(t/2)=t by ring,show Complex.cosh t=0 from free_deformation_sinh_cosh.2] at h
    simpa only [sub_zero,Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_cosh] using h
  have hc : (Real.cosh (2*y) : ℂ)≠0 := by
    exact_mod_cast (Real.cosh_pos (2*y)).ne'
  have h := bethe_factor_swap_hasDerivAt t (y : ℂ) hd
  change HasDerivAt (fun z : ℂ => betheF t ((y : ℂ)-(t/2-Complex.I*z))) _ 0
  convert h using 1
  have hcos : (Real.cos (physicalRootMomentum (Real.pi/2) y) : ℂ)=
      1/(Real.cosh (2*y) : ℂ) := by
    rw [freeFermion_momentum_cos,Complex.ofReal_div,Complex.ofReal_one]
  rw [hcos]
  simp only [betheF,betheSwapCoordinate,mul_zero,sub_zero]
  change 2*(1/(Real.cosh (2*y) : ℂ))*
    (Complex.sinh ((y : ℂ)-t/2+t)/Complex.sinh ((y : ℂ)-t/2))=
      (-Complex.I*Complex.sinh t)/Complex.sinh ((y : ℂ)-t/2)^2
  rw [show (y : ℂ)-t/2+t=(y : ℂ)+t/2 by ring,
    show Complex.sinh t=Complex.I from free_deformation_sinh_cosh.1]
  rw [neg_mul,Complex.I_mul_I,neg_neg]
  generalize Complex.sinh ((y : ℂ)-t/2)=a at hd hp ⊢
  generalize Complex.sinh ((y : ℂ)+t/2)=b at hp ⊢
  generalize (Real.cosh (2*y) : ℂ)=c at hc hp ⊢
  field_simp [hd,hc]
  linear_combination hp

end
end SixVertex
