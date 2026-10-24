import SixVertex.MellinTwoPoles

namespace SixVertex
noncomputable section
open Set MeasureTheory Filter

/-- The actual unit-circle factors of the physical quadratic lie in
the slit plane and are distinct away from the free zero-kernel point. -/
theorem mellin_unit_poles_data (alpha : ℝ) (hlo : -Real.pi < alpha) (hhi : alpha < Real.pi)
    (hne : alpha ≠ 0) :
    let a := Complex.exp ((alpha : ℂ)*Complex.I)
    let b := Complex.exp (-(alpha : ℂ)*Complex.I)
    a ∈ Complex.slitPlane ∧ b ∈ Complex.slitPlane ∧ a ≠ b ∧
      a+b=2*(Real.cos alpha : ℂ) ∧ a*b=1 := by
  dsimp only
  have ha : Complex.exp ((alpha : ℂ)*Complex.I) ∈ Complex.slitPlane := by
    apply Complex.expOpenPartialHomeomorph.map_source
    change ((alpha : ℂ)*Complex.I).im ∈ Ioo (-Real.pi) Real.pi
    simpa using And.intro hlo hhi
  have hb : Complex.exp (-(alpha : ℂ)*Complex.I) ∈ Complex.slitPlane := by
    apply Complex.expOpenPartialHomeomorph.map_source
    change (-(alpha : ℂ)*Complex.I).im ∈ Ioo (-Real.pi) Real.pi
    simpa using And.intro (show -Real.pi < -alpha by linarith) (show -alpha < Real.pi by linarith)
  have hs : Real.sin alpha ≠ 0 := fun h => hne ((Real.sin_eq_zero_iff_of_lt_of_lt hlo hhi).mp h)
  refine ⟨ha,hb,?_,?_,?_⟩
  · intro he
    have hh := congrArg Complex.im he
    rw [show -(alpha : ℂ)=((-alpha : ℝ) : ℂ) by simp,Complex.exp_ofReal_mul_I,Complex.exp_ofReal_mul_I] at hh
    simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_im,Complex.I_re,
      Complex.ofReal_re,mul_one,mul_zero,add_zero,zero_add,Real.sin_neg] at hh
    apply hs
    linarith
  · rw [show -(alpha : ℂ)=((-alpha : ℝ) : ℂ) by simp,Complex.exp_ofReal_mul_I,Complex.exp_ofReal_mul_I]
    simp only [Real.cos_neg,Real.sin_neg,Complex.ofReal_neg]
    ring
  · rw [← Complex.exp_add]
    have he : (alpha : ℂ)*Complex.I+(-(alpha : ℂ))*Complex.I=0 := by ring
    rw [he,Complex.exp_zero]

/-- Principal logarithms at the actual unit factors give the sine
numerator in the quadratic Mellin formula. -/
theorem mellin_unit_power_difference (alpha : ℝ) (hlo : -Real.pi < alpha) (hhi : alpha < Real.pi)
    (z : ℂ) :
    (Complex.exp ((alpha : ℂ)*Complex.I))^(z-1)-
      (Complex.exp (-(alpha : ℂ)*Complex.I))^(z-1)=
      2*Complex.I*Complex.sin ((alpha : ℂ)*(z-1)) := by
  have hla : Complex.log (Complex.exp ((alpha : ℂ)*Complex.I))=(alpha : ℂ)*Complex.I :=
    Complex.log_exp (by simpa using hlo) (by simpa using hhi.le)
  have hlb : Complex.log (Complex.exp (-(alpha : ℂ)*Complex.I))=-(alpha : ℂ)*Complex.I :=
    Complex.log_exp (by simpa using (show -Real.pi < -alpha by linarith))
      (by simpa using (show -alpha ≤ Real.pi by linarith))
  rw [Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),hla,
    Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),hlb,Complex.sin]
  have he1 : ((alpha : ℂ)*Complex.I)*(z-1)=((alpha : ℂ)*(z-1))*Complex.I := by ring
  have he2 : (-(alpha : ℂ)*Complex.I)*(z-1)=-((alpha : ℂ)*(z-1))*Complex.I := by ring
  rw [he1,he2]
  have hI : Complex.I^2=-1 := Complex.I_sq
  ring_nf
  simp only [hI]
  ring

/-- The genuine normalized physical quadratic Mellin integral,with its
principal unit-circle factors and no unproved transform premise. -/
theorem unit_quadratic_mellin_integral (alpha : ℝ) (hlo : -Real.pi < alpha) (hhi : alpha < Real.pi)
    (z : ℂ) (h0 : 0 < z.re) (h1 : z.re < 1) :
    (∫ t in Ioi (0 : ℝ), (-(Real.sin alpha : ℂ)/(Real.pi : ℂ))*
      ((t : ℂ)^(z-1)/((t : ℂ)^2+2*(Real.cos alpha : ℂ)*(t : ℂ)+1)))=
      Complex.sin ((alpha : ℂ)*(z-1))/Complex.sin ((Real.pi : ℂ)*z) := by
  by_cases hzero : alpha=0
  · subst alpha
    simp
  · have hne : alpha ≠ 0 := hzero
    let a := Complex.exp ((alpha : ℂ)*Complex.I)
    let b := Complex.exp (-(alpha : ℂ)*Complex.I)
    obtain ⟨ha,hb,hab,hsum,hprod⟩ := mellin_unit_poles_data alpha hlo hhi hne
    have hden (t : ℝ) : ((t : ℂ)+a)*((t : ℂ)+b)=(t : ℂ)^2+2*(Real.cos alpha : ℂ)*(t : ℂ)+1 := by
      calc
        _ = (t : ℂ)^2+(a+b)*(t : ℂ)+a*b := by ring
        _ = _ := by rw [hsum,hprod]
    have hdiff : a^(z-1)-b^(z-1)=2*Complex.I*Complex.sin ((alpha : ℂ)*(z-1)) :=
      mellin_unit_power_difference alpha hlo hhi z
    have hba : b-a=-2*Complex.I*(Real.sin alpha : ℂ) := by
      dsimp [a,b]
      rw [show -(alpha : ℂ)=((-alpha : ℝ) : ℂ) by simp,Complex.exp_ofReal_mul_I,Complex.exp_ofReal_mul_I]
      simp only [Real.cos_neg,Real.sin_neg,Complex.ofReal_neg]
      ring
    have hs : (Real.sin alpha : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
      (fun h => hne ((Real.sin_eq_zero_iff_of_lt_of_lt hlo hhi).mp h))
    calc
      _ = (-(Real.sin alpha : ℂ)/(Real.pi : ℂ))*
          (∫ t in Ioi (0 : ℝ), (t : ℂ)^(z-1)/(((t : ℂ)+a)*((t : ℂ)+b))) := by
        rw [← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        change (-(Real.sin alpha : ℂ)/(Real.pi : ℂ))*((t : ℂ)^(z-1)/((t : ℂ)^2+2*(Real.cos alpha : ℂ)*(t : ℂ)+1))=
          (-(Real.sin alpha : ℂ)/(Real.pi : ℂ))*((t : ℂ)^(z-1)/(((t : ℂ)+a)*((t : ℂ)+b)))
        rw [hden]
      _ = _ := by
        rw [integral_mellin_two_poles z a b h0 h1 ha hb hab,hdiff,hba]
        field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero,hs,Complex.I_ne_zero]

end
end SixVertex
