import SixVertex.ShiftedMellinEvaluation

namespace SixVertex
noncomputable section
open Set MeasureTheory Filter

private lemma slit_add_nonnegative_ne_zero (a : ℂ) (ha : a ∈ Complex.slitPlane)
    (t : ℝ) (ht : 0 ≤ t) : (t : ℂ)+a ≠ 0 := by
  obtain ⟨c,hc,hbound⟩ := exists_slit_mellin_denominator_bound a ha
  apply norm_pos_iff.mp
  exact (mul_pos hc (by linarith : 0 < 1+t)).trans_le (hbound t ht)

/-- Partial fractions for the genuine two-pole Mellin kernel on the
integration half-line,with every denominator proved nonzero. -/
theorem mellin_two_pole_partial_fractions (z a b : ℂ) (ha : a ∈ Complex.slitPlane)
    (hb : b ∈ Complex.slitPlane) (hne : a ≠ b) (t : ℝ) (ht : 0 ≤ t) :
    (t : ℂ)^(z-1)/(((t : ℂ)+a)*((t : ℂ)+b))=
      ((t : ℂ)^(z-1)/((t : ℂ)+a)-(t : ℂ)^(z-1)/((t : ℂ)+b))/(b-a) := by
  have hA := slit_add_nonnegative_ne_zero a ha t ht
  have hB := slit_add_nonnegative_ne_zero b hb t ht
  have hD : b-a ≠ 0 := sub_ne_zero.mpr hne.symm
  field_simp [hA,hB,hD]
  ring

/-- Absolute convergence of the actual two-pole Mellin integral
follows from the two proved shifted integrals. -/
theorem integrableOn_mellin_two_poles (z a b : ℂ) (h0 : 0 < z.re) (h1 : z.re < 1)
    (ha : a ∈ Complex.slitPlane) (hb : b ∈ Complex.slitPlane) (hne : a ≠ b) :
    IntegrableOn (fun t : ℝ => (t : ℂ)^(z-1)/(((t : ℂ)+a)*((t : ℂ)+b))) (Ioi (0 : ℝ)) := by
  have hh := ((integrableOn_shifted_mellin_kernel z a h0 h1 ha).sub
    (integrableOn_shifted_mellin_kernel z b h0 h1 hb)).div_const (b-a)
  apply hh.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (mellin_two_pole_partial_fractions z a b ha hb hne t ht.le).symm

/-- The actual quadratic-denominator Mellin integral,at arbitrary two
slit-plane poles,is evaluated from the proved shifted formula. -/
theorem integral_mellin_two_poles (z a b : ℂ) (h0 : 0 < z.re) (h1 : z.re < 1)
    (ha : a ∈ Complex.slitPlane) (hb : b ∈ Complex.slitPlane) (hne : a ≠ b) :
    (∫ t in Ioi (0 : ℝ), (t : ℂ)^(z-1)/(((t : ℂ)+a)*((t : ℂ)+b)))=
      ((a^(z-1)-b^(z-1))*((Real.pi : ℂ)/Complex.sin ((Real.pi : ℂ)*z)))/(b-a) := by
  calc
    _ = ∫ t in Ioi (0 : ℝ), ((t : ℂ)^(z-1)/((t : ℂ)+a)-(t : ℂ)^(z-1)/((t : ℂ)+b))/(b-a) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact mellin_two_pole_partial_fractions z a b ha hb hne t ht.le
    _ = _ := by
      rw [integral_div,integral_sub (integrableOn_shifted_mellin_kernel z a h0 h1 ha)
        (integrableOn_shifted_mellin_kernel z b h0 h1 hb),
        integral_shifted_mellin_slit z a h0 h1 ha,integral_shifted_mellin_slit z b h0 h1 hb]
      ring

end
end SixVertex
