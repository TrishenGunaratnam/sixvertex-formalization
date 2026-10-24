import SixVertex.ExplicitDensityIdentification
import SixVertex.RadialConvolution

namespace SixVertex
noncomputable section

/-- Positivity of the actual inverse-defined density for every physical
parameter, including the positive-kernel range. -/
theorem fullLineDensityFunction_pos_all (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (u : ℝ) : 0 < fullLineDensityFunction lam h0 hpi u := by
  rw [fullLineDensityFunction_eq_explicitDensityProfile]
  unfold explicitDensityProfile
  positivity

/-- The identified actual density decreases with distance from zero
throughout the physical parameter range. -/
theorem fullLineDensityFunction_radiallyAntitone_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) : RadiallyAntitone (fun u => fullLineDensityFunction lam h0 hpi u) := by
  intro u v huv
  change fullLineDensityFunction lam h0 hpi v ≤ fullLineDensityFunction lam h0 hpi u
  rw [fullLineDensityFunction_eq_explicitDensityProfile,fullLineDensityFunction_eq_explicitDensityProfile]
  unfold explicitDensityProfile
  have he : 0 < lam/Real.pi := div_pos h0 Real.pi_pos
  apply one_div_le_one_div_of_le (mul_pos (mul_pos (by norm_num) h0) (Real.cosh_pos _))
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2*lam)
  apply Real.cosh_le_cosh.mpr
  simpa only [abs_div,abs_of_pos he] using div_le_div_of_nonneg_right huv he.le

end
end SixVertex
