import SixVertex.DensityExponentialRate
import SixVertex.ExplicitDensityRadial

namespace SixVertex
noncomputable section
open MeasureTheory Filter Set

/-- The actual exterior mass of the identified density has explicit
exponential bounds for every physical parameter, not just negative K. -/
theorem fullLineDensityExteriorMass_exponential_bounds (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (Q : ℝ) (hQ : 0 ≤ Q) :
    Real.exp (-Q/(lam/Real.pi))/Real.pi ≤ fullLineDensityExteriorMass lam h0 hpi Q ∧
      fullLineDensityExteriorMass lam h0 hpi Q ≤ 2*Real.exp (-Q/(lam/Real.pi))/Real.pi := by
  let eta : ℝ := lam/Real.pi
  have heta : 0 < eta := div_pos h0 Real.pi_pos
  let a : ℝ := -(1/eta)
  have ha : a < 0 := neg_neg_of_pos (one_div_pos.mpr heta)
  have he (u : ℝ) : -u/eta=a*u := by dsimp [a]; ring
  have hf : (fun u : ℝ => Real.exp (-u/eta))=(fun u => Real.exp (a*u)) := by
    funext u
    rw [he]
  have hi : IntegrableOn (fun u : ℝ => Real.exp (-u/eta)) (Ioi Q) := by
    rw [hf]
    exact integrableOn_exp_mul_Ioi ha Q
  have hv : (∫ u in Ioi Q,Real.exp (-u/eta))=eta*Real.exp (-Q/eta) := by
    rw [hf,integral_exp_mul_Ioi ha Q,← he Q]
    dsimp [a]
    field_simp [heta.ne']
  have hlo : (∫ u in Ioi Q,Real.exp (-u/eta)/(2*lam)) ≤
      kernelTail (fun u => fullLineDensityFunction lam h0 hpi u) Q := by
    apply integral_mono_ae (hi.div_const _) (fullLineDensityFunction_integrable lam h0 hpi).integrableOn
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (fullLineDensityFunction_exponential_bounds lam h0 hpi u (hQ.trans hu.le)).1
  have hhi : kernelTail (fun u => fullLineDensityFunction lam h0 hpi u) Q ≤
      ∫ u in Ioi Q,Real.exp (-u/eta)/lam := by
    apply integral_mono_ae (fullLineDensityFunction_integrable lam h0 hpi).integrableOn (hi.div_const _)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (fullLineDensityFunction_exponential_bounds lam h0 hpi u (hQ.trans hu.le)).2
  rw [integral_div,hv] at hlo hhi
  have hsplit : fullLineDensityExteriorMass lam h0 hpi Q=
      2*kernelTail (fun u => fullLineDensityFunction lam h0 hpi u) Q :=
    even_integral_exterior_eq_two_tail _ (fullLineDensityFunction_integrable lam h0 hpi)
      (fullLineDensityFunction_radiallyAntitone_all lam h0 hpi).even Q hQ
  have hl : (eta*Real.exp (-Q/eta))/(2*lam)=Real.exp (-Q/eta)/(2*Real.pi) := by
    dsimp [eta]
    field_simp [h0.ne',Real.pi_ne_zero]
  have hh : (eta*Real.exp (-Q/eta))/lam=Real.exp (-Q/eta)/Real.pi := by
    dsimp [eta]
    field_simp [h0.ne',Real.pi_ne_zero]
  rw [hl] at hlo
  rw [hh] at hhi
  rw [hsplit]
  change Real.exp (-Q/eta)/Real.pi ≤ _ ∧ _ ≤ 2*Real.exp (-Q/eta)/Real.pi
  constructor
  · have hm := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 2)
    rw [show 2*(Real.exp (-Q/eta)/(2*Real.pi))=Real.exp (-Q/eta)/Real.pi by field_simp [Real.pi_ne_zero]] at hm
    exact hm
  · have hm := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 2)
    exact hm.trans_eq (by ring)

end
end SixVertex
