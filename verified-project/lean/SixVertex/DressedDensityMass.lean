import SixVertex.CountingPrimitive

namespace SixVertex
noncomputable section
open MeasureTheory

theorem integral_bareDensityFunction (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) :
    (∫ u : ℝ, bareDensityFunction lam h0 hpi b L u)=(L : ℝ)*(1-lam/Real.pi) := by
  simp_rw [bareDensityFunction_apply]
  rw [integral_finsetSum]
  · simp only [integral_sub_right_eq_self,integral_kernelS lam h0 hpi,
      Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  · intro a _
    exact (kernelS_integrable lam h0 hpi).comp_sub_right (b a)

theorem dressedBareDensityFunction_equation (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) :
    dressedBareDensityFunction lam h0 hpi b L+
      boundedConvolutionOperator (kernelK lam) (kernelK_integrable lam h0 hpi)
        (dressedBareDensityFunction lam h0 hpi b L)=bareDensityFunction lam h0 hpi b L :=
  boundedConvolutionInverse_solves (kernelK lam) (kernelK_integrable lam h0 hpi)
    (kernelK_L1_mass_lt_one lam h0 hpi) _

/-- The dressed source has mass exactly L/2 for every real array.
This follows by integrating the actual inverse equation. -/
theorem integral_dressedBareDensityFunction (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) :
    (∫ u : ℝ, dressedBareDensityFunction lam h0 hpi b L u)=(L : ℝ)/2 := by
  have hp := dressedBareDensityFunction_integrable lam h0 hpi b L
  have hK := kernelK_integrable lam h0 hpi
  have hconv : Integrable (boundedConvolutionValue (kernelK lam) (dressedBareDensityFunction lam h0 hpi b L)) :=
    hK.integrable_convolution (L := ContinuousLinearMap.mul ℝ ℝ) hp
  have hh := congrArg (fun f : BoundedRealFunction => ∫ u : ℝ, f u)
    (dressedBareDensityFunction_equation lam h0 hpi b L)
  change (∫ u : ℝ, dressedBareDensityFunction lam h0 hpi b L u+
    boundedConvolutionValue (kernelK lam) (dressedBareDensityFunction lam h0 hpi b L) u)=_ at hh
  rw [integral_add hp hconv,integral_bareDensityFunction lam h0 hpi b L] at hh
  have hc : (∫ u : ℝ, boundedConvolutionValue (kernelK lam) (dressedBareDensityFunction lam h0 hpi b L) u)=
      (∫ u : ℝ, kernelK lam u)*(∫ u : ℝ, dressedBareDensityFunction lam h0 hpi b L u) :=
    integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hK hp
  rw [hc,integral_kernelK lam h0 hpi] at hh
  have hpos : 0 < 1-lam/Real.pi := by
    have hlt := (div_lt_one Real.pi_pos).mpr hpi
    linarith
  rw [show 2*lam/Real.pi=2*(lam/Real.pi) by ring] at hh
  have he : (1-lam/Real.pi)*(2*(∫ u : ℝ, dressedBareDensityFunction lam h0 hpi b L u)-(L : ℝ))=0 := by nlinarith only [hh]
  have hz := (mul_eq_zero.mp he).resolve_left hpos.ne'
  linarith

end
end SixVertex
