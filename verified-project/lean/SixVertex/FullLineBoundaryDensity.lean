import SixVertex.FullLineDensityRadial
import SixVertex.RelativeKernelVariation
import SixVertex.PhysicalKernelTails

namespace SixVertex
noncomputable section
open MeasureTheory Set Filter Topology

/-- The actual inverse-defined density satisfies the positive renewal
equation in the strict and non-strict negative-kernel regimes. -/
theorem fullLineDensityFunction_renewal (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) (u : ℝ) :
    fullLineDensityFunction lam h0 hpi u=kernelS lam u+
      ∫ v : ℝ, fullLineDensityFunction lam h0 hpi v*(-kernelK lam (u-v)) := by
  have he := congrArg (fun f : BoundedRealFunction => f u) (fullLineDensityFunction_equation lam h0 hpi)
  change fullLineDensityFunction lam h0 hpi u+
    (∫ t : ℝ, kernelK lam t*fullLineDensityFunction lam h0 hpi (u-t))=physicalSourceFunction lam h0 hpi u at he
  rw [physicalSourceFunction_apply] at he
  rw [scalar_convolution_comm] at he
  have hi : (∫ v : ℝ, fullLineDensityFunction lam h0 hpi v*(-kernelK lam (u-v)))=
      -(∫ v : ℝ, fullLineDensityFunction lam h0 hpi v*kernelK lam (u-v)) := by
    simp_rw [mul_neg]
    rw [integral_neg]
  rw [hi]
  linarith

/-- Relative spatial comparison for the actual full-line density,
derived directly from the positive renewal equation. -/
theorem fullLineDensityFunction_exponential_comparison (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (u v : ℝ) :
    Real.exp (-(kernelLogConstant lam*|v-u|))*fullLineDensityFunction lam h0 hpi u ≤
      fullLineDensityFunction lam h0 hpi v ∧
      fullLineDensityFunction lam h0 hpi v ≤
        Real.exp (kernelLogConstant lam*|v-u|)*fullLineDensityFunction lam h0 hpi u := by
  let r := fullLineDensityFunction lam h0 hpi
  let C := kernelLogConstant lam
  have hr := fullLineDensityFunction_integrable lam h0 hpi
  have hp (t : ℝ) : 0 ≤ r t := (fullLineDensityFunction_pos lam h0 hhalf hpi t).le
  have hi (x : ℝ) : Integrable (fun t : ℝ => r t*(-kernelK lam (x-t))) :=
    boundedConvolution_integrand_integrable (fun t => r t) hr (-(physicalKernelFunction lam h0 hpi)) x
  have hupper (x y : ℝ) : r y ≤ Real.exp (C*|y-x|)*r x := by
    let E : ℝ := Real.exp (C*|y-x|)
    have hs : kernelS lam y ≤ E*kernelS lam x := (kernelS_exponential_comparison lam h0 hpi x y).2
    have hint : (∫ t : ℝ, r t*(-kernelK lam (y-t))) ≤ E*(∫ t : ℝ, r t*(-kernelK lam (x-t))) := by
      rw [← integral_const_mul]
      apply integral_mono (hi y) ((hi x).const_mul E)
      intro t
      have hk := (negative_kernelK_exponential_comparison lam hhalf hpi (x-t) (y-t)).2
      have heq : (y-t)-(x-t)=y-x := by ring
      rw [heq] at hk
      have hm := mul_le_mul_of_nonneg_left hk (hp t)
      calc
        _ ≤ r t*(E*(-kernelK lam (x-t))) := hm
        _ = _ := by ring
    have hx := fullLineDensityFunction_renewal lam h0 hpi x
    have hy := fullLineDensityFunction_renewal lam h0 hpi y
    change r x=kernelS lam x+(∫ t : ℝ, r t*(-kernelK lam (x-t))) at hx
    change r y=kernelS lam y+(∫ t : ℝ, r t*(-kernelK lam (y-t))) at hy
    dsimp [E] at hs hint
    rw [hy,hx,mul_add]
    exact add_le_add hs hint
  refine ⟨?_,hupper u v⟩
  have hh := hupper v u
  rw [abs_sub_comm u v] at hh
  have he : Real.exp (-(C*|v-u|))*Real.exp (C*|v-u|)=1 := by rw [← Real.exp_add]; simp
  have hm := mul_le_mul_of_nonneg_left hh (Real.exp_pos (-(C*|v-u|))).le
  rw [← mul_assoc,he,one_mul] at hm
  exact hm

/-- A fixed positive amount of the boundary value lies in the unit
interval immediately to its right, hence in the actual right tail. -/
theorem fullLineDensityFunction_tail_lower (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Q : ℝ) :
    Real.exp (-kernelLogConstant lam)*fullLineDensityFunction lam h0 hpi Q ≤
      kernelTail (fun u => fullLineDensityFunction lam h0 hpi u) Q := by
  let r := fullLineDensityFunction lam h0 hpi
  let c : ℝ := Real.exp (-kernelLogConstant lam)*r Q
  have hr := fullLineDensityFunction_integrable lam h0 hpi
  have hc (u : ℝ) (hu : u ∈ Icc Q (Q+1)) : c ≤ r u := by
    have hd : |u-Q| ≤ 1 := abs_le.mpr ⟨by linarith [hu.1],by linarith [hu.2]⟩
    have hh := (fullLineDensityFunction_exponential_comparison lam h0 hhalf hpi Q u).1
    have he : Real.exp (-kernelLogConstant lam) ≤ Real.exp (-(kernelLogConstant lam*|u-Q|)) :=
      Real.exp_le_exp.mpr (by nlinarith [kernelLogConstant_nonneg lam])
    exact (mul_le_mul_of_nonneg_right he (fullLineDensityFunction_pos lam h0 hhalf hpi Q).le).trans hh
  have hi : c ≤ ∫ u in Icc Q (Q+1), r u := by
    calc
      _ = ∫ u in Icc Q (Q+1), c := by simp
      _ ≤ _ := setIntegral_mono_on (integrableOn_const (μ := volume) (by simp)) hr.integrableOn measurableSet_Icc hc
  have hmono : (∫ u in Icc Q (Q+1), r u) ≤ kernelTail (fun u => r u) Q := by
    rw [integral_Icc_eq_integral_Ioc]
    exact setIntegral_mono_set hr.integrableOn (Eventually.of_forall (fun u => (fullLineDensityFunction_pos lam h0 hhalf hpi u).le))
      (Eventually.of_forall (fun u (hu : u ∈ Ioc Q (Q+1)) => hu.1))
  exact hi.trans hmono

end
end SixVertex
