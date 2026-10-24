import SixVertex.ShiftedMellinHolomorphy
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace SixVertex
noncomputable section
open Set MeasureTheory Filter Topology

/-- Positive real scaling of the true shifted Mellin kernel. -/
theorem shifted_mellin_positive_scaling (z : ℂ) (a t : ℝ) (ha : 0 < a) (ht : 0 ≤ t) :
    (a : ℂ)*(((a*t : ℝ) : ℂ)^(z-1)/(((a*t : ℝ) : ℂ)+(a : ℂ)))=
      (a : ℂ)^(z-1)*((t : ℂ)^(z-1)/(1+(t : ℂ))) := by
  have hA : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hp : 0 < 1+t := by linarith
  have hD : (a : ℂ)*(t : ℂ)+(a : ℂ) ≠ 0 := by
    have hh : 0 < a*t+a := by nlinarith [mul_nonneg ha.le ht]
    exact_mod_cast hh.ne'
  have hP : (1 : ℂ)+(t : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg ha.le ht (z-1)]
  have hfac : (a : ℂ)*(t : ℂ)+(a : ℂ)=(a : ℂ)*(1+(t : ℂ)) := by ring
  rw [hfac]
  field_simp [hA,hP] <;> ring

/-- The shifted Mellin formula on the positive real axis follows from
actual real scaling and the proved Euler integral. -/
theorem integral_shifted_mellin_positive (z : ℂ) (h0 : 0 < z.re) (h1 : z.re < 1)
    (a : ℝ) (ha : 0 < a) :
    (∫ t in Ioi (0 : ℝ), (t : ℂ)^(z-1)/((t : ℂ)+(a : ℂ)))=
      (a : ℂ)^(z-1)*((Real.pi : ℂ)/Complex.sin ((Real.pi : ℂ)*z)) := by
  have hs := integral_comp_mul_left_Ioi' (fun t : ℝ => (t : ℂ)^(z-1)/((t : ℂ)+(a : ℂ))) 0 ha
  simp only [mul_zero] at hs
  calc
    _ = a • (∫ t in Ioi (0 : ℝ), ((a*t : ℝ) : ℂ)^(z-1)/(((a*t : ℝ) : ℂ)+(a : ℂ))) := hs.symm
    _ = ∫ t in Ioi (0 : ℝ), (a : ℂ)*(((a*t : ℝ) : ℂ)^(z-1)/(((a*t : ℝ) : ℂ)+(a : ℂ))) := by
      rw [integral_const_mul]
      rfl
    _ = ∫ t in Ioi (0 : ℝ), (a : ℂ)^(z-1)*((t : ℂ)^(z-1)/(1+(t : ℂ))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact shifted_mellin_positive_scaling z a t ha ht.le
    _ = _ := by rw [integral_const_mul,integral_euler_mellin z h0 h1]

/-- The actual shifted Mellin integral is evaluated on the entire slit
plane by proved holomorphy and analytic uniqueness from positive real shifts. -/
theorem integral_shifted_mellin_slit (z a : ℂ) (h0 : 0 < z.re) (h1 : z.re < 1)
    (ha : a ∈ Complex.slitPlane) :
    (∫ t in Ioi (0 : ℝ), (t : ℂ)^(z-1)/((t : ℂ)+a))=
      a^(z-1)*((Real.pi : ℂ)/Complex.sin ((Real.pi : ℂ)*z)) := by
  let f : ℂ → ℂ := fun b => ∫ t in Ioi (0 : ℝ), (t : ℂ)^(z-1)/((t : ℂ)+b)
  let C : ℂ := (Real.pi : ℂ)/Complex.sin ((Real.pi : ℂ)*z)
  let g : ℂ → ℂ := fun b => b^(z-1)*C
  have hf : AnalyticOnNhd ℂ f Complex.slitPlane :=
    (differentiableOn_shifted_mellin_integral z h0 h1).analyticOnNhd Complex.isOpen_slitPlane
  have hgD : DifferentiableOn ℂ g Complex.slitPlane := by
    intro b hb
    exact ((differentiableAt_id.cpow_const hb).mul_const C).differentiableWithinAt
  have hg := hgD.analyticOnNhd Complex.isOpen_slitPlane
  have hconn : IsPreconnected Complex.slitPlane :=
    (Complex.starConvex_one_slitPlane.isPathConnected Complex.one_mem_slitPlane).isConnected.isPreconnected
  have hcl : (1 : ℂ) ∈ closure ({b : ℂ | f b=g b} \ {(1 : ℂ)}) := by
    apply Metric.mem_closure_iff.mpr
    intro eps heps
    have hp : 0 < 1+eps/2 := by linarith
    refine ⟨((1+eps/2 : ℝ) : ℂ),⟨?_,?_⟩,?_⟩
    · exact integral_shifted_mellin_positive z h0 h1 (1+eps/2) hp
    · change ((1+eps/2 : ℝ) : ℂ) ≠ 1
      norm_cast
      linarith
    · rw [dist_comm,dist_eq_norm,← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_of_nonneg (by linarith : 0 ≤ 1+eps/2-1)]
      linarith
  exact (hf.eqOn_of_preconnected_of_mem_closure hg hconn Complex.one_mem_slitPlane hcl) ha

end
end SixVertex
