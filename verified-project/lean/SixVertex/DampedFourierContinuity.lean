import SixVertex.WeightedKernel
import SixVertex.MellinBeta

namespace SixVertex
noncomputable section
open Set MeasureTheory Filter Topology

/-- Removing a small real exponential damping from the actual Fourier
integral is justified by one genuine integrable whole-line majorant. -/
theorem continuousAt_damped_fourier_zero (k : ℝ → ℝ) (hk : Continuous k) (C : ℝ) (hC : 0 ≤ C)
    (hdecay : ∀ u, |k u| ≤ C*Real.exp (-2*|u|)) (p : ℝ) :
    ContinuousAt (fun eps : ℝ => ∫ u : ℝ, Complex.exp (-Complex.I*(p : ℂ)*(u : ℂ))*
      ((Real.exp (-2*eps*u)*k u : ℝ) : ℂ)) 0 := by
  have hphase (u : ℝ) : ‖Complex.exp (-Complex.I*(p : ℂ)*(u : ℂ))‖=1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re,Complex.mul_im]
  apply continuousAt_of_dominated (bound := fun u : ℝ => C*Real.exp (-|u|))
  · exact Eventually.of_forall (fun eps => by fun_prop)
  · filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1/2)] with eps heps
    have he : |eps| < 1/2 := by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using heps
    apply Eventually.of_forall
    intro u
    rw [norm_mul,hphase,one_mul,Complex.norm_real,Real.norm_eq_abs]
    have habs : |-2*eps*u|=2*|eps| *|u| := by rw [abs_mul,abs_mul]; norm_num
    have hle : -2*eps*u ≤ |u| := by
      have hh := mul_le_mul_of_nonneg_right (show 2*|eps| ≤ 1 by linarith) (abs_nonneg u)
      have hp := le_abs_self (-2*eps*u)
      rw [habs] at hp
      nlinarith only [hh,hp]
    calc
      _ = Real.exp (-2*eps*u)*|k u| := by rw [abs_mul,abs_of_pos (Real.exp_pos _)]
      _ ≤ Real.exp |u| *|k u| := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hle) (abs_nonneg _)
      _ = |Real.exp (1*|u|)*k u| := by rw [abs_mul,abs_of_pos (Real.exp_pos _)]; simp
      _ ≤ _ := exponential_weight_majorant k C hC hdecay 1 (by norm_num) u
  · exact integrable_exp_neg_abs.const_mul C
  · exact Eventually.of_forall (fun u => by fun_prop)

/-- The actual physical interaction kernel admits the genuine undamped
Fourier limit;its integrable majorant is already proved from its formula. -/
theorem kernelK_damped_fourier_continuousAt_zero (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (p : ℝ) :
    ContinuousAt (fun eps : ℝ => ∫ u : ℝ, Complex.exp (-Complex.I*(p : ℂ)*(u : ℂ))*
      ((Real.exp (-2*eps*u)*kernelK lam u : ℝ) : ℂ)) 0 := by
  exact continuousAt_damped_fourier_zero (kernelK lam)
    (continuous_phaseDensity lam (Real.sin_pos_of_pos_of_lt_pi h0 hpi).ne')
    (2/(Real.pi*(Real.sin lam)^2)) (by positivity)
    (fun u => kernelK_exponential_bound lam u h0 hpi) p

end
end SixVertex
