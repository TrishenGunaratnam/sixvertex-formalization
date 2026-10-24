import SixVertex.KernelMass

namespace SixVertex
open MeasureTheory

noncomputable def phaseDensityPrime (theta u : ℝ) : ℝ :=
  -(2*Real.sinh (2*u)/(Real.cosh (2*u)-Real.cos (2*theta)))*phaseDensity theta u

theorem hasDerivAt_phaseDensity (theta u : ℝ) (hs : Real.sin theta ≠ 0) :
    HasDerivAt (phaseDensity theta) (phaseDensityPrime theta u) u := by
  have hp := phase_denominator_pos theta u hs
  have hd : HasDerivAt (fun v : ℝ => Real.cosh (2*v)-Real.cos (2*theta))
      (2*Real.sinh (2*u)) u := by
    simpa only [Function.comp_def,id_eq,mul_one,one_mul,mul_comm] using
      ((Real.hasDerivAt_cosh (2*u)).comp u ((hasDerivAt_id u).const_mul 2)).sub_const
        (Real.cos (2*theta))
  have h := (hasDerivAt_const u (Real.sin (2*theta))).div
    (hd.const_mul Real.pi) (mul_pos Real.pi_pos hp).ne'
  convert h using 1
  · rfl
  · unfold phaseDensityPrime phaseDensity
    field_simp [Real.pi_ne_zero,hp.ne']
    <;> ring

theorem abs_sinh_le_cosh_real (u : ℝ) : |Real.sinh u| ≤ Real.cosh u := by
  rw [Real.sinh_eq,Real.cosh_eq]
  apply abs_le.mpr
  constructor <;> linarith [Real.exp_pos u,Real.exp_pos (-u)]

theorem phase_denominator_scaled_cosh (theta u : ℝ) :
    (Real.sin theta)^2*Real.cosh (2*u) ≤ Real.cosh (2*u)-Real.cos (2*theta) := by
  have hd:=phase_denominator_cosh_bound theta u
  rw [Real.cosh_two_mul] at hd ⊢
  have hh:=Real.cosh_sq u
  nlinarith [sq_nonneg (Real.sin theta)]

/-- The logarithmic-derivative constant depends on the physical parameter
only, and is uniform over the whole real line. The zero kernel is included. -/
theorem phaseDensityPrime_relative_bound (theta u : ℝ) (hs : Real.sin theta ≠ 0) :
    |phaseDensityPrime theta u| ≤ (2/(Real.sin theta)^2)*|phaseDensity theta u| := by
  have hp:=phase_denominator_pos theta u hs
  have hs2:=sq_pos_of_ne_zero hs
  have hd:=phase_denominator_scaled_cosh theta u
  have hh:=mul_le_mul_of_nonneg_left (abs_sinh_le_cosh_real (2*u)) hs2.le
  have hratio : |2*Real.sinh (2*u)/(Real.cosh (2*u)-Real.cos (2*theta))| ≤ 2/(Real.sin theta)^2 := by
    rw [abs_div,abs_of_pos hp,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply (div_le_div_iff₀ hp hs2).mpr
    nlinarith
  unfold phaseDensityPrime
  rw [abs_mul,abs_neg]
  exact mul_le_mul_of_nonneg_right hratio (abs_nonneg _)

theorem kernelS_eq_phaseDensity (lam u : ℝ) : kernelS lam u=phaseDensity (lam/2) u := by
  unfold kernelS phaseDensity
  rw [show 2*(lam/2)=lam by ring]

noncomputable def kernelSPrime (lam u : ℝ) : ℝ := phaseDensityPrime (lam/2) u
noncomputable def kernelKPrime (lam u : ℝ) : ℝ := phaseDensityPrime lam u

theorem hasDerivAt_kernelS (lam u : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    HasDerivAt (kernelS lam) (kernelSPrime lam u) u := by
  have hs : Real.sin (lam/2) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])).ne'
  have he : kernelS lam=phaseDensity (lam/2) := funext (kernelS_eq_phaseDensity lam)
  rw [he]
  exact hasDerivAt_phaseDensity _ _ hs

theorem hasDerivAt_kernelK (lam u : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    HasDerivAt (kernelK lam) (kernelKPrime lam u) u :=
  hasDerivAt_phaseDensity _ _ (Real.sin_pos_of_pos_of_lt_pi h0 hpi).ne'

theorem kernelSPrime_relative_bound (lam u : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    |kernelSPrime lam u| ≤ (2/(Real.sin (lam/2))^2)*kernelS lam u := by
  have hs : Real.sin (lam/2) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])).ne'
  have h:=phaseDensityPrime_relative_bound (lam/2) u hs
  rw [← kernelS_eq_phaseDensity,abs_of_pos (kernelS_pos lam u h0 hpi)] at h
  exact h

theorem kernelKPrime_relative_bound (lam u : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    |kernelKPrime lam u| ≤ (2/(Real.sin lam)^2)*|kernelK lam u| :=
  phaseDensityPrime_relative_bound lam u (Real.sin_pos_of_pos_of_lt_pi h0 hpi).ne'

theorem continuous_phaseDensity (theta : ℝ) (hs : Real.sin theta ≠ 0) :
    Continuous (phaseDensity theta) := by
  unfold phaseDensity
  apply Continuous.div continuous_const
  · fun_prop
  · intro u
    exact (mul_pos Real.pi_pos (phase_denominator_pos theta u hs)).ne'

theorem continuous_phaseDensityPrime (theta : ℝ) (hs : Real.sin theta ≠ 0) :
    Continuous (phaseDensityPrime theta) := by
  unfold phaseDensityPrime
  apply Continuous.mul _ (continuous_phaseDensity theta hs)
  apply Continuous.neg
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro u
    exact (phase_denominator_pos theta u hs).ne'

/-- The first kernel derivative has an integrable majorant.
This is a direct consequence of the actual derivative formula. -/
theorem phaseDensityPrime_integrable (theta : ℝ) (h0 : 0 < theta) (hpi : theta < Real.pi) :
    Integrable (phaseDensityPrime theta) := by
  have hs := (Real.sin_pos_of_pos_of_lt_pi h0 hpi).ne'
  have hi := (kernelK_integrable theta h0 hpi).norm.const_mul (2/(Real.sin theta)^2)
  apply hi.mono' (continuous_phaseDensityPrime theta hs).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun u => by
    simpa only [Real.norm_eq_abs,kernelK] using phaseDensityPrime_relative_bound theta u hs)

theorem kernelKPrime_integrable (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    Integrable (kernelKPrime lam) := phaseDensityPrime_integrable lam h0 hpi

theorem kernelSPrime_integrable (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    Integrable (kernelSPrime lam) :=
  phaseDensityPrime_integrable (lam/2) (by linarith) (by linarith [Real.pi_pos])

theorem kernelKPrime_exponential_bound (lam u : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    |kernelKPrime lam u| ≤
      ((2/(Real.sin lam)^2)*(2/(Real.pi*(Real.sin lam)^2)))*Real.exp (-2*|u|) := by
  calc
    _ ≤ (2/(Real.sin lam)^2)*|kernelK lam u| := kernelKPrime_relative_bound lam u h0 hpi
    _ ≤ (2/(Real.sin lam)^2)*((2/(Real.pi*(Real.sin lam)^2))*Real.exp (-2*|u|)) :=
      mul_le_mul_of_nonneg_left (kernelK_exponential_bound lam u h0 hpi) (by positivity)
    _ = _ := by ring

end SixVertex
