import SixVertex.MellinBeta

namespace SixVertex
noncomputable section
open Set MeasureTheory

/-- On the slit plane,the shifted Mellin denominator has a positive
linear lower bound throughout the positive integration half-line. -/
theorem exists_slit_mellin_denominator_bound (a : ℂ) (ha : a ∈ Complex.slitPlane) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 0 ≤ t → c*(1+t) ≤ ‖(t : ℂ)+a‖ := by
  let f : ℝ → ℂ := fun x => ((1-x : ℝ) : ℂ)*a+(x : ℂ)
  have hn (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : f x ≠ 0 := by
    by_cases hx1 : x=1
    · simp [f,hx1]
    · have hxlt : x < 1 := (lt_or_eq_of_le hx.2).resolve_right hx1
      have hp : 0 < 1-x := by linarith
      intro hh
      rcases Complex.mem_slitPlane_iff.mp ha with hre | him
      · have h := congrArg Complex.re hh
        change (f x).re=0 at h
        dsimp [f] at h
        simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero] at h
        nlinarith [mul_pos hp hre,hx.1]
      · have h := congrArg Complex.im hh
        change (f x).im=0 at h
        dsimp [f] at h
        simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero] at h
        exact (mul_ne_zero hp.ne' him) h
  have hf : Continuous (fun x : ℝ => ‖f x‖) := by dsimp [f]; fun_prop
  obtain ⟨c,hc,hbound⟩ := isCompact_Icc.exists_forall_le' hf.continuousOn (fun x hx => norm_pos_iff.mpr (hn x hx))
  refine ⟨c,hc,?_⟩
  intro t ht
  have hp : 0 < 1+t := by linarith
  let x : ℝ := t/(1+t)
  have hx : x ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg ht hp.le,(div_le_one hp).mpr (by linarith)⟩
  have he : ((1+t : ℝ) : ℂ)*f x=(t : ℂ)+a := by
    dsimp [f,x]
    push_cast
    field_simp [show (1 : ℂ)+(t : ℂ) ≠ 0 by exact_mod_cast hp.ne']
    ring
  rw [← he,norm_mul,Complex.norm_of_nonneg hp.le]
  have hh := mul_le_mul_of_nonneg_left (hbound x hx) hp.le
  nlinarith only [hh]

/-- The denominator estimate is uniform in a neighborhood of each
slit-plane parameter,as required for holomorphic differentiation under
the actual Mellin integral. -/
theorem exists_local_slit_mellin_denominator_bound (a : ℂ) (ha : a ∈ Complex.slitPlane) :
    ∃ delta c : ℝ, 0 < delta ∧ 0 < c ∧ ∀ b : ℂ, dist b a < delta →
      ∀ t : ℝ, 0 ≤ t → c*(1+t) ≤ ‖(t : ℂ)+b‖ := by
  obtain ⟨c,hc,hbound⟩ := exists_slit_mellin_denominator_bound a ha
  refine ⟨c/2,c/2,by positivity,by positivity,?_⟩
  intro b hb t ht
  have hd : ‖b-a‖ < c/2 := by simpa only [dist_eq_norm] using hb
  have htri : ‖(t : ℂ)+a‖ ≤ ‖(t : ℂ)+b‖+‖b-a‖ := by
    calc
      _ = ‖((t : ℂ)+b)+(a-b)‖ := by congr 1; ring
      _ ≤ ‖(t : ℂ)+b‖+‖a-b‖ := norm_add_le _ _
      _ = _ := by rw [norm_sub_rev]
  have h := hbound t ht
  nlinarith [mul_nonneg hc.le ht]

end
end SixVertex
