import SixVertex.KernelMass
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace SixVertex
noncomputable section
open Set MeasureTheory

/-- The real Mobius map identifies the beta-integral interval with the
positive half-line, including the actual Jacobian factor. -/
theorem integral_mobius_positive_half_line (g : ℝ → ℂ) :
    (∫ x in Ioo (0 : ℝ) 1, (1/(1-x)^2 : ℝ) • g (x/(1-x)))=
      ∫ y in Ioi (0 : ℝ), g y := by
  let f : ℝ → ℝ := fun x => x/(1-x)
  have hden (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < 1-x := by linarith [hx.2]
  have himage : f '' Ioo (0 : ℝ) 1=Ioi (0 : ℝ) := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact div_pos hx.1 (hden x hx)
    · intro hy
      change 0 < y at hy
      have hyp : 0 < 1+y := by linarith [hy]
      refine ⟨y/(1+y),⟨div_pos hy hyp,(div_lt_one hyp).mpr (by linarith)⟩,?_⟩
      dsimp [f]
      field_simp [hyp.ne']
      ring
  have hderiv (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivWithinAt f (1/(1-x)^2) (Ioo (0 : ℝ) 1) x := by
    have hh := ((hasDerivAt_id x).div ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)) (hden x hx).ne')
    change HasDerivAt (fun y : ℝ => y/(1-y)) ((1*(1-x)-x*(0-1))/(1-x)^2) x at hh
    have heq : (1*(1-x)-x*(0-1))/(1-x)^2=1/(1-x)^2 := by ring
    rw [heq] at hh
    exact hh.hasDerivWithinAt
  have hinj : InjOn f (Ioo (0 : ℝ) 1) := by
    intro x hx y hy hxy
    have he := (div_eq_div_iff (hden x hx).ne' (hden y hy).ne').mp hxy
    nlinarith
  have hh := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj g
  rw [himage] at hh
  symm
  apply hh.trans
  apply setIntegral_congr_fun measurableSet_Ioo
  intro x hx
  change |1/(1-x)^2| • g (x/(1-x))=(1/(1-x)^2 : ℝ) • g (x/(1-x))
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1/(1-x)^2)]

end
end SixVertex
