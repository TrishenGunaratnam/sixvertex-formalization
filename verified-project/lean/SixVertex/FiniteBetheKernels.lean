import SixVertex.BetheConvention
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! The odd primitives in Lemma 2.2 are given explicitly by arctan.
This fixes their additive constants and retains real analyticity. -/
namespace SixVertex

open scoped ContDiff

noncomputable def barePhase (θ u : ℝ) : ℝ :=
  Real.arctan ((Real.cos θ / Real.sin θ) * (Real.sinh u / Real.cosh u)) / Real.pi

noncomputable def phaseDensity (θ u : ℝ) : ℝ :=
  Real.sin (2*θ) / (Real.pi * (Real.cosh (2*u) - Real.cos (2*θ)))

noncomputable def countingS (lam u : ℝ) : ℝ := barePhase (lam/2) u
noncomputable def countingTheta (lam u : ℝ) : ℝ := barePhase lam u
noncomputable def kernelS (lam u : ℝ) : ℝ :=
  Real.sin lam / (Real.pi * (Real.cosh (2*u) - Real.cos lam))
noncomputable def kernelK (lam u : ℝ) : ℝ := phaseDensity lam u

@[simp] theorem barePhase_zero (θ : ℝ) : barePhase θ 0 = 0 := by simp [barePhase]
@[simp] theorem barePhase_neg (θ u : ℝ) : barePhase θ (-u) = -barePhase θ u := by
  simp [barePhase, Real.sinh_neg, Real.cosh_neg, neg_div, mul_neg]

/-- The hyperbolic kernel denominator is strictly positive throughout the physical interval. -/
theorem phase_denominator_pos (θ u : ℝ) (hθ : Real.sin θ ≠ 0) :
    0 < Real.cosh (2*u) - Real.cos (2*θ) := by
  rw [Real.cosh_two_mul, Real.cos_two_mul_eq_one_sub, Real.cosh_sq]
  nlinarith [sq_nonneg (Real.sinh u), sq_pos_of_ne_zero hθ]

theorem barePhase_deriv_scalar (θ u : ℝ) (hθ : Real.sin θ ≠ 0) :
    ((1 / (1 + ((Real.cos θ / Real.sin θ) * (Real.sinh u / Real.cosh u))^2)) *
      ((Real.cos θ / Real.sin θ) *
        ((Real.cosh u * Real.cosh u - Real.sinh u * Real.sinh u) / (Real.cosh u)^2))) /
      Real.pi = phaseDensity θ u := by
  have hc : Real.cosh u ≠ 0 := (Real.cosh_pos u).ne'
  have hd : 1 + ((Real.cos θ / Real.sin θ) * (Real.sinh u / Real.cosh u))^2 ≠ 0 := by positivity
  have hp := (phase_denominator_pos θ u hθ).ne'
  have ht := Real.sin_sq_add_cos_sq θ
  have hh := Real.cosh_sq u
  unfold phaseDensity
  rw [Real.sin_two_mul, Real.cosh_two_mul, Real.cos_two_mul_eq_one_sub]
  have he : Real.cosh u ^ 2 + Real.sinh u ^ 2 - (1 - 2 * Real.sin θ ^ 2) ≠ 0 := by
    simpa only [Real.cosh_two_mul, Real.cos_two_mul_eq_one_sub] using hp
  field_simp [hθ, hc, hd, he, Real.pi_ne_zero]
  have he' : Real.cosh u ^ 2 + Real.sinh u ^ 2 - (1 - Real.sin θ ^ 2 * 2) ≠ 0 := by
    nlinarith [sq_nonneg (Real.sinh u), sq_pos_of_ne_zero hθ]
  apply (eq_div_iff he').2
  rw [Real.cosh_sq, Real.cos_sq']
  ring

theorem hasDerivAt_barePhase (θ u : ℝ) (hθ : Real.sin θ ≠ 0) :
    HasDerivAt (barePhase θ) (phaseDensity θ u) u := by
  have h := (((Real.hasDerivAt_sinh u).div (Real.hasDerivAt_cosh u)
    (Real.cosh_pos u).ne').const_mul (Real.cos θ / Real.sin θ)).arctan.div_const Real.pi
  simp only [Pi.div_apply] at h
  rw [barePhase_deriv_scalar θ u hθ] at h
  exact h

theorem contDiff_barePhase (θ : ℝ) : ContDiff ℝ ω (barePhase θ) := by
  unfold barePhase
  have h : ContDiff ℝ ω (fun u : ℝ => Real.sinh u / Real.cosh u) :=
    Real.contDiff_sinh.div Real.contDiff_cosh (fun u => (Real.cosh_pos u).ne')
  have hm : ContDiff ℝ ω (fun u : ℝ => (Real.cos θ / Real.sin θ) *
      (Real.sinh u / Real.cosh u)) := contDiff_const.mul h
  exact (Real.contDiff_arctan.comp hm).div_const Real.pi

theorem hasDerivAt_countingS (lam u : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    HasDerivAt (countingS lam) (kernelS lam u) u := by
  have hs : Real.sin (lam/2) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])).ne'
  have h := hasDerivAt_barePhase (lam/2) u hs
  change HasDerivAt (barePhase (lam/2)) _ u
  simpa only [phaseDensity, kernelS, show 2*(lam/2) = lam by ring] using h

theorem hasDerivAt_countingTheta (lam u : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    HasDerivAt (countingTheta lam) (kernelK lam u) u :=
  hasDerivAt_barePhase lam u (Real.sin_pos_of_pos_of_lt_pi h0 hpi).ne'

@[simp] theorem kernelK_neg (lam u : ℝ) : kernelK lam (-u) = kernelK lam u := by
  simp [kernelK, phaseDensity, mul_neg, Real.cosh_neg]

theorem kernelS_pos (lam u : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    0 < kernelS lam u := by
  have hs : Real.sin (lam/2) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])).ne'
  have hd := phase_denominator_pos (lam/2) u hs
  rw [show 2*(lam/2) = lam by ring] at hd
  exact div_pos (Real.sin_pos_of_pos_of_lt_pi h0 hpi) (mul_pos Real.pi_pos hd)

theorem kernelK_nonpos (lam u : ℝ) (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) :
    kernelK lam u ≤ 0 := by
  have h0 : 0 < lam := by linarith [Real.pi_pos]
  have hs := (Real.sin_pos_of_pos_of_lt_pi h0 hpi).ne'
  have hcos : Real.cos lam ≤ 0 := by
    exact Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith)
  unfold kernelK phaseDensity
  rw [Real.sin_two_mul]
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num) (Real.sin_pos_of_pos_of_lt_pi h0 hpi).le) hcos)
    (le_of_lt (mul_pos Real.pi_pos (phase_denominator_pos lam u hs)))

end SixVertex
