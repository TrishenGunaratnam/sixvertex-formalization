import SixVertex.BetheCountingPhase
import SixVertex.FiniteGaudin

namespace SixVertex

noncomputable def betheQ {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (x : ℂ) : ℂ :=
  vacuumL (Complex.I*lam) (fun j => (b j : ℂ)) x L /
    vacuumA (Complex.I*lam) (fun j => (b j : ℂ)) x L *
  ∏ k, Complex.sinh (x-Y k+Complex.I*lam) / Complex.sinh (x-Y k-Complex.I*lam)

def OnShell {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (twist : ℝ) : Prop :=
  ∀ j, betheQ lam b L Y (Y j) = -Complex.exp (2*Complex.I*twist)

theorem shifted_ratio_lower (θ u : ℝ) (hθ : Real.sin θ ≠ 0) :
    Complex.sinh ((u : ℂ)-Complex.I*θ) / Complex.sinh ((u : ℂ)+Complex.I*θ) =
      -Complex.exp (2*(Real.pi : ℂ)*Complex.I*(barePhase θ u : ℂ)) := by
  have h := congrArg Neg.neg (exp_barePhase θ u hθ)
  simpa only [neg_div, neg_neg] using h.symm

theorem shifted_ratio_upper (θ u : ℝ) (hθ : Real.sin θ ≠ 0) :
    Complex.sinh ((u : ℂ)+Complex.I*θ) / Complex.sinh ((u : ℂ)-Complex.I*θ) =
      -Complex.exp (-(2*(Real.pi : ℂ)*Complex.I*(barePhase θ u : ℂ))) := by
  have h := shifted_ratio_lower θ (-u) hθ
  rw [Complex.ofReal_neg, barePhase_neg, Complex.ofReal_neg] at h
  have e1 : -(u : ℂ)-Complex.I*θ = -((u : ℂ)+Complex.I*θ) := by ring
  have e2 : -(u : ℂ)+Complex.I*θ = -((u : ℂ)-Complex.I*θ) := by ring
  simpa only [e1,e2,Complex.sinh_neg,neg_div_neg_eq,mul_neg] using h

theorem negative_exp_product {I : Type*} (S : Finset I) (z : I → ℂ) :
    (∏ i ∈ S, -Complex.exp (z i)) = (-1 : ℂ)^S.card * Complex.exp (∑ i ∈ S, z i) := by
  have he : (fun i => -Complex.exp (z i)) = (fun i => (-1 : ℂ)*Complex.exp (z i)) := by
    funext i
    ring
  rw [he, Finset.prod_mul_distrib, Finset.prod_const, ← Complex.exp_sum]

theorem vacuum_ratio_counting_phase (lam : ℝ) (b : ℕ → ℝ) (L : ℕ) (u : ℝ)
    (h0 : 0 < lam) (hpi : lam < Real.pi) :
    vacuumL (Complex.I*lam) (fun j => (b j : ℂ)) u L /
      vacuumA (Complex.I*lam) (fun j => (b j : ℂ)) u L =
    (-1 : ℂ)^L * Complex.exp (2*(Real.pi : ℂ)*Complex.I*
      ((∑ a ∈ Finset.range L, countingS lam (u-b a) : ℝ) : ℂ)) := by
  have hs : Real.sin (lam/2) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])).ne'
  have ht := physical_deformation_ne_zero lam h0 hpi
  rw [vacuumL_product, vacuumA_product, ← Finset.prod_div_distrib]
  have hprod : (∏ j ∈ Finset.range L,
      (Complex.sinh ((u : ℂ)-b j-Complex.I*lam/2) / Complex.sinh (Complex.I*lam)) /
      (Complex.sinh ((u : ℂ)-b j+Complex.I*lam/2) / Complex.sinh (Complex.I*lam))) =
      ∏ j ∈ Finset.range L, -Complex.exp (2*(Real.pi : ℂ)*Complex.I*
        (countingS lam (u-b j) : ℂ)) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hh := shifted_ratio_lower (lam/2) (u-b j) hs
    have e1 : ((u-b j : ℝ) : ℂ) - Complex.I*(lam/2 : ℝ) =
        (u : ℂ)-b j-Complex.I*lam/2 := by push_cast; ring
    have e2 : ((u-b j : ℝ) : ℂ) + Complex.I*(lam/2 : ℝ) =
        (u : ℂ)-b j+Complex.I*lam/2 := by push_cast; ring
    rw [e1,e2] at hh
    rw [div_div_div_cancel_right₀ ht _ _]
    exact hh
  rw [hprod, negative_exp_product]
  simp only [Finset.card_range, Complex.ofReal_sum, Finset.mul_sum]

theorem betheQ_counting_phase {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hEven : Even L) (Y : Fin n → ℝ) (u : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    betheQ lam b L Y u = (-1 : ℂ)^n *
      Complex.exp (2*(Real.pi : ℂ)*Complex.I*(countingXi lam b L Y u : ℂ)) := by
  have hs := (Real.sin_pos_of_pos_of_lt_pi h0 hpi).ne'
  unfold betheQ
  rw [vacuum_ratio_counting_phase lam b L u h0 hpi]
  have hp : (∏ k, Complex.sinh ((u : ℂ)-Y k+Complex.I*lam) /
      Complex.sinh ((u : ℂ)-Y k-Complex.I*lam)) =
      ∏ k, -Complex.exp (-(2*(Real.pi : ℂ)*Complex.I*(countingTheta lam (u-Y k) : ℂ))) := by
    apply Finset.prod_congr rfl
    intro k hk
    have h := shifted_ratio_upper lam (u-Y k) hs
    simpa only [Complex.ofReal_sub, countingTheta] using h
  rw [hp, negative_exp_product]
  have heven : (-1 : ℂ)^L = 1 := hEven.neg_one_pow
  rw [heven, one_mul]
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [show ∑ k : Fin n, -(2*(Real.pi : ℂ)*Complex.I*(countingTheta lam (u-Y k) : ℂ)) =
      -(2*(Real.pi : ℂ)*Complex.I*((∑ k, countingTheta lam (u-Y k) : ℝ) : ℂ)) by
        simp only [Complex.ofReal_sum, Finset.mul_sum, Finset.sum_neg_distrib]]
  rw [show Complex.exp (2*(Real.pi : ℂ)*Complex.I*
      ((∑ a ∈ Finset.range L, countingS lam (u-b a) : ℝ) : ℂ)) *
      ((-1 : ℂ)^n * Complex.exp (-(2*(Real.pi : ℂ)*Complex.I*
        ((∑ k, countingTheta lam (u-Y k) : ℝ) : ℂ)))) =
      (-1 : ℂ)^n * (Complex.exp (2*(Real.pi : ℂ)*Complex.I*
        ((∑ a ∈ Finset.range L, countingS lam (u-b a) : ℝ) : ℂ)) *
        Complex.exp (-(2*(Real.pi : ℂ)*Complex.I*
        ((∑ k, countingTheta lam (u-Y k) : ℝ) : ℂ)))) by ring]
  rw [← Complex.exp_add]
  congr 2
  simp only [countingXi, Complex.ofReal_sub]
  ring

/-- Consecutive counting numbers give precisely the on-shell equations,
including the (-1)^n factor and the real twist normalization. -/
theorem consecutiveRoots_onShell {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hEven : Even L) (Y : Fin n → ℝ) (twist : ℝ)
    (h0 : 0 < lam) (hpi : lam < Real.pi) (hY : ConsecutiveRoots lam b L Y twist) :
    OnShell lam b L Y twist := by
  intro j
  rw [betheQ_counting_phase lam b L hEven Y (Y j) h0 hpi]
  have hy := congrFun hY.2 j
  change countingXi lam b L Y (Y j) = _ at hy
  rw [hy]
  have he : 2*(Real.pi : ℂ)*Complex.I*(countingTarget n twist j : ℂ) =
      ((j.val+1 : ℕ) : ℂ)*(2*Real.pi*Complex.I) +
      ((n+1 : ℕ) : ℂ)*(-(Real.pi : ℂ)*Complex.I) + 2*Complex.I*twist := by
    unfold countingTarget
    push_cast
    field_simp
    ring
  rw [he, Complex.exp_add, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I,
    Complex.exp_nat_mul]
  have hm : Complex.exp (-(Real.pi : ℂ)*Complex.I) = -1 := by
    rw [neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num
  rw [hm, one_mul, pow_succ]
  have hp : (-1 : ℂ)^n * (-1)^n = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  calc
    _ = ((-1 : ℂ)^n * (-1)^n) * (-Complex.exp (2*Complex.I*twist)) := by ring
    _ = _ := by rw [hp, one_mul]

end SixVertex
