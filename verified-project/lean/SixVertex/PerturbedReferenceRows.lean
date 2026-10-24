import SixVertex.ReferenceGaudin
import SixVertex.RelativeKernelVariation

namespace SixVertex
noncomputable section
open Set

theorem configuration_difference_distance {n : ℕ} (Y X : Fin n → ℝ) (eps : ℝ)
    (hclose : ∀ j, |X j-Y j| ≤ eps) (i j : Fin n) :
    |(X i-X j)-(Y i-Y j)| ≤ 2*eps := by
  have heq : (X i-X j)-(Y i-Y j)=(X i-Y i)-(X j-Y j) := by ring
  rw [heq]
  have hh := abs_sub_le (X i-Y i) 0 (X j-Y j)
  simp only [sub_zero,zero_sub,abs_neg] at hh
  exact hh.trans (by linarith [hclose i,hclose j])

/-- The actual counting density at a displaced evaluation point remains
multiplicatively comparable, uniformly in root number and location. -/
theorem homogeneous_countingSlope_configuration_lower {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (L : ℕ) (Y X : Fin n → ℝ)
    (eps : ℝ) (heps : 0 ≤ eps) (hclose : ∀ j, |X j-Y j| ≤ eps) (i : Fin n) :
    Real.exp (-(kernelLogConstant lam*(2*eps)))*countingSlope lam (fun _ => 0) L Y (Y i) ≤
      countingSlope lam (fun _ => 0) L X (X i) := by
  let beta := Real.exp (-(kernelLogConstant lam*(2*eps)))
  have hs : beta*kernelS lam (Y i) ≤ kernelS lam (X i) :=
    (exponential_comparison_of_distance_le (kernelS lam) (kernelLogConstant lam) (2*eps) (Y i) (X i)
      (kernelLogConstant_nonneg lam) (kernelS_pos lam _ h0 hpi).le (by linarith [hclose i])
      (kernelS_exponential_comparison lam h0 hpi (Y i) (X i))).1
  have hk (j : Fin n) : beta*(-kernelK lam (Y i-Y j)) ≤ -kernelK lam (X i-X j) :=
    (exponential_comparison_of_distance_le (fun x => -kernelK lam x) (kernelLogConstant lam) (2*eps)
      (Y i-Y j) (X i-X j) (kernelLogConstant_nonneg lam)
      (neg_nonneg.mpr (kernelK_nonpos lam _ hhalf hpi)) (configuration_difference_distance Y X eps hclose i j)
      (negative_kernelK_exponential_comparison lam hhalf hpi (Y i-Y j) (X i-X j))).1
  have hid (Z : Fin n → ℝ) : countingSlope lam (fun _ => 0) L Z (Z i)=
      (L : ℝ)*kernelS lam (Z i)+∑ j : Fin n, -kernelK lam (Z i-Z j) := by
    simp only [countingSlope,sub_zero,Finset.sum_const,Finset.card_range,nsmul_eq_mul,Finset.sum_neg_distrib]
    ring
  rw [hid Y,hid X,mul_add,Finset.mul_sum]
  have hsL := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
  exact add_le_add (by nlinarith only [hsL]) (Finset.sum_le_sum (fun j _ => hk j))

/-- The actual weighted kernel rows remain bounded under a uniform
small physical displacement of the reference configuration. -/
theorem perturbed_reference_kernel_row_bound {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Q : ℝ) (L : ℕ) (Y X : Fin n → ℝ)
    (R : ReferenceQuantileData lam h0 hpi Q L Y) (M : ℝ) (hM : 0 < M)
    (hlower : ∀ v ∈ Icc (-Q) Q, M ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q v)
    (eps : ℝ) (hclose : ∀ j, |X j-Y j| ≤ eps) (i : Fin n) :
    (∑ j : Fin n, (-kernelK lam (X i-X j))/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))) ≤
      Real.exp (kernelLogConstant lam*(2*eps))*
        (kernelL1Mass (kernelK lam)+referenceKernelRowErrorConstant lam/M) := by
  let alpha := Real.exp (kernelLogConstant lam*(2*eps))
  have hp (j : Fin n) : 0 < (L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j) :=
    mul_pos (Nat.cast_pos.mpr R.chain_pos) (finiteIntervalDensity_pos lam h0 hhalf hpi Q (Y j))
  have hpoint (j : Fin n) : (-kernelK lam (X i-X j))/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j)) ≤
      alpha*|kernelK lam (Y i-Y j)/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))| := by
    have hh := (exponential_comparison_of_distance_le (fun x => -kernelK lam x) (kernelLogConstant lam) (2*eps)
      (Y i-Y j) (X i-X j) (kernelLogConstant_nonneg lam)
      (neg_nonneg.mpr (kernelK_nonpos lam _ hhalf hpi)) (configuration_difference_distance Y X eps hclose i j)
      (negative_kernelK_exponential_comparison lam hhalf hpi (Y i-Y j) (X i-X j))).2
    rw [abs_div,abs_of_pos (hp j),abs_of_nonpos (kernelK_nonpos lam _ hhalf hpi)]
    exact (div_le_div_of_nonneg_right hh (hp j).le).trans_eq (by ring)
  calc
    _ ≤ ∑ j : Fin n, alpha*|kernelK lam (Y i-Y j)/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))| :=
      Finset.sum_le_sum (fun j _ => hpoint j)
    _ = alpha*(∑ j : Fin n, |kernelK lam (Y i-Y j)/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))|) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (reference_kernel_absolute_row_bound lam h0 hhalf hpi Q L Y R M hM hlower (Y i)) (Real.exp_pos _).le

/-- The divided diagonal contribution dominates the perturbed weighted
interaction row by an explicit quantity tending to 1-h as M grows. -/
theorem perturbed_reference_gaudin_row_drift {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Q : ℝ) (L : ℕ) (Y X : Fin n → ℝ)
    (R : ReferenceQuantileData lam h0 hpi Q L Y) (M : ℝ) (hM : 0 < M)
    (hlower : ∀ v ∈ Icc (-Q) Q, M ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q v)
    (eps : ℝ) (heps : 0 ≤ eps) (hclose : ∀ j, |X j-Y j| ≤ eps) (i : Fin n) :
    Real.exp (-(kernelLogConstant lam*(2*eps)))*(1-(kernelL1Mass (kernelKPrime lam)/2)/M)-
      Real.exp (kernelLogConstant lam*(2*eps))*(kernelL1Mass (kernelK lam)+referenceKernelRowErrorConstant lam/M) ≤
      countingSlope lam (fun _ => 0) L X (X i)/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y i))+
        ∑ j : Fin n, kernelK lam (X i-X j)/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j)) := by
  let w := (L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y i)
  have hw : M ≤ w := hlower (Y i) ⟨(R.location i).1.le,(R.location i).2.le⟩
  have hwp : 0 < w := hM.trans_le hw
  let D := kernelL1Mass (kernelKPrime lam)/2
  have hD : 0 ≤ D := div_nonneg (kernelL1Mass_nonneg _) (by norm_num)
  have href : 1-D/M ≤ countingSlope lam (fun _ => 0) L Y (Y i)/w := by
    have he : |(countingSlope lam (fun _ => 0) L Y (Y i)-w)/w| ≤ D/M := by
      rw [abs_div,abs_of_pos hwp]
      exact div_le_div₀ hD (reference_density_uniform_error lam h0 hhalf hpi Q L Y R (Y i)) hM hw
    have hid : (countingSlope lam (fun _ => 0) L Y (Y i)-w)/w=
        countingSlope lam (fun _ => 0) L Y (Y i)/w-1 := by field_simp
    rw [hid] at he
    linarith [(abs_le.mp he).1]
  have hconfig := div_le_div_of_nonneg_right
    (homogeneous_countingSlope_configuration_lower lam h0 hhalf hpi L Y X eps heps hclose i) hwp.le
  have hlow := (mul_le_mul_of_nonneg_left href (Real.exp_pos (-(kernelLogConstant lam*(2*eps)))).le).trans
    (by simpa only [mul_div_assoc] using hconfig)
  have hrow := perturbed_reference_kernel_row_bound lam h0 hhalf hpi Q L Y X R M hM hlower eps hclose i
  simp only [neg_div,Finset.sum_neg_distrib] at hrow
  change Real.exp (-(kernelLogConstant lam*(2*eps)))*(1-D/M)-_ ≤ _
  linarith

end
end SixVertex
