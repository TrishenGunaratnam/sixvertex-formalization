import SixVertex.WeightedRootCorrection
import SixVertex.RelativeKernelIncrement

namespace SixVertex
noncomputable section
open Set

/-- Density variation from an actual density-scaled displacement bound.
The bound is uniform on the whole real line and in the cutoff. -/
theorem reference_weighted_countingSlope_displacement_bound {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Q : ℝ) (L : ℕ) (Y Z : Fin n → ℝ)
    (R : ReferenceQuantileData lam h0 hpi Q L Y) (M radius : ℝ) (hM : 0 < M) (hrad : 0 ≤ radius)
    (hlower : ∀ v ∈ Icc (-Q) Q, M ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q v)
    (hdis : ∀ j, (L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j)*|Z j-Y j| ≤ radius) (u : ℝ) :
    |countingSlope lam (fun _ => 0) L Z u-countingSlope lam (fun _ => 0) L Y u| ≤
      kernelLogConstant lam*Real.exp (kernelLogConstant lam*(radius/M))*radius*
        (kernelL1Mass (kernelK lam)+referenceKernelRowErrorConstant lam/M) := by
  let w : Fin n → ℝ := fun j => (L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j)
  let A := kernelLogConstant lam*Real.exp (kernelLogConstant lam*(radius/M))
  have hA : 0 ≤ A := mul_nonneg (kernelLogConstant_nonneg _) (Real.exp_pos _).le
  have hw (j : Fin n) : M ≤ w j := hlower (Y j) ⟨(R.location j).1.le,(R.location j).2.le⟩
  have hwp (j : Fin n) : 0 < w j := hM.trans_le (hw j)
  have hd (j : Fin n) : |Z j-Y j| ≤ radius/w j := by
    apply (le_div_iff₀ (hwp j)).mpr
    have hh := hdis j
    change w j*|Z j-Y j| ≤ radius at hh
    nlinarith only [hh]
  have hpoint (j : Fin n) : |kernelK lam (u-Z j)-kernelK lam (u-Y j)| ≤
      A*radius*|kernelK lam (u-Y j)/w j| := by
    have hdiff : (u-Z j)-(u-Y j)=-(Z j-Y j) := by ring
    have hde : |(u-Z j)-(u-Y j)| ≤ radius/M := by
      rw [hdiff,abs_neg]
      exact (hd j).trans (div_le_div₀ hrad le_rfl hM (hw j))
    have he := kernelK_relative_increment_bound lam h0 hhalf hpi (radius/M) (u-Y j) (u-Z j) hde
    rw [hdiff,abs_neg] at he
    have hp := mul_le_mul_of_nonneg_left (hd j) (mul_nonneg hA (abs_nonneg (kernelK lam (u-Y j))))
    apply he.trans
    rw [abs_div,abs_of_pos (hwp j)]
    apply hp.trans_eq
    ring
  have hid : countingSlope lam (fun _ => 0) L Z u-countingSlope lam (fun _ => 0) L Y u=
      -(∑ j : Fin n, (kernelK lam (u-Z j)-kernelK lam (u-Y j))) := by
    unfold countingSlope
    rw [Finset.sum_sub_distrib]
    ring
  rw [hid,abs_neg]
  calc
    _ ≤ ∑ j : Fin n, |kernelK lam (u-Z j)-kernelK lam (u-Y j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin n, A*radius*|kernelK lam (u-Y j)/w j| := Finset.sum_le_sum (fun j _ => hpoint j)
    _ = (A*radius)*(∑ j : Fin n, |kernelK lam (u-Y j)/w j|) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (reference_kernel_absolute_row_bound lam h0 hhalf hpi Q L Y R M hM hlower u) (mul_nonneg hA hrad)

/-- Uniform correction and the actual whole-line counting-density error
for arbitrary cutoffs satisfying one true scaled-density threshold. -/
theorem uniform_reference_root_and_density_correction (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) :
    ∃ M radius C : ℝ, 0 < M ∧ 0 < radius ∧ 0 ≤ C ∧
      ∀ (n : ℕ) (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ), ∀ R : ReferenceQuantileData lam h0 hpi Q L Y,
      (∀ v ∈ Icc (-Q) Q, M ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q v) →
      ∃ Z : Fin n → ℝ, ConsecutiveRoots lam (fun _ => 0) L Z 0 ∧
        (∀ i, (L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y i)*|Z i-Y i| ≤ radius) ∧
        ∀ u : ℝ, |countingSlope lam (fun _ => 0) L Z u-(L : ℝ)*finiteIntervalDensity lam h0 hpi Q u| ≤ C := by
  obtain ⟨M,radius,hM,hrad,hcorr⟩ := exists_uniform_reference_root_correction lam h0 hhalf hpi
  let A := kernelLogConstant lam*Real.exp (kernelLogConstant lam*(radius/M))*radius*
    (kernelL1Mass (kernelK lam)+referenceKernelRowErrorConstant lam/M)
  let D := kernelL1Mass (kernelKPrime lam)/2
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (mul_nonneg (mul_nonneg (kernelLogConstant_nonneg _) (Real.exp_pos _).le) hrad.le)
      (add_nonneg (kernelL1Mass_nonneg _) (div_nonneg (referenceKernelRowErrorConstant_nonneg _) hM.le))
  have hD : 0 ≤ D := div_nonneg (kernelL1Mass_nonneg _) (by norm_num)
  refine ⟨M,radius,A+D,hM,hrad,add_nonneg hA hD,?_⟩
  intro n Q L Y R hlower
  obtain ⟨Z,hZ,hdis⟩ := hcorr n Q L Y R hlower
  refine ⟨Z,hZ,hdis,?_⟩
  intro u
  have heq : countingSlope lam (fun _ => 0) L Z u-(L : ℝ)*finiteIntervalDensity lam h0 hpi Q u=
      (countingSlope lam (fun _ => 0) L Z u-countingSlope lam (fun _ => 0) L Y u)+
      (countingSlope lam (fun _ => 0) L Y u-(L : ℝ)*finiteIntervalDensity lam h0 hpi Q u) := by ring
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add
    (reference_weighted_countingSlope_displacement_bound lam h0 hhalf hpi Q L Y Z R M radius hM hrad.le hlower hdis u)
    (reference_density_uniform_error lam h0 hhalf hpi Q L Y R u))

end
end SixVertex
