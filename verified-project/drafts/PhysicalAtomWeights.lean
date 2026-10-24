import SixVertex.PhysicalReferenceIntervalMass
import SixVertex.SmoothQuadrature

namespace SixVertex
noncomputable section
open Set MeasureTheory

/-- Actual density error at a displaced root,retaining the individual
reference weight rather than replacing it by the global density scale. -/
def physicalRootDensityErrorBound (lam radius M : ℝ) : ℝ :=
  kernelL1Mass (kernelKPrime lam)/2+
    (kernelLogConstant lam*Real.exp (kernelLogConstant lam*(radius/M))*radius)*
      (kernelL1Mass (kernelK lam)+physicalReferenceKernelRowErrorConstant lam/M)+
    physicalDensityLogConstant lam*Real.exp (physicalDensityLogConstant lam*(radius/M))*radius

theorem physicalRootDensityErrorBound_nonneg (lam radius M : ℝ) (h0 : 0 < lam)
    (hrad : 0 ≤ radius) (hM : 0 < M) : 0 ≤ physicalRootDensityErrorBound lam radius M := by
  have hk := kernelLogConstant_nonneg lam
  have hf := (physicalDensityLogConstant_pos lam h0).le
  have hb := physicalReferenceKernelRowErrorConstant_nonneg lam h0
  have hm := kernelL1Mass_nonneg (kernelK lam)
  have hd := kernelL1Mass_nonneg (kernelKPrime lam)
  dsimp [physicalRootDensityErrorBound]
  positivity

/-- The actual counting density at each perturbed root differs from its
own reference scaled density by one uniform additive constant. -/
theorem weighted_configuration_root_density_error_all {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (Q : ℝ) (L : ℕ) (Y X : Fin n → ℝ)
    (R : ReferenceQuantileData lam h0 hpi Q L Y) (M : ℝ) (hM : 0 < M)
    (hlower : ∀ v ∈ Icc (-Q) Q,M ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q v)
    (radius : ℝ) (hrad : 0 ≤ radius)
    (hclose : ∀ j,|X j-Y j| ≤ radius/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))) (j : Fin n) :
    |countingSlope lam (fun _ => 0) L X (X j)-
      (L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j)| ≤ physicalRootDensityErrorBound lam radius M := by
  let f := finiteIntervalDensity lam h0 hpi Q
  let w := (L : ℝ)*f (Y j)
  let A := physicalDensityLogConstant lam*Real.exp (physicalDensityLogConstant lam*(radius/M))
  have hw : 0 < w := hM.trans_le (hlower (Y j) ⟨(R.location j).1.le,(R.location j).2.le⟩)
  have hA : 0 ≤ A := mul_nonneg (physicalDensityLogConstant_pos lam h0).le (Real.exp_pos _).le
  have hd : |X j-Y j| ≤ radius/M := (hclose j).trans (div_le_div₀ hrad le_rfl hM
    (hlower (Y j) ⟨(R.location j).1.le,(R.location j).2.le⟩))
  have hp := finiteIntervalDensity_relative_translation_error_all lam h0 hpi Q (Y j) (X j) (radius/M) hd
  have hprof : |(L : ℝ)*f (X j)-(L : ℝ)*f (Y j)| ≤ A*radius := by
    rw [← mul_sub,abs_mul,abs_of_nonneg (Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
    have hp' := hp.trans (mul_le_mul_of_nonneg_left (hclose j)
      (mul_nonneg hA (finiteIntervalDensity_pos_all lam h0 hpi Q (Y j)).le))
    apply (mul_le_mul_of_nonneg_left hp' (Nat.cast_nonneg L : (0 : ℝ) ≤ L)).trans_eq
    change (L : ℝ)*(A*f (Y j)*(radius/w))=A*radius
    have he : (L : ℝ)*(A*f (Y j))=A*w := by dsimp [w]; ring
    rw [← mul_assoc,he,mul_assoc,mul_div_cancel₀ radius hw.ne']
  have hx := weighted_configuration_density_error_all lam h0 hpi Q L Y X R M hM hlower radius hrad hclose (X j)
  have ht := abs_add_le
    (countingSlope lam (fun _ => 0) L X (X j)-(L : ℝ)*f (X j))
    ((L : ℝ)*f (X j)-(L : ℝ)*f (Y j))
  rw [sub_add_sub_cancel] at ht
  exact (ht.trans (add_le_add hx hprof)).trans_eq (by rfl)

/-- An explicit density error bound independent of every larger scaled
density threshold,for a fixed weighted radius. -/
theorem physicalRootDensityErrorBound_le_at_one (lam radius M : ℝ) (h0 : 0 < lam)
    (hrad : 0 ≤ radius) (hM : 1 ≤ M) :
    physicalRootDensityErrorBound lam radius M ≤ physicalRootDensityErrorBound lam radius 1 := by
  have hMp : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hk := kernelLogConstant_nonneg lam
  have hf := (physicalDensityLogConstant_pos lam h0).le
  have hb := physicalReferenceKernelRowErrorConstant_nonneg lam h0
  have hm := kernelL1Mass_nonneg (kernelK lam)
  have hd : radius/M ≤ radius := by
    exact (div_le_iff₀ hMp).mpr (by nlinarith only [hM,hrad])
  have hB : physicalReferenceKernelRowErrorConstant lam/M ≤ physicalReferenceKernelRowErrorConstant lam :=
    (div_le_iff₀ hMp).mpr (by nlinarith only [hM,hb])
  have hek : Real.exp (kernelLogConstant lam*(radius/M)) ≤ Real.exp (kernelLogConstant lam*radius) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hd hk)
  have hef : Real.exp (physicalDensityLogConstant lam*(radius/M)) ≤ Real.exp (physicalDensityLogConstant lam*radius) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hd hf)
  dsimp [physicalRootDensityErrorBound]
  simp only [div_one]
  apply add_le_add
  · apply add_le_add le_rfl
    exact mul_le_mul
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hek hk) hrad)
      (add_le_add le_rfl hB) (by positivity) (by positivity)
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hef hf) hrad


/-- Positive actual atom weights and a quadratic reciprocal-weight error
hold uniformly near every actual reference configuration once its
minimum scaled density exceeds one fixed threshold. -/
theorem exists_weighted_root_atom_comparison_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (radius : ℝ) (hrad : 0 ≤ radius) :
    ∃ M C : ℝ,0 < M ∧ 0 < C ∧ ∀ (n : ℕ) (Q : ℝ) (L : ℕ) (Y X : Fin n → ℝ),
      ∀ R : ReferenceQuantileData lam h0 hpi Q L Y,
      (∀ u ∈ Icc (-Q) Q,M ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q u) →
      (∀ j,|X j-Y j| ≤ radius/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))) →
      ∀ j : Fin n,0 < countingSlope lam (fun _ => 0) L X (X j) ∧
        (countingSlope lam (fun _ => 0) L X (X j))⁻¹ ≤
          2/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j)) ∧
        |(countingSlope lam (fun _ => 0) L X (X j))⁻¹-
          ((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))⁻¹| ≤
          C/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))^2 := by
  let E := physicalRootDensityErrorBound lam radius 1
  let M := 2*E+1
  have hE : 0 ≤ E := physicalRootDensityErrorBound_nonneg lam radius 1 h0 hrad (by norm_num)
  have hM : 0 < M := by dsimp [M]; linarith
  have hM1 : 1 ≤ M := by dsimp [M]; linarith
  refine ⟨M,M,hM,hM,?_⟩
  intro n Q L Y X R hlower hclose j
  let w := (L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j)
  let rho := countingSlope lam (fun _ => 0) L X (X j)
  have hwM : M ≤ w := hlower (Y j) ⟨(R.location j).1.le,(R.location j).2.le⟩
  have hw : 0 < w := hM.trans_le hwM
  have he : |rho-w| ≤ E :=
    (weighted_configuration_root_density_error_all lam h0 hpi Q L Y X R M hM hlower radius hrad hclose j).trans
      (physicalRootDensityErrorBound_le_at_one lam radius M h0 hrad hM1)
  have hhalf : w/2 ≤ rho := by
    have h := (abs_le.mp he).1
    dsimp [M] at hwM
    linarith
  have hrho : 0 < rho := (by positivity : (0 : ℝ) < w/2).trans_le hhalf
  refine ⟨hrho,?_,?_⟩
  · change rho⁻¹ ≤ 2/w
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ hrho hw).mpr
    linarith
  · change |rho⁻¹-w⁻¹| ≤ M/w^2
    have hid : rho⁻¹-w⁻¹=(w-rho)/(rho*w) := by field_simp
    rw [hid,abs_div,abs_mul,abs_of_pos hrho,abs_of_pos hw,abs_sub_comm w rho]
    have hden : w^2/2 ≤ rho*w := by nlinarith only [mul_le_mul_of_nonneg_right hhalf hw.le]
    calc
      _ ≤ E/(w^2/2) := div_le_div₀ hE he (by positivity) hden
      _ = (2*E)/w^2 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (by dsimp [M]; linarith) (sq_nonneg w)

end
end SixVertex
