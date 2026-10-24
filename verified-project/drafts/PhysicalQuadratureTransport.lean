import SixVertex.PhysicalQuadratureMass

namespace SixVertex
noncomputable section
open Set MeasureTheory
open scoped NNReal

/-- Transport from the actual reference atoms to the actual
inverse-counting-density measure,with a local rather than global density
scale. The estimate is uniform over positions of a fixed-length window. -/
theorem exists_weighted_quadrature_transport_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (radius ell eps : ℝ) (hrad : 0 ≤ radius) (hell : 0 ≤ ell) (heps : 0 < eps) :
    ∃ M T : ℝ,0 < M ∧ 0 < T ∧ ∀ (n : ℕ) (Q : ℝ) (L : ℕ) (Y X : Fin n → ℝ),
      ∀ R : ReferenceQuantileData lam h0 hpi Q L Y,
      (∀ u ∈ Icc (-Q) Q,M ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q u) →
      (∀ j,|X j-Y j| ≤ radius/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))) →
      ∀ (a N : ℝ),0 < N →
      (∀ u ∈ Icc (a-eps) (a+ell+eps),N ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q u) →
      ∀ (phi : BoundedRealFunction) (K : ℝ≥0),LipschitzWith K (fun x => phi x) →
      (∀ x,x ∉ Icc a (a+ell) → phi x=0) →
      |(∫ x,phi x ∂rootQuadratureMeasure lam (fun _ => 0) L X)-
        (∑ j : Fin n,phi (Y j)/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j)))| ≤
        (T/N)*((K : ℝ)+‖phi‖) := by
  obtain ⟨m,C,hm,hC,hcomp⟩ := exists_weighted_root_atom_comparison_all lam h0 hpi radius hrad
  let M := max m (radius/eps)
  have hM : 0 < M := hm.trans_le (le_max_left _ _)
  let delta := radius/M
  let len := ell+2*delta
  let E := Real.exp (physicalDensityLogConstant lam*len)
  let B := E^2*len+E/M
  let T := B*(2*radius+C)
  have hd : 0 ≤ delta := div_nonneg hrad hM.le
  have hdelta_eps : delta ≤ eps := by
    change radius/M ≤ eps
    apply (div_le_iff₀ hM).mpr
    have hr : radius ≤ M*eps := (div_le_iff₀ heps).mp (le_max_right m (radius/eps))
    nlinarith only [hr]
  have hlen : 0 ≤ len := by dsimp [len]; positivity
  have hE : 0 < E := Real.exp_pos _
  have hB : 0 < B := by dsimp [B]; positivity
  have hT : 0 < T := mul_pos hB (by linarith)
  refine ⟨M,T,hM,hT,?_⟩
  intro n Q L Y X R hlower hclose a N hN hlocal phi K hLip hs
  let w : Fin n → ℝ := fun j => (L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j)
  let rho : Fin n → ℝ := fun j => countingSlope lam (fun _ => 0) L X (X j)
  let A := 2*radius*(K : ℝ)+C*‖phi‖
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hw (j : Fin n) : 0 < w j := hM.trans_le (hlower (Y j) ⟨(R.location j).1.le,(R.location j).2.le⟩)
  have hpoint := hcomp n Q L Y X R (fun u hu => (le_max_left _ _).trans (hlower u hu)) hclose
  have hphysical (j : Fin n) : |X j-Y j| ≤ delta := (hclose j).trans
    (div_le_div₀ hrad le_rfl hM (hlower (Y j) ⟨(R.location j).1.le,(R.location j).2.le⟩))
  have hterm (j : Fin n) : |phi (X j)/rho j-phi (Y j)/w j| ≤ A/(w j)^2 := by
    have hdiff : |phi (X j)-phi (Y j)| ≤ (K : ℝ)*radius/w j := by
      have hp : |phi (X j)-phi (Y j)| ≤ (K : ℝ)*|X j-Y j| := by simpa only [Real.dist_eq] using hLip.dist_le_mul (X j) (Y j)
      exact (hp.trans (mul_le_mul_of_nonneg_left (hclose j) K.coe_nonneg)).trans_eq (by ring)
    have hval : |phi (Y j)| ≤ ‖phi‖ := by simpa only [Real.norm_eq_abs] using phi.norm_coe_le_norm (Y j)
    have hid : phi (X j)/rho j-phi (Y j)/w j=
        (phi (X j)-phi (Y j))*(rho j)⁻¹+phi (Y j)*((rho j)⁻¹-(w j)⁻¹) := by
      simp only [div_eq_mul_inv]
      ring
    rw [hid]
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_of_nonneg (inv_nonneg.mpr (hpoint j).1.le),abs_mul]
    have h₁ := mul_le_mul hdiff (hpoint j).2.1 (inv_nonneg.mpr (hpoint j).1.le)
      (div_nonneg (mul_nonneg K.coe_nonneg hrad) (hw j).le)
    have h₂ := mul_le_mul hval (hpoint j).2.2 (abs_nonneg _) (norm_nonneg phi)
    change |phi (X j)-phi (Y j)| *(rho j)⁻¹ ≤ ((K : ℝ)*radius/w j)*(2/w j) at h₁
    change |phi (Y j)| *|(rho j)⁻¹-(w j)⁻¹| ≤ ‖phi‖*(C/(w j)^2) at h₂
    exact (add_le_add h₁ h₂).trans_eq (by dsimp [A]; ring)
  have hzero (j : Fin n) (hj : Y j ∉ Icc (a-delta) (a+ell+delta)) :
      phi (X j)/rho j-phi (Y j)/w j=0 := by
    have hx : X j ∉ Icc a (a+ell) := by
      intro hx
      have hdj := abs_le.mp (hphysical j)
      apply hj
      exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
    have hy : Y j ∉ Icc a (a+ell) := by
      intro hy
      exact hj ⟨by linarith [hy.1],by linarith [hy.2]⟩
    rw [hs _ hx,hs _ hy,zero_div,zero_div,sub_self]
  have hpointlocal (j : Fin n) : |phi (X j)/rho j-phi (Y j)/w j| ≤
      if Y j ∈ Icc (a-delta) (a+ell+delta) then (A/N)*(w j)⁻¹ else 0 := by
    by_cases hj : Y j ∈ Icc (a-delta) (a+ell+delta)
    · rw [if_pos hj]
      have hNj : N ≤ w j := hlocal (Y j) ⟨by linarith [hj.1],by linarith [hj.2]⟩
      calc
        _ ≤ A/(w j)^2 := hterm j
        _ ≤ A/(N*w j) := div_le_div₀ hA le_rfl (mul_pos hN (hw j)) (by nlinarith only [mul_le_mul_of_nonneg_right hNj (hw j).le])
        _ = _ := by simp only [div_eq_mul_inv,mul_inv_rev]; ring
    · rw [if_neg hj,hzero j hj,abs_zero]
  have href := reference_weighted_interval_mass_bound_all lam h0 hpi Q L Y R M hM hlower
    (a-delta) (a+ell+delta) (by linarith)
  have hlen_eq : (a+ell+delta)-(a-delta)=len := by dsimp [len]; ring
  rw [hlen_eq] at href
  have hcoeff : A ≤ (2*radius+C)*((K : ℝ)+‖phi‖) := by
    have h₁ := mul_nonneg (show 0 ≤ 2*radius by positivity) (norm_nonneg phi)
    have h₂ := mul_nonneg hC.le K.coe_nonneg
    dsimp [A]
    nlinarith
  rw [integral_rootQuadratureMeasure_of_density_nonneg lam (fun _ => 0) L X (fun j => (hpoint j).1.le)]
  change |(∑ j : Fin n,phi (X j)/rho j)-(∑ j : Fin n,phi (Y j)/w j)| ≤ _
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j : Fin n,|phi (X j)/rho j-phi (Y j)/w j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin n,if Y j ∈ Icc (a-delta) (a+ell+delta) then (A/N)*(w j)⁻¹ else 0 :=
      Finset.sum_le_sum (fun j _ => hpointlocal j)
    _ = (A/N)*(∑ j ∈ rootsInInterval Y (a-delta) (a+ell+delta),(w j)⁻¹) := by
      simp only [rootsInInterval,Finset.mul_sum,Finset.sum_filter,mem_Icc,mul_ite,mul_zero]
    _ ≤ (A/N)*B := mul_le_mul_of_nonneg_left href (div_nonneg hA hN.le)
    _ ≤ _ := (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hcoeff hN.le) hB.le).trans_eq
      (by dsimp [T]; ring)

end
end SixVertex
