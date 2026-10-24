import SixVertex.PhysicalIntervalQuadratureMass

namespace SixVertex
noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal

/-- A compact test has bounded quadrature error under any measure with
a fixed mass bound on its supporting interval. No density or smoothness
assumption is needed for this finite-scale estimate. -/
theorem compact_test_error_of_interval_mass (mu : Measure ℝ) (a ell B : ℝ)
    (hell : 0 ≤ ell) (hB : 0 ≤ B) (hmass : mu (Icc a (a+ell)) ≤ ENNReal.ofReal B)
    (phi : BoundedRealFunction) (hs : ∀ x,x ∉ Icc a (a+ell) → phi x=0) :
    |(∫ x,phi x ∂mu)-(∫ x : ℝ,phi x)| ≤ (B+ell)*‖phi‖ := by
  have hfin : mu (Icc a (a+ell)) < ∞ := hmass.trans_lt ENNReal.ofReal_lt_top
  have hreal : mu.real (Icc a (a+ell)) ≤ B := by
    change (mu (Icc a (a+ell))).toReal ≤ B
    simpa only [ENNReal.toReal_ofReal hB] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass
  have hmu := norm_setIntegral_le_of_norm_le_const (μ := mu) (s := Icc a (a+ell))
    (f := fun x => phi x) (C := ‖phi‖) hfin (fun x _ => phi.norm_coe_le_norm x)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hs] at hmu
  have hmu' : ‖∫ x,phi x ∂mu‖ ≤ ‖phi‖*B := hmu.trans (mul_le_mul_of_nonneg_left hreal (norm_nonneg phi))
  have hvol := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc a (a+ell))
    (f := fun x => phi x) (C := ‖phi‖) isCompact_Icc.measure_lt_top (fun x _ => phi.norm_coe_le_norm x)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hs,
    Real.volume_real_Icc_of_le (by linarith : a ≤ a+ell)] at hvol
  have hvol' : ‖∫ x : ℝ,phi x‖ ≤ ‖phi‖*ell := hvol.trans_eq (by ring)
  rw [← Real.norm_eq_abs]
  exact ((norm_sub_le _ _).trans (add_le_add hmu' hvol')).trans_eq (by ring)

/-- The actual-density bounded-Lipschitz quadrature estimate for every
positive local density scale. The finite low-density range is controlled
by actual interval mass,not an additional asymptotic hypothesis. -/
theorem exists_uniform_actual_density_quadrature_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (radius ell eps : ℝ) (hrad : 0 ≤ radius)
    (hell : 0 ≤ ell) (heps : 0 < eps) :
    ∃ M D : ℝ,0 < M ∧ 0 < D ∧ ∀ (n : ℕ) (Q : ℝ) (L : ℕ) (Y X : Fin n → ℝ),
      ∀ R : ReferenceQuantileData lam h0 hpi Q L Y,
      (∀ u ∈ Icc (-Q) Q,M ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q u) →
      (∀ j,|X j-Y j| ≤ radius/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))) →
      ∀ (a N : ℝ),-Q ≤ a → a+ell ≤ Q → 0 < N →
      (∀ u ∈ Icc (a-eps) (a+ell+eps),N ≤ countingSlope lam (fun _ => 0) L X u) →
      ∀ (phi : BoundedRealFunction) (K : ℝ≥0),LipschitzWith K (fun x => phi x) →
      (∀ x,x ∉ Icc a (a+ell) → phi x=0) →
      |(∫ x,phi x ∂rootQuadratureMeasure lam (fun _ => 0) L X)-(∫ x : ℝ,phi x)| ≤
        (D/N)*((K : ℝ)+‖phi‖) := by
  obtain ⟨mq,Dq,H,hmq,hDq,hH,hquad⟩ := exists_actual_density_bounded_lipschitz_quadrature_all lam h0 hpi radius ell eps hrad hell heps
  obtain ⟨mm,B,hmm,hB,hmass⟩ := exists_weighted_configuration_interval_quadrature_mass_all lam h0 hpi radius ell hrad hell
  let M := max mq mm
  let D := max Dq (2*H*(B+ell))
  have hM : 0 < M := hmq.trans_le (le_max_left _ _)
  have hD : 0 < D := hDq.trans_le (le_max_left _ _)
  refine ⟨M,D,hM,hD,?_⟩
  intro n Q L Y X R hlower hclose a N ha hz hN hlocal phi K hLip hs
  have hS : 0 ≤ (K : ℝ)+‖phi‖ := add_nonneg K.coe_nonneg (norm_nonneg phi)
  by_cases hbig : 2*H ≤ N
  · have h := hquad n Q L Y X R (fun u hu => (le_max_left _ _).trans (hlower u hu))
      hclose a N ha hz hbig hlocal phi K hLip hs
    exact h.trans (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (le_max_left _ _) hN.le) hS)
  · have hsmall : N ≤ 2*H := (lt_of_not_ge hbig).le
    have hm := (hmass n Q L Y X R (fun u hu => (le_max_right _ _).trans (hlower u hu)) hclose).2 a
    have h := compact_test_error_of_interval_mass (rootQuadratureMeasure lam (fun _ => 0) L X)
      a ell B hell hB.le hm phi hs
    have hcoef : B+ell ≤ (2*H*(B+ell))/N := by
      apply (le_div_iff₀ hN).mpr
      nlinarith only [mul_le_mul_of_nonneg_right hsmall (show 0 ≤ B+ell by linarith)]
    calc
      _ ≤ (B+ell)*‖phi‖ := h
      _ ≤ (B+ell)*((K : ℝ)+‖phi‖) := mul_le_mul_of_nonneg_left (by linarith [K.coe_nonneg]) (by linarith)
      _ ≤ ((2*H*(B+ell))/N)*((K : ℝ)+‖phi‖) := mul_le_mul_of_nonneg_right hcoef hS
      _ ≤ _ := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (le_max_right _ _) hN.le) hS

end
end SixVertex
