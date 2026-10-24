import SixVertex.PhysicalReferenceIntervalMass
import SixVertex.LipschitzCountingError
import SixVertex.NormalizedLipschitz

namespace SixVertex
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal

/-- The actual finite-window cumulative density is bounded on the whole
line by the ordinary L1 mass of its actual derivative. -/
theorem finiteIntervalCumulative_abs_le_L1 (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Q u : ℝ) : |finiteIntervalCumulative lam h0 hpi Q u| ≤
      kernelL1Mass (fun v => finiteIntervalDensity lam h0 hpi Q v) := by
  have hi := (finiteIntervalDensity_integrable lam h0 hpi Q).norm
  have ht : (∫ v in Set.uIoc (-Q) u,‖finiteIntervalDensity lam h0 hpi Q v‖) ≤
      ∫ v : ℝ,‖finiteIntervalDensity lam h0 hpi Q v‖ :=
    setIntegral_le_integral hi (Eventually.of_forall (fun _ => norm_nonneg _))
  have he := intervalIntegral.norm_integral_le_integral_norm_uIoc
    (f := fun v => finiteIntervalDensity lam h0 hpi Q v) (a := -Q) (b := u) (μ := volume)
  unfold finiteIntervalCumulative kernelL1Mass
  simpa only [Real.norm_eq_abs] using he.trans ht

/-- Bounded continuous representative of the actual cumulative integral. -/
def finiteIntervalCumulativeFunction (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Q : ℝ) : BoundedRealFunction :=
  BoundedContinuousFunction.ofNormedAddCommGroup (finiteIntervalCumulative lam h0 hpi Q)
    (finiteIntervalCumulative_continuous lam h0 hpi Q)
    (kernelL1Mass (fun v => finiteIntervalDensity lam h0 hpi Q v))
    (fun u => by simpa only [Real.norm_eq_abs] using finiteIntervalCumulative_abs_le_L1 lam h0 hpi Q u)

/-- Reference quantile quadrature for genuine compact Lipschitz tests,
proved by absolute-continuity integration by parts and the actual
counting sawtooth. -/
theorem reference_lipschitz_discrete_smooth_error_all {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ)
    (R : ReferenceQuantileData lam h0 hpi Q L Y)
    (f : BoundedRealFunction) (K : ℝ≥0) (hLip : LipschitzWith K (fun x => f x))
    (a z : ℝ) (haz : a ≤ z) (ha : -Q ≤ a) (hz : z ≤ Q)
    (hs : ∀ x,x ∉ Icc a z → f x=0) :
    |(∑ j : Fin n,f (Y j))-(∫ x : ℝ,f x*((L : ℝ)*finiteIntervalDensity lam h0 hpi Q x))| ≤
      (z-a)*(K : ℝ)/2 := by
  let P : BoundedRealFunction := (L : ℝ) • finiteIntervalCumulativeFunction lam h0 hpi Q
  let p : BoundedRealFunction := (L : ℝ) • finiteIntervalDensity lam h0 hpi Q
  let F : ℝ → ℝ := fun x => (rootCountLe Y x : ℝ)-P x
  have hP (x : ℝ) : P x=(L : ℝ)*finiteIntervalCumulative lam h0 hpi Q x := rfl
  have hp (x : ℝ) : p x=(L : ℝ)*finiteIntervalDensity lam h0 hpi Q x := rfl
  have hpi' : Integrable (fun x => p x) := (finiteIntervalDensity_integrable lam h0 hpi Q).const_mul (L : ℝ)
  have hdP (x : ℝ) : HasDerivAt (fun v => P v) (p x) x :=
    (finiteIntervalCumulative_hasDerivAt lam h0 hpi Q x).const_mul (L : ℝ)
  have he := integral_lipschitz_compact_primitive f P p K hLip a z haz hs hpi' hdP
  have hdint := lipschitz_compact_deriv_integrable (fun x => f x) K hLip a z haz hs
  have hc := hdint.mul_bdd (rootCountLe_measurable Y).aestronglyMeasurable
    (Eventually.of_forall (rootCountLe_norm_bound Y))
  have hPb := hdint.mul_bdd P.continuous.aestronglyMeasurable (Eventually.of_forall P.norm_coe_le_norm)
  have hid : (∫ x : ℝ,deriv (fun v => f v) x*F x)=
      -((∑ j : Fin n,f (Y j))-(∫ x : ℝ,f x*p x)) := by
    simp only [F,mul_sub]
    rw [integral_sub hc hPb,integral_deriv_compact_rootCount Y (fun x => f x) K hLip a z haz hs]
    linarith [he]
  have hsupport : ∀ x,x ∉ Icc a z → deriv (fun v => f v) x*F x=0 := by
    intro x hx
    rw [deriv_zero_outside_Icc (fun v => f v) a z hs x hx,zero_mul]
  have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc a z)
    (f := fun x : ℝ => deriv (fun v => f v) x*F x) (C := (K : ℝ)/2)
    (isCompact_Icc.measure_lt_top) (by
      intro x hx
      rw [norm_mul,Real.norm_eq_abs (F x)]
      have hF : |F x| ≤ 1/2 := by
        exact referenceQuantileDiscrepancy_bound_all lam h0 hpi Q R.interval_nonneg L R.chain_pos Y
          R.ordered R.mass R.level x ⟨ha.trans hx.1,hx.2.trans hz⟩
      calc
        _ ≤ ‖deriv (fun v => f v) x‖*(1/2) := mul_le_mul_of_nonneg_left hF (norm_nonneg _)
        _ ≤ (K : ℝ)*(1/2) := mul_le_mul_of_nonneg_right (norm_deriv_le_of_lipschitz hLip) (by norm_num)
        _ = (K : ℝ)/2 := by ring)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hsupport,hid,norm_neg,Real.norm_eq_abs,
    Real.volume_real_Icc_of_le haz] at hb
  change |(∑ j : Fin n,f (Y j))-(∫ x : ℝ,f x*p x)| ≤ _
  exact hb.trans_eq (by ring)

/-- Genuine bounded-Lipschitz quadrature with the actual inverse
reference-density weights and a local density lower bound. -/
theorem reference_weighted_bounded_lipschitz_error_all {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ)
    (R : ReferenceQuantileData lam h0 hpi Q L Y)
    (phi : BoundedRealFunction) (K : ℝ≥0) (hLip : LipschitzWith K (fun x => phi x))
    (a z N : ℝ) (haz : a ≤ z) (ha : -Q ≤ a) (hz : z ≤ Q) (hN : 0 < N)
    (hs : ∀ x,x ∉ Icc a z → phi x=0)
    (hlower : ∀ x ∈ Icc a z,N ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q x) :
    |(∑ j : Fin n,phi (Y j)/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j)))-
      (∫ x : ℝ,phi x)| ≤ (z-a)*((K : ℝ)+physicalDensityLogConstant lam*‖phi‖)/(2*N) := by
  let p : ℝ → ℝ := fun x => (L : ℝ)*finiteIntervalDensity lam h0 hpi Q x
  let p' : ℝ → ℝ := fun x => (L : ℝ)*finiteIntervalDensityPrimeFunction lam h0 hpi Q x
  have hp (x : ℝ) : 0 < p x := mul_pos (Nat.cast_pos.mpr R.chain_pos) (finiteIntervalDensity_pos_all lam h0 hpi Q x)
  have hrelative (x : ℝ) : |p' x| ≤ physicalDensityLogConstant lam*p x := by
    rw [show p' x=(L : ℝ)*finiteIntervalDensityPrimeFunction lam h0 hpi Q x from rfl,
      abs_mul,abs_of_nonneg (Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
    exact (mul_le_mul_of_nonneg_left (finiteIntervalDensityPrime_relative_bound_all lam h0 hpi Q x)
      (Nat.cast_nonneg L : (0 : ℝ) ≤ L)).trans_eq (by dsimp [p]; ring)
  obtain ⟨f,hf,hfs,hfLip⟩ := exists_normalized_lipschitz_test phi K hLip p p'
    (continuous_const.mul (finiteIntervalDensity lam h0 hpi Q).continuous) hp
    (fun x => (finiteIntervalDensity_hasDerivAt lam h0 hpi Q x).const_mul (L : ℝ))
    a z N (physicalDensityLogConstant lam) haz hN (physicalDensityLogConstant_pos lam h0).le hs hlower hrelative
  have he := reference_lipschitz_discrete_smooth_error_all lam h0 hpi Q L Y R f _ hfLip a z haz ha hz hfs
  have hcancel (x : ℝ) : f x*p x=phi x := by rw [hf x,div_mul_cancel₀ _ (hp x).ne']
  change |(∑ j : Fin n,f (Y j))-(∫ x : ℝ,f x*p x)| ≤ _ at he
  simp_rw [hcancel,hf] at he
  change |(∑ j : Fin n,phi (Y j)/p (Y j))-(∫ x : ℝ,phi x)| ≤
    (z-a)*(((K : ℝ)+physicalDensityLogConstant lam*‖phi‖)/N)/2 at he
  exact he.trans_eq (by ring)

end
end SixVertex
