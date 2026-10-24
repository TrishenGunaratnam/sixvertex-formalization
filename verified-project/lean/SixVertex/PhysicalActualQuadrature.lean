import SixVertex.PhysicalQuadratureTransport
import SixVertex.PhysicalReferenceLipschitz

namespace SixVertex
noncomputable section
open Set MeasureTheory Filter Topology
open scoped NNReal

/-- Uniform bounded-Lipschitz quadrature for the actual inverse-density
root measure,using a local reference-density lower bound on an arbitrarily
small fixed enlargement of the test window. -/
theorem exists_weighted_actual_bounded_lipschitz_quadrature_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (radius ell eps : ℝ) (hrad : 0 ≤ radius)
    (hell : 0 ≤ ell) (heps : 0 < eps) :
    ∃ M D : ℝ,0 < M ∧ 0 < D ∧ ∀ (n : ℕ) (Q : ℝ) (L : ℕ) (Y X : Fin n → ℝ),
      ∀ R : ReferenceQuantileData lam h0 hpi Q L Y,
      (∀ u ∈ Icc (-Q) Q,M ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q u) →
      (∀ j,|X j-Y j| ≤ radius/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))) →
      ∀ (a N : ℝ),-Q ≤ a → a+ell ≤ Q → 0 < N →
      (∀ u ∈ Icc (a-eps) (a+ell+eps),N ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q u) →
      ∀ (phi : BoundedRealFunction) (K : ℝ≥0),LipschitzWith K (fun x => phi x) →
      (∀ x,x ∉ Icc a (a+ell) → phi x=0) →
      |(∫ x,phi x ∂rootQuadratureMeasure lam (fun _ => 0) L X)-(∫ x : ℝ,phi x)| ≤
        (D/N)*((K : ℝ)+‖phi‖) := by
  obtain ⟨M,T,hM,hT,htransport⟩ := exists_weighted_quadrature_transport_all lam h0 hpi radius ell eps hrad hell heps
  let D := T+ell*(1+physicalDensityLogConstant lam)/2
  have hf : 0 ≤ physicalDensityLogConstant lam := (physicalDensityLogConstant_pos lam h0).le
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨M,D,hM,hD,?_⟩
  intro n Q L Y X R hlower hclose a N ha hz hN hlocal phi K hLip hs
  have ht := htransport n Q L Y X R hlower hclose a N hN hlocal phi K hLip hs
  have hr := reference_weighted_bounded_lipschitz_error_all lam h0 hpi Q L Y R phi K hLip a (a+ell) N
    (by linarith) ha hz hN hs
    (fun u hu => hlocal u ⟨by linarith [hu.1],by linarith [hu.2]⟩)
  have hlen : a+ell-a=ell := by ring
  rw [hlen] at hr
  have hc : (K : ℝ)+physicalDensityLogConstant lam*‖phi‖ ≤
      (1+physicalDensityLogConstant lam)*((K : ℝ)+‖phi‖) := by
    have h := mul_nonneg hf K.coe_nonneg
    nlinarith [norm_nonneg phi]
  have hcoeff : (T/N)*((K : ℝ)+‖phi‖)+ell*((K : ℝ)+physicalDensityLogConstant lam*‖phi‖)/(2*N) ≤
      (D/N)*((K : ℝ)+‖phi‖) := by
    calc
      _ = (T*((K : ℝ)+‖phi‖)+(ell/2)*((K : ℝ)+physicalDensityLogConstant lam*‖phi‖))/N := by ring
      _ ≤ (T*((K : ℝ)+‖phi‖)+(ell/2)*((1+physicalDensityLogConstant lam)*((K : ℝ)+‖phi‖)))/N :=
        div_le_div_of_nonneg_right (add_le_add le_rfl (mul_le_mul_of_nonneg_left hc (by positivity))) hN.le
      _ = _ := by dsimp [D]; ring
  exact ((abs_sub_le
    (∫ x,phi x ∂rootQuadratureMeasure lam (fun _ => 0) L X)
    (∑ j : Fin n,phi (Y j)/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j)))
    (∫ x : ℝ,phi x)).trans (add_le_add ht hr)).trans hcoeff

/-- The same actual-measure quadrature estimate uses the actual local
counting density,as in the paper. Only a fixed finite lower cutoff on
the local density scale is required. -/
theorem exists_actual_density_bounded_lipschitz_quadrature_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (radius ell eps : ℝ) (hrad : 0 ≤ radius)
    (hell : 0 ≤ ell) (heps : 0 < eps) :
    ∃ M D H : ℝ,0 < M ∧ 0 < D ∧ 0 < H ∧
    ∀ (n : ℕ) (Q : ℝ) (L : ℕ) (Y X : Fin n → ℝ),
      ∀ R : ReferenceQuantileData lam h0 hpi Q L Y,
      (∀ u ∈ Icc (-Q) Q,M ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q u) →
      (∀ j,|X j-Y j| ≤ radius/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))) →
      ∀ (a N : ℝ),-Q ≤ a → a+ell ≤ Q → 2*H ≤ N →
      (∀ u ∈ Icc (a-eps) (a+ell+eps),N ≤ countingSlope lam (fun _ => 0) L X u) →
      ∀ (phi : BoundedRealFunction) (K : ℝ≥0),LipschitzWith K (fun x => phi x) →
      (∀ x,x ∉ Icc a (a+ell) → phi x=0) →
      |(∫ x,phi x ∂rootQuadratureMeasure lam (fun _ => 0) L X)-(∫ x : ℝ,phi x)| ≤
        (D/N)*((K : ℝ)+‖phi‖) := by
  obtain ⟨M,D,hM,hD,hquad⟩ := exists_weighted_actual_bounded_lipschitz_quadrature_all lam h0 hpi radius ell eps hrad hell heps
  let E := kernelL1Mass (kernelKPrime lam)/2+
    (kernelLogConstant lam*Real.exp (kernelLogConstant lam*(radius/M))*radius)*
      (kernelL1Mass (kernelK lam)+physicalReferenceKernelRowErrorConstant lam/M)
  let H := |E|+1
  have hH : 0 < H := by dsimp [H]; positivity
  refine ⟨M,2*D,H,hM,by positivity,hH,?_⟩
  intro n Q L Y X R hlower hclose a N ha hz hN hlocal phi K hLip hs
  have hNp : 0 < N := (by positivity : (0 : ℝ) < 2*H).trans_le hN
  have herr (u : ℝ) : |countingSlope lam (fun _ => 0) L X u-
      (L : ℝ)*finiteIntervalDensity lam h0 hpi Q u| ≤ H := by
    exact (weighted_configuration_density_error_all lam h0 hpi Q L Y X R M hM hlower radius hrad hclose u).trans
      (by change E ≤ |E|+1; linarith [le_abs_self E])
  have hlocal' (u : ℝ) (hu : u ∈ Icc (a-eps) (a+ell+eps)) :
      N/2 ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q u := by
    have he := (abs_le.mp (herr u)).2
    have h := hlocal u hu
    linarith
  have he := hquad n Q L Y X R hlower hclose a (N/2) ha hz (by positivity) hlocal' phi K hLip hs
  exact he.trans_eq (by ring)


/-- Local convergence to Lebesgue measure for the actual weighted root
measures in every eventually dense enlarged window,throughout the
physical range. The finite root number may vary along the filter. -/
theorem exists_dense_actual_quadrature_limit_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (radius ell eps : ℝ) (hrad : 0 ≤ radius)
    (hell : 0 ≤ ell) (heps : 0 < eps) :
    ∃ M : ℝ,0 < M ∧ ∀ {ι : Type} (l : Filter ι)
      (n L : ι → ℕ) (Q : ι → ℝ) (Y X : (i : ι) → Fin (n i) → ℝ),
      (∀ i,ReferenceQuantileData lam h0 hpi (Q i) (L i) (Y i)) →
      (∀ᶠ i in l,∀ u ∈ Icc (-(Q i)) (Q i),M ≤ (L i : ℝ)*finiteIntervalDensity lam h0 hpi (Q i) u) →
      (∀ᶠ i in l,∀ j,|X i j-Y i j| ≤ radius/((L i : ℝ)*finiteIntervalDensity lam h0 hpi (Q i) (Y i j))) →
      ∀ (a : ℝ) (N : ι → ℝ),Tendsto N l atTop →
      (∀ᶠ i in l,-(Q i) ≤ a ∧ a+ell ≤ Q i) →
      (∀ᶠ i in l,∀ u ∈ Icc (a-eps) (a+ell+eps),N i ≤ countingSlope lam (fun _ => 0) (L i) (X i) u) →
      ∀ (phi : BoundedRealFunction) (K : ℝ≥0),LipschitzWith K (fun x => phi x) →
      (∀ x,x ∉ Icc a (a+ell) → phi x=0) →
      Tendsto (fun i => ∫ x,phi x ∂rootQuadratureMeasure lam (fun _ => 0) (L i) (X i))
        l (nhds (∫ x : ℝ,phi x)) := by
  obtain ⟨M,D,H,hM,hD,hH,hquad⟩ := exists_actual_density_bounded_lipschitz_quadrature_all lam h0 hpi radius ell eps hrad hell heps
  refine ⟨M,hM,?_⟩
  intro ι l n L Q Y X R hglobal hclose a N hN hwindow hlocal phi K hLip hs
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (g := fun i => (D/N i)*((K : ℝ)+‖phi‖))
    (Eventually.of_forall (fun i => norm_nonneg _))
  · filter_upwards [hglobal,hclose,hwindow,hlocal,hN.eventually (eventually_ge_atTop (2*H))] with i hgi hci hwi hli hNi
    rw [Real.norm_eq_abs]
    exact hquad (n i) (Q i) (L i) (Y i) (X i) (R i) hgi hci a (N i) hwi.1 hwi.2 hNi hli phi K hLip hs
  · simpa only [zero_mul] using (tendsto_const_nhds.div_atTop hN).mul_const ((K : ℝ)+‖phi‖)

end
end SixVertex
