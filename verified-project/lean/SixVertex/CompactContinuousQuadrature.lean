import SixVertex.CompactQuadratureError
import SixVertex.UnitLipschitzRescaling

namespace SixVertex
noncomputable section
open Set MeasureTheory Filter Topology
open scoped NNReal

/-- Uniform compact mass control and proved Lipschitz approximation
extend actual root-measure convergence to every compact continuous test. -/
theorem compact_continuous_quadrature_tendsto {ι : Type*} (lam : ℝ)
    (hhalf : Real.pi/2 < lam) (hpi : lam < Real.pi) (l : Filter ι)
    (n L : ι → ℕ) (b : ι → ℕ → ℝ) (Z : (i : ι) → Fin (n i) → ℝ)
    (hL : ∀ i, 0 < L i) (hZ : ∀ i, ConsecutiveRoots lam (b i) (L i) (Z i) 0)
    (A : ℝ) (hA : 0 ≤ A)
    (hunit : ∀ psi : BoundedRealFunction, LipschitzWith 1 (fun x => psi x) → ‖psi‖ ≤ 1 →
      (∀ x, x ∉ Icc (-(A+1)) (A+1) → psi x=0) →
      Tendsto (fun i => ∫ x, psi x ∂rootQuadratureMeasure lam (b i) (L i) (Z i))
        l (𝓝 (∫ x : ℝ, psi x)))
    (phi : BoundedRealFunction) (hs : ∀ x, x ∉ Icc (-A) A → phi x=0) :
    Tendsto (fun i => ∫ x, phi x ∂rootQuadratureMeasure lam (b i) (L i) (Z i))
      l (𝓝 (∫ x : ℝ, phi x)) := by
  let B : ℝ := A+1
  let M : ℝ := (Real.exp (kernelLogConstant lam*(B-(-B))))^2*(B-(-B))+
    Real.exp (kernelLogConstant lam*(B-(-B)))/(-kernelK lam 0)+(B-(-B))
  have hB : 0 < B := by dsimp [B]; linarith
  have hk : 0 < -kernelK lam 0 := neg_pos.mpr (kernelK_strict_neg lam 0 hhalf hpi)
  have hlen : 0 ≤ B-(-B) := by linarith
  have hM : 0 ≤ M := by dsimp [M]; positivity
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  let delta : ℝ := eps/(4*(M+1))
  have hd : 0 < delta := div_pos heps (by positivity)
  obtain ⟨psi,K,hLip,hps,hnear⟩ := exists_compact_lipschitz_test_approximation phi A hA hs delta hd
  obtain ⟨D,tau,hD,htLip,htNorm,hscale,hzero⟩ := exists_unit_lipschitz_rescaling psi K hLip
  have hts : ∀ x, x ∉ Icc (-B) B → tau x=0 := by
    intro x hx
    exact hzero x (hps x hx)
  have hi (mu : Measure ℝ) : (∫ x, psi x ∂mu)=D*(∫ x, tau x ∂mu) := by
    calc
      _ = ∫ x, D*tau x ∂mu := integral_congr_ae (Eventually.of_forall hscale)
      _ = _ := integral_const_mul _ _
  have hc : Tendsto (fun i => ∫ x, psi x ∂rootQuadratureMeasure lam (b i) (L i) (Z i))
      l (𝓝 (∫ x : ℝ, psi x)) := by
    simpa only [hi] using (hunit tau htLip htNorm hts).const_mul D
  have hsmall := Metric.tendsto_nhds.mp hc (eps/2) (by linarith)
  have hphi : ∀ x, x ∉ Icc (-B) B → phi x=0 := by
    intro x hx
    apply hs x
    intro hxx
    apply hx
    exact ⟨by dsimp [B]; linarith [hxx.1],by dsimp [B]; linarith [hxx.2]⟩
  have hdm : delta*M < eps/2 := by
    have hh : delta*(4*(M+1))=eps := by dsimp [delta]; field_simp
    nlinarith [mul_nonneg hd.le hM]
  filter_upwards [hsmall] with i hiSmall
  rw [Real.dist_eq] at hiSmall ⊢
  have he := compact_quadrature_error_transfer lam (b i) (L i) (hL i) (Z i) hhalf hpi (hZ i)
    phi psi (-B) B delta (by linarith) hd.le hphi hps hnear
  change |(∫ x, phi x ∂rootQuadratureMeasure lam (b i) (L i) (Z i))-(∫ x : ℝ, phi x)| ≤
    |(∫ x, psi x ∂rootQuadratureMeasure lam (b i) (L i) (Z i))-(∫ x : ℝ, psi x)|+delta*M at he
  linarith

/-- Dense reference quadrature for arbitrary compact continuous tests,
with occupation proved on the enlarged approximation window. -/
theorem dense_reference_continuous_quadrature_tendsto {ι : Type*} (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 < lam) (hpi : lam < Real.pi) (A : ℝ) (hA : 0 ≤ A)
    (l : Filter ι) (n L : ι → ℕ) (Q : ι → ℝ) (Y Z : (i : ι) → Fin (n i) → ℝ)
    (R : ∀ i, ReferenceQuantileData lam h0 hpi (Q i) (L i) (Y i))
    (hZ : ∀ i, ConsecutiveRoots lam (fun _ => 0) (L i) (Z i) 0)
    (hL : Tendsto L l atTop) (hQ : ∀ᶠ i in l, A+2 ≤ Q i)
    (hdense : Tendsto (fun i => (L i : ℝ)*fullLineDensityFunction lam h0 hpi (Q i)) l atTop)
    (phi : BoundedRealFunction) (hs : ∀ x, x ∉ Icc (-A) A → phi x=0) :
    Tendsto (fun i => ∫ x, phi x ∂rootQuadratureMeasure lam (fun _ => 0) (L i) (Z i))
      l (𝓝 (∫ x : ℝ, phi x)) := by
  apply compact_continuous_quadrature_tendsto lam hhalf hpi l n L (fun _ _ => 0) Z
    (fun i => (R i).chain_pos) hZ A hA _ phi hs
  intro psi hpLip hpNorm hpS
  apply dense_reference_quadrature_tendsto lam h0 hhalf.le hpi (A+1) (by linarith) l n L Q Y Z R hZ hL _ hdense psi hpLip hpNorm hpS
  have heq : A+1+1=A+2 := by ring
  rw [heq]
  exact hQ

/-- Regular-filling quadrature for arbitrary compact continuous tests
whenever the proved reference window eventually contains their support. -/
theorem regular_filling_continuous_quadrature_tendsto {ι : Type*} (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 < lam) (hpi : lam < Real.pi) (A : ℝ) (hA : 0 ≤ A)
    (l : Filter ι) (n L : ι → ℕ) (Q : ι → ℝ) (Y Z : (i : ι) → Fin (n i) → ℝ)
    (R : ∀ i, ReferenceQuantileData lam h0 hpi (Q i) (L i) (Y i))
    (hZ : ∀ i, ConsecutiveRoots lam (fun _ => 0) (L i) (Z i) 0)
    (hL : Tendsto L l atTop) (rho : ℝ) (hrho : rho < 1/2)
    (hwindow : finiteIntervalMass lam h0 hpi (A+2) < rho)
    (hfill : Tendsto (fun i => (n i : ℝ)/(L i : ℝ)) l (𝓝 rho))
    (phi : BoundedRealFunction) (hs : ∀ x, x ∉ Icc (-A) A → phi x=0) :
    Tendsto (fun i => ∫ x, phi x ∂rootQuadratureMeasure lam (fun _ => 0) (L i) (Z i))
      l (𝓝 (∫ x : ℝ, phi x)) := by
  apply compact_continuous_quadrature_tendsto lam hhalf hpi l n L (fun _ _ => 0) Z
    (fun i => (R i).chain_pos) hZ A hA _ phi hs
  intro psi hpLip hpNorm hpS
  apply regular_filling_quadrature_tendsto lam h0 hhalf.le hpi (A+1) (by linarith) l n L Q Y Z R hZ hL rho hrho _ hfill psi hpLip hpNorm hpS
  have heq : A+1+1=A+2 := by ring
  rw [heq]
  exact hwindow

/-- Actual half-filled chains with uniformly bounded inhomogeneities
converge against every compact continuous real test. -/
theorem half_filled_continuous_quadrature_tendsto {ι : Type*} (lam : ℝ)
    (hhalf : Real.pi/2 < lam) (hpi : lam < Real.pi) (A B : ℝ) (hA : 0 ≤ A)
    (l : Filter ι) (n L : ι → ℕ) (b : ι → ℕ → ℝ) (Z : (i : ι) → Fin (n i) → ℝ)
    (hL : ∀ i, 0 < L i) (hLinf : Tendsto L l atTop) (hfill : ∀ i, L i=2*n i)
    (hZ : ∀ i, ConsecutiveRoots lam (b i) (L i) (Z i) 0)
    (hb : ∀ i, ∀ a ∈ Finset.range (L i), |b i a| ≤ B)
    (phi : BoundedRealFunction) (hs : ∀ x, x ∉ Icc (-A) A → phi x=0) :
    Tendsto (fun i => ∫ x, phi x ∂rootQuadratureMeasure lam (b i) (L i) (Z i))
      l (𝓝 (∫ x : ℝ, phi x)) := by
  apply compact_continuous_quadrature_tendsto lam hhalf hpi l n L b Z hL hZ A hA _ phi hs
  intro psi hpLip hpNorm hpS
  obtain ⟨C,_,hbound⟩ := exists_half_filled_quadrature_rate lam hhalf.le hpi (A+1) B (by linarith)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (g := fun i => C/(L i : ℝ)) (Eventually.of_forall (fun i => norm_nonneg _))
  · apply Eventually.of_forall
    intro i
    rw [Real.norm_eq_abs]
    exact hbound (n i) (b i) (L i) (hL i) (hfill i) (Z i) (hZ i) (hb i) psi hpLip hpNorm hpS
  · exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hLinf)

end
end SixVertex
