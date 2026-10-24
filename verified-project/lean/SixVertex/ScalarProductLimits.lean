import SixVertex.ScalarProductSetup
import SixVertex.ScalarProductDeterminants

namespace SixVertex
open Filter Topology

theorem tendsto_shift_punctured (p : ℂ) :
    Tendsto (fun z : ℂ => p+z) (𝓝[≠] 0) (𝓝[≠] p) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc : ContinuousAt (fun z : ℂ => p+z) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with z hz
    simpa using hz

/-- Residue of the extracted vacuum factor at a simple root. -/
theorem extractedVacuum_residue {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) (Y : Fin n → ℝ) (hY : Function.Injective Y) (k : Fin n) :
    Tendsto (fun u => Complex.sinh (u-Y k)*extractedVacuum lam b L Y u)
      (𝓝[≠] (Y k : ℂ))
      (𝓝 (-Complex.sinh (Complex.I*lam)*rootVacuumFactor lam b L Y k)) := by
  have hprod : ContinuousAt (fun u => ∏ j ∈ Finset.univ.erase k,
      betheF (Complex.I*lam) ((Y j : ℂ)-u)) (Y k : ℂ) := by
    apply tendsto_finsetProd
    intro j hj
    apply ContinuousAt.div <;> try fun_prop
    have hne := (Finset.mem_erase.mp hj).1
    have hh := real_sinh_sub_ne Y hY hne.symm
    exact hh
  have ha : ContinuousAt (fun u => vacuumA (Complex.I*lam) (fun a => (b a : ℂ)) u L) (Y k : ℂ) := by
    simp only [vacuumA_product]; fun_prop
  have hc : ContinuousAt (fun u => -Complex.sinh ((Y k : ℂ)-u+Complex.I*lam) *
      vacuumA (Complex.I*lam) (fun a => (b a : ℂ)) u L *
      ∏ j ∈ Finset.univ.erase k, betheF (Complex.I*lam) ((Y j : ℂ)-u)) (Y k : ℂ) := by
    exact ((by fun_prop : ContinuousAt (fun u => -Complex.sinh ((Y k : ℂ)-u+Complex.I*lam)) (Y k : ℂ)).mul ha).mul hprod
  have hl := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {(Y k : ℂ)}ᶜ))
  simp only [sub_self, zero_add, rootVacuumFactor, mul_assoc] at hl ⊢
  apply hl.congr'
  filter_upwards [eventually_sinh_sub_ne (Y k : ℂ)] with u hu
  unfold extractedVacuum betheFProduct
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
  have he : Complex.sinh ((Y k : ℂ)-u) = -Complex.sinh (u-Y k) := by
    rw [show (Y k : ℂ)-u = -(u-Y k) by ring, Complex.sinh_neg]
  unfold betheF
  rw [he]
  field_simp

/-- One scalar pole cancellation turns a Cauchy column into a unit column. -/
theorem cauchy_root_column_limit {n : ℕ} (Y : Fin n → ℝ) (hY : Function.Injective Y)
    (j k : Fin n) :
    Tendsto (fun z : ℂ => Complex.sinh z * (Complex.sinh ((Y k : ℂ)+z-Y j))⁻¹)
      (𝓝[≠] 0) (𝓝 ((1 : Matrix (Fin n) (Fin n) ℂ) j k)) := by
  by_cases hjk : j=k
  · subst j
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_sinh_sub_ne (0 : ℂ)] with z hz
    simp only [sub_zero] at hz
    simp [show (Y k : ℂ)+z-Y k = z by ring, hz]
  · have hd : ContinuousAt (fun z : ℂ => (Complex.sinh ((Y k : ℂ)+z-Y j))⁻¹) 0 := by
      apply ContinuousAt.inv₀ <;> try fun_prop
      simpa using real_sinh_sub_ne Y hY hjk
    have hc' : ContinuousAt (fun z : ℂ => Complex.sinh z * (Complex.sinh ((Y k : ℂ)+z-Y j))⁻¹) 0 := Complex.continuous_sinh.continuousAt.mul hd
    have hc := hc'.tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
    simpa [Matrix.one_apply, hjk] using hc

/-- A simultaneous perturbation of unchanged roots and new spectral slots.
Only the generic Slavnov formula is used before taking this limit. -/
theorem slavnov_partial_coincidence {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) (hEven : Even L) (Y : Fin n → ℝ) (hY : Function.Injective Y)
    (twist : ℝ) (hShell : OnShell lam b L Y twist)
    (hSlavnov : SlavnovSourceIdentity lam b L Y twist) (H : Finset (Fin n)) (V : Fin n → ℂ)
    (hV : ∀ k ∈ H, SourceRegular lam b L Y (V k))
    (hcross : ∀ k ∈ H, ∀ j, Complex.sinh (V k-Y j) ≠ 0) :
    algebraicScalarProduct lam b L Y (fun k => if k ∈ H then V k else (Y k : ℂ)) *
      (replaceColumns 1 (scalarCauchy Y V) H).det =
      (-2*(Real.pi : ℂ)*Complex.I)^n *
      (∏ j, vacuumL (Complex.I*lam) (fun a => (b a : ℂ)) (Y j) L) *
      (∏ k, if k ∈ H then extractedVacuum lam b L Y (V k)
        else -Complex.sinh (Complex.I*lam)*rootVacuumFactor lam b L Y k) *
      (replaceColumns (complexGaudin lam b L Y) (scalarSourceMatrix lam b L Y twist V) H).det := by
  classical
  let U₀ : Fin n → ℂ := fun k => if k ∈ H then V k else (Y k : ℂ)
  let U : ℂ → Fin n → ℂ := fun z k => U₀ k+z
  let scale : ℂ → Fin n → ℂ := fun z k => if k ∈ H then 1 else Complex.sinh z
  let C : ℂ → Matrix (Fin n) (Fin n) ℂ := fun z =>
    Matrix.of (fun j k => scale z k * scalarCauchy Y (U z) j k)
  let A : ℂ → Fin n → ℂ := fun z k => scale z k * extractedVacuum lam b L Y (U z k)
  have hU (k : Fin n) : Tendsto (fun z => U z k) (𝓝[≠] 0) (𝓝 (U₀ k)) := by
    have hc : ContinuousAt (fun z : ℂ => U₀ k+z) 0 := by fun_prop
    simpa [U] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hreg : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ k, SourceRegular lam b L Y (U z k) := by
    apply eventually_all.mpr
    intro k
    have hr : SourceRegular lam b L Y (U₀ k) := by
      by_cases hk : k ∈ H
      · simpa [U₀, hk] using hV k hk
      · simpa [U₀, hk] using sourceRegular_real lam h0 hpi b L Y (Y k)
    exact (hU k).eventually (isOpen_sourceRegular lam b L Y |>.mem_nhds hr)
  have hcross' : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ j k, Complex.sinh (U z k-Y j) ≠ 0 := by
    apply eventually_all.mpr
    intro j
    apply eventually_all.mpr
    intro k
    by_cases hk : k ∈ H
    · have hc : ContinuousAt (fun z : ℂ => Complex.sinh (V k+z-Y j)) 0 := by fun_prop
      simpa [U, U₀, hk] using hc.eventually_ne (by simpa using hcross k hk j) |>.filter_mono nhdsWithin_le_nhds
    · by_cases hjk : j=k
      · subst j
        simpa [U, U₀, hk] using eventually_sinh_sub_ne (0 : ℂ)
      · have hc : ContinuousAt (fun z : ℂ => Complex.sinh ((Y k : ℂ)+z-Y j)) 0 := by fun_prop
        simpa [U, U₀, hk] using hc.eventually_ne (by simpa using real_sinh_sub_ne Y hY hjk) |>.filter_mono nhdsWithin_le_nhds
  have hC : Tendsto C (𝓝[≠] (0 : ℂ)) (𝓝 (replaceColumns 1 (scalarCauchy Y V) H)) := by
    apply tendsto_pi_nhds.mpr
    intro j
    apply tendsto_pi_nhds.mpr
    intro k
    by_cases hk : k ∈ H
    · have hc : ContinuousAt (fun z : ℂ => (Complex.sinh (V k+z-Y j))⁻¹) 0 := by
        apply ContinuousAt.inv₀ <;> try fun_prop
        simpa using hcross k hk j
      simpa [C, scale, scalarCauchy, U, U₀, hk, replaceColumns] using hc.tendsto.mono_left nhdsWithin_le_nhds
    · simpa [C, scale, scalarCauchy, U, U₀, hk, replaceColumns] using cauchy_root_column_limit Y hY j k
  have hM : Tendsto (fun z => scalarSourceMatrix lam b L Y twist (U z)) (𝓝[≠] (0 : ℂ))
      (𝓝 (replaceColumns (complexGaudin lam b L Y) (scalarSourceMatrix lam b L Y twist V) H)) := by
    apply tendsto_pi_nhds.mpr
    intro j
    apply tendsto_pi_nhds.mpr
    intro k
    by_cases hk : k ∈ H
    · have huk : Tendsto (fun z => U z k) (𝓝[≠] (0 : ℂ)) (𝓝 (V k)) := by simpa only [U₀, hk, ite_true] using hU k
      have hc := (scalarSource_continuousAt lam b L Y twist (V k) (hV k hk) (hcross k hk) j).tendsto.comp huk
      simpa [scalarSourceMatrix, U₀, hk, replaceColumns, Function.comp_def] using hc
    · have hc := (scalarSource_gaudin_limit lam h0 hpi b L hEven Y hY twist hShell k j).comp
        (tendsto_shift_punctured (Y k : ℂ))
      simpa [scalarSourceMatrix, U, U₀, hk, replaceColumns, Function.comp_def] using hc
  have hA : ∀ k, Tendsto (fun z => A z k) (𝓝[≠] (0 : ℂ))
      (𝓝 (if k ∈ H then extractedVacuum lam b L Y (V k)
        else -Complex.sinh (Complex.I*lam)*rootVacuumFactor lam b L Y k)) := by
    intro k
    by_cases hk : k ∈ H
    · have hc : ContinuousAt (extractedVacuum lam b L Y) (V k) := by
        unfold extractedVacuum betheFProduct
        apply ContinuousAt.mul
        · simp only [vacuumA_product]; fun_prop
        · apply tendsto_finsetProd
          intro j hj
          apply ContinuousAt.div <;> try fun_prop
          rw [show (Y j : ℂ)-V k = -(V k-Y j) by ring, Complex.sinh_neg]
          exact neg_ne_zero.mpr (hcross k hk j)
      have huk : Tendsto (fun z => U z k) (𝓝[≠] (0 : ℂ)) (𝓝 (V k)) := by simpa only [U₀, hk, ite_true] using hU k
      simpa [A, scale, U₀, hk, Function.comp_def] using hc.tendsto.comp huk
    · have hc := (extractedVacuum_residue lam h0 hpi b L Y hY k).comp (tendsto_shift_punctured (Y k : ℂ))
      simpa [A, scale, U, U₀, hk, add_sub_cancel_left, Function.comp_def] using hc
  have hleft := (algebraicScalarProduct_tendsto (𝓝[≠] (0 : ℂ)) lam b L Y U U₀ hU).mul
    (continuous_id.matrix_det.tendsto _ |>.comp hC)
  have hright := ((tendsto_finset_prod Finset.univ (fun k _ => hA k)).const_mul
      ((-2*(Real.pi : ℂ)*Complex.I)^n * ∏ j, vacuumL (Complex.I*lam) (fun a => (b a : ℂ)) (Y j) L)).mul
    (continuous_id.matrix_det.tendsto _ |>.comp hM)
  apply tendsto_nhds_unique hleft (hright.congr' ?_)
  filter_upwards [hreg, hcross'] with z hz hcz
  have he := hSlavnov (U z) hz hcz
  dsimp [C]
  rw [Matrix.det_mul_row]
  dsimp [A]
  rw [Finset.prod_mul_distrib]
  linear_combination -(∏ k, scale z k)*he

end SixVertex
