import SixVertex.ScalarProductSource

namespace SixVertex
open Filter Topology

/-- The paper's algebraic scalar product. No Hermitian-adjoint identification
is assumed. The right vector keeps the multiplicity and slot order of U. -/
noncomputable def algebraicScalarProduct {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (U : Fin n → ℂ) : ℂ :=
  (((List.finRange n).map (fun j => betheC (Complex.I*lam) (fun a => (b a : ℂ)) L (Y j))).prod *
    betheListState (Complex.I*lam) (fun a => (b a : ℂ)) L ((List.finRange n).map U))
      (plusSpins L) (plusSpins L)

noncomputable def scalarCauchy {n : ℕ} (Y : Fin n → ℝ) (U : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun j k => (Complex.sinh (U k-Y j))⁻¹)

noncomputable def scalarSourceMatrix {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (twist : ℝ) (U : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of (fun j k => scalarSource lam b L Y twist (U k) j)

noncomputable def extractedVacuum {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (u : ℂ) : ℂ :=
  vacuumA (Complex.I*lam) (fun a => (b a : ℂ)) u L * betheFProduct lam Y u

noncomputable def rootVacuumFactor {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (k : Fin n) : ℂ :=
  vacuumA (Complex.I*lam) (fun a => (b a : ℂ)) (Y k) L *
    ∏ j ∈ Finset.univ.erase k, betheF (Complex.I*lam) ((Y j : ℂ)-Y k)

/-- Regularity for the displayed source formula. Root coincidences are excluded
separately; no condition here asserts an eigenvector or determinant identity. -/
def SourceRegular {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (u : ℂ) : Prop :=
  vacuumA (Complex.I*lam) (fun a => (b a : ℂ)) u L ≠ 0 ∧
  ∀ j, Complex.sinh (u-Y j-Complex.I*lam) ≠ 0 ∧
    Complex.sinh (u-Y j+Complex.I*lam) ≠ 0

/-- ASSUMED by explicit user instruction: the twisted Slavnov identity in
source-column normalization, cross-multiplied to include zero Cauchy
determinants. Its only domain is the generic displayed formula. Coincident
limits, the norm, and deleted-column consequences are NOT assumed here. -/
def SlavnovSourceIdentity {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (twist : ℝ) : Prop :=
  ∀ U : Fin n → ℂ, (∀ k, SourceRegular lam b L Y (U k)) →
    (∀ j k, Complex.sinh (U k-Y j) ≠ 0) →
    algebraicScalarProduct lam b L Y U * (scalarCauchy Y U).det =
      (-2*(Real.pi : ℂ)*Complex.I)^n *
      (∏ j, vacuumL (Complex.I*lam) (fun a => (b a : ℂ)) (Y j) L) *
      (∏ k, extractedVacuum lam b L Y (U k)) * (scalarSourceMatrix lam b L Y twist U).det

theorem sourceRegular_real {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) (Y : Fin n → ℝ) (u : ℝ) :
    SourceRegular lam b L Y (u : ℂ) := by
  refine ⟨vacuumA_real_ne_zero lam h0 hpi b L u, ?_⟩
  intro j
  constructor
  · have h := sinh_real_shift_ne_zero (u-Y j) (-lam)
      (by simpa using (Real.sin_pos_of_pos_of_lt_pi h0 hpi).ne')
    convert h using 1 <;> push_cast <;> congr 1 <;> ring
  · simpa only [Complex.ofReal_sub] using
      sinh_real_shift_ne_zero (u-Y j) lam (Real.sin_pos_of_pos_of_lt_pi h0 hpi).ne'

theorem isOpen_sourceRegular {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) : IsOpen {u | SourceRegular lam b L Y u} := by
  rw [isOpen_iff_mem_nhds]
  intro u hu
  have hcA : ContinuousAt (fun v => vacuumA (Complex.I*lam) (fun a => (b a : ℂ)) v L) u := by
    simp only [vacuumA_product]; fun_prop
  have hA := hcA.eventually_ne hu.1
  have hB : ∀ j, ∀ᶠ v in 𝓝 u, Complex.sinh (v-Y j-Complex.I*lam) ≠ 0 ∧
      Complex.sinh (v-Y j+Complex.I*lam) ≠ 0 := by
    intro j
    have hm : ContinuousAt (fun v => Complex.sinh (v-Y j-Complex.I*lam)) u := by fun_prop
    have hp : ContinuousAt (fun v => Complex.sinh (v-Y j+Complex.I*lam)) u := by fun_prop
    exact (hm.eventually_ne (hu.2 j).1).and (hp.eventually_ne (hu.2 j).2)
  filter_upwards [hA, eventually_all.mpr hB] with v ha hb
  exact ⟨ha, hb⟩

theorem scalarSource_continuousAt {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (twist : ℝ) (u : ℂ) (hu : SourceRegular lam b L Y u)
    (hcross : ∀ j, Complex.sinh (u-Y j) ≠ 0) (j : Fin n) :
    ContinuousAt (fun x => scalarSource lam b L Y twist x j) u := by
  have hq : ContinuousAt (betheQ lam b L Y) u := by
    unfold betheQ
    apply ContinuousAt.mul
    · apply ContinuousAt.div
      · simp only [vacuumL_product]; fun_prop
      · simp only [vacuumA_product]; fun_prop
      · exact hu.1
    · apply tendsto_finsetProd
      intro k hk
      apply ContinuousAt.div <;> try fun_prop
      exact (hu.2 k).1
  have hc : ContinuousAt (fun x => hyperbolicCot (x-Y j)) u := by
    apply ContinuousAt.div <;> try fun_prop
    exact hcross j
  have hm : ContinuousAt (fun x => hyperbolicCot (x-Y j-Complex.I*lam)) u := by
    apply ContinuousAt.div <;> try fun_prop
    exact (hu.2 j).1
  have hp : ContinuousAt (fun x => hyperbolicCot (x-Y j+Complex.I*lam)) u := by
    apply ContinuousAt.div <;> try fun_prop
    exact (hu.2 j).2
  exact continuousAt_const.mul (((continuousAt_const.add (continuousAt_const.mul hq)).mul hc).sub hm |>.sub ((continuousAt_const.mul hq).mul hp))

/-- The actual finite scalar product is continuous at arbitrary collisions. -/
theorem algebraicScalarProduct_tendsto {J : Type*} {n : ℕ} (r : Filter J)
    (lam : ℝ) (b : ℕ → ℝ) (L : ℕ) (Y : Fin n → ℝ)
    (U : J → Fin n → ℂ) (U₀ : Fin n → ℂ)
    (hU : ∀ k, Tendsto (fun z => U z k) r (𝓝 (U₀ k))) :
    Tendsto (fun z => algebraicScalarProduct lam b L Y (U z)) r
      (𝓝 (algebraicScalarProduct lam b L Y U₀)) := by
  have hv := betheListState_tendsto r (Complex.I*lam) (fun a => (b a : ℂ)) L
    (List.finRange n) U U₀ (fun k _ => hU k)
  unfold algebraicScalarProduct
  simp only [Matrix.mul_apply]
  apply tendsto_finset_sum
  intro q hq
  apply Tendsto.const_mul
  exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hv q) (plusSpins L)

end SixVertex
