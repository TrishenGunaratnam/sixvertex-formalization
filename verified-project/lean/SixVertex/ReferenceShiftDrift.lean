import SixVertex.PerturbedReferenceRows
import SixVertex.FiniteCountingOrder

namespace SixVertex
noncomputable section
open Set Filter Topology

def referenceShift {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ) (t : ℝ) : Fin n → ℝ :=
  fun j => Y j+t/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))

theorem gaudinCLM_coordinate {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (X v : Fin n → ℝ) (i : Fin n) :
    gaudinCLM lam b L X v i=countingSlope lam b L X (X i)*v i+
      ∑ j : Fin n, kernelK lam (X i-X j)*v j := by
  classical
  change (gaudinMatrix lam b L X).mulVec v i=_
  simp only [Matrix.mulVec,dotProduct,gaudinMatrix,Matrix.of_apply,add_mul,Finset.sum_add_distrib,
    ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

theorem referenceShift_counting_hasDerivAt {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ) (t : ℝ) (i : Fin n) :
    HasDerivAt (fun s => countingSystem lam (fun _ => 0) L (referenceShift lam h0 hpi Q L Y s) i)
      (countingSlope lam (fun _ => 0) L (referenceShift lam h0 hpi Q L Y t)
        (referenceShift lam h0 hpi Q L Y t i)/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y i))+
      ∑ j : Fin n, kernelK lam (referenceShift lam h0 hpi Q L Y t i-referenceShift lam h0 hpi Q L Y t j)/
        ((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))) t := by
  let v : Fin n → ℝ := fun j => 1/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))
  have hl : HasDerivAt (referenceShift lam h0 hpi Q L Y) v t := by
    apply hasDerivAt_pi.mpr
    intro j
    simpa only [referenceShift,v,Pi.add_def,id_eq,zero_add] using! (hasDerivAt_const t (Y j)).add ((hasDerivAt_id t).div_const ((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j)))
  have hc := (hasFDerivAt_countingSystem lam (fun _ => 0) L (referenceShift lam h0 hpi Q L Y t) h0 hpi).comp_hasDerivAt t hl
  have hi := hasDerivAt_pi.mp hc i
  rw [gaudinCLM_coordinate] at hi
  simpa only [v,mul_one_div,Function.comp_def] using! hi

theorem referenceShift_displacement_bound {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ)
    (R : ReferenceQuantileData lam h0 hpi Q L Y) (M : ℝ) (hM : 0 < M)
    (hlower : ∀ v ∈ Icc (-Q) Q, M ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q v)
    (radius t : ℝ) (ht : |t| ≤ radius) :
    ∀ j, |referenceShift lam h0 hpi Q L Y t j-Y j| ≤ radius/M := by
  intro j
  have hw := hlower (Y j) ⟨(R.location j).1.le,(R.location j).2.le⟩
  have hwp : 0 < (L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j) := hM.trans_le hw
  change |Y j+t/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))-Y j| ≤ _
  rw [add_sub_cancel_left,abs_div,abs_of_pos hwp]
  exact div_le_div₀ ((abs_nonneg t).trans ht) ht hM hw

/-- One threshold gives a positive row drift on the whole fixed-radius
weighted shift segment, uniformly in cutoff and root number. -/
theorem exists_uniform_referenceShift_drift (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (radius : ℝ) (hrad : 0 ≤ radius) :
    ∃ M : ℝ, 0 < M ∧ ∀ (n : ℕ) (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ),
      ∀ R : ReferenceQuantileData lam h0 hpi Q L Y,
      (∀ v ∈ Icc (-Q) Q, M ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q v) →
      ∀ t ∈ Icc (-radius) radius, ∀ i : Fin n,
      (1-kernelL1Mass (kernelK lam))/2 ≤
      countingSlope lam (fun _ => 0) L (referenceShift lam h0 hpi Q L Y t)
        (referenceShift lam h0 hpi Q L Y t i)/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y i))+
      ∑ j : Fin n, kernelK lam (referenceShift lam h0 hpi Q L Y t i-referenceShift lam h0 hpi Q L Y t j)/
        ((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j)) := by
  let h := kernelL1Mass (kernelK lam)
  let D := kernelL1Mass (kernelKPrime lam)/2
  let B := referenceKernelRowErrorConstant lam
  let C := kernelLogConstant lam
  let delta := (1-h)/2
  let g : ℝ → ℝ := fun s => Real.exp (-(C*(2*(radius*s))))*(1-D*s)-
    Real.exp (C*(2*(radius*s)))*(h+B*s)
  have hh : h < 1 := kernelK_L1_mass_lt_one lam h0 hpi
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hg0 : g 0=1-h := by simp [g]
  have hd : delta < g 0 := by rw [hg0]; dsimp [delta]; linarith
  have hlim : Tendsto (fun M : ℝ => g M⁻¹) atTop (𝓝 (g 0)) :=
    hg.continuousAt.tendsto.comp tendsto_inv_atTop_zero
  obtain ⟨M,hMp,hMg⟩ := ((eventually_gt_atTop (0 : ℝ)).and (hlim.eventually (Ioi_mem_nhds hd))).exists
  refine ⟨M,hMp,?_⟩
  intro n Q L Y R hlower t ht i
  have hclose := referenceShift_displacement_bound lam h0 hhalf hpi Q L Y R M hMp hlower radius t (abs_le.mpr ht)
  have hdrift := perturbed_reference_gaudin_row_drift lam h0 hhalf hpi Q L Y
    (referenceShift lam h0 hpi Q L Y t) R M hMp hlower (radius/M) (div_nonneg hrad hMp.le) hclose i
  apply le_trans (le_of_lt hMg) _
  simpa only [g,C,D,B,h,div_eq_mul_inv] using hdrift

end
end SixVertex
