import SixVertex.FiniteBetheData
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace SixVertex
open scoped Matrix

/-- In the negative-kernel regime the counting density is positive at every
real argument, for every finite real root list and real inhomogeneity array. -/
theorem countingSlope_pos_nonpositiveK {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (Y : Fin n → ℝ) (u : ℝ)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) : 0 < countingSlope lam b L Y u := by
  have h0 : 0 < lam := by linarith [Real.pi_pos]
  have hs : 0 < ∑ a ∈ Finset.range L, kernelS lam (u-b a) := by
    apply Finset.sum_pos
    · intro a ha
      exact kernelS_pos lam _ h0 hpi
    · exact ⟨0,Finset.mem_range.mpr hL⟩
  have hk : (∑ j, kernelK lam (u-Y j)) ≤ 0 :=
    Finset.sum_nonpos (fun j hj => kernelK_nonpos lam _ hhalf hpi)
  unfold countingSlope
  linarith

theorem countingXi_strictMono_nonpositiveK {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (Y : Fin n → ℝ) (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) :
    StrictMono (countingXi lam b L Y) := by
  have h0 : 0 < lam := by linarith [Real.pi_pos]
  exact strictMono_of_hasDerivAt_pos (fun u => hasDerivAt_countingXi lam b L Y u h0 hpi)
    (fun u => countingSlope_pos_nonpositiveK lam b L hL Y u hhalf hpi)

/-- Positive Gaudin Jacobians give strict positivity along every root-space
line segment. No root solution, ordering or asymptotic estimate is assumed. -/
theorem countingSystem_strict_energy {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi)
    (X Y : Fin n → ℝ) (hXY : X ≠ Y) :
    (X-Y) ⬝ᵥ countingSystem lam b L Y < (X-Y) ⬝ᵥ countingSystem lam b L X := by
  have h0 : 0 < lam := by linarith [Real.pi_pos]
  let v := X-Y
  have hv : v ≠ 0 := sub_ne_zero.mpr hXY
  let line : ℝ → Fin n → ℝ := fun s => Y+s • v
  let f : ℝ → ℝ := fun s => v ⬝ᵥ countingSystem lam b L (line s)
  have hd (s : ℝ) : HasDerivAt f (v ⬝ᵥ (gaudinMatrix lam b L (line s) *ᵥ v)) s := by
    have hl : HasDerivAt line v s := by
      apply hasDerivAt_pi.mpr
      intro j
      simpa only [line,Pi.add_def,Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_zero,zero_add,mul_one,one_mul,id_eq] using
        (hasDerivAt_const s (Y j)).add ((hasDerivAt_id s).mul_const (v j))
    have hc := (hasFDerivAt_countingSystem lam b L (line s) h0 hpi).comp_hasDerivAt s hl
    have hj := fun j : Fin n => (hasDerivAt_pi.mp hc j).const_mul (v j)
    convert HasDerivAt.fun_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hj j) using 1
    · rfl
    · simp only [gaudinCLM,LinearMap.coe_toContinuousLinearMap',
        Matrix.toLin'_apply]
      rfl
  have hp (s : ℝ) : 0 < v ⬝ᵥ (gaudinMatrix lam b L (line s) *ᵥ v) := by
    simpa only [star_trivial] using (gaudinMatrix_posDef lam b L hL (line s) hhalf hpi).dotProduct_mulVec_pos hv
  have hm := strictMono_of_hasDerivAt_pos hd hp
  have h := hm (show (0 : ℝ) < 1 by norm_num)
  have he : line 0 = Y := by simp [line]
  have he1 : line 1 = X := by simp [line,v]
  simpa only [f,he,he1,v] using h

/-- The finite counting equations have at most one labelled real solution in
the regime lambda >= pi/2, for any prescribed counting levels. -/
theorem countingSystem_injective_nonpositiveK {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) :
    Function.Injective (countingSystem (n := n) lam b L) := by
  intro X Y he
  by_contra hn
  have h := countingSystem_strict_energy lam b L hL hhalf hpi X Y hn
  rw [he] at h
  exact lt_irrefl _ h

theorem consecutiveRoots_unique_nonpositiveK {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi)
    (twist : ℝ) (X Y : Fin n → ℝ) (hX : ConsecutiveRoots lam b L X twist)
    (hY : ConsecutiveRoots lam b L Y twist) : X = Y := by
  apply countingSystem_injective_nonpositiveK lam b L hL hhalf hpi
  exact hX.2.trans hY.2.symm

end SixVertex
