import SixVertex.FiniteGaudin

namespace SixVertex

open scoped Matrix

/-- The quadratic-form identity for a symmetric weighted graph matrix. -/
theorem symmetric_gaudin_energy {I : Type*} [Fintype I]
    (d : I → ℝ) (K : I → I → ℝ) (x : I → ℝ) (hK : ∀ i j, K i j = K j i) :
    (∑ i, x i * ((d i - ∑ j, K i j) * x i + ∑ j, K i j * x j)) =
      (∑ i, d i * (x i)^2) - (∑ i, ∑ j, K i j * (x i-x j)^2)/2 := by
  have hswap : (∑ i, ∑ j, K i j * (x j)^2) = ∑ i, ∑ j, K i j * (x i)^2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hK j i]
  have he : (∑ i, ∑ j, K i j * (x i-x j)^2) =
      (∑ i, ∑ j, K i j * (x i)^2) - 2*(∑ i, ∑ j, K i j * x i * x j) +
        ∑ i, ∑ j, K i j * (x j)^2 := by
    calc
      _ = ∑ i, ∑ j, (K i j * (x i)^2 - 2*(K i j * x i * x j) + K i j * (x j)^2) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  have hr : (∑ i, x i * ((d i - ∑ j, K i j) * x i + ∑ j, K i j * x j)) =
      (∑ i, d i * (x i)^2) - (∑ i, ∑ j, K i j * (x i)^2) +
        ∑ i, ∑ j, K i j * x i * x j := by
    calc
      _ = ∑ i, (d i * (x i)^2 - (∑ j, K i j) * (x i)^2 +
          x i * (∑ j, K i j * x j)) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_mul, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
  rw [he, hswap, hr]
  ring

theorem gaudinMatrix_isHermitian {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ) (Y : Fin n → ℝ) :
    (gaudinMatrix lam b L Y).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  ext j k
  simp only [Matrix.transpose_apply, gaudinMatrix, Matrix.of_apply]
  have he : kernelK lam (Y k-Y j) = kernelK lam (Y j-Y k) := by
    rw [show Y k-Y j = -(Y j-Y k) by ring, kernelK_neg]
  by_cases hjk : j = k
  · subst k
    rfl
  · simp [hjk, Ne.symm hjk, he]

theorem gaudin_quadratic_energy {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y x : Fin n → ℝ) :
    x ⬝ᵥ (gaudinMatrix lam b L Y *ᵥ x) =
      (∑ j, (∑ a ∈ Finset.range L, kernelS lam (Y j-b a)) * (x j)^2) -
      (∑ j, ∑ k, kernelK lam (Y j-Y k) * (x j-x k)^2)/2 := by
  classical
  have he := symmetric_gaudin_energy
    (fun j => ∑ a ∈ Finset.range L, kernelS lam (Y j-b a))
    (fun j k => kernelK lam (Y j-Y k)) x
    (fun j k => by rw [show Y j-Y k = -(Y k-Y j) by ring, kernelK_neg])
  rw [← he]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Matrix.mulVec, dotProduct, gaudinMatrix, Matrix.of_apply, countingSlope,
    add_mul, ite_mul, zero_mul, Finset.sum_add_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem gaudinMatrix_posDef {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (Y : Fin n → ℝ) (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) :
    (gaudinMatrix lam b L Y).PosDef := by
  classical
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (gaudinMatrix_isHermitian lam b L Y)
  intro x hx
  rw [show star x = x by simp]
  rw [gaudin_quadratic_energy]
  have h0 : 0 < lam := by linarith [Real.pi_pos]
  have hd : ∀ j : Fin n, 0 < ∑ a ∈ Finset.range L, kernelS lam (Y j-b a) := by
    intro j
    apply Finset.sum_pos
    · intro a ha
      exact kernelS_pos lam _ h0 hpi
    · exact ⟨0, Finset.mem_range.mpr hL⟩
  have hsum : 0 < ∑ j, (∑ a ∈ Finset.range L, kernelS lam (Y j-b a)) * (x j)^2 := by
    apply Finset.sum_pos'
    · intro j hj
      exact mul_nonneg (hd j).le (sq_nonneg _)
    · obtain ⟨j,hj⟩ : ∃ j, x j ≠ 0 := by
        by_contra hn
        apply hx
        ext j
        simpa using not_exists.mp hn j
      exact ⟨j, Finset.mem_univ j, mul_pos (hd j) (sq_pos_of_ne_zero hj)⟩
  have hn : (∑ j, ∑ k, kernelK lam (Y j-Y k) * (x j-x k)^2) ≤ 0 := by
    apply Finset.sum_nonpos
    intro j hj
    apply Finset.sum_nonpos
    intro k hk
    exact mul_nonpos_of_nonpos_of_nonneg (kernelK_nonpos lam _ hhalf hpi) (sq_nonneg _)
  linarith

end SixVertex
