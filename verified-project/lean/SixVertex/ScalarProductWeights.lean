import SixVertex.ScalarProductConsequences

namespace SixVertex

noncomputable def gaudinEll {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (j : Fin n) : ℂ := ((countingSlope lam b L Y (Y j))⁻¹ : ℝ)

noncomputable def weightedGaudin {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  1 + Matrix.of (fun j k => (kernelK lam (Y j-Y k) : ℂ) * gaudinEll lam b L Y k)

theorem complex_gaudin_weights {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (hpos : ∀ j, 0 < countingSlope lam b L Y (Y j)) :
    complexGaudin lam b L Y * Matrix.diagonal (gaudinEll lam b L Y) = weightedGaudin lam b L Y := by
  have h := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A.map Complex.ofRealHom)
    (gaudin_weight_identity lam b L Y hpos)
  rw [Matrix.map_mul] at h
  convert h using 1
  · congr 1
    ext j k
    simp [gaudinEll, Matrix.diagonal_apply]
    split_ifs <;> simp_all
  · ext j k
    simp [weightedGaudin, gaudinEll, Matrix.one_apply]
    split_ifs <;> simp_all

theorem weighted_source_minor {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (twist : ℝ) (hdet : (gaudinMatrix lam b L Y).det ≠ 0)
    (hpos : ∀ j, 0 < countingSlope lam b L Y (Y j))
    (H : Finset (Fin n)) (V : Fin n → ℂ) :
    (((complexGaudin lam b L Y)⁻¹ * scalarSourceMatrix lam b L Y twist V).submatrix
      (fun i : H => i.val) (fun j : H => j.val)).det =
      (∏ i : H, gaudinEll lam b L Y i.val) *
      (((weightedGaudin lam b L Y)⁻¹ * scalarSourceMatrix lam b L Y twist V).submatrix
        (fun i : H => i.val) (fun j : H => j.val)).det := by
  have hG : (complexGaudin lam b L Y).det ≠ 0 := by
    rw [complexGaudin_det]
    exact Complex.ofReal_ne_zero.mpr hdet
  have hell : ∀ j, gaudinEll lam b L Y j ≠ 0 := fun j =>
    Complex.ofReal_ne_zero.mpr (inv_ne_zero (hpos j).ne')
  rw [inverse_column_weights _ _ hG hell, complex_gaudin_weights lam b L Y hpos,
    Matrix.mul_assoc, det_weighted_minor]

end SixVertex
