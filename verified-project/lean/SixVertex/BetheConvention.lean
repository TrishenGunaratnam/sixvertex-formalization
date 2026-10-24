import SixVertex.BetheRows

namespace SixVertex

theorem sinh_physical_deformation (lam : ℝ) :
    Complex.sinh (Complex.I * (lam : ℂ)) = Complex.I * Complex.sin (lam : ℂ) := by
  rw [mul_comm Complex.I, Complex.sinh_mul_I, mul_comm]

theorem physical_deformation_ne_zero (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    Complex.sinh (Complex.I * (lam : ℂ)) ≠ 0 := by
  rw [sinh_physical_deformation]
  apply mul_ne_zero Complex.I_ne_zero
  have h : (Real.sin lam : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sin_pos_of_pos_of_lt_pi h0 hpi).ne'
  simpa only [Complex.ofReal_sin] using h

/-- Exact identification with the standard local matrix displayed in Section 2. -/
theorem hyperbolicR_eq_standardL (lam : ℝ) (x : ℂ) :
    hyperbolicR (Complex.I * (lam : ℂ)) (x-Complex.I*lam/2) = standardL lam x := by
  unfold hyperbolicR standardL
  rw [sinh_physical_deformation]
  rw [show x-Complex.I*lam/2+Complex.I*lam = x+Complex.I*lam/2 by ring]

/-- The action proofs use exactly the paper's ordered standard monodromy. -/
theorem betheBlock_eq_standard (lam : ℝ) (b : ℕ → ℝ) (n : ℕ)
    (x : ℂ) (a c : Fin 2) :
    betheBlock (Complex.I * (lam : ℂ)) (fun j => (b j : ℂ)) n x a c =
      rowBlock (fun j => standardL lam (x-b j)) n a c := by
  unfold betheBlock
  have he : (fun j => hyperbolicR (Complex.I * (lam : ℂ))
      (x-(b j : ℂ)-Complex.I*lam/2)) = (fun j => standardL lam (x-b j)) := by
    funext j
    exact hyperbolicR_eq_standardL lam (x-b j)
  rw [he]

end SixVertex
