import SixVertex.YangBaxter
import SixVertex.RowTrain

namespace SixVertex

theorem localRTT_intertwines (R P Q : Matrix PairSpin PairSpin ℂ)
    (h : LocalRTT R P Q) (q r : Fin 2) :
    R * forwardTile P Q q r = reverseTile P Q q r * R := by
  ext ⟨a,b⟩ ⟨c,d⟩
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, forwardTile, reverseTile,
    Finset.mul_sum, Finset.sum_mul]
  simpa only [mul_assoc] using h a b c d q r

/-- The full RTT relation on every finite chain, proved by moving the same
intertwiner through all sites. Quantum matrix products and both auxiliary
spins are retained explicitly in forwardRows and reverseRows. -/
theorem finite_chain_RTT (R : Matrix PairSpin PairSpin ℂ)
    (P Q : ℕ → Matrix PairSpin PairSpin ℂ)
    (h : ∀ j, LocalRTT R (P j) (Q j))
    (n : ℕ) (q r : RowSpins n) :
    R * forwardRows P Q n q r = reverseRows P Q n q r * R := by
  rw [forwardRows_eq_chainAux, reverseRows_eq_chainAux]
  exact chainAux_intertwines R _ _ (fun j => localRTT_intertwines R (P j) (Q j) (h j)) n q r

/-- The paper's physical auxiliary intertwiner. -/
noncomputable def physicalIntertwiner (lam : ℝ) (u : ℂ) : Matrix PairSpin PairSpin ℂ :=
  auxZ * sixMatrix
    (Complex.sinh (u + Complex.I * lam) / (Complex.I * Complex.sin lam))
    (Complex.sinh u / (Complex.I * Complex.sin lam)) 1 * siteZ

theorem physicalIntertwiner_eq_R (lam : ℝ) (u : ℂ) :
    physicalIntertwiner lam u = physicalR lam (Complex.I * u) := by
  rw [physicalIntertwiner, sixMatrix_gauge, physicalR]
  congr 1
  · rw [sin_weight]
    congr 2
    ring_nf
    simp [Complex.I_sq]
  · rw [sin_weight]
    have h : Complex.I * u * Complex.I = -u := by
      ring_nf
      simp [Complex.I_sq]
    rw [h, Complex.sinh_neg, neg_div]

/-- The complete physical RTT clause, for arbitrary length and complex p,q.
Real inhomogeneities are exactly those used in the paper. -/
theorem physical_finite_chain_RTT (lam : ℝ) (hs : Complex.sin (lam : ℂ) ≠ 0)
    (b : ℕ → ℝ) (p s : ℂ) (n : ℕ) (q r : RowSpins n) :
    physicalIntertwiner lam (p-s) *
        forwardRows (fun j => physicalTile lam (b j) p)
          (fun j => physicalTile lam (b j) s) n q r =
      reverseRows (fun j => physicalTile lam (b j) p)
        (fun j => physicalTile lam (b j) s) n q r * physicalIntertwiner lam (p-s) := by
  rw [physicalIntertwiner_eq_R]
  apply finite_chain_RTT
  intro j
  unfold physicalTile
  have e : ((lam : ℂ)/2 + Complex.I * (p-b j)) -
      (lam/2 + Complex.I * (s-b j)) = Complex.I * (p-s) := by ring
  rw [← e]
  exact physical_local_RTT lam hs _ _

/-- An arbitrary joint auxiliary mark, as the marked auxiliary trace of the
ordered two-row product. -/
noncomputable def jointMarkedRow (D : Matrix PairSpin PairSpin ℂ)
    (F : Matrix PairSpin PairSpin ℂ) : ℂ := Matrix.trace (D * F)

/-- Conjugation of the joint mark on exchanging rows. The direction is fixed
explicitly: forward mark D becomes R D R⁻¹ on the reversed product. -/
theorem joint_mark_exchange (R : (Matrix PairSpin PairSpin ℂ)ˣ)
    (D F G : Matrix PairSpin PairSpin ℂ)
    (h : (R : Matrix PairSpin PairSpin ℂ) * F = G * R) :
    jointMarkedRow D F =
      jointMarkedRow ((R : Matrix PairSpin PairSpin ℂ) * D * (↑R⁻¹ : Matrix PairSpin PairSpin ℂ)) G := by
  have hg : G = (R : Matrix PairSpin PairSpin ℂ) * F * (↑R⁻¹ : Matrix PairSpin PairSpin ℂ) := by
    rw [h, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  unfold jointMarkedRow
  rw [hg]
  have e : ((R : Matrix PairSpin PairSpin ℂ) * D * (↑R⁻¹ : Matrix PairSpin PairSpin ℂ)) *
      ((R : Matrix PairSpin PairSpin ℂ) * F * (↑R⁻¹ : Matrix PairSpin PairSpin ℂ)) =
        (R : Matrix PairSpin PairSpin ℂ) * (D * F) * (↑R⁻¹ : Matrix PairSpin PairSpin ℂ) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (↑R⁻¹ : Matrix PairSpin PairSpin ℂ) (↑R : Matrix PairSpin PairSpin ℂ)
      (F * (↑R⁻¹ : Matrix PairSpin PairSpin ℂ)), Units.inv_mul, Matrix.one_mul]
  rw [e, Matrix.trace_units_conj]

end SixVertex
