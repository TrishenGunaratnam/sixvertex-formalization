import SixVertex.PhysicalTransferHopping
import SixVertex.PhysicalTransferSector
import SixVertex.MatrixPositivePowers

namespace SixVertex
noncomputable section

/-- The exact real matrix of the positive physical transfer row in one
particle sector. -/
def realPositiveSectorTransfer (lam : ℝ) (n particles : ℕ) :
    Matrix (ParticleConfigurations (n+2) particles) (ParticleConfigurations (n+2) particles) ℝ :=
  fun q r => (complexSectorTransfer lam n particles ((lam : ℂ)/2) q r).re

theorem realPositiveSectorTransfer_nonnegative (lam : ℝ) (h0 : 0<lam) (hpi : lam<Real.pi)
    (n particles : ℕ) (q r : ParticleConfigurations (n+2) particles) :
    0≤realPositiveSectorTransfer lam n particles q r :=
  (homogeneousPhysicalRow_midpoint_real_nonnegative lam h0 hpi (n+2) q.val r.val).2

theorem realPositiveSectorTransfer_diagonal_pos (lam : ℝ) (h0 : 0<lam) (hpi : lam<Real.pi)
    (n particles : ℕ) (q : ParticleConfigurations (n+2) particles) :
    0<realPositiveSectorTransfer lam n particles q q :=
  homogeneousPhysicalRow_midpoint_diagonal_re_pos lam h0 hpi (n+2) q.val

/-- The actual positive transfer restriction is exactly the scalar
embedding of its proved real matrix. -/
theorem complexSectorTransfer_midpoint_eq_real_map (lam : ℝ) (h0 : 0<lam)
    (hpi : lam<Real.pi) (n particles : ℕ) :
    complexSectorTransfer lam n particles ((lam : ℂ)/2)=
      (realPositiveSectorTransfer lam n particles).map Complex.ofReal := by
  ext q r
  apply Complex.ext
  · rfl
  · exact (homogeneousPhysicalRow_midpoint_real_nonnegative lam h0 hpi (n+2) q.val r.val).1

theorem complexify_real_matrix_pow {V : Type*} [Fintype V] [DecidableEq V]
    (B : Matrix V V ℝ) (N : ℕ) :
    (B.map Complex.ofReal)^N=(B^N).map Complex.ofReal := by
  induction N with
  | zero =>
    ext i j
    by_cases hij : i=j <;> simp [Matrix.one_apply,Matrix.map_apply,hij]
  | succ N ih =>
    rw [pow_succ,ih,pow_succ]
    ext i j
    simp only [Matrix.mul_apply,Matrix.map_apply,Complex.ofReal_sum,Complex.ofReal_mul]

/-- The actual physical transfer matrix is primitive in each particle
sector:a single strictly positive finite power is constructed. -/
theorem physical_positive_transfer_sector_primitive (lam : ℝ) (h0 : 0<lam)
    (hpi : lam<Real.pi) (n particles : ℕ) :
    ∃ N : ℕ,0<N ∧ ∀ q r : ParticleConfigurations (n+2) particles,
      0<(((complexSectorTransfer lam n particles ((lam : ℂ)/2))^N) q r).re := by
  let B := realPositiveSectorTransfer lam n particles
  have hB := realPositiveSectorTransfer_nonnegative lam h0 hpi n particles
  have hd := realPositiveSectorTransfer_diagonal_pos lam h0 hpi n particles
  obtain ⟨N,hN,hpow⟩ := connected_nonnegative_matrix_has_positive_power B hB hd
    (physicalPositiveTransferGraph lam n particles)
    (physicalPositiveTransferGraph_preconnected lam h0 hpi n particles)
    (fun _ _ h => h.2.1)
  refine ⟨N,hN,?_⟩
  intro q r
  rw [complexSectorTransfer_midpoint_eq_real_map lam h0 hpi,complexify_real_matrix_pow]
  exact hpow q r

end
end SixVertex
