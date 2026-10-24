import SixVertex.FiniteRTT
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Instances.Matrix

namespace SixVertex

open scoped ComplexConjugate
open Filter Topology

noncomputable def diagonalJointMark (d : Fin 2 → ℂ) : Matrix PairSpin PairSpin ℂ :=
  Matrix.diagonal (fun i => d i.1 * d i.2)

theorem diagonalJoint_commutes (d : Fin 2 → ℂ) (a b c : ℂ) :
    sixMatrix a b c * diagonalJointMark d = diagonalJointMark d * sixMatrix a b c := by
  ext ⟨i,j⟩ ⟨k,l⟩
  simp only [diagonalJointMark, Matrix.diagonal_mul, Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [sixMatrix] <;> ring

theorem markedRow_diagonal (P : ℕ → Matrix PairSpin PairSpin ℂ)
    (n : ℕ) (d : Fin 2 → ℂ) :
    markedRow P n (Matrix.diagonal d) =
      d 0 • rowBlock P n 0 0 + d 1 • rowBlock P n 1 1 := by
  ext q r
  simp [markedRow, Fin.sum_univ_two, Matrix.diagonal_apply,
    Matrix.add_apply, Matrix.smul_apply]

theorem joint_diagonal_trace (d : Fin 2 → ℂ) (F : Matrix PairSpin PairSpin ℂ) :
    jointMarkedRow (diagonalJointMark d) F =
      d 0 * d 0 * F (0,0) (0,0) + d 0 * d 1 * F (0,1) (0,1) +
      (d 1 * d 0 * F (1,0) (1,0) + d 1 * d 1 * F (1,1) (1,1)) := by
  simp [jointMarkedRow, diagonalJointMark, Matrix.trace, Matrix.diagonal_mul,
    Fintype.sum_prod_type, Fin.sum_univ_two]

theorem diagonal_forward_trace (P Q : ℕ → Matrix PairSpin PairSpin ℂ)
    (n : ℕ) (d : Fin 2 → ℂ) (q r : RowSpins n) :
    (markedRow P n (Matrix.diagonal d) * markedRow Q n (Matrix.diagonal d)) q r =
      jointMarkedRow (diagonalJointMark d) (forwardRows P Q n q r) := by
  rw [markedRow_diagonal, markedRow_diagonal, joint_diagonal_trace]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, forwardRows]
  ring

theorem diagonal_reverse_trace (P Q : ℕ → Matrix PairSpin PairSpin ℂ)
    (n : ℕ) (d : Fin 2 → ℂ) (q r : RowSpins n) :
    (markedRow Q n (Matrix.diagonal d) * markedRow P n (Matrix.diagonal d)) q r =
      jointMarkedRow (diagonalJointMark d) (reverseRows P Q n q r) := by
  rw [markedRow_diagonal, markedRow_diagonal, joint_diagonal_trace]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, reverseRows]
  ring

theorem diagonal_rows_commute_of_unit_RTT
    (R : (Matrix PairSpin PairSpin ℂ)ˣ) (P Q : ℕ → Matrix PairSpin PairSpin ℂ)
    (n : ℕ) (d : Fin 2 → ℂ)
    (hRTT : ∀ q r : RowSpins n,
      (R : Matrix PairSpin PairSpin ℂ) * forwardRows P Q n q r =
        reverseRows P Q n q r * R)
    (hc : (R : Matrix PairSpin PairSpin ℂ) * diagonalJointMark d =
      diagonalJointMark d * R) :
    markedRow P n (Matrix.diagonal d) * markedRow Q n (Matrix.diagonal d) =
      markedRow Q n (Matrix.diagonal d) * markedRow P n (Matrix.diagonal d) := by
  have hmark : (R : Matrix PairSpin PairSpin ℂ) * diagonalJointMark d *
      (↑R⁻¹ : Matrix PairSpin PairSpin ℂ) = diagonalJointMark d := by
    rw [hc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  ext q r
  rw [diagonal_forward_trace, diagonal_reverse_trace]
  have h := joint_mark_exchange R (diagonalJointMark d)
    (forwardRows P Q n q r) (reverseRows P Q n q r) (hRTT q r)
  rwa [hmark] at h

theorem physical_diagonal_commute_of_isUnit (lam : ℝ) (hs : Complex.sin (lam : ℂ) ≠ 0)
    (b : ℕ → ℝ) (p s : ℂ) (n : ℕ) (d : Fin 2 → ℂ)
    (hunit : IsUnit (physicalIntertwiner lam (p-s))) :
    markedRow (fun j => physicalTile lam (b j) p) n (Matrix.diagonal d) *
        markedRow (fun j => physicalTile lam (b j) s) n (Matrix.diagonal d) =
      markedRow (fun j => physicalTile lam (b j) s) n (Matrix.diagonal d) *
        markedRow (fun j => physicalTile lam (b j) p) n (Matrix.diagonal d) := by
  rcases hunit with ⟨R,hR⟩
  apply diagonal_rows_commute_of_unit_RTT R
  · intro q r
    rw [hR]
    exact physical_finite_chain_RTT lam hs b p s n q r
  · rw [hR, physicalIntertwiner_eq_R, physicalR]
    exact diagonalJoint_commutes d _ _ _

theorem physicalTile_analytic (lam b : ℝ) (i j : PairSpin) (z : ℂ) :
    AnalyticAt ℂ (fun x => physicalTile lam b x i j) z := by
  have harg : AnalyticAt ℂ (fun x : ℂ => (lam : ℂ)/2 + Complex.I * (x-b)) z :=
    analyticAt_const.add (analyticAt_const.mul (analyticAt_id.sub analyticAt_const))
  unfold physicalTile physicalR sixMatrix
  split_ifs
  · exact (Complex.analyticAt_sin.comp (analyticAt_const.sub harg)).div_const
  · exact (Complex.analyticAt_sin.comp harg).div_const
  · exact analyticAt_const
  · exact analyticAt_const

theorem physical_rowBlock_analytic (lam : ℝ) (b : ℕ → ℝ)
    (n : ℕ) (a c : Fin 2) (q r : RowSpins n) (z : ℂ) :
    AnalyticAt ℂ (fun x => rowBlock (fun j => physicalTile lam (b j) x) n a c q r) z := by
  induction n generalizing b a c with
  | zero =>
    simp only [rowBlock]
    exact analyticAt_const
  | succ n ih =>
    simp only [rowBlock]
    apply Finset.analyticAt_fun_sum
    intro t ht
    exact (physicalTile_analytic lam (b 0) _ _ z).mul (ih (fun j => b (j+1)) t c q.2 r.2)

theorem physical_markedRow_analytic (lam : ℝ) (b : ℕ → ℝ) (n : ℕ)
    (D : Matrix (Fin 2) (Fin 2) ℂ) (q r : RowSpins n) (z : ℂ) :
    AnalyticAt ℂ (fun x => markedRow (fun j => physicalTile lam (b j) x) n D q r) z := by
  simp only [markedRow, Fin.sum_univ_two, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  exact ((analyticAt_const.mul (physical_rowBlock_analytic lam b n 0 0 q r z)).add
    (analyticAt_const.mul (physical_rowBlock_analytic lam b n 0 1 q r z))).add
    ((analyticAt_const.mul (physical_rowBlock_analytic lam b n 1 0 q r z)).add
      (analyticAt_const.mul (physical_rowBlock_analytic lam b n 1 1 q r z)))

theorem physicalR_analytic (lam : ℝ) (i j : PairSpin) (z : ℂ) :
    AnalyticAt ℂ (fun x => physicalR lam x i j) z := by
  unfold physicalR sixMatrix
  split_ifs
  · exact (Complex.analyticAt_sin.comp (analyticAt_const.sub analyticAt_id)).div_const
  · exact Complex.analyticAt_sin.div_const
  · exact analyticAt_const
  · exact analyticAt_const

theorem physicalIntertwiner_zero_unit (lam : ℝ) (hs : Complex.sin (lam : ℂ) ≠ 0) :
    IsUnit (physicalIntertwiner lam 0) := by
  have h : physicalIntertwiner lam 0 * physicalIntertwiner lam 0 = 1 := by
    simp only [physicalIntertwiner_eq_R, mul_zero, physicalR, sub_zero,
      Complex.sin_zero, div_self hs, zero_div]
    ext ⟨a,b⟩ ⟨c,d⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp [sixMatrix, Matrix.mul_apply,
        Fintype.sum_prod_type, Fin.sum_univ_two]
  exact ⟨⟨physicalIntertwiner lam 0, physicalIntertwiner lam 0, h, h⟩, rfl⟩

theorem physicalIntertwiner_continuous (lam : ℝ) (p : ℂ) :
    Continuous (fun s : ℂ => physicalIntertwiner lam (p-s)) := by
  simp_rw [physicalIntertwiner_eq_R]
  apply continuous_matrix
  intro i j
  have h : Continuous (fun u : ℂ => physicalR lam u i j) :=
    continuous_iff_continuousAt.mpr (fun z => (physicalR_analytic lam i j z).continuousAt)
  exact h.comp (continuous_const.mul (continuous_const.sub continuous_id))

/-- The complete diagonal-twist commutation clause, including singular
spectral differences. Local invertibility near p=s supplies an open set;
the complex analytic identity theorem then supplies every p,s. -/
theorem physical_diagonal_rows_commute (lam : ℝ) (hs : Complex.sin (lam : ℂ) ≠ 0)
    (b : ℕ → ℝ) (p s : ℂ) (n : ℕ) (d : Fin 2 → ℂ) :
    markedRow (fun j => physicalTile lam (b j) p) n (Matrix.diagonal d) *
        markedRow (fun j => physicalTile lam (b j) s) n (Matrix.diagonal d) =
      markedRow (fun j => physicalTile lam (b j) s) n (Matrix.diagonal d) *
        markedRow (fun j => physicalTile lam (b j) p) n (Matrix.diagonal d) := by
  have hdet : (physicalIntertwiner lam (p-p)).det ≠ 0 := by
    rw [sub_self]
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
      (physicalIntertwiner_zero_unit lam hs))
  have hU : ∀ᶠ t in 𝓝 p, IsUnit (physicalIntertwiner lam (p-t)) := by
    have h := (physicalIntertwiner_continuous lam p).matrix_det.continuousAt.eventually_ne hdet
    exact h.mono (fun t ht => (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr ht))
  ext q r
  have hfunc :
      (fun t : ℂ => (markedRow (fun j => physicalTile lam (b j) p) n (Matrix.diagonal d) *
        markedRow (fun j => physicalTile lam (b j) t) n (Matrix.diagonal d)) q r) =
      (fun t : ℂ => (markedRow (fun j => physicalTile lam (b j) t) n (Matrix.diagonal d) *
        markedRow (fun j => physicalTile lam (b j) p) n (Matrix.diagonal d)) q r) := by
    apply AnalyticOnNhd.eq_of_eventuallyEq (𝕜 := ℂ) (z₀ := p)
    · intro z hz
      simp only [Matrix.mul_apply]
      apply Finset.analyticAt_fun_sum
      intro t ht
      exact analyticAt_const.mul (physical_markedRow_analytic lam b n (Matrix.diagonal d) t r z)
    · intro z hz
      simp only [Matrix.mul_apply]
      apply Finset.analyticAt_fun_sum
      intro t ht
      exact (physical_markedRow_analytic lam b n (Matrix.diagonal d) q t z).mul analyticAt_const
    · exact hU.mono (fun t ht => congrArg (fun M => M q r)
        (physical_diagonal_commute_of_isUnit lam hs b p t n d ht))
  exact congrFun hfunc s

end SixVertex
