import SixVertex.RootContinuation

namespace SixVertex
open Filter Topology
open scoped Matrix

/-- Distinct counting levels exclude root collisions without presupposing
that a solution is ordered or injective. -/
theorem countingTarget_strictMono (n : ℕ) (twist : ℝ) : StrictMono (countingTarget n twist) := by
  intro i j hij
  have hv : (i.val : ℝ) < j.val := by exact_mod_cast hij
  unfold countingTarget
  linarith

theorem countingSystem_solution_injective {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (twist : ℝ) (hY : countingSystem lam b L Y = countingTarget n twist) :
    Function.Injective Y := by
  intro i j hij
  apply (countingTarget_strictMono n twist).injective
  have hi := congrFun hY i
  have hj := congrFun hY j
  change countingXi lam b L Y (Y i) = _ at hi
  change countingXi lam b L Y (Y j) = _ at hj
  rw [hij] at hi
  exact hi.symm.trans hj

theorem countingSystem_solution_ordered_nonpositiveK {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi)
    (Y : Fin n → ℝ) (twist : ℝ) (hY : countingSystem lam b L Y = countingTarget n twist) :
    ConsecutiveRoots lam b L Y twist := by
  refine ⟨?_,hY⟩
  intro i j hij
  apply (countingXi_strictMono_nonpositiveK lam b L hL Y hhalf hpi).lt_iff_lt.mp
  change countingSystem lam b L Y i < countingSystem lam b L Y j
  rw [hY]
  exact countingTarget_strictMono n twist hij

theorem gaudin_nonsingular_nonpositiveK {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Y : Fin n → ℝ) :
    (gaudinMatrix lam b L Y).det ≠ 0 := by
  classical
  exact (gaudinMatrix_posDef lam b L hL Y hhalf hpi).det_pos.ne'

/-- Local continuation in lambda needs no additional nonsingularity
assumption in the negative-kernel regime. -/
theorem exists_analytic_parameter_branch_nonpositiveK {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi)
    (Y : Fin n → ℝ) (twist : ℝ) (hY : ConsecutiveRoots lam b L Y twist) :
    ∃ ψ : ℝ → Fin n → ℝ, ψ lam = Y ∧ AnalyticAt ℝ ψ lam ∧
      ∀ᶠ a in 𝓝 lam, 0 < a ∧ a < Real.pi ∧ ConsecutiveRoots a b L (ψ a) twist ∧ AnalyticAt ℝ ψ a :=
  exists_analytic_parameter_root_branch lam b L (by linarith [Real.pi_pos]) hpi Y twist hY
    (gaudin_nonsingular_nonpositiveK lam b L hL hhalf hpi Y)

/-- The finite roots constructed here have a real-analytic twist branch,
with the exact Gaudin derivative, without an assumed Gaudin determinant. -/
theorem exists_analytic_twist_branch_nonpositiveK {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi)
    (Y : Fin n → ℝ) (twist : ℝ) (hY : ConsecutiveRoots lam b L Y twist) :
    ∃ ψ : ℝ → Fin n → ℝ, ψ twist = Y ∧ AnalyticAt ℝ ψ twist ∧
      ∀ᶠ t in 𝓝 twist, ConsecutiveRoots lam b L (ψ t) t ∧ AnalyticAt ℝ ψ t ∧
        gaudinMatrix lam b L (ψ t) *ᵥ deriv ψ t = (fun _ => 1/Real.pi) :=
  exists_analytic_root_branch lam b L (by linarith [Real.pi_pos]) hpi Y twist hY
    (gaudin_nonsingular_nonpositiveK lam b L hL hhalf hpi Y)

/-- A genuine analytic family of finite real roots around the free-fermion
starting point, for every real array and every filling at most one half. -/
theorem exists_analytic_roots_near_freeFermion (b : ℕ → ℝ) (L : ℕ) (hL : 0 < L)
    (n : ℕ) (hfill : 2*n ≤ L) :
    ∃ ψ : ℝ → Fin n → ℝ,
      ConsecutiveRoots (Real.pi/2) b L (ψ (Real.pi/2)) 0 ∧ AnalyticAt ℝ ψ (Real.pi/2) ∧
      ∀ᶠ a in 𝓝 (Real.pi/2), 0 < a ∧ a < Real.pi ∧ ConsecutiveRoots a b L (ψ a) 0 ∧ AnalyticAt ℝ ψ a := by
  obtain ⟨Y,hY,hunique⟩ := exists_unique_freeFermion_roots b L hL n hfill
  obtain ⟨ψ,hbase,ha,hnear⟩ := exists_analytic_parameter_branch_nonpositiveK (Real.pi/2) b L hL
    (le_refl _) (by linarith [Real.pi_pos]) Y 0 hY
  exact ⟨ψ,by simpa only [hbase] using hY,ha,hnear⟩

end SixVertex
