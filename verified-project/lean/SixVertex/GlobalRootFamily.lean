import SixVertex.GlobalRootExistence

namespace SixVertex
open Filter Topology Set

noncomputable def nonpositiveKernelRoots (b : ℕ → ℝ) (L : ℕ) (hL : 0 < L)
    (n : ℕ) (hfill : 2*n ≤ L) (lam : ℝ) : Fin n → ℝ := by
  classical
  exact if h : Real.pi/2 ≤ lam ∧ lam < Real.pi then
    Classical.choose (exists_unique_nonpositiveKernel_roots lam b L hL h.1 h.2 n hfill)
    else 0

theorem nonpositiveKernelRoots_spec (b : ℕ → ℝ) (L : ℕ) (hL : 0 < L)
    (n : ℕ) (hfill : 2*n ≤ L) (lam : ℝ) (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) :
    ConsecutiveRoots lam b L (nonpositiveKernelRoots b L hL n hfill lam) 0 := by
  classical
  unfold nonpositiveKernelRoots
  rw [dif_pos ⟨hhalf,hpi⟩]
  exact (Classical.choose_spec (exists_unique_nonpositiveKernel_roots lam b L hL hhalf hpi n hfill)).1

/-- The globally constructed roots form a real-analytic family throughout
the open negative-kernel regime, because every local chart agrees by uniqueness. -/
theorem nonpositiveKernelRoots_analyticAt (b : ℕ → ℝ) (L : ℕ) (hL : 0 < L)
    (n : ℕ) (hfill : 2*n ≤ L) (lam : ℝ) (hhalf : Real.pi/2 < lam) (hpi : lam < Real.pi) :
    AnalyticAt ℝ (nonpositiveKernelRoots b L hL n hfill) lam := by
  have hY := nonpositiveKernelRoots_spec b L hL n hfill lam hhalf.le hpi
  obtain ⟨ψ,hbase,ha,hnear⟩ := exists_analytic_parameter_branch_nonpositiveK lam b L hL hhalf.le hpi
    (nonpositiveKernelRoots b L hL n hfill lam) 0 hY
  apply ha.congr
  filter_upwards [hnear,lt_mem_nhds hhalf,gt_mem_nhds hpi] with a hsol hapos hapi
  exact consecutiveRoots_unique_nonpositiveK a b L hL hapos.le hapi 0 _ _ hsol.2.2.1
    (nonpositiveKernelRoots_spec b L hL n hfill a hapos.le hapi)

/-- Every constructed finite chain has positive counting density, a positive
Gaudin determinant, and its exact on-shell roots for every even width. -/
theorem nonpositiveKernelRoots_finite_data (b : ℕ → ℝ) (L : ℕ) (hL : 0 < L)
    (hEven : Even L) (n : ℕ) (hfill : 2*n ≤ L) (lam : ℝ)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) :
    OnShell lam b L (nonpositiveKernelRoots b L hL n hfill lam) 0 ∧
    (∀ u, 0 < countingSlope lam b L (nonpositiveKernelRoots b L hL n hfill lam) u) ∧
    0 < (gaudinMatrix lam b L (nonpositiveKernelRoots b L hL n hfill lam)).det := by
  have h0 : 0 < lam := by linarith [Real.pi_pos]
  refine ⟨consecutiveRoots_onShell lam b L hEven _ 0 h0 hpi
    (nonpositiveKernelRoots_spec b L hL n hfill lam hhalf hpi),?_,?_⟩
  · exact fun u => countingSlope_pos_nonpositiveK lam b L hL _ u hhalf hpi
  · exact (gaudinMatrix_posDef lam b L hL _ hhalf hpi).det_pos

/-- The analytic family extends from the right at the free-fermion endpoint.
This is analyticity within the physical half-interval, with no artificial
assumption about the chosen function on the other side. -/
theorem nonpositiveKernelRoots_analyticWithinAt (b : ℕ → ℝ) (L : ℕ) (hL : 0 < L)
    (n : ℕ) (hfill : 2*n ≤ L) (lam : ℝ) (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) :
    AnalyticWithinAt ℝ (nonpositiveKernelRoots b L hL n hfill) (Ico (Real.pi/2) Real.pi) lam := by
  have hY := nonpositiveKernelRoots_spec b L hL n hfill lam hhalf hpi
  obtain ⟨ψ,hbase,ha,hnear⟩ := exists_analytic_parameter_branch_nonpositiveK lam b L hL hhalf hpi
    (nonpositiveKernelRoots b L hL n hfill lam) 0 hY
  apply ha.analyticWithinAt.congr_of_eventuallyEq _ hbase.symm
  filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with a hsol haIn
  exact consecutiveRoots_unique_nonpositiveK a b L hL haIn.1 haIn.2 0 _ _
    (nonpositiveKernelRoots_spec b L hL n hfill a haIn.1 haIn.2) hsol.2.2.1

theorem nonpositiveKernelRoots_continuousOn (b : ℕ → ℝ) (L : ℕ) (hL : 0 < L)
    (n : ℕ) (hfill : 2*n ≤ L) :
    ContinuousOn (nonpositiveKernelRoots b L hL n hfill) (Ico (Real.pi/2) Real.pi) := by
  intro lam hlam
  exact (nonpositiveKernelRoots_analyticWithinAt b L hL n hfill lam hlam.1 hlam.2).continuousWithinAt

/-- For a fixed finite chain, compact parameter intervals give a genuine
uniform coordinate bound. The bound may depend on L, n and the site array. -/
theorem finite_roots_compact_parameter_bound (b : ℕ → ℝ) (L : ℕ) (hL : 0 < L)
    (n : ℕ) (hfill : 2*n ≤ L) (lamMax : ℝ) (hMax : lamMax < Real.pi) :
    ∃ M : ℝ, 0 < M ∧ ∀ lam ∈ Icc (Real.pi/2) lamMax, ∀ j,
      |nonpositiveKernelRoots b L hL n hfill lam j| ≤ M := by
  have hsub : Icc (Real.pi/2) lamMax ⊆ Ico (Real.pi/2) Real.pi :=
    fun lam hlam => ⟨hlam.1,lt_of_le_of_lt hlam.2 hMax⟩
  have hc := (nonpositiveKernelRoots_continuousOn b L hL n hfill).mono hsub
  obtain ⟨B,hB⟩ := isCompact_Icc.bddAbove_image hc.norm
  refine ⟨max B 1,lt_of_lt_of_le (by norm_num) (le_max_right B 1),?_⟩
  intro lam hlam j
  have hnorm : ‖nonpositiveKernelRoots b L hL n hfill lam‖ ≤ B :=
    hB (mem_image_of_mem _ hlam)
  have hj := norm_le_pi_norm (nonpositiveKernelRoots b L hL n hfill lam) j
  rw [Real.norm_eq_abs] at hj
  exact hj.trans (hnorm.trans (le_max_left B 1))

/-- On a compact parameter interval, any fixed pair of distinct finite-chain
roots stays a positive distance apart. No uniformity in L is asserted. -/
theorem finite_roots_compact_parameter_gap (b : ℕ → ℝ) (L : ℕ) (hL : 0 < L)
    (n : ℕ) (hfill : 2*n ≤ L) (lamMax : ℝ) (hMin : Real.pi/2 ≤ lamMax) (hMax : lamMax < Real.pi)
    (i j : Fin n) (hij : i < j) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ lam ∈ Icc (Real.pi/2) lamMax,
      delta ≤ nonpositiveKernelRoots b L hL n hfill lam j-nonpositiveKernelRoots b L hL n hfill lam i := by
  have hsub : Icc (Real.pi/2) lamMax ⊆ Ico (Real.pi/2) Real.pi :=
    fun lam hlam => ⟨hlam.1,lt_of_le_of_lt hlam.2 hMax⟩
  have hc := (nonpositiveKernelRoots_continuousOn b L hL n hfill).mono hsub
  have hi := (continuous_apply i).comp_continuousOn hc
  have hj := (continuous_apply j).comp_continuousOn hc
  obtain ⟨a,ha,hgap⟩ := isCompact_Icc.exists_isMinOn ⟨Real.pi/2,le_refl _,hMin⟩ (hj.sub hi)
  have hp := (nonpositiveKernelRoots_spec b L hL n hfill a ha.1 (lt_of_le_of_lt ha.2 hMax)).1 hij
  refine ⟨_,sub_pos.mpr hp,?_⟩
  intro lam hlam
  exact hgap hlam

end SixVertex
