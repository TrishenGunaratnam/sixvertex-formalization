import SixVertex.RootCompactness
import Mathlib.Topology.Connected.Clopen

namespace SixVertex
open Filter Topology Set

/-- Real limits of consecutive-root solutions still solve the exact
counting equations; ordering is recovered from strict counting monotonicity. -/
theorem exists_roots_of_parameter_limit (n : ℕ) (lam : ℕ → ℝ) (lam0 : ℝ)
    (b : ℕ → ℝ) (L : ℕ) (hL : 0 < L) (hfill : 2*n ≤ L) (Y : ℕ → Fin n → ℝ)
    (hhalf : Real.pi/2 ≤ lam0) (hpi : lam0 < Real.pi) (hLam : Tendsto lam atTop (𝓝 lam0))
    (hsolutions : ∀ a, ConsecutiveRoots (lam a) b L (Y a) 0) :
    ∃ Z : Fin n → ℝ, ConsecutiveRoots lam0 b L Z 0 := by
  have h0 : 0 < lam0 := by linarith [Real.pi_pos]
  obtain ⟨Z,φ,hφ,hZ⟩ := finite_roots_subsequence_compact n lam lam0 b L hfill Y h0 hpi hLam
    (fun a => (hsolutions a).2)
  have hp := (hLam.comp hφ.tendsto_atTop).prodMk_nhds hZ
  have hc := (contDiffAt_parameterCountingSystem b L n lam0 Z h0 hpi).continuousAt.tendsto.comp hp
  have ht : Tendsto (fun a => countingSystem (lam (φ a)) b L (Y (φ a))) atTop (𝓝 (countingTarget n 0)) := by
    have he : (fun a => countingSystem (lam (φ a)) b L (Y (φ a))) = fun _ => countingTarget n 0 :=
      funext (fun a => (hsolutions (φ a)).2)
    rw [he]
    exact tendsto_const_nhds
  have he : countingSystem lam0 b L Z = countingTarget n 0 := tendsto_nhds_unique hc ht
  exact ⟨Z,countingSystem_solution_ordered_nonpositiveK lam0 b L hL hhalf hpi Z 0 he⟩

/-- Global finite real-root construction in the entire negative-kernel
regime. Local analytic continuation is globalized by proved no-escape
compactness and connectedness, not by an assumed continuation principle. -/
theorem exists_unique_nonpositiveKernel_roots (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi)
    (n : ℕ) (hfill : 2*n ≤ L) :
    ∃! Y : Fin n → ℝ, ConsecutiveRoots lam b L Y 0 := by
  classical
  let C := Set.Icc (Real.pi/2) lam
  let P : Set C := {a | ∃ Y : Fin n → ℝ, ConsecutiveRoots a.val b L Y 0}
  have hclosed : IsClosed P := by
    apply IsSeqClosed.isClosed
    intro a a0 ha hconv
    choose Y hY using ha
    have hLam : Tendsto (fun i => (a i).val) atTop (𝓝 a0.val) :=
      continuous_subtype_val.continuousAt.tendsto.comp hconv
    exact exists_roots_of_parameter_limit n (fun i => (a i).val) a0.val b L hL hfill Y
      a0.property.1 (lt_of_le_of_lt a0.property.2 hpi) hLam hY
  have hopen : IsOpen P := by
    apply isOpen_iff_mem_nhds.mpr
    intro a ha
    change ∃ Y : Fin n → ℝ, ConsecutiveRoots a.val b L Y 0 at ha
    obtain ⟨Y,hY⟩ := ha
    obtain ⟨ψ,hbase,hAnalytic,hnear⟩ := exists_analytic_parameter_branch_nonpositiveK a.val b L hL
      a.property.1 (lt_of_le_of_lt a.property.2 hpi) Y 0 hY
    have hchart : Tendsto (fun x : C => x.val) (𝓝 a) (𝓝 a.val) :=
      (continuous_subtype_val : Continuous (fun x : C => x.val)).continuousAt.tendsto
    have hv : ∀ᶠ x : C in 𝓝 a, 0 < x.val ∧ x.val < Real.pi ∧
        ConsecutiveRoots x.val b L (ψ x.val) 0 ∧ AnalyticAt ℝ ψ x.val := hchart.eventually hnear
    exact hv.mono (fun x hx => ⟨ψ x.val,hx.2.2.1⟩)
  have hnonempty : P.Nonempty := by
    obtain ⟨Y,hY,hunique⟩ := exists_unique_freeFermion_roots b L hL n hfill
    exact ⟨⟨Real.pi/2,le_refl _,hhalf⟩,Y,hY⟩
  haveI : PreconnectedSpace C := Subtype.preconnectedSpace isPreconnected_Icc
  have hall : P = Set.univ := IsClopen.eq_univ ⟨hclosed,hopen⟩ hnonempty
  have hex : ∃ Y : Fin n → ℝ, ConsecutiveRoots lam b L Y 0 := by
    have hm : (⟨lam,hhalf,le_refl _⟩ : C) ∈ P := by rw [hall]; trivial
    exact hm
  obtain ⟨Y,hY⟩ := hex
  refine ⟨Y,hY,?_⟩
  intro Z hZ
  exact consecutiveRoots_unique_nonpositiveK lam b L hL hhalf hpi 0 Z Y hZ hY

end SixVertex
