import SixVertex.FiniteBetheEigen
import SixVertex.BetheRootBranch
import SixVertex.GaudinPositivity

/-!
# Complete Lemma 2.2: Finite Bethe data (`lem:bethe-data`)

All clauses are proved from the pinned finite-row matrices and explicit real
odd primitives. Fin n labels the roots in increasing order; j.val+1 is the
paper's one-based counting number. The twist is real and independent of the
complex deformation t = I*lambda used in the action proofs.

The eigenvalue is an entire continuation of the displayed factorized tau,
agreeing with that expression wherever its displayed denominators are
nonzero. The standard and physical eigenvector equalities hold at every
complex spectral argument. In particular, poles are proved removable;
no division-by-zero convention is used to fill them.

The real analytic root branch is constructed using Mathlib's proved
analytic inverse-function theorem. It retains ordering and satisfies
G dY/dtwist = 1/pi on a neighborhood. Positivity is finite-dimensional;
no inverse bound uniform in chain length is asserted or assumed.
-/
namespace SixVertex

open Filter Topology
open scoped Matrix

structure FiniteBetheData (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) : Prop where
  counting_on_shell : ∀ (n : ℕ) (Y : Fin n → ℝ) (twist : ℝ),
    ConsecutiveRoots lam b L Y twist → OnShell lam b L Y twist
  eigenvectors : ∀ (n : ℕ) (Y : Fin n → ℝ) (twist : ℝ),
    Function.Injective Y → OnShell lam b L Y twist →
    betheState (Complex.I*lam) (physical_deformation_ne_zero lam h0 hpi)
      (fun j => (b j : ℂ)) L (rootSet Y) ≠ 0 →
    BetheEigenvectorConclusion lam h0 hpi b L Y twist
  counting_derivative : ∀ (n : ℕ) (Y : Fin n → ℝ) (u : ℝ),
    HasDerivAt (countingXi lam b L Y) (countingSlope lam b L Y u) u
  jacobian : ∀ (n : ℕ) (Y : Fin n → ℝ),
    HasFDerivAt (countingSystem lam b L) (gaudinCLM lam b L Y) Y
  analytic_branch : ∀ (n : ℕ) (Y : Fin n → ℝ) (twist : ℝ),
    ConsecutiveRoots lam b L Y twist → (gaudinMatrix lam b L Y).det ≠ 0 →
    ∃ ψ : ℝ → Fin n → ℝ, ψ twist = Y ∧ AnalyticAt ℝ ψ twist ∧
      ∀ᶠ t in 𝓝 twist, ConsecutiveRoots lam b L (ψ t) t ∧ AnalyticAt ℝ ψ t ∧
        gaudinMatrix lam b L (ψ t) *ᵥ deriv ψ t = (fun _ => 1/Real.pi)
  positive_definite : Real.pi/2 ≤ lam → ∀ (n : ℕ) (Y : Fin n → ℝ),
    (gaudinMatrix lam b L Y).PosDef
  weights : ∀ (n : ℕ) (Y : Fin n → ℝ), (∀ j, 0 < countingSlope lam b L Y (Y j)) →
    gaudinMatrix lam b L Y * Matrix.diagonal (fun j => (countingSlope lam b L Y (Y j))⁻¹) =
      1 + Matrix.of (fun j k => kernelK lam (Y j-Y k) * (countingSlope lam b L Y (Y k))⁻¹)

/-- Section 2, Lemma 2.2, including every eigenvector, Jacobian, analytic
continuation, positivity and weighted-matrix clause. The chain convention
even L >= 4 is inherited from Section 1 of the pinned manuscript. -/
theorem finite_bethe_data (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) (hL : 4 ≤ L) (hEven : Even L) :
    FiniteBetheData lam h0 hpi b L := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n Y twist hY
    exact consecutiveRoots_onShell lam b L hEven Y twist h0 hpi hY
  · intro n Y twist hY hShell hM
    exact onShell_entire_eigenvectors lam h0 hpi b L hEven Y hY twist hShell hM
  · intro n Y u
    exact hasDerivAt_countingXi lam b L Y u h0 hpi
  · intro n Y
    exact hasFDerivAt_countingSystem lam b L Y h0 hpi
  · intro n Y twist hY hdet
    exact exists_analytic_root_branch lam b L h0 hpi Y twist hY hdet
  · intro hhalf n Y
    exact gaudinMatrix_posDef lam b L (by omega) Y hhalf hpi
  · intro n Y hpos
    exact gaudin_weight_identity lam b L Y hpos

end SixVertex
