import SixVertex.BetheSpectral
import SixVertex.BetheAnalyticEigenvalue

namespace SixVertex

/-- A real spectral value has no shifted-sinh singularities. -/
theorem real_insert_rootSet_regular {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Y : Fin n → ℝ) (u : ℝ) :
    BetheRegular (Complex.I*lam) (insert (u : ℂ) (rootSet Y)) := by
  classical
  have he : rootSet (Fin.cons u Y) = insert (u : ℂ) (rootSet Y) := by
    ext p
    simp [rootSet, Fin.exists_fin_succ, eq_comm]
  rw [← he]
  exact real_rootSet_regular lam h0 hpi (Fin.cons u Y)

theorem exists_real_fresh_spectral {n : ℕ} (Y : Fin n → ℝ) : ∃ u : ℝ, (u : ℂ) ∉ rootSet Y := by
  classical
  refine ⟨(∑ j, |Y j|)+1, ?_⟩
  intro h
  obtain ⟨j,hj,hjval⟩ := Finset.mem_image.mp h
  have hle : Y j ≤ ∑ k, |Y k| :=
    (le_abs_self _).trans (Finset.single_le_sum (fun k _ => abs_nonneg (Y k)) (Finset.mem_univ j))
  have he := Complex.ofReal_inj.mp hjval
  linarith

/-- The standard and physical vector conclusions, including the entire
extension of tau and the physical parity factor. -/
def BetheEigenvectorConclusion {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) (Y : Fin n → ℝ) (twist : ℝ) : Prop :=
  ∃ ρ : ℂ → ℂ, (∀ z, AnalyticAt ℂ ρ z) ∧
      (∀ x, x ∉ rootSet Y → BetheRegular (Complex.I*lam) (insert x (rootSet Y)) →
        vacuumA (Complex.I*lam) (fun j => (b j : ℂ)) x L ≠ 0 → ρ x = betheTau lam b L Y twist x) ∧
      (∀ x, twistedStandardRow (Complex.I*lam) (fun j => (b j : ℂ)) L twist x *
        betheState (Complex.I*lam) (physical_deformation_ne_zero lam h0 hpi)
          (fun j => (b j : ℂ)) L (rootSet Y) =
        ρ x • betheState (Complex.I*lam) (physical_deformation_ne_zero lam h0 hpi)
          (fun j => (b j : ℂ)) L (rootSet Y)) ∧
      (∀ x, physicalTwistedRow lam b L twist x *
        (quantumGauge L * betheState (Complex.I*lam) (physical_deformation_ne_zero lam h0 hpi)
          (fun j => (b j : ℂ)) L (rootSet Y)) =
        ((-1 : ℂ)^n * ρ x) • (quantumGauge L *
          betheState (Complex.I*lam) (physical_deformation_ne_zero lam h0 hpi)
            (fun j => (b j : ℂ)) L (rootSet Y))) ∧
      quantumGauge L * betheState (Complex.I*lam) (physical_deformation_ne_zero lam h0 hpi)
        (fun j => (b j : ℂ)) L (rootSet Y) ≠ 0

/-- Full standard and physical eigenvector statements, with an entire
eigenvalue agreeing with the paper's tau on its generic domain. -/
theorem onShell_entire_eigenvectors {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) (hEven : Even L) (Y : Fin n → ℝ) (hY : Function.Injective Y)
    (twist : ℝ) (hShell : OnShell lam b L Y twist)
    (hM : betheState (Complex.I*lam) (physical_deformation_ne_zero lam h0 hpi)
      (fun j => (b j : ℂ)) L (rootSet Y) ≠ 0) :
    BetheEigenvectorConclusion lam h0 hpi b L Y twist := by
  classical
  obtain ⟨u,hu⟩ := exists_real_fresh_spectral Y
  obtain ⟨ρ,hρ,heigen,hgen⟩ := balancedRoots_entire_eigenvalue
    (Complex.I*lam) (physical_deformation_ne_zero lam h0 hpi) (fun j => (b j : ℂ)) L twist (rootSet Y)
    (onShell_balancedRoots lam h0 hpi b L Y hY twist hShell) hM u hu
    (real_insert_rootSet_regular lam h0 hpi Y u)
  refine ⟨ρ,hρ,?_,heigen,?_,quantumGauge_mul_ne_zero L _ hM⟩
  · intro x hx hr ha
    rw [hgen x hx hr, betheTau_eq_abaEigenvalue lam b L Y hY twist x hx hr ha]
  · obtain ⟨k,hk⟩ := hEven
    have hL : L = 2*k := by omega
    clear hk
    subst L
    intro x
    have h := physical_eigenvector_of_standard lam (physical_deformation_ne_zero lam h0 hpi)
      b k twist (rootSet Y) x (ρ x) (heigen x)
    simpa only [rootSet_card Y hY] using h

end SixVertex
