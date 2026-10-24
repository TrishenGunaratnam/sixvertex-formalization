import SixVertex.ActualFreeSlaterEigen
import Mathlib.LinearAlgebra.Matrix.Symmetric

namespace SixVertex
noncomputable section

/-- Two strictly positive eigenvectors of a real symmetric finite matrix
have the same eigenvalue. Nonemptiness is explicit. -/
theorem positive_symmetric_eigenvalues_equal {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : Matrix V V ℝ) (hA : A.IsSymm) (mu nu : ℝ) (v w : V → ℝ)
    (hvpos : ∀ i,0<v i) (hwpos : ∀ i,0<w i)
    (hv : A.mulVec v=mu • v) (hw : A.mulVec w=nu • w) : mu=nu := by
  have hpos : 0<v ⬝ᵥ w := Finset.sum_pos (fun i _ => mul_pos (hvpos i) (hwpos i)) Finset.univ_nonempty
  have h := hA.dotProduct_mulVec_comm (x:=v) (y:=w)
  rw [hw,hv] at h
  have he : nu*(v ⬝ᵥ w)=mu*(v ⬝ᵥ w) := by
    simpa only [dotProduct,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,mul_comm,mul_left_comm,mul_assoc] using h
  exact (mul_right_cancel₀ hpos.ne' he).symm

/-- Exact physical free Slater energy,as a real number. -/
def freeSlaterEnergy {particles : ℕ} (Y : Fin particles → ℝ) : ℝ :=
  ∑ k,-Real.cos (physicalRootMomentum (Real.pi/2) (Y k))

theorem actual_free_slater_real_eigenvector {particles : ℕ} (n : ℕ)
    (Y : Fin particles → ℝ) (hY : ConsecutiveRoots (Real.pi/2) (fun _ => 0) (n+2) Y 0) :
    (realSectorHamiltonian (Real.pi/2) (1/2) n particles).mulVec
      (fun q => (spinFreeSlaterVector (n+2) Y q).re)=
      freeSlaterEnergy Y • (fun q => (spinFreeSlaterVector (n+2) Y q).re) := by
  have he := actual_free_slater_eigenvector n Y hY
  have hc : (∑ k : Fin particles,-(Real.cos (physicalRootMomentum (Real.pi/2) (Y k)) : ℂ))=
      (freeSlaterEnergy Y : ℂ) := by simp [freeSlaterEnergy]
  rw [hc,complexSectorHamiltonian_eq_real_map] at he
  funext q
  have h := congrArg Complex.re (congrFun he q)
  simpa only [Matrix.mulVec,dotProduct,Matrix.map_apply,Pi.smul_apply,smul_eq_mul,
    Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using h

/-- The constructed Slater state is the ACTUAL physical free ground line:
its energy is a lower bound for every complex vector,and its entire complex
eigenspace is its span. This does not yet identify the ABA Bethe vector. -/
theorem actual_free_slater_ground_state {particles : ℕ} (n : ℕ) (hp : particles≤n+2)
    (Y : Fin particles → ℝ) (hY : ConsecutiveRoots (Real.pi/2) (fun _ => 0) (n+2) Y 0) :
    (∀ q : ParticleConfigurations (n+2) particles,
      (spinFreeSlaterVector (n+2) Y q).im=0 ∧ 0<(spinFreeSlaterVector (n+2) Y q).re) ∧
    (∀ w : ParticleConfigurations (n+2) particles → ℂ,
      freeSlaterEnergy Y*(∑ q,‖w q‖^2)≤
        complexMatrixRealEnergy (complexSectorHamiltonian (Real.pi/2) (1/2) n particles) w) ∧
    (∀ w : ParticleConfigurations (n+2) particles → ℂ,
      (complexSectorHamiltonian (Real.pi/2) (1/2) n particles).mulVec w=(freeSlaterEnergy Y : ℂ) • w →
      ∃ c : ℂ,w=c • spinFreeSlaterVector (n+2) Y) := by
  obtain ⟨q,hq⟩ := exists_minusCount_eq (n+2) particles hp
  letI : Nonempty (ParticleConfigurations (n+2) particles) := ⟨⟨q,hq⟩⟩
  obtain ⟨mu,v,hpos,hground,hlower,hsimple⟩ := physical_sector_complex_positive_simple_minimum
    (Real.pi/2) (1/2) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (by norm_num) n particles hp
  have hvreal : (realSectorHamiltonian (Real.pi/2) (1/2) n particles).mulVec v=mu • v := by
    rw [complexSectorHamiltonian_eq_real_map] at hground
    funext r
    have h := congrArg Complex.re (congrFun hground r)
    simpa only [Matrix.mulVec,dotProduct,Matrix.map_apply,Pi.smul_apply,smul_eq_mul,
      Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero] using h
  have hwpos (r : ParticleConfigurations (n+2) particles) :
      0<(spinFreeSlaterVector (n+2) Y r).re :=
    (spinFreeSlaterVector_positive (n+2) (by omega) Y hY r).2
  have hmu : mu=freeSlaterEnergy Y := positive_symmetric_eigenvalues_equal _
    (realSectorHamiltonian_isHermitian (Real.pi/2) (1/2) n particles).isSymm
    mu (freeSlaterEnergy Y) v (fun r => (spinFreeSlaterVector (n+2) Y r).re)
    hpos hwpos hvreal (actual_free_slater_real_eigenvector n Y hY)
  have he := actual_free_slater_eigenvector n Y hY
  have hc : (∑ k : Fin particles,-(Real.cos (physicalRootMomentum (Real.pi/2) (Y k)) : ℂ))=
      (freeSlaterEnergy Y : ℂ) := by simp [freeSlaterEnergy]
  rw [hc] at he
  obtain ⟨a,ha⟩ := hsimple (spinFreeSlaterVector (n+2) Y) (by simpa only [hmu] using he)
  have hane : a≠0 := by
    intro hz
    have hne := spinFreeSlaterVector_ne_zero (n+2) (by omega) hp Y hY
    rw [ha,hz,zero_smul] at hne
    exact hne rfl
  refine ⟨spinFreeSlaterVector_positive (n+2) (by omega) Y hY,?_,?_⟩
  · intro w
    rw [← hmu]
    exact hlower w
  · intro w hw
    obtain ⟨b,hb⟩ := hsimple w (by simpa only [hmu] using hw)
    refine ⟨b/a,?_⟩
    rw [hb,ha,smul_smul,div_mul_cancel₀ _ hane]

end
end SixVertex
