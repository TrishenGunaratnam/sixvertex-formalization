import SixVertex.FinitePositiveMinimum
import SixVertex.PhysicalHoppingConnectivity

namespace SixVertex
noncomputable section

/-- Every allowed particle number has a concrete spin configuration. -/
theorem exists_minusCount_eq (L particles : ℕ) (h : particles≤L) :
    ∃ q : RowSpins L,minusCount L q=particles := by
  induction L generalizing particles with
  | zero =>
    have hp : particles=0 := by omega
    subst particles
    exact ⟨(),rfl⟩
  | succ L ih =>
    cases particles with
    | zero => exact ⟨plusSpins (L+1),minusCount_plus (L+1)⟩
    | succ p =>
      obtain ⟨q,hq⟩ := ih p (by omega)
      refine ⟨(1,q),?_⟩
      simp only [minusCount,hq]
      omega

abbrev ParticleConfigurations (L particles : ℕ) :=
  {q : RowSpins L // minusCount L q=particles}

/-- The exact real matrix of the actual Hamiltonian restricted to a
particle sector;the full matrix was already proved real. -/
def realSectorHamiltonian (lam eta : ℝ) (n particles : ℕ) :
    Matrix (ParticleConfigurations (n+2) particles) (ParticleConfigurations (n+2) particles) ℝ :=
  fun q r => (homogeneousLinkHamiltonian lam eta (n+1) q.val r.val).re

theorem realSectorHamiltonian_isHermitian (lam eta : ℝ) (n particles : ℕ) :
    (realSectorHamiltonian lam eta n particles).IsHermitian := by
  unfold Matrix.IsHermitian
  ext q r
  change (homogeneousLinkHamiltonian lam eta (n+1) r.val q.val).re=
    (homogeneousLinkHamiltonian lam eta (n+1) q.val r.val).re
  have h := congrArg Complex.re (congrArg
    (fun A : Matrix (RowSpins (n+2)) (RowSpins (n+2)) ℂ => A q.val r.val)
      (homogeneousLinkHamiltonian_isHermitian lam eta n).eq)
  simpa only [Matrix.conjTranspose_apply,Complex.star_def,Complex.conj_re] using h

/-- The actual Hamiltonian has a strictly positive simple minimum in
each valid particle sector. Its energy lower bound is uniform over all
real vectors in that finite sector. -/
theorem physical_sector_positive_simple_minimum (lam eta : ℝ) (h0 : 0<lam)
    (hpi : lam<Real.pi) (heta : 0<eta) (n particles : ℕ) (hp : particles≤n+2) :
    ∃ (mu : ℝ) (v : ParticleConfigurations (n+2) particles → ℝ), (∀ q,0<v q) ∧
      (realSectorHamiltonian lam eta n particles).mulVec v=mu • v ∧
      (∀ w : ParticleConfigurations (n+2) particles → ℝ,
        mu*(∑ q,(w q)^2)≤realMatrixEnergy (realSectorHamiltonian lam eta n particles) w) ∧
      (∀ w : ParticleConfigurations (n+2) particles → ℝ,
        (realSectorHamiltonian lam eta n particles).mulVec w=mu • w → ∃ c : ℝ,w=c • v) := by
  obtain ⟨q,hq⟩ := exists_minusCount_eq (n+2) particles hp
  letI : Nonempty (ParticleConfigurations (n+2) particles) := ⟨⟨q,hq⟩⟩
  refine exists_positive_simple_ground_state
    (realSectorHamiltonian lam eta n particles) (realSectorHamiltonian_isHermitian lam eta n particles)
    ?_ (physicalSectorHoppingGraph lam eta n particles)
    (physicalSectorHoppingGraph_preconnected lam eta h0 hpi heta n particles) ?_
  · intro u v huv
    apply homogeneousLinkHamiltonian_offdiag_re_nonpos lam eta h0 hpi heta.le n u.val v.val
    intro h
    exact huv (Subtype.ext h)
  · intro u v huv
    exact huv.2

end
end SixVertex
