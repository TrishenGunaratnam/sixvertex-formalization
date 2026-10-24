import SixVertex.PhysicalSectorMinimum

namespace SixVertex
noncomputable section

/-- A real eigenvector remains an eigenvector after the exact scalar
embedding of its matrix into the complex numbers. -/
theorem real_eigenvector_complexify {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (mu : ℝ) (v : V → ℝ) (hv : A.mulVec v=mu • v) :
    (A.map Complex.ofReal).mulVec (fun i => (v i : ℂ))=
      (mu : ℂ) • (fun i => (v i : ℂ)) := by
  funext i
  have h := congrArg Complex.ofReal (congrFun hv i)
  simpa only [Matrix.mulVec,dotProduct,Matrix.map_apply,Pi.smul_apply,smul_eq_mul,
    Complex.ofReal_sum,Complex.ofReal_mul] using h

/-- A simple real eigenspace of a real matrix is also a simple complex
eigenspace at the same real eigenvalue. -/
theorem real_simple_eigenspace_complexify {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (mu : ℝ) (v : V → ℝ)
    (hsimple : ∀ w : V → ℝ,A.mulVec w=mu • w → ∃ c : ℝ,w=c • v)
    (w : V → ℂ) (hw : (A.map Complex.ofReal).mulVec w=(mu : ℂ) • w) :
    ∃ c : ℂ,w=c • (fun i => (v i : ℂ)) := by
  have hre : A.mulVec (fun i => (w i).re)=mu • (fun i => (w i).re) := by
    funext i
    have h := congrArg Complex.re (congrFun hw i)
    simpa only [Matrix.mulVec,dotProduct,Matrix.map_apply,Pi.smul_apply,smul_eq_mul,
      Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using h
  have him : A.mulVec (fun i => (w i).im)=mu • (fun i => (w i).im) := by
    funext i
    have h := congrArg Complex.im (congrFun hw i)
    simpa only [Matrix.mulVec,dotProduct,Matrix.map_apply,Pi.smul_apply,smul_eq_mul,
      Complex.im_sum,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,zero_add] using h
  obtain ⟨a,ha⟩ := hsimple _ hre
  obtain ⟨b,hb⟩ := hsimple _ him
  refine ⟨(a : ℂ)+Complex.I*b,?_⟩
  funext i
  apply Complex.ext
  · simpa only [Pi.smul_apply,smul_eq_mul,Complex.mul_re,Complex.add_re,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,zero_mul,mul_zero,one_mul,zero_add,add_zero,sub_zero] using congrFun ha i
  · simpa only [Pi.smul_apply,smul_eq_mul,Complex.mul_im,Complex.add_im,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,zero_mul,mul_zero,one_mul,zero_add,add_zero,sub_zero] using congrFun hb i

/-- The real part of the exact finite Hermitian quadratic form. -/
def complexMatrixRealEnergy {V : Type*} [Fintype V] (B : Matrix V V ℂ) (w : V → ℂ) : ℝ :=
  (∑ i : V,∑ j : V,star (w i)*B i j*w j).re

/-- Real-matrix complex energy splits exactly into its real and
imaginary coordinate energies. -/
theorem complexMatrixRealEnergy_split {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (w : V → ℂ) :
    complexMatrixRealEnergy (A.map Complex.ofReal) w=
      realMatrixEnergy A (fun i => (w i).re)+realMatrixEnergy A (fun i => (w i).im) := by
  simp only [complexMatrixRealEnergy,realMatrixEnergy,Matrix.map_apply,Complex.re_sum,
    ← Finset.sum_add_distrib,Complex.mul_re,Complex.mul_im,Complex.star_def,
    Complex.conj_re,Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A real lower quadratic bound is also the full complex lower bound,
with the same eigenvalue and the ordinary complex Euclidean norm. -/
theorem real_quadratic_lower_bound_complexify {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (mu : ℝ)
    (hlower : ∀ v : V → ℝ,mu*(∑ i,(v i)^2)≤realMatrixEnergy A v) (w : V → ℂ) :
    mu*(∑ i : V,‖w i‖^2)≤complexMatrixRealEnergy (A.map Complex.ofReal) w := by
  rw [complexMatrixRealEnergy_split]
  have hn : (∑ i : V,‖w i‖^2)=(∑ i : V,(w i).re^2)+(∑ i : V,(w i).im^2) := by
    simp only [Complex.sq_norm,Complex.normSq_apply,← sq,Finset.sum_add_distrib]
  rw [hn,mul_add]
  exact add_le_add (hlower (fun i => (w i).re)) (hlower (fun i => (w i).im))

/-- The exact complex particle-sector restriction of the actual full
logarithmic Hamiltonian. -/
def complexSectorHamiltonian (lam eta : ℝ) (n particles : ℕ) :
    Matrix (ParticleConfigurations (n+2) particles) (ParticleConfigurations (n+2) particles) ℂ :=
  (homogeneousLinkHamiltonian lam eta (n+1)).submatrix Subtype.val Subtype.val

theorem complexSectorHamiltonian_eq_real_map (lam eta : ℝ) (n particles : ℕ) :
    complexSectorHamiltonian lam eta n particles=
      (realSectorHamiltonian lam eta n particles).map Complex.ofReal := by
  ext q r
  apply Complex.ext
  · rfl
  · exact homogeneousLinkHamiltonian_im_zero lam eta n q.val r.val

/-- The actual complex sector Hamiltonian has a positive real ground
vector,and its entire complex eigenspace at the minimum is its span. -/
theorem physical_sector_complex_positive_simple_minimum (lam eta : ℝ) (h0 : 0<lam)
    (hpi : lam<Real.pi) (heta : 0<eta) (n particles : ℕ) (hp : particles≤n+2) :
    ∃ (mu : ℝ) (v : ParticleConfigurations (n+2) particles → ℝ), (∀ q,0<v q) ∧
      (complexSectorHamiltonian lam eta n particles).mulVec (fun q => (v q : ℂ))=
        (mu : ℂ) • (fun q => (v q : ℂ)) ∧
      (∀ w : ParticleConfigurations (n+2) particles → ℂ,
        mu*(∑ q,‖w q‖^2)≤complexMatrixRealEnergy (complexSectorHamiltonian lam eta n particles) w) ∧
      (∀ w : ParticleConfigurations (n+2) particles → ℂ,
        (complexSectorHamiltonian lam eta n particles).mulVec w=(mu : ℂ) • w →
          ∃ c : ℂ,w=c • (fun q => (v q : ℂ))) := by
  obtain ⟨mu,v,hpos,heig,hlower,hsimple⟩ := physical_sector_positive_simple_minimum
    lam eta h0 hpi heta n particles hp
  refine ⟨mu,v,hpos,?_,?_,?_⟩
  · rw [complexSectorHamiltonian_eq_real_map]
    exact real_eigenvector_complexify _ _ _ heig
  · intro w
    rw [complexSectorHamiltonian_eq_real_map]
    exact real_quadratic_lower_bound_complexify _ mu hlower w
  · intro w hw
    rw [complexSectorHamiltonian_eq_real_map] at hw
    exact real_simple_eigenspace_complexify _ _ _ hsimple w hw

end
end SixVertex
