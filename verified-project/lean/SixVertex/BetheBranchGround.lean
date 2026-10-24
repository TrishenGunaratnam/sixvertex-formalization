import SixVertex.BetheBranchHamiltonian
import SixVertex.PhysicalSectorPerron
import SixVertex.ActualFreeBetheGround

namespace SixVertex
open Filter Topology Set
noncomputable section

/-- Restrict a charge-preserving eigenvector equation to its exact finite
particle sector. The vector's support condition removes all terms outside the
sector from the full matrix-vector sum. -/
theorem complexSectorTransfer_restrict_eigenvector (lam : ℝ) (m particles : ℕ)
    (z tau : ℂ) (v : RowSpins (m+2) → ℂ)
    (hv : SpinSector (m+2) (particles : ℤ) v)
    (heig : (homogeneousPhysicalRow lam (m+2) z).mulVec v=tau • v) :
    (complexSectorTransfer lam m particles z).mulVec (fun q => v q.val)=
      tau • (fun q => v q.val) := by
  classical
  funext q
  simp only [Matrix.mulVec, dotProduct, complexSectorTransfer, Matrix.submatrix_apply]
  rw [sum_subtype_eq_full_of_zero_outside
    (fun r : RowSpins (m+2) => minusCount (m+2) r=particles)
    (fun r => homogeneousPhysicalRow lam (m+2) z q.val r*v r)
    (by
      intro r hr
      have hc : (minusCount (m+2) r : ℤ) ≠ particles := by omega
      rw [hv r hc, mul_zero])]
  exact congrFun heig q.val

/-- If the continued physical Bethe vector has strictly positive real
coordinates, its transfer eigenline is the actual positive Hamiltonian
ground-state line. Thus the remaining continuation step is reduced to proving
coordinatewise reality and positivity of this explicit vector. -/
theorem nonpositiveKernel_physicalBetheVector_ground_line_of_positive
    {m n : ℕ} (lam eta : ℝ) (heta : 0<eta)
    (hEven : Even (m+2)) (hfill : 2*n≤m+2)
    (hhalf : Real.pi/2≤lam) (hpi : lam<Real.pi)
    (hreal : ∀ q : ParticleConfigurations (m+2) n,
      (physicalBetheVector lam (fun _ => 0) (m+2)
        (nonpositiveKernelRoots (fun _ => 0) (m+2) (by omega) n hfill lam) q.val).im=0)
    (hpos : ∀ q : ParticleConfigurations (m+2) n,
      0<(physicalBetheVector lam (fun _ => 0) (m+2)
        (nonpositiveKernelRoots (fun _ => 0) (m+2) (by omega) n hfill lam) q.val).re) :
    ∃ (mu tau : ℝ) (v : ParticleConfigurations (m+2) n → ℝ) (c : ℂ),
      PhysicalSectorPerronData lam eta m n mu tau v ∧ c≠0 ∧
        (fun q => physicalBetheVector lam (fun _ => 0) (m+2)
          (nonpositiveKernelRoots (fun _ => 0) (m+2) (by omega) n hfill lam) q.val)=
          c • (fun q => (v q : ℂ)) := by
  classical
  let L : ℕ := (m+1)+1
  have hL : 0<L := by dsimp [L]; omega
  have h0 : 0<lam := lt_of_lt_of_le (by positivity : (0:ℝ)<Real.pi/2) hhalf
  let Y : Fin n → ℝ := nonpositiveKernelRoots (fun _ => 0) L hL n hfill lam
  have hroots := nonpositiveKernelRoots_spec (fun _ => 0) (m+2) hL n hfill lam hhalf hpi
  have hY : Function.Injective Y := hroots.1.injective
  have hfinite := nonpositiveKernelRoots_finite_data (fun _ => 0) (m+2) hL hEven n hfill
    lam hhalf hpi
  obtain ⟨q₀,hq₀⟩ := exists_minusCount_eq (m+2) n (by omega)
  let qInst : ParticleConfigurations (m+2) n := ⟨q₀,hq₀⟩
  letI : Nonempty (ParticleConfigurations (m+2) n) := ⟨qInst⟩
  have hVne : physicalBetheVector lam (fun _ => 0) (m+2) Y≠0 := by
    intro hz
    have he := congrArg (fun x : SpinHilbert (m+2) => x.ofLp qInst.val) hz
    have hre : (physicalBetheVector lam (fun _ => 0) (m+2) Y qInst.val).re=0 := by
      simpa [Y] using congrArg Complex.re he
    have hpq : 0<(physicalBetheVector lam (fun _ => 0) (m+2) Y qInst.val).re := by
      simpa [Y] using hpos qInst
    exact hpq.ne' hre
  have hBne : betheState (Complex.I*(lam : ℂ))
      (physical_deformation_ne_zero lam h0 hpi) (fun _ => 0) (m+2) (rootSet Y)≠0 :=
    betheState_ne_zero_of_physicalBetheVector lam h0 hpi (fun _ => 0) (m+2) Y hY hVne
  obtain ⟨rho,hrho,hgen,hstd,hphysical,hnonzero⟩ :=
    onShell_entire_eigenvectors lam h0 hpi (fun _ => 0) (m+2) hEven Y hY 0 hfinite.1 hBne
  let x₀ : ℂ := betheSwapCoordinate lam ((lam : ℂ)/2)
  let M : Matrix (RowSpins (m+2)) (RowSpins (m+2)) ℂ :=
    quantumGauge (m+2) * betheState (Complex.I*(lam : ℂ))
      (physical_deformation_ne_zero lam h0 hpi) (fun _ => 0) (m+2) (rootSet Y)
  have hrow : physicalTwistedRow lam (fun _ => 0) (m+2) 0 x₀=
      homogeneousPhysicalRow lam (m+2) ((lam : ℂ)/2) := by
    simpa [x₀] using physicalTwistedRow_swapCoordinate lam (m+2) ((lam : ℂ)/2)
  have hM_eig : homogeneousPhysicalRow lam (m+2) ((lam : ℂ)/2)*M=
      (((-1 : ℂ)^n)*rho x₀) • M := by
    have h := hphysical x₀
    rw [hrow] at h
    simpa [M,rootSet_card Y hY] using h
  let e : RowSpins (m+2) → ℂ := Pi.single (plusSpins (m+2)) 1
  have hcolumn : M.mulVec e=physicalBetheVector lam (fun _ => 0) (m+2) Y := by
    rw [show e=Pi.single (plusSpins (m+2)) 1 by rfl,Matrix.mulVec_single_one]
    funext q
    simpa [M,Y] using (physicalBetheVector_eq_betheState_column lam h0 hpi
      (fun _ => 0) (m+2) Y hY q).symm
  have hfull : (homogeneousPhysicalRow lam (m+2) ((lam : ℂ)/2)).mulVec
      (physicalBetheVector lam (fun _ => 0) (m+2) Y)=
        (((-1 : ℂ)^n)*rho x₀) • physicalBetheVector lam (fun _ => 0) (m+2) Y := by
    have h := congrArg (fun A : Matrix (RowSpins (m+2)) (RowSpins (m+2)) ℂ => A.mulVec e) hM_eig
    rw [← Matrix.mulVec_mulVec] at h
    simp only [Matrix.smul_mulVec] at h
    simpa [hcolumn] using h
  have hsector := complexSectorTransfer_restrict_eigenvector lam m n
    ((lam : ℂ)/2) (((-1 : ℂ)^n)*rho x₀)
    (physicalBetheVector lam (fun _ => 0) (m+2) Y)
    (physicalBetheVector_sector lam (fun _ => 0) (m+2) Y) hfull
  let w : ParticleConfigurations (m+2) n → ℝ := fun q =>
    (physicalBetheVector lam (fun _ => 0) (m+2) Y q.val).re
  have hcomplexVec : (fun q : ParticleConfigurations (m+2) n =>
      physicalBetheVector lam (fun _ => 0) (m+2) Y q.val)=
      (fun q => (w q : ℂ)) := by
    funext q
    apply Complex.ext
    · rfl
    · simpa [Y] using hreal q
  have hwpos : ∀ q : ParticleConfigurations (m+2) n,0<w q := by
    intro q
    simpa [w,Y] using hpos q
  let B := realPositiveSectorTransfer lam m n
  have hcomplex : (B.map Complex.ofReal).mulVec (fun q => (w q : ℂ))=
      (((-1 : ℂ)^n)*rho x₀) • (fun q => (w q : ℂ)) := by
    rw [← complexSectorTransfer_midpoint_eq_real_map lam h0 hpi m n]
    simpa [hcomplexVec] using hsector
  have hrealEig := (positive_real_eigenvector_complex_root_real B w hwpos
    (((-1 : ℂ)^n)*rho x₀) hcomplex).2
  have hwe : B.mulVec w=(((-1 : ℂ)^n*rho x₀).re) • w := by
    exact hrealEig
  obtain ⟨mu,tau,v,hdata,cR,hcR⟩ := positive_real_transfer_vector_is_perron_line
    lam eta h0 hpi heta m n (by omega) w hwpos _ hwe
  have hcne : cR≠0 := by
    intro hz
    have hz' := congrFun hcR qInst
    rw [hz] at hz'
    simp at hz'
    exact (hwpos qInst).ne' hz'
  have hline : (fun q : ParticleConfigurations (m+2) n =>
      physicalBetheVector lam (fun _ => 0) (m+2) Y q.val)=
      (cR : ℂ) • (fun q => (v q : ℂ)) := by
    rw [hcomplexVec]
    funext q
    have hq := congrFun hcR q
    simp only [Pi.smul_apply,smul_eq_mul] at hq ⊢
    simpa only [Complex.ofReal_mul] using congrArg Complex.ofReal hq
  refine ⟨mu,tau,v,(cR : ℂ),hdata,by exact_mod_cast hcne,?_⟩
  simpa [Y] using hline

/-- A fixed nonzero phase making the real parts strictly positive is enough
for the ground-line conclusion. The continued vector need not itself be real:
its exact real Hamiltonian eigenvalue makes the phased real part an eigenvector,
and the positive simple ground-state theorem identifies that eigenline. -/
theorem nonpositiveKernel_physicalBetheVector_ground_line_of_positiveRealPart
    {m n : ℕ} (lam eta : ℝ) (heta : 0<eta)
    (hEven : Even (m+2)) (hfill : 2*n≤m+2)
    (hhalf : Real.pi/2≤lam) (hpi : lam<Real.pi)
    (hpositiveRealPart : ∃ phase : ℂ, phase≠0 ∧ ∀ q : ParticleConfigurations (m+2) n,
      0<(phase*(physicalBetheVector lam (fun _ => 0) (m+2)
        (nonpositiveKernelRoots (fun _ => 0) (m+2) (by omega) n hfill lam) q.val)).re) :
    ∃ (mu : ℝ) (v : ParticleConfigurations (m+2) n → ℝ) (c : ℂ),
      (∀ q,0<v q) ∧
      (realSectorHamiltonian lam eta m n).mulVec v=mu • v ∧
      (∀ w : ParticleConfigurations (m+2) n → ℝ,
        mu*(∑ q,(w q)^2)≤realMatrixEnergy (realSectorHamiltonian lam eta m n) w) ∧
      (∀ w : ParticleConfigurations (m+2) n → ℝ,
        (realSectorHamiltonian lam eta m n).mulVec w=mu • w → ∃ a : ℝ,w=a • v) ∧
      c≠0 ∧
      (fun q => physicalBetheVector lam (fun _ => 0) (m+2)
        (nonpositiveKernelRoots (fun _ => 0) (m+2) (by omega) n hfill lam) q.val)=
        c • (fun q => (v q : ℂ)) := by
  classical
  let L : ℕ := (m+1)+1
  have hL : 0<L := by dsimp [L]; omega
  have h0 : 0<lam := lt_of_lt_of_le (by positivity : (0:ℝ)<Real.pi/2) hhalf
  let Y : Fin n → ℝ := nonpositiveKernelRoots (fun _ => 0) L hL n hfill lam
  obtain ⟨phase,hphase,hpositive⟩ := hpositiveRealPart
  obtain ⟨q₀,hq₀⟩ := exists_minusCount_eq (m+2) n (by omega)
  let qInst : ParticleConfigurations (m+2) n := ⟨q₀,hq₀⟩
  have hVne : physicalBetheVector lam (fun _ => 0) L Y≠0 := by
    intro hz
    have he := congrArg (fun x : SpinHilbert L => x.ofLp qInst.val) hz
    have hcoord : physicalBetheVector lam (fun _ => 0) L Y qInst.val=0 := by
      simpa using he
    have hre : (phase*(physicalBetheVector lam (fun _ => 0) L Y qInst.val)).re=0 := by
      rw [hcoord]
      simp
    have hpq : 0<(phase*(physicalBetheVector lam (fun _ => 0) L Y qInst.val)).re := by
      simpa [Y,L] using hpositive qInst
    exact hpq.ne' hre
  have hmatrix := nonpositiveKernel_hamiltonian_eigenline_of_nonzero
    (K:=m+1) (n:=n) lam eta hEven hfill hhalf hpi (by simpa [Y,L] using hVne)
  let B : Matrix (RowSpins L) (RowSpins L) ℂ :=
    betheState (Complex.I*(lam : ℂ)) (physical_deformation_ne_zero lam h0 hpi)
      (fun _ => 0) L (rootSet Y)
  let M : Matrix (RowSpins L) (RowSpins L) ℂ := quantumGauge L*B
  let E : ℝ := -eta*(2*Real.pi*∑ j,kernelS lam (Y j)-(L : ℝ)*Real.cot lam)
  have hmatrix' : homogeneousLinkHamiltonian lam eta (m+1)*M=(E : ℂ) • M := by
    simpa [M,B,Y,E,L,Complex.ofReal_mul] using hmatrix
  let e : RowSpins L → ℂ := Pi.single (plusSpins L) 1
  have hcolumn : M.mulVec e=physicalBetheVector lam (fun _ => 0) L Y := by
    rw [show e=Pi.single (plusSpins L) 1 by rfl,Matrix.mulVec_single_one]
    funext q
    have hroots := nonpositiveKernelRoots_spec (fun _ => 0) L hL n hfill lam hhalf hpi
    simpa [M,B,Y,L] using (physicalBetheVector_eq_betheState_column lam h0 hpi
      (fun _ => 0) L Y hroots.1.injective q).symm
  have hfull : (homogeneousLinkHamiltonian lam eta (m+1)).mulVec
      (physicalBetheVector lam (fun _ => 0) L Y)=(E : ℂ) •
        physicalBetheVector lam (fun _ => 0) L Y := by
    have h := congrArg (fun A : Matrix (RowSpins L) (RowSpins L) ℂ => A.mulVec e) hmatrix'
    rw [← Matrix.mulVec_mulVec] at h
    simp only [Matrix.smul_mulVec] at h
    simpa [hcolumn] using h
  let V₀ : ParticleConfigurations (m+2) n → ℂ := fun q =>
    physicalBetheVector lam (fun _ => 0) L Y q.val
  have hsector₀ : (complexSectorHamiltonian lam eta m n).mulVec V₀=(E : ℂ) • V₀ := by
    funext q
    rw [complexSectorHamiltonian_mulVec_eq_full,
      physicalSectorExtension_restriction_eq _ (physicalBetheVector_sector lam (fun _ => 0) L Y)]
    exact congrFun hfull q.val
  let V : ParticleConfigurations (m+2) n → ℂ := phase • V₀
  have hsector : (complexSectorHamiltonian lam eta m n).mulVec V=(E : ℂ) • V := by
    calc
      (complexSectorHamiltonian lam eta m n).mulVec V = phase •
          (complexSectorHamiltonian lam eta m n).mulVec V₀ := by
            simp only [V, Matrix.mulVec_smul]
      _ = phase • ((E : ℂ) • V₀) := by rw [hsector₀]
      _ = (E : ℂ) • V := by
            simp only [V, smul_smul]
            congr 1
            ring
  let w : ParticleConfigurations (m+2) n → ℝ := fun q => (V q).re
  have hwpos : ∀ q,0<w q := by
    intro q
    simpa [w,V,Pi.smul_apply,smul_eq_mul,Y,L] using hpositive q
  have hwEig : (realSectorHamiltonian lam eta m n).mulVec w=E • w := by
    rw [complexSectorHamiltonian_eq_real_map] at hsector
    funext q
    have h := congrArg Complex.re (congrFun hsector q)
    simpa only [Matrix.mulVec,dotProduct,Matrix.map_apply,Pi.smul_apply,smul_eq_mul,
      Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,
      sub_zero] using h
  letI : Nonempty (ParticleConfigurations (m+2) n) := ⟨qInst⟩
  obtain ⟨mu,v,hposG,hEigG,hLowerG,hSimpleG⟩ :=
    physical_sector_positive_simple_minimum lam eta h0 hpi heta m n (by omega)
  have hmuE : mu=E := positive_symmetric_eigenvalues_equal _
    (realSectorHamiltonian_isHermitian lam eta m n).isSymm mu E v w hposG hwpos hEigG hwEig
  have hsectorMu : (complexSectorHamiltonian lam eta m n).mulVec V=(mu : ℂ) • V := by
    simpa [V,hmuE] using hsector
  rw [complexSectorHamiltonian_eq_real_map] at hsectorMu
  have hline := real_simple_eigenspace_complexify (realSectorHamiltonian lam eta m n)
    mu v hSimpleG V hsectorMu
  have hcne : hline.choose≠0 := by
    intro hz
    have hzq := congrFun hline.choose_spec qInst
    rw [hz] at hzq
    have hre : (V qInst).re=0 := by
      simpa [V] using congrArg Complex.re hzq
    have hpq : 0<(V qInst).re := hwpos qInst
    exact hpq.ne' hre
  have hlineFun : V=hline.choose • (fun q => (v q : ℂ)) := hline.choose_spec
  have hlineOrig : V₀=(phase⁻¹*hline.choose) • (fun q => (v q : ℂ)) := by
    calc
      V₀ = phase⁻¹ • V := by
        funext q
        simp only [V,Pi.smul_apply,smul_eq_mul]
        rw [← mul_assoc, inv_mul_cancel₀ hphase]
        simp
      _ = phase⁻¹ • (hline.choose • (fun q => (v q : ℂ))) :=
        congrArg (fun f => phase⁻¹ • f) hlineFun
      _ = (phase⁻¹*hline.choose) • (fun q => (v q : ℂ)) := by rw [smul_smul]
  have hcoef : phase⁻¹*hline.choose≠0 := mul_ne_zero (inv_ne_zero hphase) hcne
  refine ⟨mu,v,phase⁻¹*hline.choose,hposG,hEigG,hLowerG,hSimpleG,hcoef,?_⟩
  simpa [V₀,Y,L] using hlineOrig

/-- The actual continued Bethe vector is the Hamiltonian ground line on a
relative neighborhood of the free point. The phase is fixed at the endpoint
by the free Slater identification; finite-coordinate continuity then preserves
strict positivity nearby. -/
theorem nonpositiveKernel_physicalBetheVector_ground_line_eventually_near_free
    {m n : ℕ} (eta : ℝ) (heta : 0<eta)
    (hEven : Even (m+2)) (hfill : 2*n≤m+2)
    (hSlavnov : SlavnovIdentity (Real.pi/2) (fun _ => 0) (m+2)
      (nonpositiveKernelRoots (fun _ => 0) (m+2) (by omega) n hfill (Real.pi/2)) 0) :
    ∀ᶠ lam in 𝓝[Ico (Real.pi/2) Real.pi] (Real.pi/2),
      ∃ (mu : ℝ) (v : ParticleConfigurations (m+2) n → ℝ) (c : ℂ),
        (∀ q,0<v q) ∧
        (realSectorHamiltonian lam eta m n).mulVec v=mu • v ∧
        (∀ w : ParticleConfigurations (m+2) n → ℝ,
          mu*(∑ q,(w q)^2)≤realMatrixEnergy (realSectorHamiltonian lam eta m n) w) ∧
        (∀ w : ParticleConfigurations (m+2) n → ℝ,
          (realSectorHamiltonian lam eta m n).mulVec w=mu • w → ∃ a : ℝ,w=a • v) ∧
        c≠0 ∧
        (fun q => physicalBetheVector lam (fun _ => 0) (m+2)
          (nonpositiveKernelRoots (fun _ => 0) (m+2) (by omega) n hfill lam) q.val)=
          c • (fun q => (v q : ℂ)) := by
  classical
  let S : Set ℝ := Ico (Real.pi/2) Real.pi
  let F : ℝ → SpinHilbert (m+2) := fun x => physicalBetheVector x (fun _ => 0)
    (m+2) (nonpositiveKernelRoots (fun _ => 0) (m+2) (by omega) n hfill x)
  have hS : Real.pi/2∈S := by
    change Real.pi/2≤Real.pi/2 ∧ Real.pi/2<Real.pi
    exact ⟨le_rfl,by linarith [Real.pi_pos]⟩
  have hFcont : ContinuousOn F S := by
    simpa [F,S] using nonpositiveKernelPhysicalBetheVector_continuousOn
      (fun _ => 0) (m+2) (by omega) n hfill
  have hroot0 := nonpositiveKernelRoots_spec (fun _ => 0) (m+2) (by omega)
    n hfill (Real.pi/2) le_rfl (by linarith [Real.pi_pos])
  obtain ⟨c,hc,hfree⟩ := actual_free_bethe_ground_line (particles:=n) m hEven (by omega)
    (nonpositiveKernelRoots (fun _ => 0) (m+2) (by omega) n hfill (Real.pi/2))
    hroot0 hSlavnov
  let phase : ℂ := c⁻¹
  have hphase : phase≠0 := inv_ne_zero hc
  have hphaseFree : ∀ q : ParticleConfigurations (m+2) n,
      phase*(F (Real.pi/2) q.val)=spinFreeSlaterVector (m+2)
        (nonpositiveKernelRoots (fun _ => 0) (m+2) (by omega) n hfill (Real.pi/2)) q := by
    intro q
    have hq := congrFun hfree q
    have hq' : F (Real.pi/2) q.val=c*spinFreeSlaterVector (m+2)
        (nonpositiveKernelRoots (fun _ => 0) (m+2) (by omega) n hfill (Real.pi/2)) q := by
      simpa only [F,Pi.smul_apply,smul_eq_mul] using hq
    calc
      phase*(F (Real.pi/2) q.val) = phase*(c*spinFreeSlaterVector (m+2)
          (nonpositiveKernelRoots (fun _ => 0) (m+2) (by omega) n hfill (Real.pi/2)) q) := by
            rw [hq']
      _ = spinFreeSlaterVector (m+2)
          (nonpositiveKernelRoots (fun _ => 0) (m+2) (by omega) n hfill (Real.pi/2)) q := by
            dsimp [phase]
            rw [← mul_assoc,inv_mul_cancel₀ hc,one_mul]
  have hFAt : ContinuousWithinAt F S (Real.pi/2) := hFcont _ hS
  have hposEvent : ∀ᶠ x in 𝓝[S] (Real.pi/2),
      ∀ q : ParticleConfigurations (m+2) n,0<(phase*(F x q.val)).re := by
    rw [Filter.eventually_all]
    intro q
    have hEvalCont : Continuous (fun v : SpinHilbert (m+2) => v q.val) :=
      PiLp.continuous_apply 2 (fun _ : RowSpins (m+2) => ℂ) q.val
    have heval : ContinuousWithinAt (fun x : ℝ => F x q.val) S (Real.pi/2) := by
      exact hEvalCont.continuousAt.comp_continuousWithinAt hFAt
    have hmul : ContinuousWithinAt (fun x : ℝ => phase*(F x q.val))
        S (Real.pi/2) := continuousWithinAt_const.mul heval
    have hreal : ContinuousWithinAt (fun x : ℝ => (phase*(F x q.val)).re)
        S (Real.pi/2) := by
      exact Complex.continuous_re.continuousAt.comp_continuousWithinAt hmul
    have hpositive0 : 0<(phase*(F (Real.pi/2) q.val)).re := by
      rw [hphaseFree q]
      exact (spinFreeSlaterVector_positive (m+2) (by omega)
        (nonpositiveKernelRoots (fun _ => 0) (m+2) (by omega) n hfill (Real.pi/2))
        hroot0 q).2
    exact hreal.eventually (lt_mem_nhds hpositive0)
  filter_upwards [hposEvent,eventually_mem_nhdsWithin] with lam hpos hlam
  have hhalf : Real.pi/2≤lam := hlam.1
  have hpi : lam<Real.pi := hlam.2
  obtain ⟨mu,v,c,hposG,hEigG,hLowerG,hSimpleG,hcG,hlineG⟩ :=
    nonpositiveKernel_physicalBetheVector_ground_line_of_positiveRealPart
      lam eta heta hEven hfill hhalf hpi ⟨phase,hphase,hpos⟩
  exact ⟨mu,v,c,hposG,hEigG,hLowerG,hSimpleG,hcG,hlineG⟩

end
end SixVertex
