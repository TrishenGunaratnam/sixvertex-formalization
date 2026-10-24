/- Proof tools for the ground-line and endpoint-inclusive quadrature clauses
of the root construction lemma. The full named statement remains partial. -/
import SixVertex.BetheBranchGround
import SixVertex.LipschitzQuadrature
import Mathlib.Topology.Connected.Clopen

namespace SixVertex
open Filter Topology Set MeasureTheory
open scoped NNReal
noncomputable section

/-- The absolute interaction kernel decreases away from the origin for both
signs of the physical kernel. -/
theorem kernelK_abs_radiallyAntitone_all (lam : ℝ) (h0 : 0<lam)
    (hpi : lam<Real.pi) : RadiallyAntitone (fun u=>|kernelK lam u|) := by
  intro u v huv
  by_cases hhalf : Real.pi/2≤lam
  · have hu := kernelK_nonpos lam u hhalf hpi
    have hv := kernelK_nonpos lam v hhalf hpi
    change |kernelK lam v|≤|kernelK lam u|
    rw [abs_of_nonpos hu,abs_of_nonpos hv]
    exact negative_kernelK_radiallyAntitone lam hhalf hpi u v huv
  · have hpU := kernelK_nonneg lam u h0 (le_of_not_ge hhalf)
    have hpV := kernelK_nonneg lam v h0 (le_of_not_ge hhalf)
    have hcos : 0≤Real.cos lam :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos]) (le_of_not_ge hhalf)
    have hsin : 0≤Real.sin (2*lam) := by
      rw [Real.sin_two_mul]
      have hsinLam : 0≤Real.sin lam := (Real.sin_pos_of_pos_of_lt_pi h0 hpi).le
      positivity
    have hrad := phase_fraction_radiallyAntitone lam (Real.sin (2*lam))
      (Real.sin_pos_of_pos_of_lt_pi h0 hpi).ne' hsin u v huv
    change |kernelK lam v|≤|kernelK lam u|
    rw [abs_of_nonneg hpV,abs_of_nonneg hpU]
    simpa only [kernelK,phaseDensity] using hrad

/-- A parameter-only linear bound on the homogeneous counting curvature.
On any fixed compact interval this becomes a relative-derivative bound as
soon as the counting density has its expected order-L lower bound. -/
theorem homogeneous_countingCurvature_linear_bound {n L : ℕ} (lam : ℝ)
    (h0 : 0<lam) (hpi : lam<Real.pi) (hfill : 2*n≤L)
    (X : Fin n→ℝ) (u : ℝ) :
    |countingCurvature lam (fun _=>0) L X u| ≤
      (L:ℝ)*(2/(Real.sin (lam/2))^2*kernelS lam 0+
        2/(Real.sin lam)^2*|kernelK lam 0|) := by
  let Cs := 2/(Real.sin (lam/2))^2
  let Ck := 2/(Real.sin lam)^2
  have hs0 : 0≤kernelS lam 0 := (kernelS_pos lam 0 h0 hpi).le
  have hk0 : 0≤|kernelK lam 0| := abs_nonneg _
  have hsC : 0≤Cs := by dsimp [Cs]; positivity
  have hkC : 0≤Ck := by dsimp [Ck]; positivity
  have hsBound : |kernelSPrime lam u|≤Cs*kernelS lam 0 := by
    have hder := kernelSPrime_relative_bound lam u h0 hpi
    have hrad := kernelS_radiallyAntitone lam h0 hpi 0 u (by simp)
    simpa [Cs,sub_zero] using hder.trans (mul_le_mul_of_nonneg_left hrad hsC)
  have hkBound (j : Fin n) :
      |kernelKPrime lam (u-X j)|≤Ck*|kernelK lam 0| := by
    have hder := kernelKPrime_relative_bound lam (u-X j) h0 hpi
    have hrad := kernelK_abs_radiallyAntitone_all lam h0 hpi 0 (u-X j) (by simp)
    simpa [Ck] using hder.trans (mul_le_mul_of_nonneg_left hrad hkC)
  have hn : (n:ℝ)≤(L:ℝ) := by
    have hn' : n≤L := by omega
    exact_mod_cast hn'
  unfold countingCurvature
  calc
    _≤|∑ a ∈ Finset.range L,kernelSPrime lam (u-0)|+
        |∑ j,kernelKPrime lam (u-X j)| := abs_sub _ _
    _≤(∑ a ∈ Finset.range L,|kernelSPrime lam (u-0)|)+
        ∑ j,|kernelKPrime lam (u-X j)| :=
      add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)
    _≤(L:ℝ)*(Cs*kernelS lam 0)+(n:ℝ)*(Ck*|kernelK lam 0|) := by
      have hfirst : (∑ a ∈ Finset.range L,|kernelSPrime lam (u-0)|)≤
          (L:ℝ)*(Cs*kernelS lam 0) := by
        calc
          _≤∑ a ∈ Finset.range L,Cs*kernelS lam 0 := by
            apply Finset.sum_le_sum
            intro a ha
            simpa only [sub_zero] using hsBound
          _=(L:ℝ)*(Cs*kernelS lam 0) := by simp
      have hsecond : (∑ j : Fin n,|kernelKPrime lam (u-X j)|)≤
          (n:ℝ)*(Ck*|kernelK lam 0|) := by
        calc
          _≤∑ j : Fin n,Ck*|kernelK lam 0| := by
            apply Finset.sum_le_sum
            intro j hj
            exact hkBound j
          _=(n:ℝ)*(Ck*|kernelK lam 0|) := by simp
      exact add_le_add hfirst hsecond
    _≤(L:ℝ)*(Cs*kernelS lam 0+Ck*|kernelK lam 0|) := by
      have hsecond := mul_le_mul_of_nonneg_right hn (mul_nonneg hkC hk0)
      nlinarith [hsecond]
    _=_ := by dsimp [Cs,Ck]

/-- The actual consecutive-root Bethe vector restricted to its particle sector. -/
def consecutiveBetheSectorVector {m n : ℕ} (hfill : 2*n≤m+2) (lam : ℝ) :
    ParticleConfigurations (m+2) n → ℂ := fun q =>
  physicalBetheVector lam (fun _ => 0) (m+2)
    (nonpositiveKernelRoots (fun _ => 0) (m+2) (by omega) n hfill lam) q.val

/-- The coordinate sum used to fix a projective normalization of the Bethe vector. -/
def consecutiveBetheSectorSum {m n : ℕ} (hfill : 2*n≤m+2) (lam : ℝ) : ℂ :=
  ∑ q, consecutiveBetheSectorVector hfill lam q

/-- After dividing by its coordinate sum, the Bethe vector lies in the closed
nonnegative real cone. The sum-one normalization rules out the zero vector. -/
def consecutiveBetheClosedCone {m n : ℕ} (hfill : 2*n≤m+2) (lam : ℝ) : Prop :=
  consecutiveBetheSectorSum hfill lam ≠ 0 ∧
    ∀ q, 0 ≤ (consecutiveBetheSectorVector hfill lam q /
      consecutiveBetheSectorSum hfill lam).re ∧
      (consecutiveBetheSectorVector hfill lam q /
        consecutiveBetheSectorSum hfill lam).im = 0

/-- Dividing a nonzero scalar multiple of a strictly positive real vector by
its coordinate sum removes the scalar and lands in the normalized cone. -/
theorem normalizedCone_of_positiveLine {α : Type*} [Fintype α] [Nonempty α]
    (F : α → ℂ) (v : α → ℝ) (c : ℂ) (hc : c≠0)
    (hv : ∀ q,0<v q) (hline : F=c • fun q => (v q : ℂ)) :
    (∑ q,F q)≠0 ∧ ∀ q,0≤(F q/(∑ i,F i)).re ∧ (F q/(∑ i,F i)).im=0 := by
  classical
  let T : ℝ := ∑ q,v q
  have hT : 0<T := Finset.sum_pos (fun q _ => hv q) Finset.univ_nonempty
  have hlineq (q : α) : F q=c*(v q : ℂ) := by
    have h := congrFun hline q
    simpa only [Pi.smul_apply,smul_eq_mul] using h
  have hsum : (∑ q,F q)=c*(T : ℂ) := by
    calc
      (∑ q,F q)=∑ q,c*(v q : ℂ) := by
        apply Finset.sum_congr rfl
        intro q _
        exact hlineq q
      _=c*(T : ℂ) := by simp [T,Finset.mul_sum]
  have hct : c*(T : ℂ)≠0 := mul_ne_zero hc (Complex.ofReal_ne_zero.mpr hT.ne')
  refine ⟨by rw [hsum]; exact hct,?_⟩
  intro q
  have hratio : F q/(∑ i,F i)=(v q/T : ℝ) := by
    rw [hlineq q,hsum]
    push_cast
    field_simp [hc,hT.ne']
    <;> ring
  have hpos : 0<v q/T := div_pos (hv q) hT
  rw [hratio]
  exact ⟨by simpa using hpos.le,by simp⟩

/-- Every coordinate of a normalized nonnegative vector has modulus at most
one, since its coordinates sum to one. -/
theorem normalizedCone_ratio_norm_le_one {α : Type*} [Fintype α]
    (F : α → ℂ) (hcone : (∑ q,F q)≠0 ∧
      ∀ q,0≤(F q/(∑ i,F i)).re ∧ (F q/(∑ i,F i)).im=0) (q : α) :
    ‖F q/(∑ i,F i)‖≤1 := by
  classical
  let S : ℂ := ∑ i,F i
  let f : α → ℝ := fun i => (F i/S).re
  have hsum : (∑ i,F i/S)=1 := by
    rw [← Finset.sum_div]
    simp [S,hcone.1]
  have hsumRe : (∑ i,f i)=1 := by
    have h := congrArg Complex.re hsum
    simpa [f,Complex.re_sum] using h
  have hnonneg (i : α) : 0≤f i := by
    simpa [f,S] using (hcone.2 i).1
  have hle : f q≤∑ i,f i :=
    Finset.single_le_sum (s:=Finset.univ) (f:=f)
      (fun i _ => hnonneg i) (Finset.mem_univ q)
  have hleone : f q≤1 := by simpa [hsumRe] using hle
  have hratio : F q/S=(f q:ℂ) := by
    apply Complex.ext
    · rfl
    · simpa [f,S] using (hcone.2 q).2
  calc
    ‖F q/(∑ i,F i)‖=‖(f q:ℂ)‖ := by simpa [S] using congrArg norm hratio
    _=|f q| := by simp
    _=f q := abs_of_nonneg (hnonneg q)
    _≤1 := hleone

/-- Coordinates of the unnormalized Bethe vector are dominated by its
coordinate sum on the normalized cone. -/
theorem normalizedCone_coordinate_norm_le {α : Type*} [Fintype α]
    (F : α → ℂ) (hcone : (∑ q,F q)≠0 ∧
      ∀ q,0≤(F q/(∑ i,F i)).re ∧ (F q/(∑ i,F i)).im=0) (q : α) :
    ‖F q‖≤‖∑ i,F i‖ := by
  have hS : (∑ i,F i)≠0 := hcone.1
  have hmul : (∑ i,F i)*(F q/(∑ i,F i))=F q := by
    rw [div_eq_mul_inv]
    calc
      (∑ i,F i)*(F q*(∑ i,F i)⁻¹)=F q*((∑ i,F i)*(∑ i,F i)⁻¹) := by ring
      _=F q := by simp [hS]
  calc
    ‖F q‖=‖(∑ i,F i)*(F q/(∑ i,F i))‖ := by rw [hmul]
    _=‖∑ i,F i‖*‖F q/(∑ i,F i)‖ := norm_mul _ _
    _≤‖∑ i,F i‖*1 := mul_le_mul_of_nonneg_left
      (normalizedCone_ratio_norm_le_one F hcone q) (norm_nonneg _)
    _=‖∑ i,F i‖ := by ring

/-- The closed normalized cone improves to strict positivity because the real
Hamiltonian is irreducible with strictly negative hopping entries. -/
theorem consecutiveBethe_closedCone_strictly_positive {m n : ℕ} (lam eta : ℝ)
    (heta : 0<eta) (hEven : Even (m+2)) (hfill : 2*n≤m+2)
    (hhalf : Real.pi/2≤lam) (hpi : lam<Real.pi)
    (hSlavnov : SlavnovIdentity lam (fun _ => 0) (m+2)
      (nonpositiveKernelRoots (fun _ => 0) (m+2) (by omega) n hfill lam) 0)
    (hcone : consecutiveBetheClosedCone hfill lam) :
    ∀ q, 0< (consecutiveBetheSectorVector hfill lam q /
      consecutiveBetheSectorSum hfill lam).re := by
  classical
  let V := consecutiveBetheSectorVector hfill lam
  let S := consecutiveBetheSectorSum hfill lam
  let phase : ℂ := S⁻¹
  let W : ParticleConfigurations (m+2) n → ℂ := fun q => phase*V q
  let w : ParticleConfigurations (m+2) n → ℝ := fun q => (W q).re
  have hS : S≠0 := by simpa [S] using hcone.1
  have hphase : phase≠0 := inv_ne_zero hS
  have hWratio (q : ParticleConfigurations (m+2) n) : W q=V q/S := by
    simp only [W, phase]
    rw [div_eq_mul_inv]
    ring
  have hWreal (q : ParticleConfigurations (m+2) n) : (W q).im=0 := by
    rw [hWratio]
    exact (hcone.2 q).2
  have hWnonneg (q : ParticleConfigurations (m+2) n) : 0≤w q := by
    change 0≤(W q).re
    rw [hWratio]
    exact (hcone.2 q).1
  have hsumW : ∑ q, W q=1 := by
    calc
      (∑ q, W q) = phase*(∑ q,V q) := by simp [W,Finset.mul_sum]
      _ = phase*S := by simp [S,V,consecutiveBetheSectorSum,consecutiveBetheSectorVector]
      _ = 1 := by simp [phase,S,hS]
  have hsumw : ∑ q, w q=1 := by
    have h := congrArg Complex.re hsumW
    simpa [w,Complex.re_sum] using h
  have hwne : w≠0 := by
    intro hz
    have hz' : (∑ q,w q)=0 := by simp [hz]
    rw [hsumw] at hz'
    norm_num at hz'
  let L : ℕ := (m+1)+1
  have hL : 0<L := by dsimp [L]; omega
  have h0 : 0<lam := lt_of_lt_of_le (by positivity : (0:ℝ)<Real.pi/2) hhalf
  let Y : Fin n → ℝ := nonpositiveKernelRoots (fun _ => 0) L hL n hfill lam
  let E : ℝ := -eta*(2*Real.pi*∑ j,kernelS lam (Y j)-(L : ℝ)*Real.cot lam)
  have hmatrix := nonpositiveKernel_hamiltonian_eigenline
    (K:=m+1) (n:=n) lam eta hEven hfill hhalf hpi hSlavnov
  let B : Matrix (RowSpins L) (RowSpins L) ℂ :=
    betheState (Complex.I*(lam : ℂ)) (physical_deformation_ne_zero lam h0 hpi)
      (fun _ => 0) L (rootSet Y)
  let M : Matrix (RowSpins L) (RowSpins L) ℂ := quantumGauge L*B
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
  have hV₀V : V₀=V := by
    funext q
    simp [V₀,V,consecutiveBetheSectorVector,Y,L]
  have hsector0 : (complexSectorHamiltonian lam eta m n).mulVec V₀=
      (E : ℂ) • V₀ := by
    funext q
    rw [complexSectorHamiltonian_mulVec_eq_full,
      physicalSectorExtension_restriction_eq _ (physicalBetheVector_sector lam (fun _ => 0) L Y)]
    exact congrFun hfull q.val
  have hsector0' : (complexSectorHamiltonian lam eta m n).mulVec V=
      (E : ℂ) • V := by
    rw [← hV₀V]
    exact hsector0
  have hsector : (complexSectorHamiltonian lam eta m n).mulVec W=
      (E : ℂ) • W := by
    rw [show W=phase • V by funext q; simp [W,Pi.smul_apply,smul_eq_mul]]
    rw [Matrix.mulVec_smul,hsector0']
    simp only [smul_smul]
    congr 1
    ring
  have hwEig : (realSectorHamiltonian lam eta m n).mulVec w=E • w := by
    have h := hsector
    rw [complexSectorHamiltonian_eq_real_map] at h
    funext q
    have hq := congrArg Complex.re (congrFun h q)
    simpa only [Matrix.mulVec,dotProduct,Matrix.map_apply,Pi.smul_apply,smul_eq_mul,
      Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,
      sub_zero] using hq
  have h0 : 0<lam := lt_of_lt_of_le (by positivity : (0:ℝ)<Real.pi/2) hhalf
  have hA : ∀ q r,q≠r → (realSectorHamiltonian lam eta m n) q r≤0 := by
    intro q r hqr
    apply homogeneousLinkHamiltonian_offdiag_re_nonpos lam eta h0 hpi heta.le m q.val r.val
    intro h
    exact hqr (Subtype.ext h)
  let G := physicalSectorHoppingGraph lam eta m n
  have hG : G.Preconnected := physicalSectorHoppingGraph_preconnected lam eta h0 hpi heta m n
  have hedge : ∀ q r,G.Adj q r → (realSectorHamiltonian lam eta m n) q r<0 := by
    intro q r hqr
    exact hqr.2
  have hstrict := nonnegative_eigenvector_strictly_positive
    (realSectorHamiltonian lam eta m n) hA G hG hedge w hWnonneg hwne E hwEig
  intro q
  change 0 < (V q / S).re
  rw [← hWratio q]
  exact hstrict q

/-- The FTC on a closed interval for an arbitrary globally Lipschitz real test. -/
theorem integral_deriv_lipschitz_Icc (f : ℝ → ℝ) (K : ℝ≥0)
    (hLip : LipschitzWith K f) (a b : ℝ) (hab : a≤b) :
    (∫ x in Icc a b, deriv f x)=f b-f a := by
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hab]
  exact hLip.lipschitzOnWith.absolutelyContinuousOnInterval.integral_deriv_eq_sub

/-- Integrating the derivative against one counting jump keeps both endpoint
terms, including a root exactly at the left endpoint. -/
theorem integral_deriv_lipschitz_jump_Icc (f : ℝ → ℝ) (K : ℝ≥0)
    (hLip : LipschitzWith K f) (a b y : ℝ) (hab : a≤b) :
    (∫ x in Icc a b, deriv f x*(Ici y).indicator (fun _ : ℝ => (1:ℝ)) x)=
      if y≤a then f b-f a else if y≤b then f b-f y else 0 := by
  simp_rw [← Set.indicator_mul_right (Ici y) (fun x => deriv f x)
    (fun _ : ℝ => (1:ℝ))]
  rw [integral_indicator measurableSet_Ici,Measure.restrict_restrict measurableSet_Ici]
  by_cases hya : y≤a
  · have he : Ici y∩Icc a b=Icc a b := by
      ext x
      simp only [mem_inter_iff,mem_Ici,mem_Icc]
      constructor
      · rintro ⟨hyx,hax,hxb⟩
        exact ⟨hax,hxb⟩
      · rintro ⟨hax,hxb⟩
        exact ⟨hya.trans hax,hax,hxb⟩
    rw [he]
    simp only [mul_one,if_pos hya]
    exact integral_deriv_lipschitz_Icc f K hLip a b hab
  · have hay : a<y := lt_of_not_ge hya
    by_cases hyb : y≤b
    · have he : Ici y∩Icc a b=Icc y b := by
        ext x
        simp only [mem_inter_iff,mem_Ici,mem_Icc]
        constructor
        · rintro ⟨hyx,hax,hxb⟩
          exact ⟨hyx,hxb⟩
        · rintro ⟨hyx,hxb⟩
          exact ⟨hyx,hay.le.trans hyx,hxb⟩
      rw [he]
      simp only [mul_one,if_neg hya,if_pos hyb]
      exact integral_deriv_lipschitz_Icc f K hLip y b hyb
    · have hby : b<y := lt_of_not_ge hyb
      have he : Ici y∩Icc a b=∅ := by
        ext x
        simp only [mem_inter_iff,mem_Ici,mem_Icc,Set.mem_empty_iff_false]
        constructor
        · rintro ⟨hyx,hax,hxb⟩
          linarith
        · intro hx
          exact hx.elim
      rw [he]
      simp [hya,hyb]

/-- Interval integration of a Lipschitz derivative against the counting
function, expressed as the finite collection of its boundary and jump terms. -/
theorem integral_deriv_rootCount_lipschitz_Icc {n : ℕ} (Y : Fin n → ℝ)
    (f : ℝ → ℝ) (K : ℝ≥0) (hLip : LipschitzWith K f)
    (a b : ℝ) (hab : a≤b) :
    (∫ x in Icc a b, deriv f x*(rootCountLe Y x : ℝ))=
      ∑ j : Fin n, if Y j≤a then f b-f a else if Y j≤b then f b-f (Y j) else 0 := by
  have hderiv : IntegrableOn (deriv f) (Icc a b) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact hLip.lipschitzOnWith.absolutelyContinuousOnInterval.intervalIntegrable_deriv.1
  simp_rw [rootCountLe_eq_sum_indicators,Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j hj
    exact integral_deriv_lipschitz_jump_Icc f K hLip a b (Y j) hab
  · intro j hj
    simp_rw [← Set.indicator_mul_right (Ici (Y j)) (fun x => deriv f x)
      (fun _ : ℝ => (1:ℝ))]
    exact (hderiv.mul_const 1).indicator measurableSet_Ici

def rootCountStrictlyBelow {n : ℕ} (Y : Fin n → ℝ) (u : ℝ) : ℕ :=
  (Finset.univ.filter (fun j => Y j<u)).card

theorem rootCountStrictlyBelow_gap {n : ℕ} (Y : Fin n → ℝ) (hY : StrictMono Y) (u : ℝ) :
    rootCountStrictlyBelow Y u≤rootCountLe Y u ∧
      rootCountLe Y u≤rootCountStrictlyBelow Y u+1 := by
  classical
  have hsub : (Finset.univ.filter (fun j : Fin n => Y j<u))⊆rootsAtMost Y u := by
    intro j hj
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,(Finset.mem_filter.mp hj).2.le⟩
  have h₁ : rootCountStrictlyBelow Y u≤rootCountLe Y u := by
    unfold rootCountStrictlyBelow rootCountLe
    exact Finset.card_le_card hsub
  by_cases hEq : ∃ j : Fin n,Y j=u
  · obtain ⟨j,hj⟩ := hEq
    have hlt : rootCountStrictlyBelow Y u=j.val := by
      unfold rootCountStrictlyBelow
      have hs : Finset.univ.filter (fun i : Fin n => Y i<u)=Finset.Iio j := by
        ext i
        simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Iio]
        constructor
        · intro hi
          apply hY.lt_iff_lt.mp
          exact lt_of_lt_of_eq hi hj.symm
        · intro hij
          have hi := hY hij
          rw [hj] at hi
          exact hi
      rw [hs]
      simp
    have hle : rootCountLe Y u=j.val+1 := by
      rw [← hj]
      exact rootCountLe_at_root Y hY j
    rw [hlt,hle]
    omega
  · have hs : Finset.univ.filter (fun j : Fin n => Y j<u)=rootsAtMost Y u := by
      ext j
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,rootsAtMost]
      constructor
      · exact fun hj => hj.le
      · intro hj
        by_contra hlt
        have hu : u≤Y j := le_of_not_gt hlt
        exact hEq ⟨j,le_antisymm hj hu⟩
    have hEqCount : rootCountStrictlyBelow Y u=rootCountLe Y u := by
      unfold rootCountStrictlyBelow rootCountLe
      rw [hs]
    rw [hEqCount]
    omega

/-- A local sawtooth bound tolerating an additive error in the primitive's
range. The exact root levels keep the interior error at one half. -/
theorem ordered_count_sawtooth_local_slack {n : ℕ} (Y : Fin n → ℝ) (hY : Monotone Y)
    (xi : ℝ → ℝ) (hxi : Monotone xi)
    (hlevels : ∀ j : Fin n,xi (Y j)=(j.val : ℝ)+1/2-(n : ℝ)/2)
    (u E : ℝ) (hE : 0≤E)
    (hlo : -(n : ℝ)/2-E≤xi u) (hhi : xi u≤(n : ℝ)/2+E) :
    |(rootCountLe Y u : ℝ)-(xi u+(n : ℝ)/2)|≤E+1/2 := by
  let clipped : ℝ→ℝ := fun x => max (-(n : ℝ)/2) (min ((n : ℝ)/2) (xi x))
  have hc : Monotone clipped := by
    intro x y hxy
    apply max_le_max le_rfl
    exact min_le_min le_rfl (hxi hxy)
  have hlevels' (j : Fin n) : clipped (Y j)=(j.val : ℝ)+1/2-(n : ℝ)/2 := by
    have hlo' : -(n : ℝ)/2≤(j.val : ℝ)+1/2-(n : ℝ)/2 := by
      have hj : 0≤(j.val : ℝ) := Nat.cast_nonneg _
      linarith
    have hhi' : (j.val : ℝ)+1/2-(n : ℝ)/2≤(n : ℝ)/2 := by
      have hj : (j.val : ℝ)+1≤(n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt j.isLt
      linarith
    dsimp [clipped]
    rw [hlevels j,min_eq_right hhi',max_eq_right hlo']
  have hlo' : -(n : ℝ)/2≤clipped u := le_max_left _ _
  have hhi' : clipped u≤(n : ℝ)/2 := by
    have hn : (0:ℝ)≤(n:ℝ) := Nat.cast_nonneg n
    exact max_le (by linarith) (min_le_left _ _)
  have hsaw := ordered_count_sawtooth_local Y hY clipped hc hlevels' u hlo' hhi'
  have hclip : |clipped u-xi u|≤E := by
    by_cases hlow : xi u < -(n : ℝ)/2
    · have hmin : min ((n : ℝ)/2) (xi u)≤-(n : ℝ)/2 :=
        (min_le_right _ _).trans (le_of_lt hlow)
      have heq : clipped u=-(n : ℝ)/2 := by simp [clipped,max_eq_left hmin]
      rw [heq]
      rw [abs_of_nonneg (by linarith : 0≤-(n : ℝ)/2-xi u)]
      linarith
    · by_cases hupp : (n : ℝ)/2<xi u
      · have heq : clipped u=(n : ℝ)/2 := by
          change max (-(n : ℝ)/2) (min ((n : ℝ)/2) (xi u))=(n : ℝ)/2
          rw [min_eq_left (le_of_lt hupp)]
          have hn : (0:ℝ)≤(n:ℝ) := Nat.cast_nonneg n
          exact max_eq_right (by linarith)
        rw [heq]
        rw [abs_sub_comm,abs_of_nonneg (by linarith : 0≤xi u-(n : ℝ)/2)]
        linarith
      · have hinside : xi u∈Icc (-(n : ℝ)/2) ((n : ℝ)/2) := ⟨le_of_not_gt hlow,le_of_not_gt hupp⟩
        change |max (-(n : ℝ)/2) (min ((n : ℝ)/2) (xi u))-xi u|≤E
        rw [min_eq_right hinside.2,max_eq_right hinside.1]
        simp [hE]
  have hid : (rootCountLe Y u : ℝ)-(xi u+(n : ℝ)/2)=
      ((rootCountLe Y u : ℝ)-(clipped u+(n : ℝ)/2))+(clipped u-xi u) := by ring
  rw [hid]
  calc
    _≤|((rootCountLe Y u : ℝ)-(clipped u+(n : ℝ)/2))|+|clipped u-xi u| := abs_add_le _ _
    _≤1/2+E := add_le_add hsaw hclip
    _=E+1/2 := by ring

/-- The ordered-root sawtooth estimate is local: monotonicity of the counting
phase is only needed between the roots and the point being counted. -/
theorem ordered_count_sawtooth_localOn_slack {n : ℕ} (Y : Fin n → ℝ)
    (hY : Monotone Y) (xi : ℝ → ℝ) (a b : ℝ) (hab : a≤b)
    (hxi : MonotoneOn xi (Icc a b)) (hroots : ∀ j : Fin n,Y j∈Icc a b)
    (hlevels : ∀ j : Fin n,xi (Y j)=(j.val : ℝ)+1/2-(n : ℝ)/2)
    (u E : ℝ) (hu : u∈Icc a b) (hE : 0≤E)
    (hlo : -(n : ℝ)/2-E≤xi u) (hhi : xi u≤(n : ℝ)/2+E) :
    |(rootCountLe Y u : ℝ)-(xi u+(n : ℝ)/2)|≤E+1/2 := by
  let clamp : ℝ→ℝ := fun x => max a (min b x)
  let xiExt : ℝ→ℝ := fun x => xi (clamp x)
  have hclampMono : Monotone clamp := by
    intro x y hxy
    dsimp [clamp]
    exact max_le_max le_rfl (min_le_min le_rfl hxy)
  have hclampMem (x : ℝ) : clamp x∈Icc a b := by
    constructor
    · exact le_max_left _ _
    · exact max_le hab (min_le_left _ _)
  have hclampEq (x : ℝ) (hx : x∈Icc a b) : clamp x=x := by
    dsimp [clamp]
    rw [min_eq_right hx.2,max_eq_right hx.1]
  have hxiExtMono : Monotone xiExt := by
    intro x y hxy
    exact hxi (hclampMem x) (hclampMem y) (hclampMono hxy)
  have huEq : xiExt u=xi u := by
    dsimp [xiExt]
    rw [hclampEq u hu]
  have hlevelsExt : ∀ j : Fin n,xiExt (Y j)=(j.val : ℝ)+1/2-(n : ℝ)/2 := by
    intro j
    dsimp [xiExt]
    rw [hclampEq (Y j) (hroots j)]
    exact hlevels j
  have hlo' : -(n : ℝ)/2-E≤xiExt u := by simpa [huEq] using hlo
  have hhi' : xiExt u≤(n : ℝ)/2+E := by simpa [huEq] using hhi
  rw [← huEq]
  exact ordered_count_sawtooth_local_slack Y hY xiExt hxiExtMono hlevelsExt u E hE hlo' hhi'

/-- The perturbed on-shell roots retain a bounded counting discrepancy
from their finite-interval continuum primitive on the occupied interval. -/
theorem weighted_rootCount_primitive_error_local {n : ℕ} (lam : ℝ) (h0 : 0<lam)
    (hhalf : Real.pi/2≤lam) (hpi : lam<Real.pi) (Q : ℝ) (L : ℕ) (hL : 0<L) (Y X : Fin n→ℝ)
    (R : ReferenceQuantileData lam h0 hpi Q L Y)
    (hroots : ConsecutiveRoots lam (fun _=>0) L X 0)
    (M radius : ℝ) (hM : 0<M) (hrad : 0≤radius)
    (hlower : ∀ u∈Icc (-Q) Q,M≤(L:ℝ)*finiteIntervalDensity lam h0 hpi Q u)
    (hclose : ∀ j,|X j-Y j|≤radius/((L:ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j)))
    (x : ℝ) (hx : x∈Icc (-Q) Q) :
    |(rootCountLe X x:ℝ)-(L:ℝ)*finiteIntervalCumulative lam h0 hpi Q x| ≤
      2*(Real.exp (kernelLogConstant lam*(radius/M))*radius*
        (kernelL1Mass (kernelK lam)+physicalReferenceKernelRowErrorConstant lam/M)+
        |1-2*lam/Real.pi|/2)+1/2 := by
  let E := Real.exp (kernelLogConstant lam*(radius/M))*radius*
    (kernelL1Mass (kernelK lam)+physicalReferenceKernelRowErrorConstant lam/M)+
    |1-2*lam/Real.pi|/2
  let P : ℝ→ℝ := fun u => (L:ℝ)*finiteIntervalCumulative lam h0 hpi Q u
  let xi : ℝ→ℝ := countingXi lam (fun _=>0) L X
  have hE : 0≤E := by
    have hk := kernelLogConstant_nonneg lam
    have hr := kernelL1Mass_nonneg (kernelK lam)
    have hb := physicalReferenceKernelRowErrorConstant_nonneg lam h0
    dsimp [E]
    exact add_nonneg
      (mul_nonneg (mul_nonneg (Real.exp_pos _).le hrad)
        (add_nonneg hr (div_nonneg hb hM.le)))
      (div_nonneg (abs_nonneg _) (by norm_num))
  have hprim : |xi x-(P x-(n:ℝ)/2)|≤E := by
    exact weighted_configuration_counting_primitive_error_all lam h0 hpi Q L Y X R
      M radius hM hrad hlower hclose x
  have hPmono : Monotone P := by
    intro u v huv
    dsimp [P]
    exact mul_le_mul_of_nonneg_left
      ((finiteIntervalCumulative_strictMono_all lam h0 hpi Q).monotone huv)
      (Nat.cast_nonneg L)
  have hPa : P (-Q)=0 := by
    dsimp [P]
    rw [finiteIntervalCumulative_left,mul_zero]
  have hPb : P Q=(n:ℝ) := by
    dsimp [P]
    rw [finiteIntervalCumulative_right lam h0 hpi Q R.interval_nonneg,R.mass]
  have hPlo : 0≤P x := by have h:=hPmono hx.1; rw [hPa] at h; exact h
  have hPhi : P x≤(n:ℝ) := by have h:=hPmono hx.2; rw [hPb] at h; exact h
  have hxiRange : -(n:ℝ)/2-E≤xi x ∧ xi x≤(n:ℝ)/2+E := by
    have hh := abs_le.mp hprim
    constructor <;> dsimp [xi] <;> dsimp [P] at hh ⊢ <;> linarith
  have hlevels : ∀ j : Fin n,xi (X j)=(j.val:ℝ)+1/2-(n:ℝ)/2 := by
    intro j
    have ht : xi (X j)=countingTarget n 0 j := congrFun hroots.2 j
    calc
      xi (X j)=countingTarget n 0 j := ht
      _=(j.val:ℝ)+1/2-(n:ℝ)/2 := by unfold countingTarget; push_cast; ring
  have hsaw := ordered_count_sawtooth_local_slack X hroots.1.monotone xi
    (countingXi_strictMono_nonpositiveK lam (fun _=>0) L hL X hhalf hpi).monotone
    hlevels x E hE hxiRange.1 hxiRange.2
  have hxierr : |xi x+(n:ℝ)/2-P x|≤E := by
    rw [show xi x+(n:ℝ)/2-P x=xi x-(P x-(n:ℝ)/2) by ring]
    exact hprim
  have hid : (rootCountLe X x:ℝ)-P x=
      ((rootCountLe X x:ℝ)-(xi x+(n:ℝ)/2))+(xi x+(n:ℝ)/2-P x) := by ring
  rw [hid]
  calc
    _≤|((rootCountLe X x:ℝ)-(xi x+(n:ℝ)/2))|+|xi x+(n:ℝ)/2-P x| := abs_add_le _ _
    _≤(E+1/2)+E := add_le_add hsaw hxierr
    _=2*E+1/2 := by ring

/-- On a dense occupied window, the actual counting function has the same
bounded primitive discrepancy for either sign of the interaction kernel.
For the positive-kernel case only local positivity of the counting slope is
used; tails outside the root window do not enter the argument. -/
theorem weighted_rootCount_primitive_error_local_all {n : ℕ} (lam : ℝ)
    (h0 : 0<lam) (hpi : lam<Real.pi) (Q : ℝ) (L : ℕ) (hL : 0<L)
    (Y X : Fin n→ℝ) (R : ReferenceQuantileData lam h0 hpi Q L Y)
    (hroots : ConsecutiveRoots lam (fun _=>0) L X 0)
    (M radius : ℝ) (hM : 0<M) (hrad : 0≤radius)
    (hlower : ∀ u∈Icc (-Q) Q,M≤(L:ℝ)*finiteIntervalDensity lam h0 hpi Q u)
    (hclose : ∀ j,|X j-Y j|≤radius/((L:ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j)))
    (hlarge : kernelL1Mass (kernelKPrime lam)/2+
      (kernelLogConstant lam*Real.exp (kernelLogConstant lam*(radius/M))*radius)*
        (kernelL1Mass (kernelK lam)+physicalReferenceKernelRowErrorConstant lam/M) <
      M*Real.exp (-(physicalDensityLogConstant lam*(radius/M))))
    (x : ℝ) (hx : x∈Icc (-Q) Q) :
    |(rootCountLe X x:ℝ)-(L:ℝ)*finiteIntervalCumulative lam h0 hpi Q x| ≤
      2*(Real.exp (kernelLogConstant lam*(radius/M))*radius*
        (kernelL1Mass (kernelK lam)+physicalReferenceKernelRowErrorConstant lam/M)+
        |1-2*lam/Real.pi|/2)+1/2 := by
  let E := Real.exp (kernelLogConstant lam*(radius/M))*radius*
    (kernelL1Mass (kernelK lam)+physicalReferenceKernelRowErrorConstant lam/M)+
      |1-2*lam/Real.pi|/2
  let P : ℝ→ℝ := fun u => (L:ℝ)*finiteIntervalCumulative lam h0 hpi Q u
  let xi : ℝ→ℝ := countingXi lam (fun _=>0) L X
  have hE : 0≤E := by
    dsimp [E]
    exact add_nonneg
      (mul_nonneg (mul_nonneg (Real.exp_pos _).le hrad)
        (add_nonneg (kernelL1Mass_nonneg _) (div_nonneg
          (physicalReferenceKernelRowErrorConstant_nonneg lam h0) hM.le)))
      (div_nonneg (abs_nonneg _) (by norm_num))
  have hprim : |xi x-(P x-(n:ℝ)/2)|≤E := by
    exact weighted_configuration_counting_primitive_error_all lam h0 hpi Q L Y X R
      M radius hM hrad hlower hclose x
  have hPmono : Monotone P := by
    intro u v huv
    dsimp [P]
    exact mul_le_mul_of_nonneg_left
      ((finiteIntervalCumulative_strictMono_all lam h0 hpi Q).monotone huv)
      (Nat.cast_nonneg L)
  have hPa : P (-Q)=0 := by dsimp [P]; rw [finiteIntervalCumulative_left,mul_zero]
  have hPb : P Q=(n:ℝ) := by
    dsimp [P]
    rw [finiteIntervalCumulative_right lam h0 hpi Q R.interval_nonneg,R.mass]
  have hPlo : 0≤P x := by have hh:=hPmono hx.1; rw [hPa] at hh; exact hh
  have hPhi : P x≤(n:ℝ) := by have hh:=hPmono hx.2; rw [hPb] at hh; exact hh
  have hxiRange : -(n:ℝ)/2-E≤xi x ∧ xi x≤(n:ℝ)/2+E := by
    have hh:=abs_le.mp hprim
    constructor <;> dsimp [xi,P] at hh ⊢ <;> linarith
  let a := -Q-radius/M
  let b := Q+radius/M
  have hab : a≤b := by
    dsimp [a,b]
    have hn:=div_nonneg hrad hM.le
    linarith [R.interval_nonneg]
  have hrootLoc (j : Fin n) : X j∈Icc a b := by
    have hw : M≤(L:ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j) :=
      hlower (Y j) ⟨(R.location j).1.le,(R.location j).2.le⟩
    have hwp : 0<(L:ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j) := hM.trans_le hw
    have hdisp : |X j-Y j|≤radius/M :=
      (hclose j).trans (div_le_div₀ hrad le_rfl hM hw)
    have hYlo := (R.location j).1
    have hYhi := (R.location j).2
    have hdisp' := abs_le.mp hdisp
    constructor <;> dsimp [a,b] <;> linarith
  have hpos : ∀ u∈Icc a b,0<countingSlope lam (fun _=>0) L X u := by
    intro u hu
    dsimp [a,b] at hu
    exact weighted_configuration_countingSlope_pos_expanded_all lam h0 hpi Q L Y X R M hM
      hlower radius hrad hclose hlarge u hu
  have hxiMono : MonotoneOn xi (Icc a b) := by
    apply (strictMonoOn_of_deriv_pos (convex_Icc a b) (by
      intro u _
      exact (hasDerivAt_countingXi lam (fun _=>0) L X u h0 hpi).continuousAt.continuousWithinAt)
      (by
        intro u hu
        rw [(hasDerivAt_countingXi lam (fun _=>0) L X u h0 hpi).deriv]
        exact hpos u (interior_subset hu))).monotoneOn
  have hlevels : ∀ j : Fin n,xi (X j)=(j.val:ℝ)+1/2-(n:ℝ)/2 := by
    intro j
    have hh := congrFun hroots.2 j
    change countingXi lam (fun _=>0) L X (X j)=_ at hh
    dsimp [xi]
    rw [hh]
    unfold countingTarget
    push_cast
    ring
  have hx' : x∈Icc a b := by
    constructor <;> dsimp [a,b] <;>
      have hn:=div_nonneg hrad hM.le <;> linarith [hx.1,hx.2,R.interval_nonneg]
  have hsaw := ordered_count_sawtooth_localOn_slack X hroots.1.monotone xi a b hab
    hxiMono hrootLoc hlevels x E hx' hE hxiRange.1 hxiRange.2
  have hxierr : |xi x+(n:ℝ)/2-P x|≤E := by
    rw [show xi x+(n:ℝ)/2-P x=xi x-(P x-(n:ℝ)/2) by ring]
    exact hprim
  have hid : (rootCountLe X x:ℝ)-P x=
      ((rootCountLe X x:ℝ)-(xi x+(n:ℝ)/2))+(xi x+(n:ℝ)/2-P x) := by ring
  rw [hid]
  calc
    _≤|((rootCountLe X x:ℝ)-(xi x+(n:ℝ)/2))|+|xi x+(n:ℝ)/2-P x| := abs_add_le _ _
    _≤(E+1/2)+E := add_le_add hsaw hxierr
    _=2*E+1/2 := by ring

/-- Integration by parts on a closed interval, with both partial counting
cells retained in the endpoint terms. -/
theorem interval_lipschitz_quadrature_parts {n : ℕ} (Y : Fin n → ℝ)
    (f : ℝ → ℝ) (K : ℝ≥0) (hLip : LipschitzWith K f)
    (P p : BoundedRealFunction)
    (hdP : ∀ x, HasDerivAt P (p x) x) (a b : ℝ) (hab : a≤b) :
    (∑ j ∈ rootsInInterval Y a b,f (Y j))-(∫ x in Icc a b,f x*p x)=
      f b*((rootCountLe Y b : ℝ)-P b)-
        f a*((rootCountStrictlyBelow Y a : ℝ)-P a)-
        (∫ x in Icc a b,deriv f x*((rootCountLe Y x : ℝ)-P x)) := by
  classical
  have hderiv : IntegrableOn (deriv f) (Icc a b) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact hLip.lipschitzOnWith.absolutelyContinuousOnInterval.intervalIntegrable_deriv.1
  have hroot : IntegrableOn (fun x : ℝ => deriv f x*(rootCountLe Y x : ℝ)) (Icc a b) :=
    hderiv.mul_bdd (rootCountLe_measurable Y).aestronglyMeasurable
      (Eventually.of_forall (rootCountLe_norm_bound Y))
  have hP : IntegrableOn (fun x : ℝ => deriv f x*P x) (Icc a b) :=
    hderiv.mul_bdd P.continuous.aestronglyMeasurable
      (Eventually.of_forall (fun x => P.norm_coe_le_norm x))
  have hprod : IntegrableOn (fun x : ℝ => f x*p x) (Icc a b) :=
    (hLip.continuous.mul p.continuous).integrableOn_Icc
  have hcountLe (u : ℝ) : (rootCountLe Y u : ℝ)=
      ∑ j : Fin n,if Y j≤u then (1:ℝ) else 0 := by
    rw [rootCountLe_eq_sum_indicators]
    simp [Set.indicator_apply]
  have hcountLt (u : ℝ) : (rootCountStrictlyBelow Y u : ℝ)=
      ∑ j : Fin n,if Y j<u then (1:ℝ) else 0 := by
    simp [rootCountStrictlyBelow,Finset.sum_ite_irrel]
  have hdiscrete : (∑ j ∈ rootsInInterval Y a b,f (Y j))=
      (rootCountLe Y b : ℝ)*f b-(rootCountStrictlyBelow Y a : ℝ)*f a-
        (∑ j : Fin n,if Y j≤a then f b-f a else if Y j≤b then f b-f (Y j) else 0) := by
    have hpoint (j : Fin n) :
        (if a≤Y j ∧ Y j≤b then f (Y j) else 0)=
          (if Y j≤b then f b else 0)-(if Y j<a then f a else 0)-
            (if Y j≤a then f b-f a else if Y j≤b then f b-f (Y j) else 0) := by
      by_cases hja : Y j<a
      · have hjb : Y j≤b := (le_of_lt hja).trans hab
        have hjaN : ¬a≤Y j := not_le_of_gt hja
        have hjaL : Y j≤a := le_of_lt hja
        simp [hja,hjaN,hjaL,hjb]
      · have hja' : a≤Y j := le_of_not_gt hja
        by_cases hjb : Y j≤b
        · by_cases hjaL : Y j≤a
          · have hyeq : Y j=a := le_antisymm hjaL hja'
            simp [hab,hyeq] <;> ring
          · simp [hja,hja',hjaL,hjb]
        · have hbj : b<Y j := lt_of_not_ge hjb
          have hjaL : ¬Y j≤a := not_le_of_gt (lt_of_le_of_lt hab hbj)
          simp [hja,hja',hjaL,hjb]
    have hsum := Finset.sum_congr (s₁:=Finset.univ) rfl (fun j _ => hpoint j)
    have hinterval : (∑ j ∈ rootsInInterval Y a b,f (Y j))=
        ∑ j : Fin n,if a≤Y j ∧ Y j≤b then f (Y j) else 0 := by
      rw [rootsInInterval,Finset.sum_filter]
    rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib] at hsum
    have hright : (∑ j : Fin n,if Y j≤b then f b else 0)=
        (rootCountLe Y b : ℝ)*f b := by
      rw [hcountLe b,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> simp
    have hleft : (∑ j : Fin n,if Y j<a then f a else 0)=
        (rootCountStrictlyBelow Y a : ℝ)*f a := by
      rw [hcountLt a,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> simp
    rw [hright,hleft] at hsum
    exact hinterval.trans hsum
  have hcountInt := integral_deriv_rootCount_lipschitz_Icc Y f K hLip a b hab
  have hPLip : LipschitzWith ‖p‖₊ (fun x => P x) := by
    apply lipschitzWith_of_nnnorm_deriv_le (fun x => (hdP x).differentiableAt)
    intro x
    rw [(hdP x).deriv]
    exact_mod_cast p.norm_coe_le_norm x
  have hparts := hLip.lipschitzOnWith.absolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul
    hPLip.lipschitzOnWith.absolutelyContinuousOnInterval (a:=a) (b:=b)
  have hparts' : (∫ x in Icc a b,f x*p x)=
      f b*P b-f a*P a-(∫ x in Icc a b,deriv f x*P x) := by
    simp_rw [show ∀ x, deriv (fun v => P v) x=p x from fun x => (hdP x).deriv] at hparts
    simpa only [intervalIntegral.integral_of_le hab,← integral_Icc_eq_integral_Ioc] using hparts
  have hsplit : (∫ x in Icc a b,deriv f x*((rootCountLe Y x : ℝ)-P x))=
      (∫ x in Icc a b,deriv f x*(rootCountLe Y x : ℝ))-
        (∫ x in Icc a b,deriv f x*P x) := by
    rw [← integral_sub hroot hP]
    congr 1
    funext x
    ring
  rw [hdiscrete,hsplit,hcountInt,hparts']
  ring

/-- A normalized Lipschitz test gives the local weighted sum estimate;
the discrepancy terms at both ends are kept instead of assuming the test
vanishes at the interval boundary. -/
theorem interval_weighted_sum_quadrature_error {n : ℕ} (a b : ℝ) (Y : Fin n→ℝ)
    (hY : StrictMono Y) (rho : ℝ→ℝ) (hrho : ∀ x∈Icc a b,0<rho x)
    (P p : BoundedRealFunction) (hdP : ∀ x,HasDerivAt P (p x) x)
    (f phi : BoundedRealFunction) (Kf : ℝ≥0) (hLipf : LipschitzWith Kf (fun x=>f x))
    (A B E : ℝ) (hab : a≤b) (hA : 0≤A) (hB : 0≤B) (hE : 0≤E)
    (hfnorm : ∀ x∈Icc a b,|f x|≤A)
    (hfeq : ∀ x∈Icc a b,f x*rho x=phi x)
    (hF : ∀ x∈Icc a b,|(rootCountLe Y x:ℝ)-P x|≤B)
    (hRho : ∀ x∈Icc a b,|rho x-p x|≤E) :
    |(∑ j∈rootsInInterval Y a b,phi (Y j)/rho (Y j))-
      (∫ x in Icc a b,phi x)| ≤
      (2*B+1)*A+(b-a)*(B*(Kf:ℝ)+A*E) := by
  classical
  have hvalue (x : ℝ) (hx : x∈Icc a b) : f x=phi x/rho x := by
    have he := hfeq x hx
    calc
      f x=(f x*rho x)/rho x := by field_simp [ne_of_gt (hrho x hx)]
      _=phi x/rho x := by rw [he]
  have hsum : (∑ j∈rootsInInterval Y a b,phi (Y j)/rho (Y j))=
      ∑ j∈rootsInInterval Y a b,f (Y j) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hx : Y j∈Icc a b := (Finset.mem_filter.mp hj).2
    rw [hvalue (Y j) hx]
  have hbelow : |(rootCountStrictlyBelow Y a:ℝ)-P a|≤B+1 := by
    have hg := rootCountStrictlyBelow_gap Y hY a
    have hle : (rootCountStrictlyBelow Y a:ℝ)≤(rootCountLe Y a:ℝ) := by exact_mod_cast hg.1
    have hgap : (rootCountLe Y a:ℝ)≤(rootCountStrictlyBelow Y a:ℝ)+1 := by exact_mod_cast hg.2
    have habs : |(rootCountStrictlyBelow Y a:ℝ)-(rootCountLe Y a:ℝ)|≤1 := by
      rw [abs_le]
      constructor <;> linarith
    calc
      _=|((rootCountStrictlyBelow Y a:ℝ)-(rootCountLe Y a:ℝ))+
          ((rootCountLe Y a:ℝ)-P a)| := by congr 1; ring
      _≤|((rootCountStrictlyBelow Y a:ℝ)-(rootCountLe Y a:ℝ))|+
          |((rootCountLe Y a:ℝ)-P a)| := abs_add_le _ _
      _≤1+B := add_le_add habs (hF a (left_mem_Icc.mpr hab))
      _=B+1 := by ring
  have hendpoint : |f b*((rootCountLe Y b:ℝ)-P b)-
      f a*((rootCountStrictlyBelow Y a:ℝ)-P a)|≤(2*B+1)*A := by
    calc
      _≤|f b| * |(rootCountLe Y b:ℝ)-P b|+
          |f a| * |(rootCountStrictlyBelow Y a:ℝ)-P a| := by
            calc
              _=|f b*((rootCountLe Y b:ℝ)-P b)+
                  -(f a*((rootCountStrictlyBelow Y a:ℝ)-P a))| := by congr 1
              _≤|f b*((rootCountLe Y b:ℝ)-P b)|+
                  |-(f a*((rootCountStrictlyBelow Y a:ℝ)-P a))| := abs_add_le _ _
              _=|f b| * |(rootCountLe Y b:ℝ)-P b|+
                  |f a| * |(rootCountStrictlyBelow Y a:ℝ)-P a| := by simp only [abs_mul,abs_neg]
      _≤A*B+A*(B+1) := add_le_add
        (mul_le_mul (hfnorm b (right_mem_Icc.mpr hab)) (hF b (right_mem_Icc.mpr hab))
          (abs_nonneg _) hA)
        (mul_le_mul (hfnorm a (left_mem_Icc.mpr hab)) hbelow (abs_nonneg _) hA)
      _=(2*B+1)*A := by ring
  have hI : |(∫ x in Icc a b,deriv f x*((rootCountLe Y x:ℝ)-P x))|≤
      (b-a)*(Kf:ℝ)*B := by
    rw [← Real.norm_eq_abs]
    have hh := norm_setIntegral_le_of_norm_le_const (μ:=volume) (s:=Icc a b)
      (f:=fun x : ℝ=>deriv f x*((rootCountLe Y x:ℝ)-P x))
      (C:=(Kf:ℝ)*B) isCompact_Icc.measure_lt_top (by
        intro x hx
        rw [norm_mul,Real.norm_eq_abs]
        exact mul_le_mul (norm_deriv_le_of_lipschitz hLipf) (hF x hx)
          (norm_nonneg _) Kf.coe_nonneg)
    rw [Real.volume_real_Icc_of_le hab] at hh
    exact hh.trans_eq (by ring)
  have hprod : IntegrableOn (fun x : ℝ=>f x*p x) (Icc a b) :=
    (f.continuous.mul p.continuous).integrableOn_Icc
  have hphi : IntegrableOn (fun x : ℝ=>phi x) (Icc a b) := phi.continuous.integrableOn_Icc
  have hcancel (x : ℝ) (hx : x∈Icc a b) : f x*rho x=phi x := hfeq x hx
  have hfun (x : ℝ) (hx : x∈Icc a b) :
      f x*p x-phi x=f x*(p x-rho x) := by rw [← hcancel x hx]; ring
  have hdiffInt : (∫ x in Icc a b,f x*p x)-(∫ x in Icc a b,phi x)=
      ∫ x in Icc a b,f x*(p x-rho x) := by
    rw [← integral_sub hprod hphi]
    apply integral_congr_ae
    apply (ae_restrict_iff' measurableSet_Icc).2
    exact Eventually.of_forall hfun
  have hdensityInt : |(∫ x in Icc a b,f x*(p x-rho x))|≤
      (b-a)*(A*E) := by
    rw [← Real.norm_eq_abs]
    have hh := norm_setIntegral_le_of_norm_le_const (μ:=volume) (s:=Icc a b)
      (f:=fun x : ℝ=>f x*(p x-rho x)) (C:=A*E) isCompact_Icc.measure_lt_top (by
        intro x hx
        rw [norm_mul,Real.norm_eq_abs]
        have hRho' : ‖p x-rho x‖≤E := by
          simpa only [Real.norm_eq_abs,abs_sub_comm] using hRho x hx
        exact mul_le_mul (hfnorm x hx) hRho' (norm_nonneg _) hA)
    rw [Real.volume_real_Icc_of_le hab] at hh
    exact hh.trans_eq (by ring)
  have hparts := interval_lipschitz_quadrature_parts Y (fun x=>f x) Kf hLipf P p hdP a b hab
  have hbase : |(∑ j∈rootsInInterval Y a b,f (Y j))-(∫ x in Icc a b,f x*p x)|≤
      (2*B+1)*A+(b-a)*(Kf:ℝ)*B := by
    have hparts' : (∑ j∈rootsInInterval Y a b,f (Y j))-(∫ x in Icc a b,f x*p x)=
        (f b*((rootCountLe Y b:ℝ)-P b)-f a*((rootCountStrictlyBelow Y a:ℝ)-P a))-
          (∫ x in Icc a b,deriv f x*((rootCountLe Y x:ℝ)-P x)) := by
      rw [hparts]
    rw [hparts']
    calc
      _≤|f b*((rootCountLe Y b:ℝ)-P b)-f a*((rootCountStrictlyBelow Y a:ℝ)-P a)|+
          |(∫ x in Icc a b,deriv f x*((rootCountLe Y x:ℝ)-P x))| := by
            calc
              _=|(f b*((rootCountLe Y b:ℝ)-P b)-f a*((rootCountStrictlyBelow Y a:ℝ)-P a))+
                  -(∫ x in Icc a b,deriv f x*((rootCountLe Y x:ℝ)-P x))| := by congr 1
              _≤|f b*((rootCountLe Y b:ℝ)-P b)-f a*((rootCountStrictlyBelow Y a:ℝ)-P a)|+
                  |-(∫ x in Icc a b,deriv f x*((rootCountLe Y x:ℝ)-P x))| := abs_add_le _ _
              _= _ := by rw [abs_neg]
      _≤_ := add_le_add hendpoint hI
  have hdecomp : (∑ j∈rootsInInterval Y a b,phi (Y j)/rho (Y j))-
      (∫ x in Icc a b,phi x)=
      ((∑ j∈rootsInInterval Y a b,f (Y j))-(∫ x in Icc a b,f x*p x))+
        ((∫ x in Icc a b,f x*p x)-(∫ x in Icc a b,phi x)) := by rw [hsum]; ring
  rw [hdecomp]
  calc
    _≤((2*B+1)*A+(b-a)*(Kf:ℝ)*B)+((b-a)*(A*E)) :=
      (abs_add_le _ _).trans (add_le_add hbase (by rw [hdiffInt]; exact hdensityInt))
    _=(2*B+1)*A+(b-a)*(B*(Kf:ℝ)+A*E) := by ring

theorem integral_rootQuadratureMeasure_Icc_local {n : ℕ} (lam : ℝ) (b : ℕ→ℝ)
    (L : ℕ) (X : Fin n→ℝ) (hpos : ∀ j,0≤countingSlope lam b L X (X j))
    (phi : ℝ→ℝ) (a z : ℝ) :
    (∫ x in Icc a z,phi x ∂rootQuadratureMeasure lam b L X)=
      ∑ j∈rootsInInterval X a z,phi (X j)/countingSlope lam b L X (X j) := by
  rw [← integral_indicator measurableSet_Icc]
  rw [integral_rootQuadratureMeasure_of_density_nonneg lam b L X hpos
    (fun x=>(Icc a z).indicator phi x)]
  rw [rootsInInterval,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : a≤X j ∧ X j≤z
  · simp [hj]
  · simp [hj]

/-! ### Global continuation of the normalized cone -/

/-- On every compact physical parameter interval ending strictly below `π`,
the actual consecutive-root Bethe vector remains in the normalized closed
positive cone. The only nonvanishing input is the pointwise A01 identity. -/
theorem consecutiveBethe_closedCone_global {m n : ℕ} (eta : ℝ)
    (heta : 0<eta) (hEven : Even (m+2)) (hfill : 2*n≤m+2)
    (lamMax : ℝ) (hhalfMax : Real.pi/2≤lamMax) (hpiMax : lamMax<Real.pi)
    (hSlavnov : ∀ lam, Real.pi/2≤lam → lam≤lamMax →
      SlavnovIdentity lam (fun _ => 0) (m+2)
        (nonpositiveKernelRoots (fun _ => 0) (m+2) (by omega) n hfill lam) 0)
    (lam : ℝ) (hhalf : Real.pi/2≤lam) (hbound : lam≤lamMax) :
    consecutiveBetheClosedCone hfill lam := by
  classical
  let L : ℕ := m+2
  obtain ⟨q₀,hq₀⟩ := exists_minusCount_eq (m+2) n (by omega)
  letI : Nonempty (ParticleConfigurations (m+2) n) := ⟨⟨q₀,hq₀⟩⟩
  let U : Set ℝ := Set.Ico (Real.pi/2) Real.pi
  let C := Set.Icc (Real.pi/2) lamMax
  let P : Set C := {a | consecutiveBetheClosedCone hfill a.val}
  let F : ℝ → ParticleConfigurations L n → ℂ := fun x q =>
    consecutiveBetheSectorVector hfill x q
  let S : ℝ → ℂ := fun x => consecutiveBetheSectorSum hfill x
  have hCtoU (a : C) : a.val ∈ U := by
    change Real.pi/2≤a.val ∧ a.val<Real.pi
    exact ⟨a.property.1, lt_of_le_of_lt a.property.2 hpiMax⟩
  have hFcontOn (q : ParticleConfigurations L n) :
      ContinuousOn (fun x => F x q) U := by
    intro x hx
    have hF := nonpositiveKernelPhysicalBetheVector_continuousOn
      (fun _ => 0) L (by omega) n hfill x hx
    have heval : Continuous (fun v : SpinHilbert L => v q.val) :=
      PiLp.continuous_apply 2 (fun _ : RowSpins L => ℂ) q.val
    exact heval.continuousAt.comp_continuousWithinAt hF
  have hScontOn : ContinuousOn S U := by
    dsimp [S]
    exact continuousOn_finsetSum Finset.univ (by
      intro q hq
      exact hFcontOn q)
  have hsum_coord_bound (x : ℝ) (hx : x ∈ U)
      (hcone : consecutiveBetheClosedCone hfill x)
      (q : ParticleConfigurations L n) : ‖F x q‖≤‖S x‖ := by
    have hcone' : (∑ q,F x q)≠0 ∧ ∀ q,0≤(F x q/(∑ i,F x i)).re ∧
        (F x q/(∑ i,F x i)).im=0 := by
      change consecutiveBetheClosedCone hfill x
      exact hcone
    have h := normalizedCone_coordinate_norm_le (F x) hcone' q
    change ‖F x q‖≤‖∑ i,F x i‖
    exact h
  have hclosed : IsClosed P := by
    apply IsSeqClosed.isClosed
    intro a a₀ ha hconv
    have hparam : Tendsto (fun k => (a k).val) atTop (𝓝 a₀.val) :=
      continuous_subtype_val.continuousAt.tendsto.comp hconv
    have hparamU : Tendsto (fun k => (a k).val) atTop (𝓝[U] a₀.val) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨hparam, Filter.Eventually.of_forall ?_⟩
      intro k
      exact hCtoU (a k)
    have hFseq (q : ParticleConfigurations L n) :
        Tendsto (fun k => F (a k).val q) atTop (𝓝 (F a₀.val q)) := by
      have hx := hCtoU a₀
      exact (hFcontOn q a₀.val hx).tendsto.comp hparamU
    have hSseq : Tendsto (fun k => S (a k).val) atTop (𝓝 (S a₀.val)) := by
      have hx := hCtoU a₀
      exact (hScontOn a₀.val hx).tendsto.comp hparamU
    have hfull_ne : physicalBetheVector a₀.val (fun _ => 0) L
        (nonpositiveKernelRoots (fun _ => 0) L (by omega) n hfill a₀.val) ≠ 0 :=
      nonpositiveKernelPhysicalBetheVector_ne_zero (fun _ => 0) L (by omega) hEven n hfill
        a₀.val a₀.property.1 (lt_of_le_of_lt a₀.property.2 hpiMax)
        (hSlavnov a₀.val a₀.property.1 a₀.property.2)
    have hraw_ne : (physicalBetheVector a₀.val (fun _ => 0) L
        (nonpositiveKernelRoots (fun _ => 0) L (by omega) n hfill a₀.val)).ofLp ≠ 0 := by
      intro hz
      apply hfull_ne
      exact (WithLp.ofLp_eq_zero 2).mp hz
    have hsector_ne : F a₀.val ≠ 0 := by
      exact physical_sector_restriction_ne_zero _
        (physicalBetheVector_sector a₀.val (fun _ => 0) L
          (nonpositiveKernelRoots (fun _ => 0) L (by omega) n hfill a₀.val)) hraw_ne
    have hqexists : ∃ q : ParticleConfigurations L n,F a₀.val q≠0 := by
      by_contra h
      push_neg at h
      apply hsector_ne
      funext q
      exact h q
    obtain ⟨qInst,hqInst⟩ := hqexists
    have hS_ne : S a₀.val≠0 := by
      by_contra hzero
      have hzero' : S a₀.val=0 := by simpa using hzero
      have hleft : Tendsto (fun k => ‖F (a k).val qInst‖) atTop
          (𝓝 ‖F a₀.val qInst‖) := by
        exact continuous_norm.continuousAt.tendsto.comp (hFseq qInst)
      have hright : Tendsto (fun k => ‖S (a k).val‖) atTop (𝓝 0) := by
        have hright' : Tendsto (fun k => ‖S (a k).val‖) atTop
            (𝓝 ‖S a₀.val‖) := continuous_norm.continuousAt.tendsto.comp hSseq
        simpa [hzero'] using hright'
      have hbound : ∀ᶠ k : ℕ in atTop,
          ‖F (a k).val qInst‖≤‖S (a k).val‖ :=
        Filter.Eventually.of_forall (fun k =>
          hsum_coord_bound (a k).val (hCtoU (a k)) (ha k) qInst)
      have hlim := le_of_tendsto_of_tendsto hleft hright hbound
      have hnorm : ‖F a₀.val qInst‖=0 :=
        le_antisymm hlim (norm_nonneg _)
      exact hqInst (norm_eq_zero.mp hnorm)
    have hcone : consecutiveBetheClosedCone hfill a₀.val := by
      refine ⟨hS_ne,?_⟩
      intro q
      have hquot : Tendsto (fun k => F (a k).val q / S (a k).val) atTop
          (𝓝 (F a₀.val q / S a₀.val)) := (hFseq q).div hSseq hS_ne
      have hreal : Tendsto (fun k => (F (a k).val q / S (a k).val).re) atTop
          (𝓝 (F a₀.val q / S a₀.val).re) :=
        Complex.continuous_re.continuousAt.tendsto.comp hquot
      have hnonneg : 0≤(F a₀.val q / S a₀.val).re :=
        le_of_tendsto_of_tendsto tendsto_const_nhds hreal
          (Filter.Eventually.of_forall (fun k => (ha k).2 q |>.1))
      have himag : Tendsto (fun k => (F (a k).val q / S (a k).val).im) atTop
          (𝓝 (F a₀.val q / S a₀.val).im) :=
        Complex.continuous_im.continuousAt.tendsto.comp hquot
      have himag_zero : Tendsto (fun k => (F (a k).val q / S (a k).val).im) atTop
          (𝓝 (0 : ℝ)) := by
        have heq : (fun k => (F (a k).val q / S (a k).val).im)=fun _ => 0 := by
          funext k
          simpa [F,S,consecutiveBetheSectorVector,consecutiveBetheSectorSum,L] using
            (ha k).2 q |>.2
        rw [heq]
        exact tendsto_const_nhds
      have himag_eq : (F a₀.val q / S a₀.val).im=0 :=
        tendsto_nhds_unique himag himag_zero
      exact ⟨hnonneg,himag_eq⟩
    change consecutiveBetheClosedCone hfill a₀.val
    exact hcone
  have hopen : IsOpen P := by
    apply isOpen_iff_mem_nhds.mpr
    intro a ha
    change consecutiveBetheClosedCone hfill a.val at ha
    have hSlavnovA := hSlavnov a.val a.property.1 a.property.2
    have hstrict := consecutiveBethe_closedCone_strictly_positive
      a.val eta heta hEven hfill a.property.1 (lt_of_le_of_lt a.property.2 hpiMax)
      hSlavnovA ha
    have hvalU : Tendsto (fun y : C => y.val) (𝓝 a) (𝓝[U] a.val) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨continuous_subtype_val.continuousAt.tendsto,
        Filter.Eventually.of_forall ?_⟩
      intro y
      exact hCtoU y
    have hpositiveEvent : ∀ᶠ y : C in 𝓝 a,
        ∀ q : ParticleConfigurations L n,
          0<(F y.val q / S y.val).re := by
      rw [Filter.eventually_all]
      intro q
      have hquot : Tendsto (fun y : C => F y.val q / S y.val) (𝓝 a)
          (𝓝 (F a.val q / S a.val)) := by
        have hq := (hFcontOn q a.val (hCtoU a)).tendsto.comp hvalU
        have hs := (hScontOn a.val (hCtoU a)).tendsto.comp hvalU
        exact hq.div hs ha.1
      have hreal : Tendsto (fun y : C => (F y.val q / S y.val).re) (𝓝 a)
          (𝓝 (F a.val q / S a.val).re) :=
        Complex.continuous_re.continuousAt.tendsto.comp hquot
      exact hreal.eventually (lt_mem_nhds (hstrict q))
    filter_upwards [hpositiveEvent] with y hy
    have hhalfY : Real.pi/2≤y.val := y.property.1
    have hpiY : y.val<Real.pi := lt_of_le_of_lt y.property.2 hpiMax
    obtain ⟨q₀,hq₀⟩ := exists_minusCount_eq L n (by omega)
    let qInst : ParticleConfigurations L n := ⟨q₀,hq₀⟩
    have hS_y : S y.val≠0 := by
      by_contra hz
      have hz' : S y.val=0 := by simpa using hz
      have hpos := hy qInst
      simp [hz'] at hpos
    let phase : ℂ := (S y.val)⁻¹
    have hphase : phase≠0 := inv_ne_zero hS_y
    have hphasePos : ∀ q : ParticleConfigurations L n,
        0<(phase*F y.val q).re := by
      intro q
      have heq : phase*F y.val q=F y.val q/S y.val := by
        dsimp [phase]
        rw [div_eq_mul_inv]
        ring
      rw [heq]
      exact hy q
    obtain ⟨mu,v,c,hposG,hEigG,hLowerG,hSimpleG,hcG,hlineG⟩ :=
      nonpositiveKernel_physicalBetheVector_ground_line_of_positiveRealPart
        y.val eta heta hEven hfill hhalfY hpiY
        ⟨phase,hphase,hphasePos⟩
    have hline : (F y.val)=c • (fun q => (v q : ℂ)) := by
      funext q
      change (physicalBetheVector y.val (fun _ => 0) L
        (nonpositiveKernelRoots (fun _ => 0) L (by omega) n hfill y.val)).ofLp q.val =
          c*(v q : ℂ)
      have hq := congrFun hlineG q
      simpa only [Pi.smul_apply,smul_eq_mul] using hq
    have hconeY : consecutiveBetheClosedCone hfill y.val := by
      have hnorm := normalizedCone_of_positiveLine (F y.val) v c hcG hposG hline
      change consecutiveBetheClosedCone hfill y.val
      exact hnorm
    simpa [P] using hconeY
  have hnonempty : P.Nonempty := by
    let Y := nonpositiveKernelRoots (fun _ => 0) L (by omega) n hfill (Real.pi/2)
    have hroot : ConsecutiveRoots (Real.pi/2) (fun _ => 0) L Y 0 :=
      nonpositiveKernelRoots_spec (fun _ => 0) L (by omega) n hfill (Real.pi/2)
        le_rfl (by linarith [Real.pi_pos])
    obtain ⟨c,hc,hfree⟩ := actual_free_bethe_ground_line (particles:=n) m hEven
      (by omega) Y hroot (hSlavnov (Real.pi/2) le_rfl hhalfMax)
    have hYpos : ∀ q : ParticleConfigurations L n,0<(spinFreeSlaterVector L Y q).re :=
      fun q => (spinFreeSlaterVector_positive L (by omega) Y hroot q).2
    have hbaseCone : consecutiveBetheClosedCone hfill (Real.pi/2) := by
      apply normalizedCone_of_positiveLine (F (Real.pi/2))
        (fun q => (spinFreeSlaterVector L Y q).re) c hc hYpos
      funext q
      have hq := congrFun hfree q
      have hslater : spinFreeSlaterVector L Y q =
          ((spinFreeSlaterVector L Y q).re : ℂ) := by
        apply Complex.ext
        · rfl
        · simpa using (spinFreeSlaterVector_positive L (by omega) Y hroot q).1
      have hq' : F (Real.pi/2) q=c*spinFreeSlaterVector L Y q := by
        change (physicalBetheVector (Real.pi/2) (fun _ => 0) L
          (nonpositiveKernelRoots (fun _ => 0) L (by omega) n hfill (Real.pi/2))).ofLp q.val = _
        exact hq
      rw [hslater] at hq'
      change F (Real.pi/2) q=
        c*((spinFreeSlaterVector L Y q).re : ℂ)
      simpa only [Pi.smul_apply,smul_eq_mul] using hq'
    exact ⟨⟨Real.pi/2,le_rfl,hhalfMax⟩,by simpa [P] using hbaseCone⟩
  letI : PreconnectedSpace C := Subtype.preconnectedSpace isPreconnected_Icc
  have hall : P=Set.univ := IsClopen.eq_univ ⟨hclosed,hopen⟩ hnonempty
  have hmem : (⟨lam,hhalf,hbound⟩ : C)∈P := by
    rw [hall]
    trivial
  simpa [P] using hmem

/-- The actual consecutive-root Bethe vector is the actual physical transfer
Perron vector throughout any compact physical parameter interval. This is the
global ground-line clause of Lemma 3.1, conditional only on A01. -/
theorem consecutiveBethe_global_perron_line {m n : ℕ} (eta : ℝ)
    (heta : 0<eta) (hEven : Even (m+2)) (hfill : 2*n≤m+2)
    (lamMax : ℝ) (hhalfMax : Real.pi/2≤lamMax) (hpiMax : lamMax<Real.pi)
    (hSlavnov : ∀ lam, Real.pi/2≤lam → lam≤lamMax →
      SlavnovIdentity lam (fun _ => 0) (m+2)
        (nonpositiveKernelRoots (fun _ => 0) (m+2) (by omega) n hfill lam) 0)
    (lam : ℝ) (hhalf : Real.pi/2≤lam) (hbound : lam≤lamMax) :
    ∃ (mu tau : ℝ) (v : ParticleConfigurations (m+2) n → ℝ),
      PhysicalSectorPerronData lam eta m n mu tau v ∧
      ∃ c : ℂ,c≠0 ∧
        (fun q : ParticleConfigurations (m+2) n =>
          physicalBetheVector lam (fun _ => 0) (m+2)
            (nonpositiveKernelRoots (fun _ => 0) (m+2) (by omega) n hfill lam) q.val)=
          c • (fun q => (v q : ℂ)) := by
  classical
  obtain ⟨q₀,hq₀⟩ := exists_minusCount_eq (m+2) n (by omega)
  letI : Nonempty (ParticleConfigurations (m+2) n) := ⟨⟨q₀,hq₀⟩⟩
  have hcone := consecutiveBethe_closedCone_global eta heta hEven hfill lamMax
    hhalfMax hpiMax hSlavnov lam hhalf hbound
  have hpi : lam<Real.pi := lt_of_le_of_lt hbound hpiMax
  have hSlavnovLam := hSlavnov lam hhalf hbound
  have hstrict := consecutiveBethe_closedCone_strictly_positive
    lam eta heta hEven hfill hhalf hpi hSlavnovLam hcone
  let V : ParticleConfigurations (m+2) n → ℂ := fun q =>
    physicalBetheVector lam (fun _ => 0) (m+2)
      (nonpositiveKernelRoots (fun _ => 0) (m+2) (by omega) n hfill lam) q.val
  let S : ℂ := ∑ q,V q
  have hS : S≠0 := by simpa [S,V,consecutiveBetheSectorSum,consecutiveBetheSectorVector] using hcone.1
  let phase : ℂ := S⁻¹
  have hphase : phase≠0 := inv_ne_zero hS
  have hphasePos : ∀ q,0<(phase*V q).re := by
    intro q
    have heq : phase*V q=V q/S := by
      dsimp [phase,S]
      rw [div_eq_mul_inv]
      ring
    rw [heq]
    have hq := hstrict q
    simpa [S,V,consecutiveBetheSectorSum,consecutiveBetheSectorVector] using hq
  obtain ⟨muG,vG,cG,hposG,hEigG,hLowerG,hSimpleG,hcG,hlineG⟩ :=
    nonpositiveKernel_physicalBetheVector_ground_line_of_positiveRealPart
      lam eta heta hEven hfill hhalf hpi ⟨phase,hphase,hphasePos⟩
  obtain ⟨muP,tau,vP,hdata⟩ :=
    exists_physical_sector_perron_data lam eta
      (lt_of_lt_of_le (by positivity : (0:ℝ)<Real.pi/2) hhalf)
      hpi heta m n (by omega)
  let A := realSectorHamiltonian lam eta m n
  have hP_real : A.mulVec vP=muP • vP := by
    have hcomplex := hdata.ground_eigen
    rw [complexSectorHamiltonian_eq_real_map] at hcomplex
    funext q
    have hq := congrArg Complex.re (congrFun hcomplex q)
    simpa only [Matrix.mulVec,dotProduct,Matrix.map_apply,Pi.smul_apply,smul_eq_mul,
      Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,
      mul_zero,sub_zero] using hq
  have hmu : muG=muP := positive_symmetric_eigenvalues_equal A
    (realSectorHamiltonian_isHermitian lam eta m n).isSymm muG muP vG vP
    hposG hdata.positive hEigG hP_real
  have hP_complex : (complexSectorHamiltonian lam eta m n).mulVec
      (fun q => (vP q : ℂ))=(muG : ℂ) • (fun q => (vP q : ℂ)) := by
    simpa [hmu] using hdata.ground_eigen
  rw [complexSectorHamiltonian_eq_real_map] at hP_complex
  obtain ⟨a,ha⟩ := real_simple_eigenspace_complexify A muG vG hSimpleG
    (fun q => (vP q : ℂ)) hP_complex
  have ha_ne : a≠0 := by
    intro hz
    have hq := congrFun ha ⟨q₀,hq₀⟩
    have hpzero : (vP ⟨q₀,hq₀⟩ : ℂ)=0 := by simpa [hz] using hq
    exact (Complex.ofReal_ne_zero.mpr (hdata.positive ⟨q₀,hq₀⟩).ne') hpzero
  have hvG : (fun q => (vG q : ℂ))=a⁻¹ • (fun q => (vP q : ℂ)) := by
    funext q
    have hq : (vP q : ℂ)=a*(vG q : ℂ) := by
      simpa only [Pi.smul_apply,smul_eq_mul] using congrFun ha q
    calc
      (vG q : ℂ)=a⁻¹*(a*(vG q : ℂ)) := by field_simp [ha_ne]
      _=a⁻¹*(vP q : ℂ) := by rw [← hq]
  have hline : V=(cG*a⁻¹) • (fun q => (vP q : ℂ)) := by
    calc
      V=cG • (fun q => (vG q : ℂ)) := by
        simpa [V] using hlineG
      _=cG • (a⁻¹ • (fun q => (vP q : ℂ))) := congrArg (fun w => cG • w) hvG
      _=(cG*a⁻¹) • (fun q => (vP q : ℂ)) := by rw [smul_smul]
  refine ⟨muP,tau,vP,hdata,cG*a⁻¹,mul_ne_zero hcG (inv_ne_zero ha_ne),?_⟩
  simpa [V] using hline

/-- Extend a bounded Lipschitz interval test by linear ramps to a compactly
supported Lipschitz test, with explicit norm and Lipschitz bounds. -/
theorem exists_compact_lipschitz_interval_extension (phi : BoundedRealFunction)
    (K : ℝ≥0) (hLip : LipschitzWith K (fun x => phi x))
    (a b delta : ℝ) (hab : a≤b) (hdelta : 0<delta) :
    ∃ psi : BoundedRealFunction,
      (∀ x∈Icc a b,psi x=phi x) ∧
      (∀ x,x∉Icc (a-delta) (b+delta) → psi x=0) ∧
      LipschitzWith ⟨(K:ℝ)+‖phi‖/delta,by positivity⟩ (fun x => psi x) ∧
      ‖psi‖≤‖phi‖ := by
  classical
  let c : ℝ→ℝ := fun x => max a (min b x)
  have hc : LipschitzWith 1 c := (LipschitzWith.id.const_min b).const_max a
  have hc_mem (x : ℝ) : c x∈Icc a b :=
    ⟨le_max_left _ _,max_le hab (min_le_left _ _)⟩
  have hc_eq (x : ℝ) (hx : x∈Icc a b) : c x=x := by
    dsimp [c]
    rw [min_eq_right hx.2,max_eq_right hx.1]
  let slope : ℝ≥0 := ⟨1/delta,by positivity⟩
  let left : ℝ→ℝ := fun x => (x-(a-delta))/delta
  let right : ℝ→ℝ := fun x => (b+delta-x)/delta
  have hleft : LipschitzWith slope left := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change |left x-left y|≤(slope:ℝ)*|x-y|
    have heq : left x-left y=(x-y)/delta := by dsimp [left]; ring
    rw [heq,abs_div,abs_of_pos hdelta]
    change |x-y|/delta≤(1/delta)*|x-y|
    rw [div_eq_mul_inv,one_div]
    exact le_of_eq (mul_comm _ _)
  have hright : LipschitzWith slope right := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change |right x-right y|≤(slope:ℝ)*|x-y|
    have heq : right x-right y=(y-x)/delta := by dsimp [right]; ring
    rw [heq,abs_div,abs_of_pos hdelta]
    rw [abs_sub_comm y x]
    change |x-y|/delta≤(1/delta)*|x-y|
    rw [div_eq_mul_inv,one_div]
    exact le_of_eq (mul_comm _ _)
  let cutoff : ℝ→ℝ := fun x => max 0 (min 1 (min (left x) (right x)))
  have hcutLip : LipschitzWith slope cutoff := by
    simpa [cutoff] using (hleft.min hright).const_min 1 |>.const_max 0
  have hcut_nonneg (x : ℝ) : 0≤cutoff x := le_max_left _ _
  have hcut_le (x : ℝ) : cutoff x≤1 := by
    dsimp [cutoff]
    exact max_le (by norm_num) (min_le_left _ _)
  have hcut_one (x : ℝ) (hx : x∈Icc a b) : cutoff x=1 := by
    have hl : 1≤left x := by
      dsimp [left]
      rw [one_le_div₀ hdelta]
      linarith [hx.1]
    have hr : 1≤right x := by
      dsimp [right]
      rw [one_le_div₀ hdelta]
      linarith [hx.2]
    have hmin : 1≤min (left x) (right x) := le_min hl hr
    simp [cutoff,min_eq_left hmin]
  have hcut_zero (x : ℝ) (hx : x∉Icc (a-delta) (b+delta)) : cutoff x=0 := by
    rcases not_and_or.mp hx with hleft'|hright'
    · have hleftneg : left x<0 := by
        dsimp [left]
        exact div_neg_of_neg_of_pos (by linarith) hdelta
      have hmin : min 1 (min (left x) (right x))≤0 :=
        le_trans (min_le_right _ _) (le_of_lt (lt_of_le_of_lt (min_le_left _ _) hleftneg))
      exact max_eq_left hmin
    · have hrightneg : right x<0 := by
        dsimp [right]
        exact div_neg_of_neg_of_pos (by linarith) hdelta
      have hmin : min 1 (min (left x) (right x))≤0 :=
        le_trans (min_le_right _ _) (le_of_lt (lt_of_le_of_lt (min_le_right _ _) hrightneg))
      exact max_eq_left hmin
  have hfc : LipschitzWith K (fun x => phi (c x)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hφ := hLip.dist_le_mul (c x) (c y)
    change |phi (c x)-phi (c y)|≤(K:ℝ)*|c x-c y| at hφ
    have hcxy := hc.dist_le_mul x y
    change |c x-c y|≤1*|x-y| at hcxy
    calc
      |phi (c x)-phi (c y)|≤(K:ℝ)*|c x-c y| := hφ
      _≤(K:ℝ)*(1*|x-y|) := mul_le_mul_of_nonneg_left hcxy K.coe_nonneg
      _=(K:ℝ)*|x-y| := by ring
  have hcutnorm (x : ℝ) : |cutoff x|≤1 := by
    rw [abs_of_nonneg (hcut_nonneg x)]
    exact hcut_le x
  let Kext : ℝ≥0 := ⟨(K:ℝ)+‖phi‖/delta,by positivity⟩
  let psiFun : ℝ→ℝ := fun x => phi (c x)*cutoff x
  have hpsiLip : LipschitzWith Kext psiFun := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hφxy : |phi (c x)-phi (c y)|≤(K:ℝ)*|x-y| := by
      have h := hfc.dist_le_mul x y
      simpa only [Real.dist_eq] using h
    have hχxy : |cutoff x-cutoff y|≤(1/delta)*|x-y| := by
      have h := hcutLip.dist_le_mul x y
      change |cutoff x-cutoff y|≤(1/delta)*|x-y| at h
      exact h
    have hφbound : |phi (c y)|≤‖phi‖ := by
      simpa only [Real.norm_eq_abs] using phi.norm_coe_le_norm (c y)
    change |phi (c x)*cutoff x-phi (c y)*cutoff y|≤(Kext:ℝ)*|x-y|
    calc
      _=|(phi (c x)-phi (c y))*cutoff x+phi (c y)*(cutoff x-cutoff y)| := by
        congr 1
        ring
      _≤|(phi (c x)-phi (c y))*cutoff x|+|phi (c y)*(cutoff x-cutoff y)| := abs_add_le _ _
      _=|phi (c x)-phi (c y)| * |cutoff x| + |phi (c y)| * |cutoff x-cutoff y| := by
        rw [abs_mul,abs_mul]
      _≤(K:ℝ)*|x-y| + ‖phi‖*((1/delta)*|x-y|) := add_le_add
        (calc
          |phi (c x)-phi (c y)| * |cutoff x|
              ≤((K:ℝ)*|x-y|) * |cutoff x| :=
                mul_le_mul_of_nonneg_right hφxy (abs_nonneg _)
          _≤((K:ℝ)*|x-y|) * 1 :=
                mul_le_mul_of_nonneg_left (hcutnorm x)
                  (mul_nonneg K.coe_nonneg (abs_nonneg _))
          _=(K:ℝ)*|x-y| := by ring)
        (mul_le_mul hφbound hχxy (abs_nonneg _) (norm_nonneg _))
      _=((K:ℝ)+‖phi‖/delta)*|x-y| := by ring
      _=(Kext:ℝ)*|x-y| := by rfl
  have hpsiCont : Continuous psiFun :=
    (phi.continuous.comp hc.continuous).mul hcutLip.continuous
  have hpsiBound (x : ℝ) : ‖psiFun x‖≤‖phi‖ := by
    rw [norm_mul]
    calc
      ‖phi (c x)‖ * ‖cutoff x‖ ≤ ‖phi‖ * ‖cutoff x‖ :=
        mul_le_mul_of_nonneg_right (phi.norm_coe_le_norm (c x)) (norm_nonneg _)
      _≤‖phi‖ * 1 :=
        mul_le_mul_of_nonneg_left (by
          rw [Real.norm_eq_abs]
          exact hcutnorm x) (norm_nonneg _)
      _=‖phi‖ := by ring
  let psi : BoundedRealFunction := BoundedContinuousFunction.ofNormedAddCommGroup
    psiFun hpsiCont ‖phi‖ (fun x => by
      change |psiFun x|≤‖phi‖
      simpa only [Real.norm_eq_abs] using hpsiBound x)
  have hpsiLip' : LipschitzWith Kext (fun x => psi x) := by
    simpa [psi] using hpsiLip
  have hpsiNorm : ‖psi‖≤‖phi‖ := by
    apply (BoundedContinuousFunction.norm_le_of_nonempty (f:=psi)).2
    intro x
    change ‖psiFun x‖≤‖phi‖
    exact hpsiBound x
  refine ⟨psi,?_,?_,hpsiLip',hpsiNorm⟩
  · intro x hx
    change phi (c x)*cutoff x=phi x
    rw [hc_eq x hx,hcut_one x hx]
    ring
  · intro x hx
    change phi (c x)*cutoff x=0
    rw [hcut_zero x hx]
    ring

/-- Explicit interval quadrature constant, bundling the cumulative-count,
density, and normalization contributions in the estimate below. -/
def actualIntervalQuadratureErrorConstant (lam radius M a b delta : ℝ) : ℝ :=
  let C := kernelLogConstant lam
  let Ecount := Real.exp (C*(radius/M))*radius*
      (kernelL1Mass (kernelK lam)+physicalReferenceKernelRowErrorConstant lam/M)+
      |1-2*lam/Real.pi|/2
  let B := 2*Ecount+1/2
  let Edens := kernelL1Mass (kernelKPrime lam)/2+
      (C*Real.exp (C*(radius/M))*radius)*
        (kernelL1Mass (kernelK lam)+physicalReferenceKernelRowErrorConstant lam/M)
  let Rlip := 1/delta+C
  (2*B+1)+(b-a)*(B*(1+Rlip)+Edens)

/-- The actual inverse-counting-density measure obeys the bounded-Lipschitz
estimate on a closed interval, including tests with nonzero endpoint values.
The enlargement is used only to normalize the test by the local density. -/
theorem actual_interval_bounded_lipschitz_quadrature_error {n : ℕ}
    (lam : ℝ) (h0 : 0<lam) (hhalf : Real.pi/2≤lam) (hpi : lam<Real.pi)
    (Q : ℝ) (L : ℕ) (hL : 0<L) (Y X : Fin n→ℝ)
    (R : ReferenceQuantileData lam h0 hpi Q L Y)
    (hroots : ConsecutiveRoots lam (fun _=>0) L X 0)
    (M radius : ℝ) (hM : 0<M) (hrad : 0≤radius)
    (hlower : ∀ u∈Icc (-Q) Q,M≤(L:ℝ)*finiteIntervalDensity lam h0 hpi Q u)
    (hclose : ∀ j,|X j-Y j|≤radius/((L:ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j)))
    (a b delta N : ℝ) (hab : a≤b) (ha : -Q≤a) (hb : b≤Q)
    (hdelta : 0<delta) (hN : 0<N)
    (hlocal : ∀ u∈Icc (a-delta) (b+delta),N≤countingSlope lam (fun _=>0) L X u)
    (phi : BoundedRealFunction) (K : ℝ≥0) (hLip : LipschitzWith K (fun x=>phi x)) :
    |(∫ x in Icc a b,phi x ∂rootQuadratureMeasure lam (fun _=>0) L X)-
      (∫ x in Icc a b,phi x)| ≤
      (actualIntervalQuadratureErrorConstant lam radius M a b delta/N)*
        ((K:ℝ)+‖phi‖) := by
  classical
  let C := kernelLogConstant lam
  let Ecount := Real.exp (C*(radius/M))*radius*
      (kernelL1Mass (kernelK lam)+physicalReferenceKernelRowErrorConstant lam/M)+
      |1-2*lam/Real.pi|/2
  let B := 2*Ecount+1/2
  let Edens := kernelL1Mass (kernelKPrime lam)/2+
      (C*Real.exp (C*(radius/M))*radius)*
        (kernelL1Mass (kernelK lam)+physicalReferenceKernelRowErrorConstant lam/M)
  let Rlip := 1/delta+C
  let D := actualIntervalQuadratureErrorConstant lam radius M a b delta
  let rho : ℝ→ℝ := countingSlope lam (fun _=>0) L X
  let rho' : ℝ→ℝ := countingCurvature lam (fun _=>0) L X
  let P : BoundedRealFunction := (L:ℝ) • finiteIntervalCumulativeFunction lam h0 hpi Q
  let p : BoundedRealFunction := (L:ℝ) • finiteIntervalDensity lam h0 hpi Q
  have hC : 0≤C := kernelLogConstant_nonneg lam
  have hRlip : 0≤Rlip := by dsimp [Rlip]; positivity
  have hEcount : 0≤Ecount := by
    dsimp [Ecount,C]
    exact add_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le hrad)
      (add_nonneg (kernelL1Mass_nonneg _) (div_nonneg (physicalReferenceKernelRowErrorConstant_nonneg lam h0) hM.le)))
      (div_nonneg (abs_nonneg _) (by norm_num))
  have hB : 0≤B := by dsimp [B]; positivity
  have hEdens : 0≤Edens := by
    dsimp [Edens,C]
    have hCE : 0≤kernelLogConstant lam*Real.exp
        (kernelLogConstant lam*(radius/M)) :=
      mul_nonneg hC (Real.exp_pos _).le
    exact add_nonneg (div_nonneg (kernelL1Mass_nonneg _) (by norm_num))
      (mul_nonneg (mul_nonneg hCE hrad)
        (add_nonneg (kernelL1Mass_nonneg _) (div_nonneg (physicalReferenceKernelRowErrorConstant_nonneg lam h0) hM.le)))
  have hlen : 0≤b-a := sub_nonneg.mpr hab
  have hD : 0≤D := by dsimp [D,actualIntervalQuadratureErrorConstant]; positivity
  have hrhopos (x : ℝ) : 0<rho x := by
    exact countingSlope_pos_nonpositiveK lam (fun _=>0) L hL X x hhalf hpi
  have hrhocont : Continuous rho := continuous_iff_continuousAt.mpr (fun x =>
    (hasDerivAt_countingSlope lam (fun _=>0) L X x h0 hpi).continuousAt)
  have hdrho (x : ℝ) : HasDerivAt rho (rho' x) x := by
    exact hasDerivAt_countingSlope lam (fun _=>0) L X x h0 hpi
  have hrelative (x : ℝ) : |rho' x|≤C*rho x := by
    exact countingCurvature_relative_bound lam (fun _=>0) L X hhalf hpi x
  obtain ⟨psi,hpsiEq,hpsiSupport,hpsiLip,hpsiNorm⟩ :=
    exists_compact_lipschitz_interval_extension phi K hLip a b delta hab hdelta
  let Kext : ℝ≥0 := ⟨(K:ℝ)+‖phi‖/delta,by positivity⟩
  obtain ⟨f,hf,hfs,hfLip⟩ := exists_normalized_lipschitz_test psi Kext hpsiLip rho rho'
    hrhocont hrhopos hdrho (a-delta) (b+delta) N C
    (by linarith) hN (kernelLogConstant_nonneg lam) hpsiSupport hlocal hrelative
  let Kf : ℝ≥0 := ⟨((Kext:ℝ)+C*‖psi‖)/N,by positivity⟩
  have hfLip' : LipschitzWith Kf (fun x=>f x) := by simpa [Kf] using hfLip
  have hA : 0≤‖phi‖/N := div_nonneg (norm_nonneg _) hN.le
  have hfnorm (x : ℝ) (hx : x∈Icc a b) : |f x|≤‖phi‖/N := by
    have hx' : x∈Icc (a-delta) (b+delta) := ⟨by linarith [hx.1],by linarith [hx.2]⟩
    rw [hf x, hpsiEq x hx, abs_div,abs_of_pos (hrhopos x)]
    calc
      |phi x|/rho x≤‖phi‖/rho x := div_le_div_of_nonneg_right
        (by simpa only [Real.norm_eq_abs] using phi.norm_coe_le_norm x) (hrhopos x).le
      _≤‖phi‖/N := div_le_div_of_nonneg_left (norm_nonneg _) hN (hlocal x hx')
  have hfeq (x : ℝ) (hx : x∈Icc a b) : f x*rho x=phi x := by
    rw [hf x,hpsiEq x hx]
    exact div_mul_cancel₀ _ (hrhopos x).ne'
  have hP (x : ℝ) : P x=(L:ℝ)*finiteIntervalCumulative lam h0 hpi Q x := rfl
  have hp (x : ℝ) : p x=(L:ℝ)*finiteIntervalDensity lam h0 hpi Q x := rfl
  have hdP (x : ℝ) : HasDerivAt P (p x) x := by
    change HasDerivAt (fun y => (L:ℝ)*finiteIntervalCumulative lam h0 hpi Q y)
      ((L:ℝ)*finiteIntervalDensity lam h0 hpi Q x) x
    exact (finiteIntervalCumulative_hasDerivAt lam h0 hpi Q x).const_mul (L:ℝ)
  have hF (x : ℝ) (hx : x∈Icc a b) : |(rootCountLe X x:ℝ)-P x|≤B := by
    have hxQ : x∈Icc (-Q) Q := ⟨ha.trans hx.1,hx.2.trans hb⟩
    have hh := weighted_rootCount_primitive_error_local lam h0 hhalf hpi Q L hL Y X R
      hroots M radius hM hrad hlower hclose x hxQ
    simpa [B,Ecount,C,hP] using hh
  have hRho (x : ℝ) (hx : x∈Icc a b) : |rho x-p x|≤Edens := by
    have hh := weighted_configuration_density_error_all lam h0 hpi Q L Y X R M hM
      hlower radius hrad hclose x
    simpa [rho,p,Edens,C,hp] using hh
  have hsum := interval_weighted_sum_quadrature_error a b X hroots.1 rho
    (fun x _ => hrhopos x) P p hdP f phi Kf hfLip' (‖phi‖/N) B Edens
    hab hA hB hEdens hfnorm hfeq hF hRho
  have hpos (j : Fin n) : 0≤countingSlope lam (fun _=>0) L X (X j) := (hrhopos (X j)).le
  rw [integral_rootQuadratureMeasure_Icc_local lam (fun _=>0) L X hpos phi a b]
  change |(∑ j∈rootsInInterval X a b,phi (X j)/rho (X j))-
    (∫ x in Icc a b,phi x)|≤_ at hsum
  have hKf : (Kf:ℝ)≤((K:ℝ)+‖phi‖*Rlip)/N := by
    have hcoef : (Kext:ℝ)+C*‖psi‖≤(K:ℝ)+‖phi‖*(1/delta+C) := by
      dsimp [Kext]
      have h₂ : C*‖psi‖≤C*‖phi‖ := mul_le_mul_of_nonneg_left hpsiNorm hC
      change (K:ℝ)+‖phi‖/delta+C*‖psi‖≤(K:ℝ)+‖phi‖*(1/delta+C)
      calc
        (K:ℝ)+‖phi‖/delta+C*‖psi‖≤(K:ℝ)+‖phi‖/delta+C*‖phi‖ := by linarith
        _=(K:ℝ)+‖phi‖*(1/delta+C) := by ring
    change ((Kext:ℝ)+C*‖psi‖)/N≤_
    exact div_le_div_of_nonneg_right hcoef hN.le
  have hDdecomp : D=(2*B+1)+(b-a)*(B*Rlip+Edens)+(b-a)*B := by
    dsimp [D,actualIntervalQuadratureErrorConstant]
    ring
  have hcoefK : (b-a)*B≤D := by
    have hrest : 0≤(2*B+1)+(b-a)*(B*Rlip+Edens) :=
      add_nonneg (by positivity)
        (mul_nonneg hlen (add_nonneg (mul_nonneg hB hRlip) hEdens))
    rw [hDdecomp]
    calc
      (b-a)*B≤(b-a)*B+((2*B+1)+(b-a)*(B*Rlip+Edens)) :=
        le_add_of_nonneg_right hrest
      _=(2*B+1)+(b-a)*(B*Rlip+Edens)+(b-a)*B := by ring
  have hcoefPhi : (2*B+1)+(b-a)*(B*Rlip+Edens)≤D := by
    rw [hDdecomp]
    exact le_add_of_nonneg_right (mul_nonneg hlen hB)
  have hnum : (b-a)*B*(K:ℝ)+((2*B+1)+(b-a)*(B*Rlip+Edens))*‖phi‖≤
      D*((K:ℝ)+‖phi‖) := by
    calc
      _≤D*(K:ℝ)+D*‖phi‖ := add_le_add
        (mul_le_mul_of_nonneg_right hcoefK K.coe_nonneg)
        (mul_le_mul_of_nonneg_right hcoefPhi (norm_nonneg phi))
      _=D*((K:ℝ)+‖phi‖) := by ring
  have hBKf : B*(Kf:ℝ)≤B*((K:ℝ)+‖phi‖*Rlip)/N := by
    calc
      B*(Kf:ℝ)≤B*(((K:ℝ)+‖phi‖*Rlip)/N) := mul_le_mul_of_nonneg_left hKf hB
      _=B*((K:ℝ)+‖phi‖*Rlip)/N := by ring
  calc
    _≤(2*B+1)*(‖phi‖/N)+(b-a)*(B*((K:ℝ)+‖phi‖*Rlip)/N+(‖phi‖/N)*Edens) := by
      refine hsum.trans ?_
      apply add_le_add
      · exact le_rfl
      · apply mul_le_mul_of_nonneg_left _ hlen
        exact add_le_add hBKf le_rfl
    _=((b-a)*B*(K:ℝ)+((2*B+1)+(b-a)*(B*Rlip+Edens))*‖phi‖)/N := by ring
    _≤(D*((K:ℝ)+‖phi‖))/N := div_le_div_of_nonneg_right hnum hN.le
    _=(D/N)*((K:ℝ)+‖phi‖) := by ring

/-- Generic endpoint-inclusive quadrature estimate. This is the finite
counting-cell argument used in every parameter regime: all model-specific
work is isolated in the primitive discrepancy and relative-density bounds. -/
theorem interval_bounded_lipschitz_quadrature_error_of_density_data {n : ℕ}
    (lam : ℝ) (b : ℕ→ℝ) (L : ℕ) (X : Fin n→ℝ) (hX : StrictMono X)
    (rho' : ℝ→ℝ)
    (hrhocont : Continuous (countingSlope lam b L X))
    (hdrho : ∀ x,HasDerivAt (countingSlope lam b L X) (rho' x) x)
    (C : ℝ) (hC : 0≤C)
    (P p : BoundedRealFunction) (hdP : ∀ x,HasDerivAt P (p x) x)
    (a z delta N B E : ℝ) (haz : a≤z) (hdelta : 0<delta) (hN : 0<N)
    (hrelative : ∀ x∈Icc (a-delta) (z+delta),
      |rho' x|≤C*countingSlope lam b L X x)
    (hB : 0≤B) (hE : 0≤E)
    (hlocal : ∀ x∈Icc (a-delta) (z+delta),N≤countingSlope lam b L X x)
    (hrootpos : ∀ j : Fin n,0≤countingSlope lam b L X (X j))
    (hF : ∀ x∈Icc a z,|(rootCountLe X x:ℝ)-P x|≤B)
    (hRho : ∀ x∈Icc a z,|countingSlope lam b L X x-p x|≤E)
    (phi : BoundedRealFunction) (K : ℝ≥0)
    (hLip : LipschitzWith K (fun x=>phi x)) :
    |(∫ x in Icc a z,phi x ∂rootQuadratureMeasure lam b L X)-
      (∫ x in Icc a z,phi x)| ≤
      (((2*B+1)+(z-a)*(B*(1+1/delta+C)+E))/N)*((K:ℝ)+‖phi‖) := by
  classical
  let Rlip : ℝ := 1/delta+C
  let D : ℝ := (2*B+1)+(z-a)*(B*(1+Rlip)+E)
  let rho : ℝ→ℝ := countingSlope lam b L X
  have hlen : 0≤z-a := sub_nonneg.mpr haz
  have hRlip : 0≤Rlip := by dsimp [Rlip]; positivity
  have hA : 0≤‖phi‖/N := div_nonneg (norm_nonneg _) hN.le
  have hpos (x : ℝ) (hx : x∈Icc (a-delta) (z+delta)) :
      0<countingSlope lam b L X x := hN.trans_le (hlocal x hx)
  obtain ⟨psi,hpsiEq,hpsiSupport,hpsiLip,hpsiNorm⟩ :=
    exists_compact_lipschitz_interval_extension phi K hLip a z delta haz hdelta
  let Kext : ℝ≥0 := ⟨(K:ℝ)+‖phi‖/delta,by positivity⟩
  obtain ⟨f,hf,hfs,hfLip⟩ := exists_normalized_lipschitz_test_local psi Kext hpsiLip
    rho rho' hrhocont (a-delta) (z+delta) N C hpos hdrho
    (by linarith) hN hC hpsiSupport hlocal hrelative
  let Kf : ℝ≥0 := ⟨((Kext:ℝ)+C*‖psi‖)/N,by positivity⟩
  have hfLip' : LipschitzWith Kf (fun x=>f x) := by simpa [Kf] using hfLip
  have hfnorm (x : ℝ) (hx : x∈Icc a z) : |f x|≤‖phi‖/N := by
    have hx' : x∈Icc (a-delta) (z+delta) := ⟨by linarith [hx.1],by linarith [hx.2]⟩
    have hposx := hpos x hx'
    rw [hf x,hpsiEq x hx,abs_div,abs_of_pos hposx]
    calc
      |phi x|/rho x≤‖phi‖/rho x := div_le_div_of_nonneg_right
        (by simpa only [Real.norm_eq_abs] using phi.norm_coe_le_norm x) hposx.le
      _≤‖phi‖/N := div_le_div_of_nonneg_left (norm_nonneg _) hN (hlocal x hx')
  have hfeq (x : ℝ) (hx : x∈Icc a z) : f x*rho x=phi x := by
    rw [hf x,hpsiEq x hx]
    exact div_mul_cancel₀ _ (hpos x ⟨by linarith [hx.1],by linarith [hx.2]⟩).ne'
  have hsum := interval_weighted_sum_quadrature_error a z X hX rho
    (fun x hx => hpos x ⟨by linarith [hx.1],by linarith [hx.2]⟩) P p hdP
    f phi Kf hfLip' (‖phi‖/N) B E haz hA hB hE hfnorm hfeq hF hRho
  rw [integral_rootQuadratureMeasure_Icc_local lam b L X hrootpos phi a z]
  change |(∑ j∈rootsInInterval X a z,phi (X j)/rho (X j))-
    (∫ x in Icc a z,phi x)|≤_ at hsum
  have hKf : (Kf:ℝ)≤((K:ℝ)+‖phi‖*Rlip)/N := by
    have hcoef : (Kext:ℝ)+C*‖psi‖≤(K:ℝ)+‖phi‖*(1/delta+C) := by
      dsimp [Kext]
      have h₂ : C*‖psi‖≤C*‖phi‖ := mul_le_mul_of_nonneg_left hpsiNorm hC
      change (K:ℝ)+‖phi‖/delta+C*‖psi‖≤(K:ℝ)+‖phi‖*(1/delta+C)
      calc
        (K:ℝ)+‖phi‖/delta+C*‖psi‖≤(K:ℝ)+‖phi‖/delta+C*‖phi‖ := by linarith
        _=(K:ℝ)+‖phi‖*(1/delta+C) := by ring
    change ((Kext:ℝ)+C*‖psi‖)/N≤_
    exact div_le_div_of_nonneg_right hcoef hN.le
  have hDdecomp : D=(2*B+1)+(z-a)*(B*Rlip+E)+(z-a)*B := by
    dsimp [D]
    ring
  have hcoefK : (z-a)*B≤D := by
    have hrest : 0≤(2*B+1)+(z-a)*(B*Rlip+E) :=
      add_nonneg (by positivity) (mul_nonneg hlen (add_nonneg (mul_nonneg hB hRlip) hE))
    rw [hDdecomp]
    calc
      (z-a)*B≤(z-a)*B+((2*B+1)+(z-a)*(B*Rlip+E)) := le_add_of_nonneg_right hrest
      _=(2*B+1)+(z-a)*(B*Rlip+E)+(z-a)*B := by ring
  have hcoefPhi : (2*B+1)+(z-a)*(B*Rlip+E)≤D := by
    rw [hDdecomp]
    exact le_add_of_nonneg_right (mul_nonneg hlen hB)
  have hnum : (z-a)*B*(K:ℝ)+((2*B+1)+(z-a)*(B*Rlip+E))*‖phi‖≤
      D*((K:ℝ)+‖phi‖) := by
    calc
      _≤D*(K:ℝ)+D*‖phi‖ := add_le_add
        (mul_le_mul_of_nonneg_right hcoefK K.coe_nonneg)
        (mul_le_mul_of_nonneg_right hcoefPhi (norm_nonneg phi))
      _=D*((K:ℝ)+‖phi‖) := by ring
  have hBKf : B*(Kf:ℝ)≤B*((K:ℝ)+‖phi‖*Rlip)/N := by
    calc
      B*(Kf:ℝ)≤B*(((K:ℝ)+‖phi‖*Rlip)/N) := mul_le_mul_of_nonneg_left hKf hB
      _=B*((K:ℝ)+‖phi‖*Rlip)/N := by ring
  calc
    _≤(2*B+1)*(‖phi‖/N)+(z-a)*(B*((K:ℝ)+‖phi‖*Rlip)/N+(‖phi‖/N)*E) := by
      refine hsum.trans ?_
      apply add_le_add
      · exact le_rfl
      · apply mul_le_mul_of_nonneg_left _ hlen
        exact add_le_add hBKf le_rfl
    _=((z-a)*B*(K:ℝ)+((2*B+1)+(z-a)*(B*Rlip+E))*‖phi‖)/N := by ring
    _≤(D*((K:ℝ)+‖phi‖))/N := div_le_div_of_nonneg_right hnum hN.le
    _=(D/N)*((K:ℝ)+‖phi‖) := by ring
    _=(((2*B+1)+(z-a)*(B*(1+1/delta+C)+E))/N)*((K:ℝ)+‖phi‖) := by
      dsimp [D,Rlip]
      ring

/-- Positive-kernel analogue of the local actual-root quadrature estimate.
The factor `scale` records the comparison between chain length and the
minimum density on the enlarged test window. All sign-sensitive estimates
are local to the occupied interval; positivity of the measure atoms follows
from the dense reference window. -/
def actualLocalPrimitiveDiscrepancyBound (lam radius M : ℝ) : ℝ :=
  2*(Real.exp (kernelLogConstant lam*(radius/M))*radius*
    (kernelL1Mass (kernelK lam)+physicalReferenceKernelRowErrorConstant lam/M)+
      |1-2*lam/Real.pi|/2)+1/2

def actualLocalDensityDiscrepancyBound (lam radius M : ℝ) : ℝ :=
  kernelL1Mass (kernelKPrime lam)/2+
    (kernelLogConstant lam*Real.exp (kernelLogConstant lam*(radius/M))*radius)*
      (kernelL1Mass (kernelK lam)+physicalReferenceKernelRowErrorConstant lam/M)

def homogeneousCountingCurvatureLinearConstant (lam : ℝ) : ℝ :=
  2/(Real.sin (lam/2))^2*kernelS lam 0+
    2/(Real.sin lam)^2*|kernelK lam 0|

/-- Every nonzero homogeneous on-shell Bethe vector is a Hamiltonian
eigenvector throughout the physical parameter interval. The argument uses
the entire transfer eigenvalue and the logarithmic derivative at the swap;
it does not depend on the sign of the interaction kernel. -/
theorem physical_homogeneous_bethe_hamiltonian_eigenline_of_nonzero
    {K n : ℕ} (lam eta : ℝ) (h0 : 0<lam) (hpi : lam<Real.pi)
    (hEven : Even (K+1)) (hfill : 2*n≤K+1) (Y : Fin n→ℝ)
    (hroots : ConsecutiveRoots lam (fun _=>0) (K+1) Y 0)
    (hV : physicalBetheVector lam (fun _=>0) (K+1) Y≠0) :
    homogeneousLinkHamiltonian lam eta K *
      (quantumGauge (K+1)*betheState (Complex.I*(lam:ℂ))
        (physical_deformation_ne_zero lam h0 hpi) (fun _=>0) (K+1) (rootSet Y)) =
      (-((eta:ℂ)*(2*Real.pi*∑ j,kernelS lam (Y j)-(K+1:ℝ)*Real.cot lam))) •
        (quantumGauge (K+1)*betheState (Complex.I*(lam:ℂ))
          (physical_deformation_ne_zero lam h0 hpi) (fun _=>0) (K+1) (rootSet Y)) := by
  classical
  let L : ℕ := K+1
  let ht := physical_deformation_ne_zero lam h0 hpi
  let hY : Function.Injective Y := hroots.1.injective
  let B := betheState (Complex.I*(lam:ℂ)) ht (fun _=>0) L (rootSet Y)
  let M := quantumGauge L*B
  have hV' : physicalBetheVector lam (fun _=>0) L Y≠0 := by simpa [L] using hV
  have hB : B≠0 := betheState_ne_zero_of_physicalBetheVector lam h0 hpi
    (fun _=>0) L Y hY hV'
  have hShell : OnShell lam (fun _=>0) L Y 0 := by
    exact consecutiveRoots_onShell lam (fun _=>0) L hEven Y 0 h0 hpi hroots
  obtain ⟨u,hu⟩ := exists_real_fresh_spectral Y
  obtain ⟨rho,hrho,heigen,hgen⟩ := balancedRoots_entire_eigenvalue
    (Complex.I*(lam:ℂ)) ht (fun _=>0) L 0 (rootSet Y)
    (onShell_balancedRoots lam h0 hpi (fun _=>0) L Y hY 0 hShell) hB u hu
    (real_insert_rootSet_regular lam h0 hpi Y u)
  have hLtwo : 2≤L := by dsimp [L]; obtain ⟨m,hm⟩ := hEven; omega
  let x₀ : ℂ := betheSwapCoordinate lam 0
  let d : ℝ := 2*Real.pi*∑ j,kernelS lam (Y j)-(L:ℝ)*Real.cot lam
  have hrhoSwap := physical_entire_bethe_swap_hasDerivAt lam h0 hpi L hLtwo
    Y hY rho hrho hgen
  let sign : ℂ := (-1:ℂ)^n
  let sigma : ℂ→ℂ := fun z=>sign*rho (betheSwapCoordinate lam z)
  have hsigDeriv : HasDerivAt sigma (sign*((d:ℂ)*rho x₀)) 0 := by
    exact hrhoSwap.const_mul sign
  have hphysical (z : ℂ) : homogeneousPhysicalRow lam L z*M=sigma z • M := by
    have hh := physical_eigenvector_of_standard_even lam ht (fun _=>0) L hEven 0
      (rootSet Y) (betheSwapCoordinate lam z) (rho (betheSwapCoordinate lam z)) (heigen _)
    rw [physicalTwistedRow_swapCoordinate] at hh
    simpa [M,B,sigma,sign,L,rootSet_card Y hY] using hh
  have hM : M≠0 := quantumGauge_mul_ne_zero L B hB
  obtain ⟨hsigma0,hHam⟩ := homogeneous_physical_eigenline_logarithmic lam eta h0 hpi K
    M sigma (sign*((d:ℂ)*rho x₀))
    hsigDeriv hphysical hM
  have hsign : sign≠0 := by simp [sign]
  have hrho0 : rho x₀≠0 := by
    intro hz
    apply hsigma0
    simp [sigma,x₀,hz]
  have hscalar : (-(eta:ℂ)*(sign*((d:ℂ)*rho x₀)))/(sign*rho x₀)=-(eta:ℂ)*(d:ℂ) := by
    field_simp [hsign,hrho0]
    <;> ring
  have hsigma : sigma 0=sign*rho x₀ := by simp [sigma,x₀]
  have hscalar' : (-(eta:ℂ)*(sign*((d:ℂ)*rho x₀)))/sigma 0=-(eta:ℂ)*(d:ℂ) := by
    rw [hsigma]
    exact hscalar
  rw [hscalar'] at hHam
  simpa [M,B,L,ht,d] using hHam

/-- A nonzero homogeneous Bethe vector with strictly positive real sector
coordinates is the actual simple Hamiltonian ground line, for either sign of
the interaction kernel. The root construction and the positivity witness are
kept explicit. -/
theorem physical_homogeneous_bethe_ground_line_of_positive_nonzero
    {m n : ℕ} (lam eta : ℝ) (h0 : 0<lam) (hpi : lam<Real.pi) (heta : 0<eta)
    (hEven : Even (m+2)) (hfill : 2*n≤m+2) (X : Fin n→ℝ)
    (hroots : ConsecutiveRoots lam (fun _=>0) (m+2) X 0)
    (hV : physicalBetheVector lam (fun _=>0) (m+2) X≠0)
    (phase : ℂ) (hphase : phase≠0)
    (hpositive : ∀ q : ParticleConfigurations (m+2) n,
      0<(phase*(physicalBetheVector lam (fun _=>0) (m+2) X q.val)).re) :
    ∃ (mu tau : ℝ) (v : ParticleConfigurations (m+2) n→ℝ) (c : ℂ),
      PhysicalSectorPerronData lam eta m n mu tau v ∧ c≠0 ∧
        (fun q=>physicalBetheVector lam (fun _=>0) (m+2) X q.val)=
          c • (fun q=>(v q:ℂ)) := by
  classical
  let L : ℕ := m+2
  obtain ⟨q₀,hq₀⟩ := exists_minusCount_eq (m+2) n (by omega)
  let qInst : ParticleConfigurations (m+2) n := ⟨q₀,hq₀⟩
  letI : Nonempty (ParticleConfigurations (m+2) n) := ⟨qInst⟩
  have hmatrix := physical_homogeneous_bethe_hamiltonian_eigenline_of_nonzero
    (K:=m+1) (n:=n) lam eta h0 hpi hEven hfill X hroots (by simpa [L] using hV)
  let E : ℝ := -eta*(2*Real.pi*∑ j,kernelS lam (X j)-
    ((m+1+1:ℕ):ℝ)*Real.cot lam)
  let M : Matrix (RowSpins L) (RowSpins L) ℂ := quantumGauge L*betheState
    (Complex.I*(lam:ℂ)) (physical_deformation_ne_zero lam h0 hpi) (fun _=>0) L (rootSet X)
  have hmatrix' : homogeneousLinkHamiltonian lam eta (m+1)*M=(E:ℂ) • M := by
    simpa [M,E,L,Complex.ofReal_mul] using hmatrix
  let e : RowSpins L→ℂ := Pi.single (plusSpins L) 1
  have hcolumn : M.mulVec e=physicalBetheVector lam (fun _=>0) L X := by
    rw [show e=Pi.single (plusSpins L) 1 by rfl,Matrix.mulVec_single_one]
    funext q
    exact (physicalBetheVector_eq_betheState_column lam h0 hpi (fun _=>0) L X
      hroots.1.injective q).symm
  have hfull : (homogeneousLinkHamiltonian lam eta (m+1)).mulVec
      (physicalBetheVector lam (fun _=>0) L X)=(E:ℂ) •
        physicalBetheVector lam (fun _=>0) L X := by
    have h := congrArg (fun A : Matrix (RowSpins L) (RowSpins L) ℂ=>A.mulVec e) hmatrix'
    rw [← Matrix.mulVec_mulVec] at h
    simp only [Matrix.smul_mulVec] at h
    simpa [hcolumn] using h
  let V : ParticleConfigurations (m+2) n→ℂ := fun q=>
    physicalBetheVector lam (fun _=>0) L X q.val
  have hsector : (complexSectorHamiltonian lam eta m n).mulVec V=(E:ℂ) • V := by
    funext q
    rw [complexSectorHamiltonian_mulVec_eq_full,
      physicalSectorExtension_restriction_eq _ (physicalBetheVector_sector lam (fun _=>0) L X)]
    exact congrFun hfull q.val
  let W : ParticleConfigurations (m+2) n→ℂ := fun q=>phase*V q
  have hsectorW : (complexSectorHamiltonian lam eta m n).mulVec W=(E:ℂ) • W := by
    have hW : W=phase • V := by funext q; simp [W,Pi.smul_apply,smul_eq_mul]
    rw [hW,Matrix.mulVec_smul,hsector]
    simp only [smul_smul]
    congr 1
    ring
  let w : ParticleConfigurations (m+2) n→ℝ := fun q=>(W q).re
  have hwpos : ∀ q,0<w q := by intro q; simpa [w,W,V,L] using hpositive q
  have hwEig : (realSectorHamiltonian lam eta m n).mulVec w=E • w := by
    rw [complexSectorHamiltonian_eq_real_map] at hsectorW
    funext q
    have hq := congrArg Complex.re (congrFun hsectorW q)
    simpa only [Matrix.mulVec,dotProduct,Matrix.map_apply,Pi.smul_apply,smul_eq_mul,
      Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,
      sub_zero] using hq
  obtain ⟨mu0,v0,hpos0,hEig0,hLower0,hSimple0⟩ :=
    physical_sector_positive_simple_minimum lam eta h0 hpi heta m n (by omega)
  obtain ⟨mu,tau,v,hdata⟩ := exists_physical_sector_perron_data lam eta h0 hpi heta m n (by omega)
  have hP_real : (realSectorHamiltonian lam eta m n).mulVec v=mu • v := by
    have hcomplex := hdata.ground_eigen
    rw [complexSectorHamiltonian_eq_real_map] at hcomplex
    funext q
    have hq := congrArg Complex.re (congrFun hcomplex q)
    simpa only [Matrix.mulVec,dotProduct,Matrix.map_apply,Pi.smul_apply,smul_eq_mul,
      Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,
      mul_zero,sub_zero] using hq
  have hmu : mu=E := positive_symmetric_eigenvalues_equal (realSectorHamiltonian lam eta m n)
    (realSectorHamiltonian_isHermitian lam eta m n).isSymm mu E v w
    hdata.positive hwpos hP_real hwEig
  have hmu0 : mu0=E := positive_symmetric_eigenvalues_equal (realSectorHamiltonian lam eta m n)
    (realSectorHamiltonian_isHermitian lam eta m n).isSymm mu0 E v0 w
    hpos0 hwpos hEig0 hwEig
  have hVmin : (realSectorHamiltonian lam eta m n).mulVec v=mu0 • v := by
    have hmuMu0 : mu=mu0 := hmu.trans hmu0.symm
    simpa [hmuMu0] using hP_real
  obtain ⟨a,haLine⟩ := hSimple0 v hVmin
  have ha : a≠0 := by
    intro hz
    have hq := congrFun haLine qInst
    rw [hz,zero_smul] at hq
    exact (hdata.positive qInst).ne' hq
  have haminv : (fun q=>(v0 q:ℂ))=(a:ℂ)⁻¹ • (fun q=>(v q:ℂ)) := by
    funext q
    have hq : v q=a*v0 q := by simpa only [Pi.smul_apply,smul_eq_mul] using congrFun haLine q
    have hane : (a:ℂ)≠0 := Complex.ofReal_ne_zero.mpr ha
    calc
      (v0 q:ℂ)=(a:ℂ)⁻¹*((a:ℂ)*(v0 q:ℂ)) := by field_simp [hane]
      _=(a:ℂ)⁻¹*(v q:ℂ) := by rw [hq]; push_cast; ring
  have hsectorW' : (complexSectorHamiltonian lam eta m n).mulVec W=(mu0:ℂ) • W := by
    simpa [hmu0] using hsectorW
  rw [complexSectorHamiltonian_eq_real_map] at hsectorW'
  obtain ⟨cW,hWline⟩ := real_simple_eigenspace_complexify
    (realSectorHamiltonian lam eta m n) mu0 v0 hSimple0 W hsectorW'
  have hcW : cW≠0 := by
    intro hz
    have hq := congrFun hWline qInst
    rw [hz,zero_smul] at hq
    have hzero : (W qInst).re=0 := by simpa using congrArg Complex.re hq
    exact (hwpos qInst).ne' hzero
  have hWlineV : W=(cW*(a:ℂ)⁻¹) • (fun q=>(v q:ℂ)) := by
    calc
      W=cW • (fun q=>(v0 q:ℂ)) := hWline
      _=cW • ((a:ℂ)⁻¹ • (fun q=>(v q:ℂ))) := by rw [haminv]
      _=(cW*(a:ℂ)⁻¹) • (fun q=>(v q:ℂ)) := by rw [smul_smul]
  have hVfromW : V=phase⁻¹ • W := by
    funext q
    simp only [W,Pi.smul_apply,smul_eq_mul]
    rw [← mul_assoc,inv_mul_cancel₀ hphase,one_mul]
  have hline : V=(phase⁻¹*(cW*(a:ℂ)⁻¹)) • (fun q=>(v q:ℂ)) := by
    calc
      V=phase⁻¹ • W := hVfromW
      _=phase⁻¹ • ((cW*(a:ℂ)⁻¹) • (fun q=>(v q:ℂ))) := by rw [hWlineV]
      _=(phase⁻¹*(cW*(a:ℂ)⁻¹)) • (fun q=>(v q:ℂ)) := by rw [smul_smul]
  have hc : phase⁻¹*(cW*(a:ℂ)⁻¹)≠0 :=
    mul_ne_zero (inv_ne_zero hphase) (mul_ne_zero hcW (inv_ne_zero (Complex.ofReal_ne_zero.mpr ha)))
  exact ⟨mu,tau,v,(phase⁻¹*(cW*(a:ℂ)⁻¹)),hdata,hc,by simpa [V,L] using hline⟩

/-- The generic positive-line theorem, with vector nonvanishing obtained from
the checked Gaudin determinant and the explicit A01 Slavnov premise. -/
theorem physical_homogeneous_bethe_ground_line_of_positive
    {m n : ℕ} (lam eta : ℝ) (h0 : 0<lam) (hpi : lam<Real.pi) (heta : 0<eta)
    (hEven : Even (m+2)) (hfill : 2*n≤m+2) (X : Fin n→ℝ)
    (hroots : ConsecutiveRoots lam (fun _=>0) (m+2) X 0)
    (hdet : (gaudinMatrix lam (fun _=>0) (m+2) X).det≠0)
    (hSlavnov : SlavnovIdentity lam (fun _=>0) (m+2) X 0)
    (phase : ℂ) (hphase : phase≠0)
    (hpositive : ∀ q : ParticleConfigurations (m+2) n,
      0<(phase*(physicalBetheVector lam (fun _=>0) (m+2) X q.val)).re) :
    ∃ (mu tau : ℝ) (v : ParticleConfigurations (m+2) n→ℝ) (c : ℂ),
      PhysicalSectorPerronData lam eta m n mu tau v ∧ c≠0 ∧
        (fun q=>physicalBetheVector lam (fun _=>0) (m+2) X q.val)=
          c • (fun q=>(v q:ℂ)) := by
  have hShell : OnShell lam (fun _=>0) (m+2) X 0 :=
    consecutiveRoots_onShell lam (fun _=>0) (m+2) hEven X 0 h0 hpi hroots
  have hV : physicalBetheVector lam (fun _=>0) (m+2) X≠0 :=
    physical_bethe_ne_zero lam h0 hpi (fun _=>0) (m+2) hEven X hroots.1.injective 0
      hShell hSlavnov hdet
  exact physical_homogeneous_bethe_ground_line_of_positive_nonzero lam eta h0 hpi heta
    hEven hfill X hroots hV phase hphase hpositive

/-- A normalized nonnegative sector Bethe eigenvector is strictly positive,
for any real on-shell root list in the physical parameter range. This removes
the old negative-kernel restriction from the positivity-improvement step. -/
theorem physical_homogeneous_bethe_closedCone_strictly_positive
    {m n : ℕ} (lam eta : ℝ) (h0 : 0<lam) (hpi : lam<Real.pi) (heta : 0<eta)
    (hEven : Even (m+2)) (hfill : 2*n≤m+2) (X : Fin n→ℝ)
    (hroots : ConsecutiveRoots lam (fun _=>0) (m+2) X 0)
    (hdet : (gaudinMatrix lam (fun _=>0) (m+2) X).det≠0)
    (hSlavnov : SlavnovIdentity lam (fun _=>0) (m+2) X 0)
    (hcone : (∑ q : ParticleConfigurations (m+2) n,
        physicalBetheVector lam (fun _=>0) (m+2) X q.val)≠0 ∧
      ∀ q : ParticleConfigurations (m+2) n,
        0≤(physicalBetheVector lam (fun _=>0) (m+2) X q.val /
        (∑ i : ParticleConfigurations (m+2) n,
          physicalBetheVector lam (fun _=>0) (m+2) X i.val)).re ∧
        (physicalBetheVector lam (fun _=>0) (m+2) X q.val /
          (∑ i : ParticleConfigurations (m+2) n,
            physicalBetheVector lam (fun _=>0) (m+2) X i.val)).im=0) :
    ∀ q : ParticleConfigurations (m+2) n,
      0<(physicalBetheVector lam (fun _=>0) (m+2) X q.val /
      (∑ i : ParticleConfigurations (m+2) n,
        physicalBetheVector lam (fun _=>0) (m+2) X i.val)).re := by
  classical
  let L : ℕ := m+2
  obtain ⟨q₀,hq₀⟩ := exists_minusCount_eq (m+2) n (by omega)
  let qInst : ParticleConfigurations (m+2) n := ⟨q₀,hq₀⟩
  letI : Nonempty (ParticleConfigurations (m+2) n) := ⟨qInst⟩
  let V : ParticleConfigurations (m+2) n→ℂ := fun q=>
    physicalBetheVector lam (fun _=>0) L X q.val
  let S : ℂ := ∑ q,V q
  let phase : ℂ := S⁻¹
  let W : ParticleConfigurations (m+2) n→ℂ := fun q=>phase*V q
  let w : ParticleConfigurations (m+2) n→ℝ := fun q=>(W q).re
  have hS : S≠0 := by simpa [S,V,L] using hcone.1
  have hphase : phase≠0 := inv_ne_zero hS
  have hWratio (q : ParticleConfigurations (m+2) n) : W q=V q/S := by
    simp only [W,phase]
    rw [div_eq_mul_inv]
    ring
  have hWreal (q : ParticleConfigurations (m+2) n) : (W q).im=0 := by
    rw [hWratio q]
    simpa [S,V,L] using (hcone.2 q).2
  have hWnonneg (q : ParticleConfigurations (m+2) n) : 0≤w q := by
    change 0≤(W q).re
    rw [hWratio q]
    simpa [S,V,L] using (hcone.2 q).1
  have hsumW : ∑ q,W q=1 := by
    calc
      (∑ q,W q)=phase*(∑ q,V q) := by simp [W,Finset.mul_sum]
      _=phase*S := by simp [S]
      _=1 := by simp [phase,S,hS]
  have hsumw : ∑ q,w q=1 := by
    have h := congrArg Complex.re hsumW
    simpa [w,Complex.re_sum] using h
  have hwne : w≠0 := by
    intro hz
    have hz' : (∑ q,w q)=0 := by simp [hz]
    rw [hsumw] at hz'
    norm_num at hz'
  have hShell : OnShell lam (fun _=>0) L X 0 :=
    consecutiveRoots_onShell lam (fun _=>0) L hEven X 0 h0 hpi hroots
  have hV : physicalBetheVector lam (fun _=>0) L X≠0 :=
    physical_bethe_ne_zero lam h0 hpi (fun _=>0) L hEven X hroots.1.injective 0
      hShell hSlavnov hdet
  have hmatrix := physical_homogeneous_bethe_hamiltonian_eigenline_of_nonzero
    (K:=m+1) (n:=n) lam eta h0 hpi hEven hfill X hroots (by simpa [L] using hV)
  let E : ℝ := -eta*(2*Real.pi*∑ j,kernelS lam (X j)-
    ((m+1+1:ℕ):ℝ)*Real.cot lam)
  let M : Matrix (RowSpins L) (RowSpins L) ℂ := quantumGauge L*betheState
    (Complex.I*(lam:ℂ)) (physical_deformation_ne_zero lam h0 hpi) (fun _=>0) L (rootSet X)
  have hmatrix' : homogeneousLinkHamiltonian lam eta (m+1)*M=(E:ℂ) • M := by
    simpa [M,E,L,Complex.ofReal_mul] using hmatrix
  let e : RowSpins L→ℂ := Pi.single (plusSpins L) 1
  have hcolumn : M.mulVec e=physicalBetheVector lam (fun _=>0) L X := by
    rw [show e=Pi.single (plusSpins L) 1 by rfl,Matrix.mulVec_single_one]
    funext q
    exact (physicalBetheVector_eq_betheState_column lam h0 hpi (fun _=>0) L X
      hroots.1.injective q).symm
  have hfull : (homogeneousLinkHamiltonian lam eta (m+1)).mulVec
      (physicalBetheVector lam (fun _=>0) L X)=(E:ℂ) •
        physicalBetheVector lam (fun _=>0) L X := by
    have h := congrArg (fun A : Matrix (RowSpins L) (RowSpins L) ℂ=>A.mulVec e) hmatrix'
    rw [← Matrix.mulVec_mulVec] at h
    simp only [Matrix.smul_mulVec] at h
    simpa [hcolumn] using h
  have hsector : (complexSectorHamiltonian lam eta m n).mulVec V=(E:ℂ) • V := by
    funext q
    rw [complexSectorHamiltonian_mulVec_eq_full,
      physicalSectorExtension_restriction_eq _
        (physicalBetheVector_sector lam (fun _=>0) L X)]
    exact congrFun hfull q.val
  have hsectorW : (complexSectorHamiltonian lam eta m n).mulVec W=(E:ℂ) • W := by
    have hW : W=phase • V := by
      funext q
      simp [W,Pi.smul_apply,smul_eq_mul]
    rw [hW,Matrix.mulVec_smul,hsector]
    simp only [smul_smul]
    congr 1
    ring
  have hwEig : (realSectorHamiltonian lam eta m n).mulVec w=E • w := by
    rw [complexSectorHamiltonian_eq_real_map] at hsectorW
    funext q
    have hq := congrArg Complex.re (congrFun hsectorW q)
    simpa only [Matrix.mulVec,dotProduct,Matrix.map_apply,Pi.smul_apply,smul_eq_mul,
      Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,
      sub_zero] using hq
  have hA : ∀ q r,q≠r→(realSectorHamiltonian lam eta m n) q r≤0 := by
    intro q r hqr
    apply homogeneousLinkHamiltonian_offdiag_re_nonpos lam eta h0 hpi heta.le m q.val r.val
    intro h
    exact hqr (Subtype.ext h)
  let G := physicalSectorHoppingGraph lam eta m n
  have hG : G.Preconnected := physicalSectorHoppingGraph_preconnected lam eta h0 hpi heta m n
  have hedge : ∀ q r,G.Adj q r→(realSectorHamiltonian lam eta m n) q r<0 := by
    intro q r hqr
    exact hqr.2
  have hstrict := nonnegative_eigenvector_strictly_positive
    (realSectorHamiltonian lam eta m n) hA G hG hedge w hWnonneg hwne E hwEig
  intro q
  change 0<(V q/S).re
  rw [← hWratio q]
  exact hstrict q

/-- The sector restriction of an actual homogeneous Bethe vector. -/
def actualBetheSectorVector {m n : ℕ} (lam : ℝ) (X : Fin n→ℝ) :
    ParticleConfigurations (m+2) n→ℂ := fun q=>
  physicalBetheVector lam (fun _=>0) (m+2) X q.val

/-- The coordinate sum fixes a projective normalization of an actual sector
Bethe vector. -/
def actualBetheSectorSum {m n : ℕ} (lam : ℝ) (X : Fin n→ℝ) : ℂ :=
  ∑ q,actualBetheSectorVector (m:=m) (n:=n) lam X q

/-- Closed projective positive cone for an actual sector Bethe vector. -/
def actualBetheSectorClosedCone {m n : ℕ} (lam : ℝ) (X : Fin n→ℝ) : Prop :=
  actualBetheSectorSum (m:=m) (n:=n) lam X≠0 ∧ ∀ q,
    0≤(actualBetheSectorVector (m:=m) (n:=n) lam X q/
      actualBetheSectorSum (m:=m) (n:=n) lam X).re ∧
    (actualBetheSectorVector (m:=m) (n:=n) lam X q/
      actualBetheSectorSum (m:=m) (n:=n) lam X).im=0

/-- A continuous nonsingular on-shell root branch that starts in the
normalized positive cone stays there on any compact physical interval. -/
theorem actualBetheClosedCone_of_continuous_root_branch {m n : ℕ}
    (eta : ℝ) (heta : 0<eta) (hEven : Even (m+2)) (hfill : 2*n≤m+2)
    (a b : ℝ) (ha : 0<a) (hab : a≤b) (hb : b<Real.pi)
    (X : ℝ→Fin n→ℝ) (hXcont : ContinuousOn X (Icc a b))
    (hroots : ∀ lam,lam∈Icc a b→ConsecutiveRoots lam (fun _=>0) (m+2) (X lam) 0)
    (hdet : ∀ lam,lam∈Icc a b→(gaudinMatrix lam (fun _=>0) (m+2) (X lam)).det≠0)
    (hSlavnov : ∀ lam,lam∈Icc a b→SlavnovIdentity lam (fun _=>0) (m+2) (X lam) 0)
    (hbase : actualBetheSectorClosedCone (m:=m) (n:=n) a (X a)) :
    ∀ lam,lam∈Icc a b→actualBetheSectorClosedCone (m:=m) (n:=n) lam (X lam) := by
  classical
  let A : Set ℝ := Icc a b
  let C := {x : ℝ // x∈A}
  let F : ℝ→ParticleConfigurations (m+2) n→ℂ := fun lam q=>
    actualBetheSectorVector (m:=m) (n:=n) lam (X lam) q
  let S : ℝ→ℂ := fun lam=>∑ q,F lam q
  have hBVcont : ContinuousOn
      (fun lam=>physicalBetheVector lam (fun _=>0) (m+2) (X lam)) A := by
    intro lam hlam
    have h0lam : 0<lam := lt_of_lt_of_le ha hlam.1
    have hpilam : lam<Real.pi := lt_of_le_of_lt hlam.2 hb
    have hjoint := physicalBetheVector_joint_continuousAt lam (fun _=>0) (m+2)
      (X lam) (physical_deformation_ne_zero lam h0lam hpilam)
    exact ContinuousAt.comp₂_continuousWithinAt hjoint continuousWithinAt_id
      (hXcont.continuousWithinAt hlam)
  have hFcont (q : ParticleConfigurations (m+2) n) : ContinuousOn (fun lam=>F lam q) A := by
    intro lam hlam
    have heval : Continuous (fun v : SpinHilbert (m+2)=>v q.val) :=
      PiLp.continuous_apply 2 (fun _ : RowSpins (m+2)=>ℂ) q.val
    exact heval.continuousAt.comp_continuousWithinAt
      (by simpa [F,actualBetheSectorVector] using hBVcont lam hlam)
  have hScont : ContinuousOn S A := by
    dsimp [S]
    exact continuousOn_finsetSum Finset.univ (by intro q hq; exact hFcont q)
  let P : Set C := {x|actualBetheSectorClosedCone (m:=m) (n:=n) x.val (X x.val)}
  have hCmem (x : C) : x.val∈A := x.property
  have hClosed : IsClosed P := by
    apply IsSeqClosed.isClosed
    intro z z₀ hz hconv
    have hparam : Tendsto (fun k=>(z k).val) atTop (𝓝 z₀.val) :=
      continuous_subtype_val.continuousAt.tendsto.comp hconv
    have hparamA : Tendsto (fun k=>(z k).val) atTop (𝓝[A] z₀.val) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨hparam,Filter.Eventually.of_forall ?_⟩
      intro k
      exact hCmem (z k)
    have hFseq (q : ParticleConfigurations (m+2) n) :
        Tendsto (fun k=>F (z k).val q) atTop (𝓝 (F z₀.val q)) :=
      (hFcont q z₀.val z₀.property).tendsto.comp hparamA
    have hSseq : Tendsto (fun k=>S (z k).val) atTop (𝓝 (S z₀.val)) :=
      (hScont z₀.val z₀.property).tendsto.comp hparamA
    obtain ⟨q₀,hq₀⟩ := exists_minusCount_eq (m+2) n (by omega)
    let qInst : ParticleConfigurations (m+2) n := ⟨q₀,hq₀⟩
    letI : Nonempty (ParticleConfigurations (m+2) n) := ⟨qInst⟩
    have hroots0 := hroots z₀.val z₀.property
    have h0lam : 0<z₀.val := lt_of_lt_of_le ha z₀.property.1
    have hpilam : z₀.val<Real.pi := lt_of_le_of_lt z₀.property.2 hb
    have hVne : physicalBetheVector z₀.val (fun _=>0) (m+2) (X z₀.val)≠0 :=
      physical_bethe_ne_zero z₀.val h0lam hpilam (fun _=>0) (m+2) hEven (X z₀.val)
        hroots0.1.injective 0
        (consecutiveRoots_onShell z₀.val (fun _=>0) (m+2) hEven (X z₀.val) 0 h0lam hpilam hroots0)
        (hSlavnov z₀.val z₀.property) (hdet z₀.val z₀.property)
    have hrawne : (physicalBetheVector z₀.val (fun _=>0) (m+2) (X z₀.val)).ofLp≠0 := by
      intro hz
      apply hVne
      exact (WithLp.ofLp_eq_zero 2).mp hz
    have hsectorne : F z₀.val≠0 := by
      have hne := physical_sector_restriction_ne_zero _
        (physicalBetheVector_sector z₀.val (fun _=>0) (m+2) (X z₀.val)) hrawne
      intro hz
      apply hne
      funext q
      exact congrFun hz q
    have hsumBound (k : ℕ) (q : ParticleConfigurations (m+2) n) :
        ‖F (z k).val q‖≤‖S (z k).val‖ := by
      have hkcone : actualBetheSectorClosedCone (m:=m) (n:=n) (z k).val (X (z k).val) := by
        change actualBetheSectorClosedCone (m:=m) (n:=n) (z k).val (X (z k).val)
        exact hz k
      have hbound := normalizedCone_coordinate_norm_le (F (z k).val)
        (by simpa [F,S,actualBetheSectorClosedCone,actualBetheSectorSum,
          actualBetheSectorVector] using hkcone) q
      simpa [S] using hbound
    have hS0 : S z₀.val≠0 := by
      intro hz0
      have hzero (q : ParticleConfigurations (m+2) n) : ‖F z₀.val q‖=0 := by
        have ht := continuous_norm.continuousAt.tendsto.comp (hFseq q)
        have htr : Tendsto (fun k=>‖S (z k).val‖) atTop (𝓝 0) := by
          have ht' := continuous_norm.continuousAt.tendsto.comp hSseq
          change Tendsto (fun k=>‖S (z k).val‖) atTop (𝓝 ‖S z₀.val‖) at ht'
          simpa [hz0] using ht'
        have hle := le_of_tendsto_of_tendsto ht htr
          (Filter.Eventually.of_forall (fun k=>hsumBound k q))
        exact le_antisymm hle (norm_nonneg _)
      apply hsectorne
      funext q
      exact norm_eq_zero.mp (hzero q)
    have hcone0 : actualBetheSectorClosedCone (m:=m) (n:=n) z₀.val (X z₀.val) := by
      refine ⟨hS0,?_⟩
      intro q
      have hquot : Tendsto (fun k=>F (z k).val q/S (z k).val) atTop
          (𝓝 (F z₀.val q/S z₀.val)) := (hFseq q).div hSseq hS0
      have hreal := Complex.continuous_re.continuousAt.tendsto.comp hquot
      have hnonneg : 0≤(F z₀.val q/S z₀.val).re :=
        le_of_tendsto_of_tendsto tendsto_const_nhds hreal
          (Filter.Eventually.of_forall (fun k=>((hz k).2 q).1))
      have himag := Complex.continuous_im.continuousAt.tendsto.comp hquot
      have himagzero : Tendsto (fun k=>(F (z k).val q/S (z k).val).im) atTop (𝓝 0) := by
        have heq : (fun k=>(F (z k).val q/S (z k).val).im)=fun _=>0 := by
          funext k
          exact ((hz k).2 q).2
        rw [heq]
        exact tendsto_const_nhds
      exact ⟨hnonneg,tendsto_nhds_unique himag himagzero⟩
    change actualBetheSectorClosedCone z₀.val (X z₀.val)
    exact hcone0
  have hOpen : IsOpen P := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    have h0z : 0<z.val := lt_of_lt_of_le ha z.property.1
    have hpiz : z.val<Real.pi := lt_of_le_of_lt z.property.2 hb
    have hconeZ : actualBetheSectorClosedCone (m:=m) (n:=n) z.val (X z.val) := by
      change actualBetheSectorClosedCone (m:=m) (n:=n) z.val (X z.val)
      exact hz
    have hstrict := physical_homogeneous_bethe_closedCone_strictly_positive
      z.val eta h0z hpiz heta hEven hfill (X z.val) (hroots z.val z.property)
      (hdet z.val z.property) (hSlavnov z.val z.property)
      (by simpa [actualBetheSectorClosedCone,actualBetheSectorSum,
        actualBetheSectorVector] using hconeZ)
    have hval : Tendsto (fun y:C=>y.val) (𝓝 z) (𝓝[A] z.val) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨continuous_subtype_val.continuousAt.tendsto,Filter.Eventually.of_forall ?_⟩
      intro y
      exact hCmem y
    have hpositive : ∀ᶠ y:C in 𝓝 z,∀ q : ParticleConfigurations (m+2) n,
        0<(F y.val q/S y.val).re := by
      rw [Filter.eventually_all]
      intro q
      have hquot : Tendsto (fun y:C=>F y.val q/S y.val) (𝓝 z)
          (𝓝 (F z.val q/S z.val)) := by
        have hq := (hFcont q z.val z.property).tendsto.comp hval
        have hs := (hScont z.val z.property).tendsto.comp hval
        exact hq.div hs hz.1
      exact (Complex.continuous_re.continuousAt.tendsto.comp hquot).eventually
        (lt_mem_nhds (hstrict q))
    filter_upwards [hpositive] with y hy
    obtain ⟨q₀,hq₀⟩ := exists_minusCount_eq (m+2) n (by omega)
    let qInst : ParticleConfigurations (m+2) n := ⟨q₀,hq₀⟩
    letI : Nonempty (ParticleConfigurations (m+2) n) := ⟨qInst⟩
    have hSy : S y.val≠0 := by
      intro hz0
      have hp := hy qInst
      simp [hz0] at hp
    let phase : ℂ := (S y.val)⁻¹
    have hphase : phase≠0 := inv_ne_zero hSy
    have hphasepos : ∀ q : ParticleConfigurations (m+2) n,
        0<(phase*F y.val q).re := by
      intro q
      have heq : phase*F y.val q=F y.val q/S y.val := by
        dsimp [phase]
        rw [div_eq_mul_inv]
        ring
      rw [heq]
      exact hy q
    obtain ⟨mu,tau,v,c,hdata,hc,hline⟩ := physical_homogeneous_bethe_ground_line_of_positive
      y.val eta (lt_of_lt_of_le ha y.property.1) (lt_of_le_of_lt y.property.2 hb) heta
      hEven hfill (X y.val) (hroots y.val y.property) (hdet y.val y.property)
      (hSlavnov y.val y.property) phase hphase hphasepos
    have hline' : F y.val=c • fun q=>(v q:ℂ) := by
      simpa [F,actualBetheSectorVector] using hline
    have hconeY : actualBetheSectorClosedCone (m:=m) (n:=n) y.val (X y.val) := by
      have hn := normalizedCone_of_positiveLine (F y.val) v c hc hdata.positive hline'
      simpa [S,actualBetheSectorSum,actualBetheSectorClosedCone] using hn
    simpa [P] using hconeY
  have hbase' : P.Nonempty := ⟨⟨a,by simp [A,hab]⟩,by simpa [P] using hbase⟩
  letI : PreconnectedSpace C := Subtype.preconnectedSpace isPreconnected_Icc
  have hall : P=Set.univ := IsClopen.eq_univ ⟨hClosed,hOpen⟩ hbase'
  intro lam hlam
  have hmem : (⟨lam,by simpa [A] using hlam⟩:C)∈P := by rw [hall]; trivial
  change actualBetheSectorClosedCone (m:=m) (n:=n) lam (X lam) at hmem
  exact hmem

/-- The actual transfer Perron line follows on the whole branch interval
once one point is identified with the positive ground line. -/
theorem actualBethePerronLine_of_continuous_root_branch {m n : ℕ}
    (eta : ℝ) (heta : 0<eta) (hEven : Even (m+2)) (hfill : 2*n≤m+2)
    (a b : ℝ) (ha : 0<a) (hab : a≤b) (hb : b<Real.pi)
    (X : ℝ→Fin n→ℝ) (hXcont : ContinuousOn X (Icc a b))
    (hroots : ∀ lam,lam∈Icc a b→ConsecutiveRoots lam (fun _=>0) (m+2) (X lam) 0)
    (hdet : ∀ lam,lam∈Icc a b→(gaudinMatrix lam (fun _=>0) (m+2) (X lam)).det≠0)
    (hSlavnov : ∀ lam,lam∈Icc a b→SlavnovIdentity lam (fun _=>0) (m+2) (X lam) 0)
    (hbase : actualBetheSectorClosedCone (m:=m) (n:=n) a (X a)) :
    ∀ lam,lam∈Icc a b→
      ∃ (mu tau : ℝ) (v : ParticleConfigurations (m+2) n→ℝ) (c : ℂ),
        PhysicalSectorPerronData lam eta m n mu tau v ∧ c≠0 ∧
          actualBetheSectorVector (m:=m) (n:=n) lam (X lam)=
            c • (fun q=>(v q:ℂ)) := by
  intro lam hlam
  have hcone := actualBetheClosedCone_of_continuous_root_branch eta heta hEven hfill
    a b ha hab hb X hXcont hroots hdet hSlavnov hbase lam hlam
  have h0lam : 0<lam := lt_of_lt_of_le ha hlam.1
  have hpilam : lam<Real.pi := lt_of_le_of_lt hlam.2 hb
  have hstrict := physical_homogeneous_bethe_closedCone_strictly_positive
    lam eta h0lam hpilam heta hEven hfill (X lam) (hroots lam hlam)
    (hdet lam hlam) (hSlavnov lam hlam)
    (by simpa [actualBetheSectorClosedCone,actualBetheSectorSum,
      actualBetheSectorVector] using hcone)
  let S := actualBetheSectorSum (m:=m) (n:=n) lam (X lam)
  let phase : ℂ := S⁻¹
  have hS : S≠0 := by simpa [S] using hcone.1
  have hphase : phase≠0 := inv_ne_zero hS
  have hpositive : ∀ q : ParticleConfigurations (m+2) n,
      0<(phase*actualBetheSectorVector (m:=m) (n:=n) lam (X lam) q).re := by
    intro q
    have heq : phase*actualBetheSectorVector (m:=m) (n:=n) lam (X lam) q=
        actualBetheSectorVector (m:=m) (n:=n) lam (X lam) q/S := by
      dsimp [phase]
      rw [div_eq_mul_inv]
      ring
    rw [heq]
    exact hstrict q
  obtain ⟨mu,tau,v,c,hdata,hc,hline⟩ := physical_homogeneous_bethe_ground_line_of_positive
    lam eta h0lam hpilam heta hEven hfill (X lam) (hroots lam hlam)
    (hdet lam hlam) (hSlavnov lam hlam) phase hphase hpositive
  have hline' : actualBetheSectorVector (m:=m) (n:=n) lam (X lam)=
      c • (fun q=>(v q:ℂ)) := by
    change (fun (q : ParticleConfigurations (m+2) n)=>
      physicalBetheVector lam (fun _=>0) (m+2) (X lam) q.val)=_
    exact hline
  exact ⟨mu,tau,v,c,hdata,hc,hline'⟩

/-- The free Slater line extends to a two-sided neighborhood of the free
parameter along the analytic Bethe-root chart. This includes the first
positive-kernel parameters immediately below `π/2`. -/
theorem actualBethePerronLine_eventually_near_free_both_sides {m n : ℕ}
    (eta : ℝ) (heta : 0<eta) (hEven : Even (m+2)) (hfill : 2*n≤m+2)
    (hA01 : ∀ Y : Fin n→ℝ, ConsecutiveRoots (Real.pi/2) (fun _=>0) (m+2) Y 0→
      SlavnovIdentity (Real.pi/2) (fun _=>0) (m+2) Y 0) :
    ∃ psi : ℝ→Fin n→ℝ,
      ConsecutiveRoots (Real.pi/2) (fun _=>0) (m+2) (psi (Real.pi/2)) 0 ∧
      AnalyticAt ℝ psi (Real.pi/2) ∧
      ∀ᶠ lam in 𝓝 (Real.pi/2),
        ∃ (mu tau : ℝ) (v : ParticleConfigurations (m+2) n→ℝ) (c : ℂ),
          PhysicalSectorPerronData lam eta m n mu tau v ∧ c≠0 ∧
            actualBetheSectorVector (m:=m) (n:=n) lam (psi lam)=
              c • (fun q=>(v q:ℂ)) := by
  classical
  obtain ⟨psi,hroot0,hpsi,hnear⟩ := exists_analytic_roots_near_freeFermion
    (fun _=>0) (m+2) (by omega) n hfill
  refine ⟨psi,hroot0,hpsi,?_⟩
  let Y : Fin n→ℝ := psi (Real.pi/2)
  have hY : ConsecutiveRoots (Real.pi/2) (fun _=>0) (m+2) Y 0 := by simpa [Y] using hroot0
  obtain ⟨c0,hc0,hfree⟩ := actual_free_bethe_ground_line (particles:=n) m hEven
    (by omega) Y hY (hA01 Y hY)
  let phase : ℂ := c0⁻¹
  have hphase : phase≠0 := inv_ne_zero hc0
  have hFcont : ContinuousAt
      (fun x : ℝ=>physicalBetheVector x (fun _=>0) (m+2) (psi x)) (Real.pi/2) := by
    have hreg := physical_deformation_ne_zero (Real.pi/2)
      (by positivity : (0:ℝ)<Real.pi/2) (by linarith [Real.pi_pos])
    have hjoint := physicalBetheVector_joint_continuousAt (Real.pi/2) (fun _=>0)
      (m+2) Y hreg
    exact hjoint.comp₂ continuousAt_id hpsi.continuousAt
  have hpositiveEvent : ∀ᶠ lam in 𝓝 (Real.pi/2),
      ∀ q : ParticleConfigurations (m+2) n,
        0<(phase*(physicalBetheVector lam (fun _=>0) (m+2) (psi lam) q.val)).re := by
    rw [Filter.eventually_all]
    intro q
    have heval : ContinuousAt
        (fun lam : ℝ=>physicalBetheVector lam (fun _=>0) (m+2) (psi lam) q.val)
        (Real.pi/2) := by
      have heval : Continuous (fun v : SpinHilbert (m+2)=>v q.val) :=
        PiLp.continuous_apply 2 (fun _ : RowSpins (m+2)=>ℂ) q.val
      exact heval.continuousAt.comp hFcont
    have hmul : ContinuousAt (fun lam : ℝ=>phase*
        physicalBetheVector lam (fun _=>0) (m+2) (psi lam) q.val) (Real.pi/2) :=
      continuousAt_const.mul heval
    have hreal := Complex.continuous_re.continuousAt.comp hmul
    have hfreeq : phase*(physicalBetheVector (Real.pi/2) (fun _=>0) (m+2) Y q.val)=
        spinFreeSlaterVector (m+2) Y q := by
      have hq := congrFun hfree q
      have hq' : physicalBetheVector (Real.pi/2) (fun _=>0) (m+2) Y q.val=
          c0*spinFreeSlaterVector (m+2) Y q := by
        simpa only [Pi.smul_apply,smul_eq_mul] using hq
      dsimp [phase]
      rw [hq']
      rw [← mul_assoc,inv_mul_cancel₀ hc0,one_mul]
    have hpos0 : 0<(phase*(physicalBetheVector (Real.pi/2) (fun _=>0)
        (m+2) (psi (Real.pi/2)) q.val)).re := by
      rw [show psi (Real.pi/2)=Y by rfl,hfreeq]
      exact (spinFreeSlaterVector_positive (m+2) (by omega) Y hY q).2
    exact hreal.eventually (lt_mem_nhds hpos0)
  filter_upwards [hnear,hpositiveEvent] with lam hrootslam hpos
  have hroots' : ConsecutiveRoots lam (fun _=>0) (m+2) (psi lam) 0 := hrootslam.2.2.1
  have hV : physicalBetheVector lam (fun _=>0) (m+2) (psi lam)≠0 := by
    intro hz
    obtain ⟨q₀,hq₀⟩ := exists_minusCount_eq (m+2) n (by omega)
    let q : ParticleConfigurations (m+2) n := ⟨q₀,hq₀⟩
    have he := congrArg (fun z : SpinHilbert (m+2)=>z q.val) hz
    have hzero : (phase*(physicalBetheVector lam (fun _=>0) (m+2) (psi lam) q.val)).re=0 := by
      rw [he]
      simp
    exact (hpos q).ne' hzero
  obtain ⟨mu,tau,v,c,hdata,hc,hline⟩ := physical_homogeneous_bethe_ground_line_of_positive_nonzero
    lam eta hrootslam.1 hrootslam.2.1 heta hEven hfill
    (psi lam) hroots' hV phase hphase hpos
  have hline' : actualBetheSectorVector (m:=m) (n:=n) lam (psi lam)=
      c • (fun q=>(v q:ℂ)) := by
    change (fun (q : ParticleConfigurations (m+2) n)=>
      physicalBetheVector lam (fun _=>0) (m+2) (psi lam) q.val)=_
    exact hline
  exact ⟨mu,tau,v,c,hdata,hc,hline'⟩

theorem actual_interval_bounded_lipschitz_quadrature_error_all_local {n : ℕ}
    (lam : ℝ) (h0 : 0<lam) (hpi : lam<Real.pi) (Q : ℝ) (L : ℕ) (hL : 0<L)
    (hfill : 2*n≤L) (Y X : Fin n→ℝ)
    (R : ReferenceQuantileData lam h0 hpi Q L Y)
    (hroots : ConsecutiveRoots lam (fun _=>0) L X 0)
    (M radius : ℝ) (hM : 0<M) (hrad : 0≤radius)
    (hlower : ∀ u∈Icc (-Q) Q,M≤(L:ℝ)*finiteIntervalDensity lam h0 hpi Q u)
    (hclose : ∀ j,|X j-Y j|≤radius/((L:ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j)))
    (hlarge : kernelL1Mass (kernelKPrime lam)/2+
      (kernelLogConstant lam*Real.exp (kernelLogConstant lam*(radius/M))*radius)*
        (kernelL1Mass (kernelK lam)+physicalReferenceKernelRowErrorConstant lam/M) <
      M*Real.exp (-(physicalDensityLogConstant lam*(radius/M))))
    (a b delta N scale : ℝ) (hab : a≤b) (ha : -Q≤a) (hb : b≤Q)
    (hdelta : 0<delta) (hN : 0<N) (hscale : (L:ℝ)≤scale*N)
    (hlocal : ∀ u∈Icc (a-delta) (b+delta),
      N≤countingSlope lam (fun _=>0) L X u)
    (phi : BoundedRealFunction) (K : ℝ≥0)
    (hLip : LipschitzWith K (fun x=>phi x)) :
    |(∫ x in Icc a b,phi x ∂rootQuadratureMeasure lam (fun _=>0) L X)-
      (∫ x in Icc a b,phi x)| ≤
      (((2*actualLocalPrimitiveDiscrepancyBound lam radius M+1)+
        (b-a)*(actualLocalPrimitiveDiscrepancyBound lam radius M*
          (1+1/delta+scale*homogeneousCountingCurvatureLinearConstant lam)+
          actualLocalDensityDiscrepancyBound lam radius M))/N)*
        ((K:ℝ)+‖phi‖) := by
  classical
  let Ecount := Real.exp (kernelLogConstant lam*(radius/M))*radius*
      (kernelL1Mass (kernelK lam)+physicalReferenceKernelRowErrorConstant lam/M)+
      |1-2*lam/Real.pi|/2
  let B := 2*Ecount+1/2
  let E := kernelL1Mass (kernelKPrime lam)/2+
      (kernelLogConstant lam*Real.exp (kernelLogConstant lam*(radius/M))*radius)*
        (kernelL1Mass (kernelK lam)+physicalReferenceKernelRowErrorConstant lam/M)
  let Ccurv := homogeneousCountingCurvatureLinearConstant lam
  let C := scale*Ccurv
  let rho : ℝ→ℝ := countingSlope lam (fun _=>0) L X
  let rho' : ℝ→ℝ := countingCurvature lam (fun _=>0) L X
  let P : BoundedRealFunction := (L:ℝ) • finiteIntervalCumulativeFunction lam h0 hpi Q
  let p : BoundedRealFunction := (L:ℝ) • finiteIntervalDensity lam h0 hpi Q
  have hCcurv : 0≤Ccurv := by
    dsimp [Ccurv,homogeneousCountingCurvatureLinearConstant]
    have hs0 : 0≤kernelS lam 0 := (kernelS_pos lam 0 h0 hpi).le
    have hsinHalf : 0<Real.sin (lam/2) := Real.sin_pos_of_pos_of_lt_pi
      (by positivity) (by nlinarith [hpi,Real.pi_pos])
    have hsin : 0<Real.sin lam := Real.sin_pos_of_pos_of_lt_pi h0 hpi
    positivity
  have hscale_pos : 0<scale := by
    by_contra hnot
    have hs : scale≤0 := le_of_not_gt hnot
    have hpos : (0:ℝ)<(L:ℝ) := Nat.cast_pos.mpr hL
    nlinarith [hscale,hN]
  have hC : 0≤C := by dsimp [C]; exact mul_nonneg (le_of_lt hscale_pos) hCcurv
  have hEcount : 0≤Ecount := by
    dsimp [Ecount]
    exact add_nonneg
      (mul_nonneg (mul_nonneg (Real.exp_pos _).le hrad)
        (add_nonneg (kernelL1Mass_nonneg _)
          (div_nonneg (physicalReferenceKernelRowErrorConstant_nonneg lam h0) hM.le)))
      (div_nonneg (abs_nonneg _) (by norm_num))
  have hB : 0≤B := by dsimp [B]; positivity
  have hE : 0≤E := by
    dsimp [E]
    have hk : 0≤kernelLogConstant lam := kernelLogConstant_nonneg lam
    have hfac : 0≤kernelLogConstant lam*Real.exp
        (kernelLogConstant lam*(radius/M))*radius :=
      mul_nonneg (mul_nonneg hk (Real.exp_pos _).le) hrad
    exact add_nonneg (div_nonneg (kernelL1Mass_nonneg _) (by norm_num))
      (mul_nonneg hfac
        (add_nonneg (kernelL1Mass_nonneg _)
          (div_nonneg (physicalReferenceKernelRowErrorConstant_nonneg lam h0) hM.le)))
  have hrhocont : Continuous rho := continuous_iff_continuousAt.mpr (fun x =>
    (hasDerivAt_countingSlope lam (fun _=>0) L X x h0 hpi).continuousAt)
  have hdrho (x : ℝ) : HasDerivAt rho (rho' x) x :=
    hasDerivAt_countingSlope lam (fun _=>0) L X x h0 hpi
  have hrelative (x : ℝ) (hx : x∈Icc (a-delta) (b+delta)) :
      |rho' x|≤C*rho x := by
    have hcurv := homogeneous_countingCurvature_linear_bound lam h0 hpi hfill X x
    have hscale' : (L:ℝ)*Ccurv≤scale*N*Ccurv :=
      mul_le_mul_of_nonneg_right hscale hCcurv
    have hlocal' := hlocal x hx
    calc
      |rho' x|≤(L:ℝ)*Ccurv := by
        simpa [rho',Ccurv,homogeneousCountingCurvatureLinearConstant] using hcurv
      _≤scale*N*Ccurv := hscale'
      _≤scale*rho x*Ccurv :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlocal' hscale_pos.le) hCcurv
      _=C*rho x := by dsimp [C]; ring
  have hrootpos (j : Fin n) : 0≤rho (X j) := by
    have hw : M≤(L:ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j) :=
      hlower (Y j) ⟨(R.location j).1.le,(R.location j).2.le⟩
    have hdisp : |X j-Y j|≤radius/M :=
      (hclose j).trans (div_le_div₀ hrad le_rfl hM hw)
    have hloc : X j∈Icc (-Q-radius/M) (Q+radius/M) := by
      have hd := abs_le.mp hdisp
      have hYlo : -Q≤Y j := (R.location j).1.le
      have hYhi : Y j≤Q := (R.location j).2.le
      constructor
      · have hY := (R.location j).1
        change -Q-radius/M≤X j
        linarith [hd.1,hYlo]
      · have hY := (R.location j).2
        change X j≤Q+radius/M
        linarith [hd.2,hYhi]
    have hpos := weighted_configuration_countingSlope_pos_expanded_all lam h0 hpi Q L Y X R M hM
      hlower radius hrad hclose hlarge (X j) hloc
    exact hpos.le
  have hP (x : ℝ) : P x=(L:ℝ)*finiteIntervalCumulative lam h0 hpi Q x := rfl
  have hp (x : ℝ) : p x=(L:ℝ)*finiteIntervalDensity lam h0 hpi Q x := rfl
  have hdP (x : ℝ) : HasDerivAt P (p x) x := by
    change HasDerivAt (fun y=>(L:ℝ)*finiteIntervalCumulative lam h0 hpi Q y)
      ((L:ℝ)*finiteIntervalDensity lam h0 hpi Q x) x
    exact (finiteIntervalCumulative_hasDerivAt lam h0 hpi Q x).const_mul (L:ℝ)
  have hF (x : ℝ) (hx : x∈Icc a b) : |(rootCountLe X x:ℝ)-P x|≤B := by
    have hxQ : x∈Icc (-Q) Q := ⟨ha.trans hx.1,hx.2.trans hb⟩
    have hh := weighted_rootCount_primitive_error_local_all lam h0 hpi Q L hL Y X R hroots
      M radius hM hrad hlower hclose hlarge x hxQ
    simpa [B,Ecount,hP] using hh
  have hRho (x : ℝ) (hx : x∈Icc a b) : |rho x-p x|≤E := by
    have hh := weighted_configuration_density_error_all lam h0 hpi Q L Y X R M hM
      hlower radius hrad hclose x
    simpa [rho,p,E,hp] using hh
  have hquad := interval_bounded_lipschitz_quadrature_error_of_density_data lam (fun _=>0) L X
    hroots.1 rho' hrhocont hdrho C hC P p hdP a b delta N B E hab hdelta hN
    hrelative hB hE hlocal hrootpos hF hRho phi K hLip
  simpa [B,E,C,Ccurv,Ecount,actualLocalPrimitiveDiscrepancyBound,
    actualLocalDensityDiscrepancyBound,homogeneousCountingCurvatureLinearConstant] using hquad

end
end SixVertex
