import SixVertex.BetheHilbertSpace
import SixVertex.BetheLimits
import SixVertex.HilbertDual
import SixVertex.GlobalRootFamily

namespace SixVertex
open Filter Topology Set

private noncomputable def physicalColumnMap (L : ℕ)
    (M : Matrix (RowSpins L) (RowSpins L) ℂ) : SpinHilbert L :=
  WithLp.toLp 2 (fun q => (quantumGauge L * M) q (plusSpins L))

private theorem physicalColumnMap_continuous (L : ℕ) :
    Continuous (physicalColumnMap L) := by
  unfold physicalColumnMap
  exact (PiLp.continuous_toLp 2 _).comp <| continuous_pi fun q =>
    (continuous_apply_apply q (plusSpins L)).comp (continuous_const.mul continuous_id)

private theorem physicalListVector_eq_columnState (lam : ℝ) (b : ℕ → ℝ)
    (L : ℕ) (U : List ℂ) :
    physicalListVector lam b L U =
      physicalColumnMap L (betheListState (Complex.I * (lam : ℂ))
        (fun j => (b j : ℂ)) L U) := by
  apply WithLp.ofLp_injective 2
  funext q
  simp only [physicalListVector, physicalColumnMap, betheListState, creationList]
  rw [← Matrix.mul_assoc, mul_vacuumProjector]
  simp

theorem physicalBetheVector_continuous {n : ℕ} (lam : ℝ) (b : ℕ → ℝ)
    (L : ℕ) :
    Continuous (fun Y : Fin n → ℝ => physicalBetheVector lam b L Y) := by
  apply continuous_iff_continuousAt.mpr
  intro Y
  let labels : List (Fin n) := List.finRange n
  have hu : ∀ i ∈ labels, ContinuousAt (fun Z : Fin n → ℝ => (Z i : ℂ)) Y := by
    intro i hi
    exact Complex.continuous_ofReal.continuousAt.comp (continuousAt_apply i Y)
  have hstate := betheListState_tendsto (r := 𝓝 Y)
    (t := Complex.I * (lam : ℂ)) (b := fun j => (b j : ℂ)) (n := L)
    (labels := labels) (u := fun Z i => (Z i : ℂ))
    (u₀ := fun i => (Y i : ℂ)) hu
  have hmap := (physicalColumnMap_continuous L).tendsto
    (betheListState (Complex.I * (lam : ℂ)) (fun j => (b j : ℂ)) L
      (labels.map fun i => (Y i : ℂ)))
  have h := hmap.comp hstate
  change Tendsto (fun Z : Fin n → ℝ =>
    physicalListVector lam b L ((List.finRange n).map fun j => (Z j : ℂ)))
    (𝓝 Y) (𝓝 (physicalListVector lam b L
      ((List.finRange n).map fun j => (Y j : ℂ))))
  simpa only [labels, Function.comp_def, physicalListVector_eq_columnState] using h


private theorem hyperbolicR_joint_continuousAt (t x b : ℂ) (ht : Complex.sinh t ≠ 0) :
    ContinuousAt (fun p : ℂ × ℂ =>
      hyperbolicR p.1 (p.2 - b - p.1 / 2)) (t, x) := by
  have harg : ContinuousAt (fun p : ℂ × ℂ => p.2 - b - p.1 / 2) (t, x) := by
    fun_prop
  have hden : ContinuousAt (fun p : ℂ × ℂ => Complex.sinh p.1) (t, x) :=
    Complex.continuous_sinh.continuousAt.comp continuousAt_fst
  have hpar : ContinuousAt (fun p : ℂ × ℂ =>
      Complex.sinh ((p.2 - b - p.1 / 2) + p.1) / Complex.sinh p.1) (t, x) := by
    exact (Complex.continuous_sinh.continuousAt.comp (harg.add continuousAt_fst)).div hden ht
  have hmix : ContinuousAt (fun p : ℂ × ℂ =>
      Complex.sinh (p.2 - b - p.1 / 2) / Complex.sinh p.1) (t, x) := by
    exact (Complex.continuous_sinh.continuousAt.comp harg).div hden ht
  apply continuousAt_pi'
  intro i
  apply continuousAt_pi'
  intro j
  simp only [hyperbolicR, sixMatrix]
  split_ifs <;> first | exact hpar | exact hmix | exact continuousAt_const

private theorem rowBlock_joint_continuousAt (b : ℕ → ℂ) (n : ℕ)
    (a c : Fin 2) (t x : ℂ) (ht : Complex.sinh t ≠ 0)
    (q r : RowSpins n) :
    ContinuousAt (fun p : ℂ × ℂ =>
      rowBlock (fun j => hyperbolicR p.1 (p.2 - b j - p.1 / 2)) n a c q r) (t, x) := by
  induction n generalizing b a c with
  | zero =>
      simp only [rowBlock]
      split_ifs <;> exact continuousAt_const
  | succ n ih =>
      simp only [rowBlock, Fin.sum_univ_two]
      have htile0 := hyperbolicR_joint_continuousAt t x (b 0) ht
      have htile1 := hyperbolicR_joint_continuousAt t x (b 0) ht
      have htail0 := ih (fun j => b (j + 1)) 0 c q.2 r.2
      have htail1 := ih (fun j => b (j + 1)) 1 c q.2 r.2
      have htile0elem := (htile0.apply_nhds (a, q.1)).apply_nhds (0, r.1)
      have htile1elem := (htile1.apply_nhds (a, q.1)).apply_nhds (1, r.1)
      change Tendsto (fun p : ℂ × ℂ =>
        hyperbolicR p.1 (p.2 - b 0 - p.1 / 2) (a, q.1) (0, r.1) *
            rowBlock (fun j => hyperbolicR p.1 (p.2 - b (j + 1) - p.1 / 2)) n 0 c q.2 r.2 +
          hyperbolicR p.1 (p.2 - b 0 - p.1 / 2) (a, q.1) (1, r.1) *
            rowBlock (fun j => hyperbolicR p.1 (p.2 - b (j + 1) - p.1 / 2)) n 1 c q.2 r.2)
        (𝓝 (t, x)) (𝓝
          (hyperbolicR t (x - b 0 - t / 2) (a, q.1) (0, r.1) *
              rowBlock (fun j => hyperbolicR t (x - b (j + 1) - t / 2)) n 0 c q.2 r.2 +
            hyperbolicR t (x - b 0 - t / 2) (a, q.1) (1, r.1) *
              rowBlock (fun j => hyperbolicR t (x - b (j + 1) - t / 2)) n 1 c q.2 r.2))
      exact (htile0elem.mul htail0).add (htile1elem.mul htail1)

private theorem betheBlock_joint_continuousAt (b : ℕ → ℂ) (n : ℕ)
    (a c : Fin 2) (t x : ℂ) (ht : Complex.sinh t ≠ 0) :
    ContinuousAt (fun p : ℂ × ℂ => betheBlock p.1 b n p.2 a c) (t, x) := by
  apply continuousAt_pi'
  intro q
  apply continuousAt_pi'
  intro r
  exact rowBlock_joint_continuousAt b n a c t x ht q r

private theorem betheB_joint_continuousAt (b : ℕ → ℂ) (n : ℕ)
    (t x : ℂ) (ht : Complex.sinh t ≠ 0) :
    ContinuousAt (fun p : ℂ × ℂ => betheB p.1 b n p.2) (t, x) := by
  simpa only [betheB] using betheBlock_joint_continuousAt b n 0 1 t x ht

private theorem betheListState_joint_tendsto {J I : Type*} (r : Filter J)
    (t₀ : ℂ) (ht₀ : Complex.sinh t₀ ≠ 0) (b : ℕ → ℂ) (L : ℕ)
    (labels : List I) (t : J → ℂ) (u : J → I → ℂ) (u₀ : I → ℂ)
    (ht : Tendsto t r (𝓝 t₀))
    (hu : ∀ i ∈ labels, Tendsto (fun ξ => u ξ i) r (𝓝 (u₀ i))) :
    Tendsto (fun ξ => betheListState (t ξ) b L (labels.map (u ξ))) r
      (𝓝 (betheListState t₀ b L (labels.map u₀))) := by
  induction labels with
  | nil =>
      simpa [betheListState] using tendsto_const_nhds
  | cons i labels ih =>
      have hpair : Tendsto (fun ξ => (t ξ, u ξ i)) r (𝓝 (t₀, u₀ i)) :=
        ht.prodMk_nhds (hu i (by simp))
      have hhead := (betheB_joint_continuousAt b L t₀ (u₀ i) ht₀).tendsto.comp hpair
      have htail := ih (fun j hj => hu j (List.mem_cons_of_mem _ hj))
      simpa only [betheListState, List.map_cons, List.prod_cons, Function.comp_def, mul_assoc] using
        hhead.mul htail

/-- The actual Hilbert Bethe vector is jointly continuous in the physical
anisotropy and all finite real root coordinates wherever the local row is
regular. -/
theorem physicalBetheVector_joint_continuousAt {n : ℕ} (lam : ℝ)
    (b : ℕ → ℝ) (L : ℕ) (Y : Fin n → ℝ)
    (hreg : Complex.sinh (Complex.I * (lam : ℂ)) ≠ 0) :
    ContinuousAt (fun p : ℝ × (Fin n → ℝ) =>
      physicalBetheVector p.1 b L p.2) (lam, Y) := by
  have ht : ContinuousAt (fun p : ℝ × (Fin n → ℝ) => Complex.I * (p.1 : ℂ))
      (lam, Y) := by
    fun_prop
  have hu : ∀ i ∈ List.finRange n, ContinuousAt
      (fun p : ℝ × (Fin n → ℝ) => (p.2 i : ℂ)) (lam, Y) := by
    intro i hi
    have hproj : ContinuousAt (fun p : ℝ × (Fin n → ℝ) => p.2 i) (lam, Y) := by
      fun_prop
    exact Complex.continuous_ofReal.continuousAt.comp hproj
  have hstate := betheListState_joint_tendsto (r := 𝓝 (lam, Y))
    (t₀ := Complex.I * (lam : ℂ)) hreg (b := fun j => (b j : ℂ)) (L := L)
    (labels := List.finRange n) (t := fun p => Complex.I * (p.1 : ℂ))
    (u := fun p i => (p.2 i : ℂ)) (u₀ := fun i => (Y i : ℂ))
    ht hu
  have hmap := (physicalColumnMap_continuous L).tendsto
    (betheListState (Complex.I * (lam : ℂ)) (fun j => (b j : ℂ)) L
      ((List.finRange n).map fun i => (Y i : ℂ)))
  have h := hmap.comp hstate
  change Tendsto (fun p : ℝ × (Fin n → ℝ) =>
    physicalListVector p.1 b L ((List.finRange n).map fun i => (p.2 i : ℂ)))
    (𝓝 (lam, Y)) (𝓝 (physicalListVector lam b L
      ((List.finRange n).map fun i => (Y i : ℂ))))
  simpa only [physicalListVector_eq_columnState, Function.comp_def] using h

/-- The actual finite Bethe vector along the globally continued roots is
continuous throughout the physical half-interval, including the free endpoint. -/
theorem nonpositiveKernelPhysicalBetheVector_continuousOn (b : ℕ → ℝ)
    (L : ℕ) (hL : 0 < L) (n : ℕ) (hfill : 2 * n ≤ L) :
    ContinuousOn (fun lam => physicalBetheVector lam b L
      (nonpositiveKernelRoots b L hL n hfill lam)) (Ico (Real.pi / 2) Real.pi) := by
  intro lam hlam
  have hpositive : 0 < lam :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < Real.pi / 2) hlam.1
  have hreg := physical_deformation_ne_zero lam hpositive hlam.2
  have hjoint := physicalBetheVector_joint_continuousAt lam b L
    (nonpositiveKernelRoots b L hL n hfill lam) hreg
  have hroots := nonpositiveKernelRoots_continuousOn b L hL n hfill lam hlam
  exact ContinuousAt.comp₂_continuousWithinAt hjoint continuousWithinAt_id hroots


/-- At every parameter in the negative-kernel regime, A01 together with the
positive Gaudin determinant proves that the actual continued Hilbert Bethe
vector is nonzero. The Slavnov input stays explicit at that parameter. -/
theorem nonpositiveKernelPhysicalBetheVector_ne_zero (b : ℕ → ℝ)
    (L : ℕ) (hL : 0 < L) (hEven : Even L) (n : ℕ) (hfill : 2 * n ≤ L)
    (lam : ℝ) (hhalf : Real.pi / 2 ≤ lam) (hpi : lam < Real.pi)
    (hSlavnov : SlavnovIdentity lam b L
      (nonpositiveKernelRoots b L hL n hfill lam) 0) :
    physicalBetheVector lam b L (nonpositiveKernelRoots b L hL n hfill lam) ≠ 0 := by
  have hpositive : 0 < lam :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < Real.pi / 2) hhalf
  have hroots := nonpositiveKernelRoots_spec b L hL n hfill lam hhalf hpi
  have hshell := consecutiveRoots_onShell lam b L hEven
    (nonpositiveKernelRoots b L hL n hfill lam) 0 hpositive hpi hroots
  have hdet := (gaudinMatrix_posDef lam b L hL
    (nonpositiveKernelRoots b L hL n hfill lam) hhalf hpi).det_pos.ne'
  exact physical_bethe_ne_zero lam hpositive hpi b L hEven
    (nonpositiveKernelRoots b L hL n hfill lam) hroots.1.injective 0 hshell hSlavnov hdet

end SixVertex
