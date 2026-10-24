import SixVertex.VacuumCancellation

namespace SixVertex
open scoped ComplexConjugate

noncomputable def vacuumColumn (L : ℕ)
    (M : Matrix (RowSpins L) (RowSpins L) ℂ) : SpinHilbert L :=
  WithLp.toLp 2 (fun q => M q (plusSpins L))

noncomputable def vacuumColumnLinear (L : ℕ) :
    Matrix (RowSpins L) (RowSpins L) ℂ →ₗ[ℂ] SpinHilbert L where
  toFun := vacuumColumn L
  map_add' M N := by
    apply WithLp.ofLp_injective 2
    rfl
  map_smul' a M := by
    apply WithLp.ofLp_injective 2
    rfl

theorem hilbertMatrixAction_vacuumColumn (L : ℕ)
    (M N : Matrix (RowSpins L) (RowSpins L) ℂ) :
    hilbertMatrixAction L M (vacuumColumn L N) = vacuumColumn L (M*N) := by
  apply WithLp.ofLp_injective 2
  rfl

theorem hilbertMatrixAction_smul (L : ℕ) (M : Matrix (RowSpins L) (RowSpins L) ℂ)
    (a : ℂ) (v : SpinHilbert L) :
    hilbertMatrixAction L M (a • v) = a • hilbertMatrixAction L M v := by
  apply WithLp.ofLp_injective 2
  exact Matrix.mulVec_smul _ _ _

/-- Unit-vector expectations are the unnormalized inner product divided by
its squared norm, with the actual Hilbert norm. -/
theorem normalized_spin_expectation (L : ℕ) (M : Matrix (RowSpins L) (RowSpins L) ℂ)
    (v : SpinHilbert L) (hv : v ≠ 0) :
    inner ℂ (normalizeSpinVector v) (hilbertMatrixAction L M (normalizeSpinVector v)) =
      inner ℂ v (hilbertMatrixAction L M v)/inner ℂ v v := by
  simp only [normalizeSpinVector, hilbertMatrixAction_smul, inner_smul_left,
    inner_smul_right, map_inv₀, Complex.conj_ofReal, inner_self_eq_norm_sq_to_K, Complex.ofReal_inv]
  have hn : (‖v‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hv)
  field_simp [hn]
  <;> first | ac_rfl | ring

noncomputable def physicalSetVector (lam : ℝ) (ht : Complex.sinh (Complex.I*lam) ≠ 0)
    (b : ℕ → ℝ) (L : ℕ) (U : Finset ℂ) : SpinHilbert L :=
  vacuumColumn L (quantumGauge L * betheState (Complex.I*lam) ht (fun j => (b j : ℂ)) L U)

theorem physicalSetVector_list (lam : ℝ) (ht : Complex.sinh (Complex.I*lam) ≠ 0)
    (b : ℕ → ℝ) (L : ℕ) (U : List ℂ) (hU : U.Nodup) :
    physicalSetVector lam ht b L U.toFinset = physicalListVector lam b L U := by
  apply WithLp.ofLp_injective 2
  funext q
  simp only [physicalSetVector, vacuumColumn, physicalListVector, betheState,
    creationProduct_list _ _ U hU, creationList, Matrix.mul_assoc,
    mul_vacuumProjector, ite_true]
  rw [← Matrix.mul_assoc, mul_vacuumProjector]
  simp

theorem physicalSetVector_indexed (lam : ℝ) (ht : Complex.sinh (Complex.I*lam) ≠ 0)
    (b : ℕ → ℝ) (L n : ℕ) (U : Fin n → ℂ) (hU : Function.Injective U) :
    physicalSetVector lam ht b L (Finset.univ.image U) =
      physicalListVector lam b L ((List.finRange n).map U) := by
  have hn : ((List.finRange n).map U).Nodup := (List.nodup_finRange n).map hU
  have he : ((List.finRange n).map U).toFinset = Finset.univ.image U := by
    classical
    ext x
    simp
  rw [← he]
  exact physicalSetVector_list lam ht b L _ hn

theorem physicalSetVector_roots {n : ℕ} (lam : ℝ) (ht : Complex.sinh (Complex.I*lam) ≠ 0)
    (b : ℕ → ℝ) (L : ℕ) (Y : Fin n → ℝ) (hY : Function.Injective Y) :
    physicalSetVector lam ht b L (rootSet Y) = physicalBetheVector lam b L Y :=
  physicalSetVector_indexed lam ht b L n (fun j => (Y j : ℂ))
    (fun i j h => hY (Complex.ofReal_injective h))

noncomputable def setScalarProduct {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (U : Finset ℂ) : ℂ :=
  algebraicListScalarProduct lam b L ((List.finRange n).map Y) U.toList

theorem physicalSetVector_inner {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) (hEven : Even L) (Y : Fin n → ℝ)
    (U : Finset ℂ) :
    inner ℂ (physicalBetheVector lam b L Y)
      (physicalSetVector lam (physical_deformation_ne_zero lam h0 hpi) b L U) =
      (-1 : ℂ)^n*setScalarProduct lam b L Y U := by
  have he := physicalSetVector_list lam (physical_deformation_ne_zero lam h0 hpi) b L U.toList U.nodup_toList
  simp only [Finset.toList_toFinset] at he
  rw [he]
  have h := physical_inner_algebraic_list lam h0 hpi b L hEven ((List.finRange n).map Y) U.toList
  simpa only [physicalBetheVector, List.map_map, Function.comp_def, List.length_map,
    List.length_finRange, setScalarProduct] using h

theorem setScalarProduct_indexed {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) (hEven : Even L) (Y : Fin n → ℝ)
    (U : Fin n → ℂ) (hU : Function.Injective U) :
    setScalarProduct lam b L Y (Finset.univ.image U) = algebraicScalarProduct lam b L Y U := by
  have h := physicalSetVector_inner lam h0 hpi b L hEven Y (Finset.univ.image U)
  rw [physicalSetVector_indexed lam (physical_deformation_ne_zero lam h0 hpi) b L n U hU,
    physical_inner_algebraic lam h0 hpi b L hEven Y U] at h
  exact mul_left_cancel₀ (pow_ne_zero n (by norm_num : (-1 : ℂ) ≠ 0)) h.symm

theorem setScalarProduct_wrong_card {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) (hEven : Even L) (Y : Fin n → ℝ)
    (U : Finset ℂ) (hcard : U.card ≠ n) : setScalarProduct lam b L Y U = 0 := by
  have hzero := physicalListVector_inner_zero lam b L
    ((List.finRange n).map (fun j => (Y j : ℂ))) U.toList (by simpa using hcard.symm)
  have he := physicalSetVector_list lam (physical_deformation_ne_zero lam h0 hpi) b L U.toList U.nodup_toList
  simp only [Finset.toList_toFinset] at he
  change inner ℂ (physicalBetheVector lam b L Y) (physicalListVector lam b L U.toList) = 0 at hzero
  rw [← he, physicalSetVector_inner lam h0 hpi b L hEven Y U] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero n (by norm_num))

theorem linearMap_weightedEval {R S : Type*} [AddCommMonoid R] [Module ℂ R]
    [AddCommMonoid S] [Module ℂ S] (f : R →ₗ[ℂ] S)
    (V : Finset ℂ → R) (T : List (ℂ × Finset ℂ)) :
    f (weightedEval V T) = weightedEval (fun U => f (V U)) T := by
  simp only [weightedEval, map_list_sum, List.map_map, Function.comp_def, map_smul]

noncomputable def vacuumExpectationLinear (L : ℕ) (v : SpinHilbert L) :
    Matrix (RowSpins L) (RowSpins L) ℂ →ₗ[ℂ] ℂ where
  toFun M := inner ℂ v (vacuumColumn L M)
  map_add' M N := by
    change inner ℂ v (vacuumColumnLinear L (M+N)) = _
    rw [map_add, inner_add_right]
    rfl
  map_smul' a M := by
    change inner ℂ v (vacuumColumnLinear L (a • M)) = _
    rw [map_smul, inner_smul_right]
    rfl

theorem weightedEval_div (V : Finset ℂ → ℂ) (T : List (ℂ × Finset ℂ)) (a : ℂ) :
    weightedEval V T / a = weightedEval (fun U => V U/a) T := by
  induction T with
  | nil => simp [weightedEval]
  | cons z T ih =>
    simp only [weightedEval,List.map_cons,List.sum_cons] at ih ⊢
    rw [add_div,ih]
    simp [mul_div_assoc]

noncomputable def normalizedEndpointAmplitude {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (w : List (RowEntry × ℂ)) (T : Finset ℂ) : ℂ :=
  vacuumPotential (Complex.I*lam) (fun j => (b j : ℂ)) L (rootSet Y) (rootSet Y) /
    vacuumPotential (Complex.I*lam) (fun j => (b j : ℂ)) L (rootSet Y) T *
    (setScalarProduct lam b L Y T / algebraicScalarProduct lam b L Y (fun j => (Y j : ℂ))) /
    wordQProduct (Complex.I*lam) (fun j => (b j : ℂ)) L (rootSet Y) w

/-- The expectation in the actual unit physical Bethe vector is the sum of
all ordered gamma paths, including their physical relative parities. -/
theorem unit_word_expectation_expansion {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (k : ℕ) (Y : Fin n → ℝ) (hYinj : Function.Injective Y)
    (hShell : OnShell lam b (2*k) Y 0) (hSlavnov : SlavnovIdentity lam b (2*k) Y 0)
    (hdet : (gaudinMatrix lam b (2*k) Y).det ≠ 0) (S : Finset ℂ) (hY : rootSet Y ⊆ S)
    (w : List (RowEntry × ℂ)) (hw : ∀ ev ∈ w, ev.2 ∈ S)
    (hreg : BetheRegular (Complex.I*lam) S)
    (ha : ∀ p ∈ S, vacuumA (Complex.I*lam) (fun j => (b j : ℂ)) p (2*k) ≠ 0)
    (hBalance : BalancedRoots (Complex.I*lam) (fun j => (b j : ℂ)) (2*k) 0 (rootSet Y))
    (hfresh : WordRegular (Complex.I*lam) (rootSet Y) w)
    (hgeneric : ∀ ev ∈ w, ev.2 ∉ rootSet Y ∧ ∀ y ∈ rootSet Y, Complex.sinh (ev.2-y) ≠ 0)
    (hQ : wordQProduct (Complex.I*lam) (fun j => (b j : ℂ)) (2*k) (rootSet Y) w ≠ 0) :
    inner ℂ (physicalUnitBetheVector lam b (2*k) Y)
      (hilbertMatrixAction (2*k) (normalizedPhysicalWord lam b (2*k) Y w)
        (physicalUnitBetheVector lam b (2*k) Y)) =
      weightedEval (normalizedEndpointAmplitude lam b (2*k) Y w)
        (relativeCorrectionWords lam b (2*k) Y w (rootSet Y)) := by
  let ht := physical_deformation_ne_zero lam h0 hpi
  have hEven : Even (2*k) := even_two_mul k
  have hnorm := physical_bethe_ne_zero lam h0 hpi b (2*k) hEven Y hYinj 0 hShell hSlavnov hdet
  have hN := gaudin_norm_ne_zero lam h0 hpi b (2*k) hEven Y hYinj 0 hShell
    (slavnov_source_of_identity lam b (2*k) Y 0 hSlavnov) hdet
  have hm := normalized_physical_word_expansion lam ht b k Y hYinj S hY w hw hreg ha hBalance hfresh hgeneric hQ
  have he := congrArg (vacuumExpectationLinear (2*k) (physicalBetheVector lam b (2*k) Y)) hm
  rw [linearMap_weightedEval] at he
  change inner ℂ (physicalBetheVector lam b (2*k) Y)
    (vacuumColumn (2*k) (normalizedPhysicalWord lam b (2*k) Y w *
      (quantumGauge (2*k) * betheState (Complex.I*lam) ht (fun j => (b j : ℂ)) (2*k) (rootSet Y)))) = _ at he
  rw [← hilbertMatrixAction_vacuumColumn] at he
  change inner ℂ (physicalBetheVector lam b (2*k) Y)
    (hilbertMatrixAction (2*k) (normalizedPhysicalWord lam b (2*k) Y w)
      (physicalSetVector lam ht b (2*k) (rootSet Y))) = _ at he
  rw [physicalSetVector_roots lam ht b (2*k) Y hYinj] at he
  have hright : (fun T => vacuumExpectationLinear (2*k) (physicalBetheVector lam b (2*k) Y)
      (quantumGauge (2*k) * betheState (Complex.I*lam) ht (fun j => (b j : ℂ)) (2*k) T)) =
      (fun T => (-1 : ℂ)^n*setScalarProduct lam b (2*k) Y T) := by
    funext T
    exact physicalSetVector_inner lam h0 hpi b (2*k) hEven Y T
  rw [hright] at he
  rw [physicalUnitBetheVector, normalized_spin_expectation _ _ _ hnorm, he,
    physical_bethe_inner lam h0 hpi b (2*k) hEven Y Y, weightedEval_div]
  unfold weightedEval
  simp only [List.map_map,Function.comp_def,smul_eq_mul]
  congr 1
  apply List.map_congr_left
  intro z hz
  unfold normalizedEndpointAmplitude
  have hs : (-1 : ℂ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  <;> ring

end SixVertex
