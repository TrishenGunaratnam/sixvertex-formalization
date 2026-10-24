import SixVertex.BetheCharge
import SixVertex.ExactScalarProducts

namespace SixVertex

/-- The quotient of old and new root factors in the paper's path corrections. -/
noncomputable def upperPathQuotient (t : ℂ) (Y T : Finset ℂ) (p : ℂ) : ℂ :=
  (∏ x ∈ T \ Y, betheF t (x-p)) / (∏ y ∈ Y \ insert p T, betheF t (y-p))

noncomputable def lowerPathQuotient (t : ℂ) (Y T : Finset ℂ) (p : ℂ) : ℂ :=
  (∏ x ∈ T \ Y, betheF t (p-x)) / (∏ y ∈ Y \ insert p T, betheF t (p-y))

noncomputable def pathVacuumBase (t : ℂ) (b : ℕ → ℂ) (L : ℕ) (Y : Finset ℂ) (p : ℂ) : ℂ :=
  vacuumA t b p L * ∏ y ∈ Y.erase p, betheF t (y-p)

noncomputable def setBetheQ (t : ℂ) (b : ℕ → ℂ) (L : ℕ) (Y : Finset ℂ) (p : ℂ) : ℂ :=
  vacuumL t b p L / vacuumA t b p L *
    ((∏ y ∈ Y, betheF t (p-y))/(∏ y ∈ Y, betheF t (y-p)))

noncomputable def pathChi (t : ℂ) (b : ℕ → ℂ) (L : ℕ) (Y : Finset ℂ) (p : ℂ) : ℂ := by
  classical
  exact if p ∈ Y then 1 else setBetheQ t b L Y p

/-- A finite product identity with every possible zero denominator retained
as an explicit hypothesis. This is the old/new-root cancellation. -/
theorem product_path_quotient (Y T : Finset ℂ) (p : ℂ) (hp : p ∉ T) (f : ℂ → ℂ)
    (hf : ∀ y ∈ Y.erase p, f y ≠ 0) :
    (∏ y ∈ Y.erase p, f y) * ((∏ x ∈ T \ Y, f x)/(∏ y ∈ Y \ insert p T, f y)) =
      ∏ x ∈ T, f x := by
  classical
  have he1 : (Y.erase p) ∩ T = Y ∩ T := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_erase]
    constructor
    · exact fun h => ⟨h.1.2,h.2⟩
    · intro h
      exact ⟨⟨fun hx => hp (hx ▸ h.2),h.1⟩,h.2⟩
  have he2 : (Y.erase p) \ T = Y \ insert p T := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert, not_or]
    tauto
  have hY := Finset.prod_inter_mul_prod_sdiff (Y.erase p) T f
  rw [he1,he2] at hY
  have hT := Finset.prod_inter_mul_prod_sdiff T Y f
  rw [Finset.inter_comm T Y] at hT
  have hn : (∏ y ∈ Y \ insert p T, f y) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro y hy
    have hh := Finset.mem_sdiff.mp hy
    exact hf y (Finset.mem_erase.mpr ⟨fun he => hh.2 (Finset.mem_insert.mpr (Or.inl he)),hh.1⟩)
  rw [← hY, ← hT]
  field_simp [hn]

theorem betheF_regular_ne {t : ℂ} {S : Finset ℂ} (h : BetheRegular t S)
    (x : ℂ) (hx : x ∈ S) (y : ℂ) (hy : y ∈ S) (hxy : x ≠ y) : betheF t (x-y) ≠ 0 :=
  div_ne_zero (h.2 x hx y hy) (h.1 x hx y hy hxy)

theorem upper_path_quotient (t : ℂ) (Y T S : Finset ℂ) (p : ℂ)
    (hY : Y ⊆ S) (hT : T ⊆ S) (hp : p ∈ S) (hpT : p ∉ T) (hreg : BetheRegular t S) :
    (∏ y ∈ Y.erase p, betheF t (y-p)) * upperPathQuotient t Y T p =
      ∏ x ∈ T, betheF t (x-p) := by
  exact product_path_quotient Y T p hpT _ (fun y hy =>
    betheF_regular_ne hreg y (hY (Finset.mem_of_mem_erase hy)) p hp (Finset.mem_erase.mp hy).1)

theorem lower_path_quotient (t : ℂ) (Y T S : Finset ℂ) (p : ℂ)
    (hY : Y ⊆ S) (hT : T ⊆ S) (hp : p ∈ S) (hpT : p ∉ T) (hreg : BetheRegular t S) :
    (∏ y ∈ Y.erase p, betheF t (p-y)) * lowerPathQuotient t Y T p =
      ∏ x ∈ T, betheF t (p-x) := by
  exact product_path_quotient Y T p hpT _ (fun y hy =>
    betheF_regular_ne hreg p hp y (hY (Finset.mem_of_mem_erase hy)) (Finset.mem_erase.mp hy).1.symm)

theorem pathVacuumBase_ne_zero (t : ℂ) (b : ℕ → ℂ) (L : ℕ) (Y S : Finset ℂ)
    (hY : Y ⊆ S) (p : ℂ) (hp : p ∈ S) (hreg : BetheRegular t S)
    (ha : vacuumA t b p L ≠ 0) : pathVacuumBase t b L Y p ≠ 0 := by
  exact mul_ne_zero ha (Finset.prod_ne_zero_iff.mpr (fun y hy =>
    betheF_regular_ne hreg y (hY (Finset.mem_of_mem_erase hy)) p hp (Finset.mem_erase.mp hy).1))

/-- The on-shell lower base equals the upper base on an original root;
off an original root their ratio is q. This fixes the self-factor sign. -/
theorem path_lower_base (t : ℂ) (b : ℕ → ℂ) (L : ℕ) (Y S : Finset ℂ)
    (hY : Y ⊆ S) (p : ℂ) (hp : p ∈ S) (hreg : BetheRegular t S)
    (ha : vacuumA t b p L ≠ 0) (hShell : BalancedRoots t b L 0 Y) :
    pathVacuumBase t b L Y p * pathChi t b L Y p =
      vacuumL t b p L * ∏ y ∈ Y.erase p, betheF t (p-y) := by
  classical
  by_cases hpy : p ∈ Y
  · have h := hShell p hpy
    simpa [pathVacuumBase, pathChi, hpy] using h
  · have hP : (∏ y ∈ Y, betheF t (y-p)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro y hy
      exact betheF_regular_ne hreg y (hY hy) p hp (fun he => hpy (he ▸ hy))
    simp only [pathChi, hpy, ite_false, pathVacuumBase, Finset.erase_eq_of_notMem hpy, setBetheQ]
    field_simp [ha,hP]
    <;> ring

noncomputable def upperPathCorrection (t : ℂ) (Y T : Finset ℂ) (v p : ℂ) : ℂ :=
  betheBeta t (v-p) * upperPathQuotient t Y T p

noncomputable def lowerPathCorrection (t : ℂ) (b : ℕ → ℂ) (L : ℕ) (Y T : Finset ℂ) (v p : ℂ) : ℂ :=
  pathChi t b L Y p * betheBeta t (p-v) * lowerPathQuotient t Y T p

noncomputable def doublePathCorrection (t : ℂ) (b : ℕ → ℂ) (L : ℕ)
    (Y T : Finset ℂ) (v p q : ℂ) : ℂ :=
  pathChi t b L Y q * betheBeta t (v-p) * betheBeta t (q-v) * betheF t (q-p) *
    upperPathQuotient t Y T p * lowerPathQuotient t Y T q

theorem upper_path_coefficient (t : ℂ) (b : ℕ → ℂ) (L : ℕ) (Y T S : Finset ℂ) (p v : ℂ)
    (hY : Y ⊆ S) (hT : T ⊆ S) (hp : p ∈ S) (hpT : p ∉ T) (hreg : BetheRegular t S) :
    pathVacuumBase t b L Y p * upperPathCorrection t Y T v p =
      vacuumA t b p L * betheBeta t (v-p) * ∏ x ∈ T, betheF t (x-p) := by
  have h := upper_path_quotient t Y T S p hY hT hp hpT hreg
  unfold pathVacuumBase upperPathCorrection
  linear_combination (vacuumA t b p L * betheBeta t (v-p))*h

theorem lower_path_coefficient (t : ℂ) (b : ℕ → ℂ) (L : ℕ) (Y T S : Finset ℂ) (p v : ℂ)
    (hY : Y ⊆ S) (hT : T ⊆ S) (hp : p ∈ S) (hpT : p ∉ T) (hreg : BetheRegular t S)
    (ha : vacuumA t b p L ≠ 0) (hShell : BalancedRoots t b L 0 Y) :
    pathVacuumBase t b L Y p * lowerPathCorrection t b L Y T v p =
      vacuumL t b p L * betheBeta t (p-v) * ∏ x ∈ T, betheF t (p-x) := by
  have hb := path_lower_base t b L Y S hY p hp hreg ha hShell
  have h := lower_path_quotient t Y T S p hY hT hp hpT hreg
  unfold lowerPathCorrection
  calc
    _ = (pathVacuumBase t b L Y p * pathChi t b L Y p)*
      lowerPathQuotient t Y T p * betheBeta t (p-v) := by ring
    _ = vacuumL t b p L * ((∏ y ∈ Y.erase p, betheF t (p-y))*lowerPathQuotient t Y T p) * betheBeta t (p-v) := by rw [hb]; ring
    _ = _ := by rw [h]; ring

/-- The ordered two-removal coefficient has exactly the extra f(q-p)
factor in the paper, after extracting one vacuum base for each removal. -/
theorem double_path_coefficient (t : ℂ) (b : ℕ → ℂ) (L : ℕ) (Y T S : Finset ℂ) (p q v : ℂ)
    (hY : Y ⊆ S) (hT : T ⊆ S) (hp : p ∈ S) (hq : q ∈ S)
    (hpT : p ∉ T) (hqT : q ∉ T) (hreg : BetheRegular t S)
    (haq : vacuumA t b q L ≠ 0) (hShell : BalancedRoots t b L 0 Y) :
    pathVacuumBase t b L Y p * pathVacuumBase t b L Y q * doublePathCorrection t b L Y T v p q =
      vacuumA t b p L * vacuumL t b q L * betheBeta t (v-p) * betheBeta t (q-v) *
        betheF t (q-p) * ∏ x ∈ T, betheF t (x-p)*betheF t (q-x) := by
  calc
    _ = (pathVacuumBase t b L Y p * upperPathCorrection t Y T v p) *
      (pathVacuumBase t b L Y q * lowerPathCorrection t b L Y T v q) * betheF t (q-p) := by
        unfold upperPathCorrection lowerPathCorrection doublePathCorrection
        ring
    _ = _ := by
      rw [upper_path_coefficient t b L Y T S p v hY hT hp hpT hreg,
        lower_path_coefficient t b L Y T S q v hY hT hq hqT hreg haq hShell]
      rw [Finset.prod_mul_distrib]
      ring

/-- The finite-set q used in the path bookkeeping is the same q as in the
paper at every generic added spectral argument. -/
theorem setBetheQ_eq {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (hY : Function.Injective Y) (p : ℂ)
    (hcross : ∀ y ∈ rootSet Y, Complex.sinh (p-y) ≠ 0) :
    setBetheQ (Complex.I*lam) (fun j => (b j : ℂ)) L (rootSet Y) p = betheQ lam b L Y p := by
  have he : (∏ y ∈ rootSet Y, Complex.sinh (p-y+Complex.I*lam)/Complex.sinh (p-y-Complex.I*lam)) =
      (∏ y ∈ rootSet Y, betheF (Complex.I*lam) (p-y))/(∏ y ∈ rootSet Y, betheF (Complex.I*lam) (y-p)) := by
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro y hy
    rw [shifted_ratio_as_f _ _ (hcross y hy)]
    congr 2
    ring
  unfold setBetheQ betheQ
  rw [← prod_rootSet Y hY (fun y => Complex.sinh (p-y+Complex.I*lam)/Complex.sinh (p-y-Complex.I*lam)), he]

/-- At a new argument the uniform vacuum base is exactly a(p) F_Y(p). -/
theorem pathVacuumBase_new {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (hY : Function.Injective Y) (p : ℂ) (hp : p ∉ rootSet Y) :
    pathVacuumBase (Complex.I*lam) (fun j => (b j : ℂ)) L (rootSet Y) p = extractedVacuum lam b L Y p := by
  unfold pathVacuumBase extractedVacuum betheFProduct
  rw [Finset.erase_eq_of_notMem hp, prod_rootSet Y hY]

end SixVertex
