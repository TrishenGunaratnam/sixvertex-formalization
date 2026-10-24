import SixVertex.WeightedPaths

namespace SixVertex

noncomputable def wordNormalization {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (w : List (RowEntry × ℂ)) : ℂ :=
  (w.map (fun ev => (-1 : ℂ)^n * betheTau lam b L Y 0 ev.2)).prod

noncomputable def normalizedPhysicalEntry {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (e : RowEntry) (x : ℂ) : Matrix (RowSpins L) (RowSpins L) ℂ :=
  (((-1 : ℂ)^n * betheTau lam b L Y 0 x)⁻¹) • physicalEntry lam b L e x

noncomputable def normalizedPhysicalWord {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) : List (RowEntry × ℂ) → Matrix (RowSpins L) (RowSpins L) ℂ
  | [] => 1
  | (e,x)::w => normalizedPhysicalWord lam b L Y w * normalizedPhysicalEntry lam b L Y e x

theorem normalizedPhysicalWord_eq {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (w : List (RowEntry × ℂ)) :
    normalizedPhysicalWord lam b L Y w =
      (wordNormalization lam b L Y w)⁻¹ • physicalWordOperator lam b L w := by
  induction w with
  | nil => simp [normalizedPhysicalWord, wordNormalization, physicalWordOperator]
  | cons ev w ih =>
    rcases ev with ⟨e,x⟩
    simp only [normalizedPhysicalWord, normalizedPhysicalEntry, ih, wordNormalization,
      List.map_cons, List.prod_cons, mul_inv_rev, physicalWordOperator,
      smul_mul_assoc, mul_smul_comm, smul_smul]
    congr 1
    ring

noncomputable def wordQProduct (t : ℂ) (b : ℕ → ℂ) (L : ℕ) (Y : Finset ℂ)
    (w : List (RowEntry × ℂ)) : ℂ :=
  (w.map (fun ev => 1+setBetheQ t b L Y ev.2)).prod

/-- The per-step relative parity equals (-1) raised to the difference
between the input magnon number and the original magnon number. -/
theorem relativeParity_eq_zpow (a n : ℕ) :
    (-1 : ℂ)^a/(-1 : ℂ)^n = (-1 : ℂ)^((a : ℤ)-(n : ℤ)) := by
  rw [zpow_sub₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  simp

noncomputable def relativeCorrectionWords {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (w : List (RowEntry × ℂ)) (U : Finset ℂ) : List (ℂ × Finset ℂ) :=
  decoratedCorrectionWords (Complex.I*lam) (fun j => (b j : ℂ)) L (rootSet Y)
    (fun V _ _ => (-1 : ℂ)^V.card/(-1 : ℂ)^n) w U

theorem physicalWordTerms_relative {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (S U : Finset ℂ) (hY : rootSet Y ⊆ S) (hU : U ⊆ S)
    (w : List (RowEntry × ℂ)) (hw : ∀ ev ∈ w, ev.2 ∈ S)
    (hreg : BetheRegular (Complex.I*lam) S)
    (ha : ∀ p ∈ S, vacuumA (Complex.I*lam) (fun j => (b j : ℂ)) p L ≠ 0)
    (hShell : BalancedRoots (Complex.I*lam) (fun j => (b j : ℂ)) L 0 (rootSet Y))
    (hfresh : WordRegular (Complex.I*lam) U w) :
    physicalWordTerms (Complex.I*lam) (fun j => (b j : ℂ)) L w U =
      (relativeCorrectionWords lam b L Y w U).map (fun z =>
        (vacuumPotential (Complex.I*lam) (fun j => (b j : ℂ)) L (rootSet Y) U *
          addedVacuumProduct (Complex.I*lam) (fun j => (b j : ℂ)) L (rootSet Y) w *
          ((-1 : ℂ)^n)^w.length /
          vacuumPotential (Complex.I*lam) (fun j => (b j : ℂ)) L (rootSet Y) z.2*z.1,z.2)) := by
  rw [physicalWordTerms_path_factorization _ _ _ _ S U hY hU w hw hreg ha hShell hfresh]
  have he : (fun V : Finset ℂ => fun (_ : RowEntry) (_ : ℂ) => (-1 : ℂ)^V.card) =
      (fun V _ _ => (-1 : ℂ)^n*((-1 : ℂ)^V.card/(-1 : ℂ)^n)) := by
    funext V e v
    field_simp
  rw [he, decoratedCorrectionWords_scale]
  simp only [relativeCorrectionWords, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro z hz
  congr 1
  ring

theorem betheTau_path_factor {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (hY : Function.Injective Y) (v : ℂ) (hv : v ∉ rootSet Y)
    (hcross : ∀ y ∈ rootSet Y, Complex.sinh (v-y) ≠ 0) :
    betheTau lam b L Y 0 v =
      pathVacuumBase (Complex.I*lam) (fun j => (b j : ℂ)) L (rootSet Y) v *
        (1+setBetheQ (Complex.I*lam) (fun j => (b j : ℂ)) L (rootSet Y) v) := by
  rw [pathVacuumBase_new lam b L Y hY v hv, setBetheQ_eq lam b L Y hY v hcross]
  simp [betheTau, extractedVacuum]

theorem wordNormalization_factor {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (hY : Function.Injective Y) (w : List (RowEntry × ℂ))
    (hw : ∀ ev ∈ w, ev.2 ∉ rootSet Y ∧ ∀ y ∈ rootSet Y, Complex.sinh (ev.2-y) ≠ 0) :
    wordNormalization lam b L Y w = ((-1 : ℂ)^n)^w.length *
      addedVacuumProduct (Complex.I*lam) (fun j => (b j : ℂ)) L (rootSet Y) w *
      wordQProduct (Complex.I*lam) (fun j => (b j : ℂ)) L (rootSet Y) w := by
  induction w with
  | nil => simp [wordNormalization, addedVacuumProduct, wordQProduct]
  | cons ev w ih =>
    rcases ev with ⟨e,v⟩
    have hv := hw (e,v) (by simp)
    have ht : ∀ ev ∈ w, ev.2 ∉ rootSet Y ∧ ∀ y ∈ rootSet Y, Complex.sinh (ev.2-y) ≠ 0 :=
      fun ev hev => hw ev (by simp [hev])
    simp only [wordNormalization, List.map_cons, List.prod_cons] at ih ⊢
    rw [betheTau_path_factor lam b L Y hY v hv.1 hv.2, ih ht]
    simp only [addedVacuumProduct, wordQProduct, List.map_cons, List.prod_cons,
      List.length_cons, pow_succ]
    ring

/-- The full normalized physical entry word, expressed by the paper's gamma
corrections and relative parity, after cancelling all newly added vacuum bases. -/
theorem normalized_physical_word_expansion {n : ℕ} (lam : ℝ)
    (ht : Complex.sinh (Complex.I*lam) ≠ 0) (b : ℕ → ℝ) (k : ℕ)
    (Y : Fin n → ℝ) (hYinj : Function.Injective Y) (S : Finset ℂ)
    (hY : rootSet Y ⊆ S) (w : List (RowEntry × ℂ)) (hw : ∀ ev ∈ w, ev.2 ∈ S)
    (hreg : BetheRegular (Complex.I*lam) S)
    (ha : ∀ p ∈ S, vacuumA (Complex.I*lam) (fun j => (b j : ℂ)) p (2*k) ≠ 0)
    (hShell : BalancedRoots (Complex.I*lam) (fun j => (b j : ℂ)) (2*k) 0 (rootSet Y))
    (hfresh : WordRegular (Complex.I*lam) (rootSet Y) w)
    (hgeneric : ∀ ev ∈ w, ev.2 ∉ rootSet Y ∧ ∀ y ∈ rootSet Y, Complex.sinh (ev.2-y) ≠ 0)
    (hQ : wordQProduct (Complex.I*lam) (fun j => (b j : ℂ)) (2*k) (rootSet Y) w ≠ 0) :
    normalizedPhysicalWord lam b (2*k) Y w *
      (quantumGauge (2*k) * betheState (Complex.I*lam) ht (fun j => (b j : ℂ)) (2*k) (rootSet Y)) =
      weightedEval (fun T => quantumGauge (2*k) *
        betheState (Complex.I*lam) ht (fun j => (b j : ℂ)) (2*k) T)
      ((relativeCorrectionWords lam b (2*k) Y w (rootSet Y)).map (fun z =>
        (vacuumPotential (Complex.I*lam) (fun j => (b j : ℂ)) (2*k) (rootSet Y) (rootSet Y) /
          vacuumPotential (Complex.I*lam) (fun j => (b j : ℂ)) (2*k) (rootSet Y) z.2 * z.1 /
          wordQProduct (Complex.I*lam) (fun j => (b j : ℂ)) (2*k) (rootSet Y) w,z.2))) := by
  rw [normalizedPhysicalWord_eq, smul_mul_assoc, physical_word_expansion lam ht b k w _ hfresh,
    physicalWordTerms_relative lam b (2*k) Y S (rootSet Y) hY hY w hw hreg ha hShell hfresh,
    ← weightedEval_scale]
  congr 1
  simp only [List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro z hz
  have hzS : z.2 ⊆ S := by
    intro x hx
    rcases Finset.mem_union.mp (decoratedCorrectionWords_support (Complex.I*lam)
      (fun j => (b j : ℂ)) (2*k) (rootSet Y) _ w (rootSet Y) z hz hx) with h | h
    · exact hY h
    · obtain ⟨ev,hev,heq⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
      exact heq ▸ hw ev hev
  have hnz := vacuumPotential_ne_zero (Complex.I*lam) (fun j => (b j : ℂ)) (2*k)
    (rootSet Y) S z.2 hY hzS hreg ha
  have hadded : addedVacuumProduct (Complex.I*lam) (fun j => (b j : ℂ)) (2*k) (rootSet Y) w ≠ 0 := by
    unfold addedVacuumProduct
    apply List.prod_ne_zero
    intro hx
    obtain ⟨ev,hev,heq⟩ := List.mem_map.mp hx
    exact pathVacuumBase_ne_zero _ _ _ _ S hY ev.2 (hw ev hev) hreg (ha ev.2 (hw ev hev)) heq
  have hsign : (((-1 : ℂ)^n)^w.length) ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (by norm_num))
  rw [wordNormalization_factor lam b (2*k) Y hYinj w hgeneric]
  congr 1
  field_simp
  <;> ring

/-- Row normalization preserves the exact spin-selection rule. -/
theorem normalizedPhysicalWord_expectation_zero {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (k : ℕ)
    (Y : Fin n → ℝ) (w : List (RowEntry × ℂ))
    (h : (w.map (fun ev => entryCharge ev.1)).sum ≠ 0) :
    inner ℂ (physicalBetheVector lam b (2*k) Y)
      (hilbertMatrixAction (2*k) (normalizedPhysicalWord lam b (2*k) Y w)
        (physicalBetheVector lam b (2*k) Y)) = 0 := by
  rw [normalizedPhysicalWord_eq]
  have he : hilbertMatrixAction (2*k)
      ((wordNormalization lam b (2*k) Y w)⁻¹ • physicalWordOperator lam b (2*k) w)
      (physicalBetheVector lam b (2*k) Y) =
      (wordNormalization lam b (2*k) Y w)⁻¹ • hilbertMatrixAction (2*k)
        (physicalWordOperator lam b (2*k) w) (physicalBetheVector lam b (2*k) Y) := by
    apply WithLp.ofLp_injective 2
    funext q
    simp [hilbertMatrixAction, Matrix.smul_mulVec]
  rw [he, inner_smul_right]
  exact mul_eq_zero_of_right _ (physicalWord_expectation_zero lam b k _ w h)

end SixVertex
