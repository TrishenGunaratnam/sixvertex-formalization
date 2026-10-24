import SixVertex.MarkedWords

namespace SixVertex

noncomputable def spinExpectationLinear (L : ℕ) (v : SpinHilbert L) :
    Matrix (RowSpins L) (RowSpins L) ℂ →ₗ[ℂ] ℂ where
  toFun M := inner ℂ v (hilbertMatrixAction L M v)
  map_add' M N := by
    have he : hilbertMatrixAction L (M+N) v = hilbertMatrixAction L M v + hilbertMatrixAction L N v := by
      apply WithLp.ofLp_injective 2
      exact Matrix.add_mulVec _ _ _
    rw [he,inner_add_right]
  map_smul' a M := by
    have he : hilbertMatrixAction L (a • M) v = a • hilbertMatrixAction L M v := by
      apply WithLp.ofLp_injective 2
      exact Matrix.smul_mulVec _ _ _
    rw [he,inner_smul_right]
    rfl

theorem spinExpectationLinear_apply (L : ℕ) (v : SpinHilbert L)
    (M : Matrix (RowSpins L) (RowSpins L) ℂ) :
    spinExpectationLinear L v M = inner ℂ v (hilbertMatrixAction L M v) := rfl

theorem marked_unit_entry_expansion {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (w : List (Matrix (Fin 2) (Fin 2) ℂ × ℂ)) :
    inner ℂ (physicalUnitBetheVector lam b L Y)
      (hilbertMatrixAction L (normalizedMarkedWord lam b L Y w) (physicalUnitBetheVector lam b L Y)) =
      ((markedWordChoices w).map (fun z => z.1 * inner ℂ (physicalUnitBetheVector lam b L Y)
        (hilbertMatrixAction L (normalizedPhysicalWord lam b L Y z.2) (physicalUnitBetheVector lam b L Y)))).sum := by
  have he := congrArg (spinExpectationLinear L (physicalUnitBetheVector lam b L Y))
    (marked_word_entry_expansion lam b L Y w)
  simpa only [map_list_sum,List.map_map,Function.comp_def,map_smul,smul_eq_mul,spinExpectationLinear_apply] using he

def MarkedWordRegular (t : ℂ) (U : Finset ℂ) : List (Matrix (Fin 2) (Fin 2) ℂ × ℂ) → Prop
  | [] => True
  | (_,x)::w => x ∉ U ∧ BetheRegular t (insert x U) ∧ MarkedWordRegular t (insert x U) w

theorem markedWordChoices_regular (t : ℂ) (U : Finset ℂ)
    (w : List (Matrix (Fin 2) (Fin 2) ℂ × ℂ)) (hw : MarkedWordRegular t U w)
    (z : ℂ × List (RowEntry × ℂ)) (hz : z ∈ markedWordChoices w) : WordRegular t U z.2 := by
  induction w generalizing U z with
  | nil => simp only [markedWordChoices,List.mem_singleton] at hz; subst z; trivial
  | cons ev w ih =>
    rcases ev with ⟨D,x⟩
    obtain ⟨y,hy,hr⟩ := List.mem_flatMap.mp hz
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hr
    have harg : y.2.2 = x := by
      simp [markedEntryChoices] at hy
      rcases hy with rfl | rfl | rfl | rfl <;> rfl
    exact ⟨harg ▸ hw.1,harg ▸ hw.2.1,harg ▸ ih (insert x U) hw.2.2 q hq⟩

theorem markedWordChoices_argument_property (P : ℂ → Prop)
    (w : List (Matrix (Fin 2) (Fin 2) ℂ × ℂ)) (hw : ∀ ev ∈ w, P ev.2)
    (z : ℂ × List (RowEntry × ℂ)) (hz : z ∈ markedWordChoices w) : ∀ ev ∈ z.2, P ev.2 := by
  intro ev hev
  have hx : ev.2 ∈ z.2.map Prod.snd := List.mem_map.mpr ⟨ev,hev,rfl⟩
  rw [markedWordChoices_arguments w z hz] at hx
  obtain ⟨dx,hdx,heq⟩ := List.mem_map.mp hx
  exact heq ▸ hw dx hdx

theorem markedWordChoices_qProduct (t : ℂ) (b : ℕ → ℂ) (L : ℕ) (Y : Finset ℂ)
    (w : List (Matrix (Fin 2) (Fin 2) ℂ × ℂ)) (z : ℂ × List (RowEntry × ℂ))
    (hz : z ∈ markedWordChoices w) :
    wordQProduct t b L Y z.2 = (w.map (fun ev => 1+setBetheQ t b L Y ev.2)).prod := by
  have he := congrArg (fun xs : List ℂ => (xs.map (fun x => 1+setBetheQ t b L Y x)).prod)
    (markedWordChoices_arguments w z hz)
  simpa only [wordQProduct,List.map_map,Function.comp_def] using he

/-- Full arbitrary-mark expectation, as a sum of ordered entry-word paths.
The marks multiply the exact gamma/parity contribution, not its modulus. -/
theorem unit_marked_word_expectation {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (k : ℕ) (Y : Fin n → ℝ) (hYinj : Function.Injective Y)
    (hShell : OnShell lam b (2*k) Y 0) (hSlavnov : SlavnovIdentity lam b (2*k) Y 0)
    (hdet : (gaudinMatrix lam b (2*k) Y).det ≠ 0) (S : Finset ℂ) (hY : rootSet Y ⊆ S)
    (w : List (Matrix (Fin 2) (Fin 2) ℂ × ℂ)) (hw : ∀ ev ∈ w, ev.2 ∈ S)
    (hreg : BetheRegular (Complex.I*lam) S)
    (ha : ∀ p ∈ S, vacuumA (Complex.I*lam) (fun j => (b j : ℂ)) p (2*k) ≠ 0)
    (hfresh : MarkedWordRegular (Complex.I*lam) (rootSet Y) w)
    (hgeneric : ∀ ev ∈ w, ev.2 ∉ rootSet Y ∧ ∀ y ∈ rootSet Y, Complex.sinh (ev.2-y) ≠ 0)
    (hQ : (w.map (fun ev => 1+setBetheQ (Complex.I*lam) (fun j => (b j : ℂ)) (2*k) (rootSet Y) ev.2)).prod ≠ 0) :
    inner ℂ (physicalUnitBetheVector lam b (2*k) Y)
      (hilbertMatrixAction (2*k) (normalizedMarkedWord lam b (2*k) Y w)
        (physicalUnitBetheVector lam b (2*k) Y)) =
      ((markedWordChoices w).map (fun z => z.1 *
        weightedEval (normalizedEndpointAmplitude lam b (2*k) Y z.2)
          (relativeCorrectionWords lam b (2*k) Y z.2 (rootSet Y)))).sum := by
  rw [marked_unit_entry_expansion]
  congr 1
  apply List.map_congr_left
  intro z hz
  congr 1
  exact unit_word_expectation_expansion lam h0 hpi b k Y hYinj hShell hSlavnov hdet S hY z.2
    (markedWordChoices_argument_property _ w hw z hz) hreg ha
    (onShell_balancedRoots lam h0 hpi b (2*k) Y hYinj 0 hShell)
    (markedWordChoices_regular _ _ w hfresh z hz)
    (markedWordChoices_argument_property (fun x => x ∉ rootSet Y ∧ ∀ y ∈ rootSet Y, Complex.sinh (x-y) ≠ 0) w hgeneric z hz)
    (by rw [markedWordChoices_qProduct _ _ _ _ w z hz]; exact hQ)

end SixVertex
