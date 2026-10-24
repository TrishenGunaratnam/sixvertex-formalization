import SixVertex.MarkedExpectations

namespace SixVertex

noncomputable def chosenReplacementSlots {n : ℕ} (Y : Fin n → ℝ) (hY : Function.Injective Y)
    (T : Finset ℂ) (hT : T.card = n) : Fin n → ℂ :=
  Classical.choose (replacement_slots_exist Y hY T hT)

theorem chosenReplacementSlots_spec {n : ℕ} (Y : Fin n → ℝ) (hY : Function.Injective Y)
    (T : Finset ℂ) (hT : T.card = n) :
    Function.Injective (chosenReplacementSlots Y hY T hT) ∧
      (∀ j, j ∉ deletedSlots Y T → chosenReplacementSlots Y hY T hT j = (Y j : ℂ)) ∧
      (∀ j, j ∈ deletedSlots Y T → chosenReplacementSlots Y hY T hT j ∈ T \ rootSet Y) ∧
      Finset.univ.image (chosenReplacementSlots Y hY T hT) = T :=
  Classical.choose_spec (replacement_slots_exist Y hY T hT)

/-- Explicit genericity domain for every finite endpoint minor. These are
nonzero-denominator hypotheses, not additional scalar-product identities. -/
structure EndpointGeneric {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (hY : Function.Injective Y) (S : Finset ℂ) : Prop where
  source : ∀ u ∈ S, u ∉ rootSet Y → SourceRegular lam b L Y u
  cross : ∀ u ∈ S, u ∉ rootSet Y → ∀ j, Complex.sinh (u-Y j) ≠ 0
  cauchy : ∀ (T : Finset ℂ), T ⊆ S → ∀ hT : T.card = n,
    ((scalarCauchy Y (chosenReplacementSlots Y hY T hT)).submatrix
      (fun i : deletedSlots Y T => i.val) (fun j : deletedSlots Y T => j.val)).det ≠ 0

noncomputable def endpointDeterminantAmplitude {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (hY : Function.Injective Y) (w : List (RowEntry × ℂ)) (T : Finset ℂ) : ℂ := by
  classical
  exact if hT : T.card = n then
    pathDeterminantAmplitude lam b L Y w (deletedSlots Y T) (chosenReplacementSlots Y hY T hT)
    else 0

/-- All endpoints, including wrong spin sectors, are represented by the
finite determinant formula on the explicit generic domain. -/
theorem endpoint_determinant_exact {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) (hEven : Even L) (Y : Fin n → ℝ) (hY : Function.Injective Y)
    (hShell : OnShell lam b L Y 0) (hSlavnov : SlavnovIdentity lam b L Y 0)
    (hdet : (gaudinMatrix lam b L Y).det ≠ 0) (hpos : ∀ j, 0 < countingSlope lam b L Y (Y j))
    (S : Finset ℂ) (hg : EndpointGeneric lam b L Y hY S)
    (w : List (RowEntry × ℂ)) (T : Finset ℂ) (hTS : T ⊆ S) :
    normalizedEndpointAmplitude lam b L Y w T = endpointDeterminantAmplitude lam b L Y hY w T := by
  classical
  by_cases hT : T.card = n
  · let V := chosenReplacementSlots Y hY T hT
    have hs := chosenReplacementSlots_spec Y hY T hT
    have hslots : ∀ j, V j = if j ∈ deletedSlots Y T then V j else (Y j : ℂ) := by
      intro j
      by_cases hj : j ∈ deletedSlots Y T
      · simp [hj]
      · simpa only [if_neg hj] using hs.2.1 j hj
    have hnew (j : Fin n) (hj : j ∈ deletedSlots Y T) : V j ∈ T \ rootSet Y := hs.2.2.1 j hj
    have hV : ∀ j ∈ deletedSlots Y T, SourceRegular lam b L Y (V j) := fun j hj =>
      hg.source (V j) (hTS (Finset.mem_sdiff.mp (hnew j hj)).1) (Finset.mem_sdiff.mp (hnew j hj)).2
    have hc : ∀ j ∈ deletedSlots Y T, ∀ i, Complex.sinh (V j-Y i) ≠ 0 := fun j hj =>
      hg.cross (V j) (hTS (Finset.mem_sdiff.mp (hnew j hj)).1) (Finset.mem_sdiff.mp (hnew j hj)).2
    have he := normalizedEndpoint_eq_pathDeterminant lam h0 hpi b L hEven Y hY hShell hSlavnov hdet hpos
      w (deletedSlots Y T) V V hs.1 hslots hV hc (hg.cauchy T hTS hT)
    rw [hs.2.2.2] at he
    simpa only [endpointDeterminantAmplitude,dif_pos hT] using he
  · simp [endpointDeterminantAmplitude,hT,normalizedEndpointAmplitude,
      setScalarProduct_wrong_card lam h0 hpi b L hEven Y T hT]

/-- Corollary 2.6's complete marked-word determinant sum, with its actual
unit physical vector, both ordered C removals and all relative parity signs. -/
theorem exact_marked_word_determinant_sum {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (k : ℕ) (Y : Fin n → ℝ) (hYinj : Function.Injective Y)
    (hShell : OnShell lam b (2*k) Y 0) (hSlavnov : SlavnovIdentity lam b (2*k) Y 0)
    (hdet : (gaudinMatrix lam b (2*k) Y).det ≠ 0) (hpos : ∀ j, 0 < countingSlope lam b (2*k) Y (Y j))
    (S : Finset ℂ) (hY : rootSet Y ⊆ S) (hg : EndpointGeneric lam b (2*k) Y hYinj S)
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
        weightedEval (endpointDeterminantAmplitude lam b (2*k) Y hYinj z.2)
          (relativeCorrectionWords lam b (2*k) Y z.2 (rootSet Y)))).sum := by
  rw [unit_marked_word_expectation lam h0 hpi b k Y hYinj hShell hSlavnov hdet S hY w hw hreg ha hfresh hgeneric hQ]
  congr 1
  apply List.map_congr_left
  intro z hz
  congr 1
  apply weightedEval_congr
  intro q hq
  have hs := decoratedCorrectionWords_support (Complex.I*lam) (fun j => (b j : ℂ)) (2*k)
    (rootSet Y) _ z.2 (rootSet Y) q hq
  have hqS : q.2 ⊆ S := by
    intro x hx
    rcases Finset.mem_union.mp (hs hx) with h | h
    · exact hY h
    · obtain ⟨ev,hev,heq⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
      exact heq ▸ markedWordChoices_argument_property _ w hw z hz ev hev
  exact endpoint_determinant_exact lam h0 hpi b (2*k) (even_two_mul k) Y hYinj hShell hSlavnov hdet hpos
    S hg z.2 q.2 hqS

end SixVertex
