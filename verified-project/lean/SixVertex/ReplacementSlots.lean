import SixVertex.BethePathNormalization

namespace SixVertex

noncomputable def deletedSlots {n : ℕ} (Y : Fin n → ℝ) (T : Finset ℂ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun j => (Y j : ℂ) ∉ T)

@[simp] theorem mem_deletedSlots {n : ℕ} (Y : Fin n → ℝ) (T : Finset ℂ) (j : Fin n) :
    j ∈ deletedSlots Y T ↔ (Y j : ℂ) ∉ T := by
  classical
  simp [deletedSlots]

theorem deletedSlots_image {n : ℕ} (Y : Fin n → ℝ) (T : Finset ℂ) :
    (deletedSlots Y T).image (fun j => (Y j : ℂ)) = rootSet Y \ T := by
  classical
  ext x
  simp only [Finset.mem_image, Finset.mem_sdiff, rootSet, Finset.mem_univ, true_and,
    mem_deletedSlots]
  constructor
  · rintro ⟨j,hj,rfl⟩
    exact ⟨⟨j,rfl⟩,hj⟩
  · rintro ⟨⟨j,rfl⟩,hj⟩
    exact ⟨j,hj,rfl⟩

theorem deletedSlots_card {n : ℕ} (Y : Fin n → ℝ) (hY : Function.Injective Y) (T : Finset ℂ) :
    (deletedSlots Y T).card = (rootSet Y \ T).card := by
  rw [← deletedSlots_image, Finset.card_image_of_injective]
  exact fun i j h => hY (Complex.ofReal_injective h)

theorem replacement_cardinality {n : ℕ} (Y : Fin n → ℝ) (hY : Function.Injective Y)
    (T : Finset ℂ) (hT : T.card = n) :
    (deletedSlots Y T).card = (T \ rootSet Y).card := by
  have h1 := Finset.card_sdiff_add_card_inter (rootSet Y) T
  have h2 := Finset.card_sdiff_add_card_inter T (rootSet Y)
  rw [Finset.inter_comm T (rootSet Y), hT] at h2
  rw [rootSet_card Y hY] at h1
  rw [deletedSlots_card Y hY T]
  omega

/-- Every equal-cardinality endpoint admits exactly the paper's replacement
slots: retained original roots stay in their original slots, and deleted slots
are bijective with surviving added arguments. -/
theorem replacement_slots_exist {n : ℕ} (Y : Fin n → ℝ) (hY : Function.Injective Y)
    (T : Finset ℂ) (hT : T.card = n) :
    ∃ V : Fin n → ℂ,
      Function.Injective V ∧
      (∀ j, j ∉ deletedSlots Y T → V j = (Y j : ℂ)) ∧
      (∀ j, j ∈ deletedSlots Y T → V j ∈ T \ rootSet Y) ∧
      Finset.univ.image V = T := by
  classical
  let H := deletedSlots Y T
  have hcard : Fintype.card H = Fintype.card ↥(T \ rootSet Y) := by
    simpa using replacement_cardinality Y hY T hT
  let e : H ≃ ↥(T \ rootSet Y) := Fintype.equivOfCardEq hcard
  let V : Fin n → ℂ := fun j => if hj : j ∈ H then (e ⟨j,hj⟩).val else (Y j : ℂ)
  have hnew (j : Fin n) (hj : j ∈ H) : V j ∈ T \ rootSet Y := by
    simpa only [V, dif_pos hj] using (e ⟨j,hj⟩).property
  have hold (j : Fin n) (hj : j ∉ H) : V j = (Y j : ℂ) := dif_neg hj
  have hroot (j : Fin n) : (Y j : ℂ) ∈ rootSet Y := by
    exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
  refine ⟨V,?_,hold,hnew,?_⟩
  · intro i j hij
    by_cases hi : i ∈ H <;> by_cases hj : j ∈ H
    · have he : e ⟨i,hi⟩ = e ⟨j,hj⟩ := Subtype.ext (by simpa only [V,dif_pos hi,dif_pos hj] using hij)
      exact congrArg Subtype.val (e.injective he)
    · have hn := (Finset.mem_sdiff.mp (hnew i hi)).2
      rw [hij,hold j hj] at hn
      exact False.elim (hn (hroot j))
    · have hn := (Finset.mem_sdiff.mp (hnew j hj)).2
      rw [← hij,hold i hi] at hn
      exact False.elim (hn (hroot i))
    · rw [hold i hi,hold j hj] at hij
      exact hY (Complex.ofReal_injective hij)
  · ext x
    constructor
    · intro hx
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
      by_cases hh : j ∈ H
      · exact (Finset.mem_sdiff.mp (hnew j hh)).1
      · rw [hold j hh]
        have hjT : ¬ (Y j : ℂ) ∉ T := by simpa only [H,mem_deletedSlots] using hh
        exact not_not.mp hjT
    · intro hx
      by_cases hxY : x ∈ rootSet Y
      · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hxY
        have hjH : j ∉ H := by simpa only [H,mem_deletedSlots] using not_not.mpr hx
        exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,hold j hjH⟩
      · let z : ↥(T \ rootSet Y) := ⟨x,Finset.mem_sdiff.mpr ⟨hx,hxY⟩⟩
        let j : H := e.symm z
        have hj : V j.val = x := by
          simp only [V,dif_pos j.property]
          exact congrArg Subtype.val (e.apply_symm_apply z)
        exact Finset.mem_image.mpr ⟨j.val,Finset.mem_univ _,hj⟩

end SixVertex
