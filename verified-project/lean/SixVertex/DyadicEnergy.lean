import SixVertex.DyadicCells

namespace SixVertex
noncomputable section
open MeasureTheory Set
open scoped ENNReal

def planeSameCellPairs (j : ℕ) : Set (ℂ × ℂ) :=
  {p | planeDyadicIndex j p.1=planeDyadicIndex j p.2}

def planeClosePairs (j : ℕ) : Set (ℂ × ℂ) :=
  {p | dist p.1 p.2 ≤ ((2 : ℝ)^j)⁻¹}

def planeNeighborOffsets : Finset PlaneCellIndex :=
  (Finset.Icc (-1 : ℤ) 1).product (Finset.Icc (-1 : ℤ) 1)

theorem planeSameCellPairs_measurable (j : ℕ) : MeasurableSet (planeSameCellPairs j) := by
  exact measurableSet_eq_fun ((planeDyadicIndex_measurable j).comp measurable_fst)
    ((planeDyadicIndex_measurable j).comp measurable_snd)

theorem planeClosePairs_measurable (j : ℕ) : MeasurableSet (planeClosePairs j) := by
  exact measurableSet_le (measurable_fst.dist measurable_snd) measurable_const

theorem planeSameCellPairs_union (j : ℕ) :
    planeSameCellPairs j=⋃ k, planeDyadicCell j k ×ˢ planeDyadicCell j k := by
  ext p
  simp only [mem_iUnion,mem_prod,planeSameCellPairs,planeDyadicCell,mem_setOf_eq]
  constructor
  · intro h
    exact ⟨planeDyadicIndex j p.1,rfl,h.symm⟩
  · rintro ⟨k,hk,ht⟩
    exact hk.trans ht.symm

theorem planeSameCellPairs_mass (μ : Measure ℂ) [SFinite μ] (j : ℕ) :
    μ.prod μ (planeSameCellPairs j)=∑' k, μ (planeDyadicCell j k)*μ (planeDyadicCell j k) := by
  rw [planeSameCellPairs_union,measure_iUnion]
  · simp only [Measure.prod_prod]
  · intro k t hkt
    apply disjoint_left.mpr
    intro p hp hq
    exact (planeDyadicCell_disjoint j hkt).le_bot ⟨hp.1,hq.1⟩
  · intro k
    exact (planeDyadicCell_measurable j k).prod (planeDyadicCell_measurable j k)

theorem planeClosePairs_cover (j : ℕ) :
    planeClosePairs j ⊆ ⋃ d ∈ planeNeighborOffsets, ⋃ k,
      planeDyadicCell j k ×ˢ planeDyadicCell j (k+d) := by
  intro p hp
  let k:=planeDyadicIndex j p.1
  let d:=planeDyadicIndex j p.2-k
  have hd : d ∈ planeNeighborOffsets := by
    have hn:=planeDyadicIndex_near j p.1 p.2 hp
    change d ∈ (Finset.Icc (-1 : ℤ) 1).product (Finset.Icc (-1 : ℤ) 1)
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_Icc.mpr
      have hh:=abs_le.mp hn.1
      change -1 ≤ (planeDyadicIndex j p.2).1-(planeDyadicIndex j p.1).1 ∧
        (planeDyadicIndex j p.2).1-(planeDyadicIndex j p.1).1 ≤ 1
      omega
    · apply Finset.mem_Icc.mpr
      have hh:=abs_le.mp hn.2
      change -1 ≤ (planeDyadicIndex j p.2).2-(planeDyadicIndex j p.1).2 ∧
        (planeDyadicIndex j p.2).2-(planeDyadicIndex j p.1).2 ≤ 1
      omega
  apply mem_iUnion.mpr
  refine ⟨d,mem_iUnion.mpr ⟨hd,mem_iUnion.mpr ⟨k,?_,?_⟩⟩⟩
  · rfl
  · change planeDyadicIndex j p.2=k+(planeDyadicIndex j p.2-k)
    abel

theorem ennreal_mul_le_self_squares (a b : ℝ≥0∞) : a*b ≤ a*a+b*b := by
  rcases le_total a b with h|h
  · exact (mul_le_mul_left h b).trans (le_add_left le_rfl)
  · exact (mul_le_mul_right h a).trans (le_add_right le_rfl)

theorem shifted_cell_product_sum_bound (μ ν : Measure ℂ) [SFinite μ] [SFinite ν]
    (j : ℕ) (d : PlaneCellIndex) :
    (∑' k, μ (planeDyadicCell j k)*ν (planeDyadicCell j (k+d))) ≤
      μ.prod μ (planeSameCellPairs j)+ν.prod ν (planeSameCellPairs j) := by
  rw [planeSameCellPairs_mass,planeSameCellPairs_mass]
  calc
    _ ≤ ∑' k, (μ (planeDyadicCell j k)*μ (planeDyadicCell j k)+
        ν (planeDyadicCell j (k+d))*ν (planeDyadicCell j (k+d))) :=
      ENNReal.tsum_le_tsum (fun k => ennreal_mul_le_self_squares _ _)
    _ = _ := by
      rw [ENNReal.tsum_add]
      congr 1
      exact (Equiv.addRight d).tsum_eq (fun k => ν (planeDyadicCell j k)*ν (planeDyadicCell j k))


theorem planeClosePairs_mass_bound (μ ν : Measure ℂ) [SFinite μ] [SFinite ν] (j : ℕ) :
    μ.prod ν (planeClosePairs j) ≤ 9*(μ.prod μ (planeSameCellPairs j)+
      ν.prod ν (planeSameCellPairs j)) := by
  calc
    _ ≤ μ.prod ν (⋃ d ∈ planeNeighborOffsets, ⋃ k,
        planeDyadicCell j k ×ˢ planeDyadicCell j (k+d)) := measure_mono (planeClosePairs_cover j)
    _ ≤ ∑ d ∈ planeNeighborOffsets, μ.prod ν (⋃ k,
        planeDyadicCell j k ×ˢ planeDyadicCell j (k+d)) := measure_biUnion_finset_le _ _
    _ ≤ ∑ d ∈ planeNeighborOffsets, ∑' k,
        μ.prod ν (planeDyadicCell j k ×ˢ planeDyadicCell j (k+d)) := by
      exact Finset.sum_le_sum (fun d hd => measure_iUnion_le _)
    _ ≤ ∑ d ∈ planeNeighborOffsets,
        (μ.prod μ (planeSameCellPairs j)+ν.prod ν (planeSameCellPairs j)) := by
      apply Finset.sum_le_sum
      intro d hd
      simp only [Measure.prod_prod]
      exact shifted_cell_product_sum_bound μ ν j d
    _ = _ := by simp only [Finset.sum_const]; norm_num [planeNeighborOffsets,Finset.card_product]; rw [mul_add]

end
end SixVertex
