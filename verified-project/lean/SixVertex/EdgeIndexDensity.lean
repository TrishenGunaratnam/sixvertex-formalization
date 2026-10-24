import SixVertex.PhysicalKernelTails
import SixVertex.KernelValueTail

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

def inwardCountingTail {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ) (Y : Fin n → ℝ) (j : Fin n) : ℝ :=
  (∑ a ∈ Finset.range L, kernelTail (kernelS lam) (Y j-b a))+
    ∑ i ∈ Finset.Iio j, kernelTail (fun v => -kernelK lam v) (Y j-Y i)

def outwardCountingTail {n : ℕ} (lam : ℝ) (Y : Fin n → ℝ) (j : Fin n) : ℝ :=
  ∑ i ∈ Finset.Ici j, kernelTail (fun v => -kernelK lam v) (Y j-Y i)

theorem countingTail_split_at_index {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (hfill : L=2*n) (Y : Fin n → ℝ)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (j : Fin n) :
    (∫ v in Ioi (Y j), countingSlope lam b L Y v)=inwardCountingTail lam b L Y j+outwardCountingTail lam Y j := by
  rw [countingTail_decomposition lam b L hL hfill Y hhalf hpi (Y j)]
  have hs : (Finset.univ : Finset (Fin n))=Finset.Iio j ∪ Finset.Ici j := by
    ext i
    simp only [Finset.mem_univ,Finset.mem_union,Finset.mem_Iio,Finset.mem_Ici,true_iff]
    exact lt_or_ge i j
  have hd : Disjoint (Finset.Iio j) (Finset.Ici j) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (not_lt_of_ge (Finset.mem_Ici.mp hj)) (Finset.mem_Iio.mp hi)
  unfold inwardCountingTail outwardCountingTail
  rw [hs,Finset.sum_union hd]
  ring

/-- The own-root half mass and the farther-out full masses are counted
exactly. This is the paper's outward-tail deficit bound. -/
theorem outwardCountingTail_upper {n : ℕ} (lam : ℝ) (Y : Fin n → ℝ)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (j : Fin n) :
    outwardCountingTail lam Y j ≤ kernelL1Mass (kernelK lam)*((n : ℝ)-(j.val : ℝ)-1/2) := by
  have hs : Finset.Ici j=insert j (Finset.Ioi j) := by
    ext i
    simp only [Finset.mem_Ici,Finset.mem_insert,Finset.mem_Ioi]
    constructor
    · intro hi
      rcases hi.eq_or_lt with he|hlt
      · exact Or.inl he.symm
      · exact Or.inr hlt
    · rintro (rfl|hi)
      · exact le_rfl
      · exact hi.le
  unfold outwardCountingTail
  rw [hs,Finset.sum_insert (by simp),sub_self,kernelTail_negativeKernel_zero lam hhalf hpi]
  have hb : (∑ i ∈ Finset.Ioi j, kernelTail (fun v => -kernelK lam v) (Y j-Y i)) ≤
      (n-j.val-1 : ℕ)*kernelL1Mass (kernelK lam) := by
    calc
      _ ≤ ∑ _i ∈ Finset.Ioi j, kernelL1Mass (kernelK lam) :=
        Finset.sum_le_sum (fun i _ => kernelTail_negativeKernel_le_mass lam hhalf hpi _)
      _ = _ := by
        have hc : n-1-j.val=n-j.val-1 := by omega
        simp only [Finset.sum_const,nsmul_eq_mul,Fin.card_Ioi,hc]
  have hjn := j.isLt
  rw [Nat.cast_sub (by omega : 1 ≤ n-j.val),Nat.cast_sub (by omega : j.val ≤ n),Nat.cast_one] at hb
  linarith

/-- A fixed proportion of the root's counting tail comes from inward
centers; no lower bound on the finite Gaudin bare deficit is assumed. -/
theorem inwardCountingTail_lower {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (hfill : L=2*n) (Y : Fin n → ℝ)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (hroots : ConsecutiveRoots lam b L Y 0) (j : Fin n) :
    (1-kernelL1Mass (kernelK lam))*((n : ℝ)-(j.val : ℝ)-1/2) ≤ inwardCountingTail lam b L Y j := by
  have hs := countingTail_split_at_index lam b L hL hfill Y hhalf hpi j
  rw [countingTail_at_root lam b L hL hfill Y hhalf hpi hroots j] at hs
  have ho := outwardCountingTail_upper lam Y hhalf hpi j
  nlinarith


/-- A density-to-tail constant independent of the chain and every
center. It also holds between roots on the whole real line. -/
theorem exists_countingSlope_tail_upper (lam : ℝ) (hhalf : Real.pi/2 < lam) (hpi : lam < Real.pi) :
    ∃ D : ℝ, 0 < D ∧ ∀ (n : ℕ) (b : ℕ → ℝ) (L : ℕ), 0 < L → L=2*n →
      ∀ (Y : Fin n → ℝ) (u : ℝ), countingSlope lam b L Y u ≤
        D*(∫ v in Ioi u, countingSlope lam b L Y v) := by
  have h0 : 0 < lam := by linarith [Real.pi_pos]
  let cS := Real.sin lam/(2*Real.pi)
  let CS := 2/(Real.pi*(Real.sin (lam/2))^2)
  let cK := |Real.sin (2*lam)|/(2*Real.pi)
  let CK := 2/(Real.pi*(Real.sin lam)^2)
  have hs : PositiveKernelTailData (kernelS lam) cS CS := kernelS_positive_tail_data lam h0 hpi
  have hk : PositiveKernelTailData (fun u => -kernelK lam u) cK CK := negative_kernel_positive_tail_data lam hhalf hpi
  let D : ℝ := max (2*CS/cS) (2*CK/cK)
  have hD : 0 < D := lt_max_of_lt_left (div_pos (mul_pos (by norm_num) hs.upper_pos) hs.lower_pos)
  refine ⟨D,hD,?_⟩
  intro n b L hL hfill Y u
  have hsbound (a : ℕ) : kernelS lam (u-b a) ≤ D*kernelTail (kernelS lam) (u-b a) :=
    (hs.value_le_tail (u-b a)).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (kernelTail_nonneg _ hs.nonnegative _))
  have hkbound (i : Fin n) : -kernelK lam (u-Y i) ≤ D*kernelTail (fun v => -kernelK lam v) (u-Y i) :=
    (hk.value_le_tail (u-Y i)).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (kernelTail_nonneg _ hk.nonnegative _))
  calc
    _ = (∑ a ∈ Finset.range L, kernelS lam (u-b a))+(∑ i : Fin n, -kernelK lam (u-Y i)) := by
      unfold countingSlope
      rw [Finset.sum_neg_distrib]
      ring
    _ ≤ (∑ a ∈ Finset.range L, D*kernelTail (kernelS lam) (u-b a))+
        ∑ i : Fin n, D*kernelTail (fun v => -kernelK lam v) (u-Y i) :=
      add_le_add (Finset.sum_le_sum (fun a _ => hsbound a)) (Finset.sum_le_sum (fun i _ => hkbound i))
    _ = D*((∑ a ∈ Finset.range L, kernelTail (kernelS lam) (u-b a))+
        ∑ i : Fin n, kernelTail (fun v => -kernelK lam v) (u-Y i)) := by
      rw [← Finset.mul_sum,← Finset.mul_sum,mul_add]
    _ = _ := by rw [countingTail_decomposition lam b L hL hfill Y hhalf.le hpi u]


/-- Every inward source contributes a fixed fraction of its tail to
the density. The constants are independent of finite arrays and roots. -/
theorem exists_inward_density_tail_lower (lam : ℝ) (hhalf : Real.pi/2 < lam) (hpi : lam < Real.pi) :
    ∃ d : ℝ, 0 < d ∧ ∀ (n : ℕ) (b : ℕ → ℝ) (L : ℕ) (Y : Fin n → ℝ), StrictMono Y →
      ∀ j : Fin n, (∀ a ∈ Finset.range L, b a ≤ Y j) →
        d*inwardCountingTail lam b L Y j ≤ countingSlope lam b L Y (Y j) := by
  have h0 : 0 < lam := by linarith [Real.pi_pos]
  let cS := Real.sin lam/(2*Real.pi)
  let CS := 2/(Real.pi*(Real.sin (lam/2))^2)
  let cK := |Real.sin (2*lam)|/(2*Real.pi)
  let CK := 2/(Real.pi*(Real.sin lam)^2)
  have hs : PositiveKernelTailData (kernelS lam) cS CS := kernelS_positive_tail_data lam h0 hpi
  have hk : PositiveKernelTailData (fun u => -kernelK lam u) cK CK := negative_kernel_positive_tail_data lam hhalf hpi
  let d : ℝ := min (2*cS/CS) (2*cK/CK)
  have hd : 0 < d := lt_min (div_pos (mul_pos (by norm_num) hs.lower_pos) hs.upper_pos)
    (div_pos (mul_pos (by norm_num) hk.lower_pos) hk.upper_pos)
  refine ⟨d,hd,?_⟩
  intro n b L Y hY j hcenters
  have hsbound (a : ℕ) (ha : a ∈ Finset.range L) :
      d*kernelTail (kernelS lam) (Y j-b a) ≤ kernelS lam (Y j-b a) :=
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (kernelTail_nonneg _ hs.nonnegative _)).trans
      (hs.tail_le_value (Y j-b a) (sub_nonneg.mpr (hcenters a ha)))
  have hkbound (i : Fin n) (hi : i ∈ Finset.Iio j) :
      d*kernelTail (fun v => -kernelK lam v) (Y j-Y i) ≤ -kernelK lam (Y j-Y i) :=
    (mul_le_mul_of_nonneg_right (min_le_right _ _) (kernelTail_nonneg _ hk.nonnegative _)).trans
      (hk.tail_le_value (Y j-Y i) (sub_nonneg.mpr (hY.monotone (Finset.mem_Iio.mp hi).le)))
  have hsubset : (∑ i ∈ Finset.Iio j, -kernelK lam (Y j-Y i)) ≤ ∑ i : Fin n, -kernelK lam (Y j-Y i) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => hk.nonnegative (Y j-Y i))
  unfold inwardCountingTail
  calc
    _ = (∑ a ∈ Finset.range L, d*kernelTail (kernelS lam) (Y j-b a))+
        ∑ i ∈ Finset.Iio j, d*kernelTail (fun v => -kernelK lam v) (Y j-Y i) := by
      rw [mul_add,Finset.mul_sum,Finset.mul_sum]
    _ ≤ (∑ a ∈ Finset.range L, kernelS lam (Y j-b a))+
        ∑ i ∈ Finset.Iio j, -kernelK lam (Y j-Y i) :=
      add_le_add (Finset.sum_le_sum hsbound) (Finset.sum_le_sum hkbound)
    _ ≤ (∑ a ∈ Finset.range L, kernelS lam (Y j-b a))+
        ∑ i : Fin n, -kernelK lam (Y j-Y i) := add_le_add le_rfl hsubset
    _ = _ := by unfold countingSlope; rw [Finset.sum_neg_distrib]; ring

/-- The paper's edge-index density estimate, for each root beyond the
bare centers. Both constants are chosen before every finite array. -/
theorem exists_edge_index_density_constants (lam : ℝ) (hhalf : Real.pi/2 < lam) (hpi : lam < Real.pi) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (n : ℕ) (b : ℕ → ℝ) (L : ℕ), 0 < L → L=2*n →
      ∀ (Y : Fin n → ℝ), ConsecutiveRoots lam b L Y 0 →
        ∀ j : Fin n, (∀ a ∈ Finset.range L, b a ≤ Y j) →
          c*((n : ℝ)-(j.val : ℝ)-1/2) ≤ countingSlope lam b L Y (Y j) ∧
            countingSlope lam b L Y (Y j) ≤ C*((n : ℝ)-(j.val : ℝ)-1/2) := by
  obtain ⟨D,hD,hupper⟩ := exists_countingSlope_tail_upper lam hhalf hpi
  obtain ⟨d,hd,hlower⟩ := exists_inward_density_tail_lower lam hhalf hpi
  have hsmall := kernelK_L1_mass_lt_one lam (by linarith [Real.pi_pos]) hpi
  refine ⟨d*(1-kernelL1Mass (kernelK lam)),D,mul_pos hd (sub_pos.mpr hsmall),hD,?_⟩
  intro n b L hL hfill Y hroots j hcenters
  constructor
  · calc
      _ = d*((1-kernelL1Mass (kernelK lam))*((n : ℝ)-(j.val : ℝ)-1/2)) := by ring
      _ ≤ d*inwardCountingTail lam b L Y j := mul_le_mul_of_nonneg_left
        (inwardCountingTail_lower lam b L hL hfill Y hhalf.le hpi hroots j) hd.le
      _ ≤ _ := hlower n b L Y hroots.1 j hcenters
  · have hh := hupper n b L hL hfill Y (Y j)
    rw [countingTail_at_root lam b L hL hfill Y hhalf.le hpi hroots j] at hh
    exact hh

end
end SixVertex
