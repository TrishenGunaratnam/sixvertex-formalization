import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Extend

namespace SixVertex
open Filter Topology
open scoped InnerProductSpace

/-- The data preceding Lemma 6.2: a dense word core and its linear
representatives, with the actual Gram convergence (6.8). Representatives
need not extend to bounded maps on the completed limit space. -/
structure RepresentativeCore (ι H K : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (l : Filter ι) where
  core : Submodule ℂ K
  dense : Dense (core : Set K)
  repr : ι → core →ₗ[ℂ] H
  gram : ∀ u v : core, Tendsto (fun i => ⟪repr i u, repr i v⟫_ℂ) l
    (𝓝 ⟪(u : K), (v : K)⟫_ℂ)

variable {ι H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] {l : Filter ι}

/-- The paper's approximation definition of strong convergence. The
strict limsup clause is equivalently expressed using eventual bounds;
shrinking epsilon makes the two definitions identical. -/
def RepresentativeStrong (R : RepresentativeCore ι H K l) (v : ι → H) (x : K) : Prop :=
  ∀ ε > 0, ∃ u : R.core, ‖x - (u : K)‖ < ε ∧ ∀ᶠ i in l, ‖v i - R.repr i u‖ < ε

theorem representative_norm_tendsto (R : RepresentativeCore ι H K l) (u : R.core) :
    Tendsto (fun i => ‖R.repr i u‖) l (𝓝 ‖(u : K)‖) := by
  have h := (Complex.continuous_re.tendsto _).comp (R.gram u u)
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp h
  change Tendsto (fun i => Real.sqrt (RCLike.re ⟪R.repr i u,R.repr i u⟫_ℂ)) l
    (𝓝 (Real.sqrt (RCLike.re ⟪(u : K),(u : K)⟫_ℂ))) at hs
  simpa only [← norm_eq_sqrt_re_inner (𝕜 := ℂ)] using hs

theorem representative_strong_core (R : RepresentativeCore ι H K l) (u : R.core) :
    RepresentativeStrong R (fun i => R.repr i u) (u : K) := by
  intro ε hε
  exact ⟨u, by simpa, Filter.Eventually.of_forall (fun i => by simpa)⟩

theorem representative_strong_norm (R : RepresentativeCore ι H K l)
    {v : ι → H} {x : K} (hv : RepresentativeStrong R v x) :
    Tendsto (fun i => ‖v i‖) l (𝓝 ‖x‖) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨u, hu, hvu⟩ := hv (ε/4) (by positivity)
  have hr := (Metric.tendsto_nhds.mp (representative_norm_tendsto R u)) (ε/4) (by positivity)
  filter_upwards [hvu, hr] with i hi hri
  have h1 := abs_norm_sub_norm_le (v i) (R.repr i u)
  have h2 := abs_norm_sub_norm_le (u : K) x
  have htri := abs_add_three (‖v i‖ - ‖R.repr i u‖)
    (‖R.repr i u‖ - ‖(u : K)‖) (‖(u : K)‖ - ‖x‖)
  rw [Real.dist_eq] at hri ⊢
  rw [norm_sub_rev] at h2
  have heq : ‖v i‖ - ‖R.repr i u‖ + (‖R.repr i u‖ - ‖(u : K)‖) +
      (‖(u : K)‖ - ‖x‖) = ‖v i‖ - ‖x‖ := by ring
  rw [heq] at htri
  linarith

theorem representative_strong_add (R : RepresentativeCore ι H K l)
    {v w : ι → H} {x y : K} (hv : RepresentativeStrong R v x)
    (hw : RepresentativeStrong R w y) :
    RepresentativeStrong R (fun i => v i + w i) (x+y) := by
  intro ε hε
  obtain ⟨u, hu, hvu⟩ := hv (ε/2) (by positivity)
  obtain ⟨t, ht, hwt⟩ := hw (ε/2) (by positivity)
  refine ⟨u+t, ?_, ?_⟩
  · change ‖x+y-((u : K)+(t : K))‖ < ε
    have hh := norm_add_le (x-(u : K)) (y-(t : K))
    rw [show x-(u : K)+(y-(t : K)) = x+y-((u : K)+(t : K)) by abel] at hh
    linarith
  · filter_upwards [hvu,hwt] with i hi hj
    rw [map_add]
    have hh := norm_add_le (v i-R.repr i u) (w i-R.repr i t)
    rw [show v i-R.repr i u+(w i-R.repr i t) = v i+w i-(R.repr i u+R.repr i t) by abel] at hh
    linarith

theorem representative_strong_smul (R : RepresentativeCore ι H K l)
    {v : ι → H} {x : K} (hv : RepresentativeStrong R v x) (c : ℂ) :
    RepresentativeStrong R (fun i => c • v i) (c • x) := by
  intro ε hε
  have hp : 0 < ‖c‖+1 := by positivity
  obtain ⟨u, hu, hvu⟩ := hv (ε/(‖c‖+1)) (div_pos hε hp)
  refine ⟨c • u, ?_, ?_⟩
  · change ‖c • x-c • (u : K)‖ < ε
    rw [← smul_sub, norm_smul]
    have hh := (mul_lt_mul_of_pos_right hu hp)
    rw [div_mul_cancel₀ _ (ne_of_gt hp)] at hh
    nlinarith [norm_nonneg (x-(u : K)), norm_nonneg c]
  · filter_upwards [hvu] with i hi
    rw [map_smul, ← smul_sub, norm_smul]
    have hh := mul_lt_mul_of_pos_right hi hp
    rw [div_mul_cancel₀ _ (ne_of_gt hp)] at hh
    nlinarith [norm_nonneg (v i-R.repr i u), norm_nonneg c]

theorem representative_strong_sub (R : RepresentativeCore ι H K l)
    {v w : ι → H} {x y : K} (hv : RepresentativeStrong R v x)
    (hw : RepresentativeStrong R w y) :
    RepresentativeStrong R (fun i => v i-w i) (x-y) := by
  simpa only [neg_one_smul, sub_eq_add_neg] using
    representative_strong_add R hv (representative_strong_smul R hw (-1))

theorem representative_strong_unique (R : RepresentativeCore ι H K l) [NeBot l]
    {v : ι → H} {x y : K} (hx : RepresentativeStrong R v x)
    (hy : RepresentativeStrong R v y) : x=y := by
  have hh := representative_strong_norm R (representative_strong_sub R hx hy)
  simp only [sub_self, norm_zero] at hh
  have hz : ‖x-y‖ = 0 := tendsto_nhds_unique hh tendsto_const_nhds
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- The last assertion of Lemma 6.2, in the varying-representative
setting. This is not an assertion about weak convergence in one fixed
Hilbert space. -/
theorem representative_strong_of_pairings_norm (R : RepresentativeCore ι H K l)
    {v : ι → H} {x : K}
    (hp : ∀ u : R.core, Tendsto (fun i => ⟪v i,R.repr i u⟫_ℂ) l (𝓝 ⟪x,(u : K)⟫_ℂ))
    (hn : Tendsto (fun i => ‖v i‖) l (𝓝 ‖x‖)) : RepresentativeStrong R v x := by
  intro ε hε
  obtain ⟨u, hu, hdist⟩ := R.dense.exists_dist_lt x (half_pos hε)
  let t : R.core := ⟨u,hu⟩
  have ht : ‖x-(t : K)‖ < ε/2 := by simpa only [dist_eq_norm] using hdist
  have hsq : Tendsto (fun i => ‖v i-R.repr i t‖^2) l (𝓝 (‖x-(t : K)‖^2)) := by
    simp only [norm_sub_sq (𝕜 := ℂ)]
    exact ((hn.pow 2).sub (tendsto_const_nhds.mul
      ((Complex.continuous_re.tendsto _).comp (hp t)))).add
      ((representative_norm_tendsto R t).pow 2)
  have hd : Tendsto (fun i => ‖v i-R.repr i t‖) l (𝓝 ‖x-(t : K)‖) := by
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  refine ⟨t, lt_trans ht (half_lt_self hε), ?_⟩
  exact hd.eventually (gt_mem_nhds (lt_trans ht (half_lt_self hε)))

/-- Uniformly bounded core limits are automatically complex-linear;
linearity is derived from the approximating operators. -/
theorem representative_core_limit_linear (R : RepresentativeCore ι H K l) [NeBot l]
    (Tδ : ι → H →L[ℂ] H) (T : R.core → K)
    (hT : ∀ u, RepresentativeStrong R (fun i => Tδ i (R.repr i u)) (T u)) :
    ∃ T₀ : R.core →ₗ[ℂ] K, ∀ u, T₀ u = T u := by
  have ha : ∀ u v, T (u+v) = T u+T v := by
    intro u v
    apply representative_strong_unique R (hT (u+v))
    simpa only [map_add] using representative_strong_add R (hT u) (hT v)
  have hs : ∀ (c : ℂ) u, T (c • u) = c • T u := by
    intro c u
    apply representative_strong_unique R (hT (c • u))
    simpa only [map_smul] using representative_strong_smul R (hT u) c
  exact ⟨{ toFun := T, map_add' := ha, map_smul' := hs },fun u => rfl⟩

theorem representative_core_limit_bound (R : RepresentativeCore ι H K l) [NeBot l]
    (Tδ : ι → H →L[ℂ] H) (T : R.core → K) (M : ℝ)
    (hb : ∀ i, ‖Tδ i‖ ≤ M)
    (hT : ∀ u, RepresentativeStrong R (fun i => Tδ i (R.repr i u)) (T u))
    (u : R.core) : ‖T u‖ ≤ M * ‖(u : K)‖ := by
  apply le_of_tendsto_of_tendsto (representative_strong_norm R (hT u))
    (tendsto_const_nhds.mul (representative_norm_tendsto R u))
  exact Filter.Eventually.of_forall (fun i => (Tδ i).le_of_opNorm_le (hb i) _)

/-- Passing to arbitrary strongly converging representatives uses only
boundedness and a dense core. There is no global representative map. -/
theorem representative_bounded_operator_action (R : RepresentativeCore ι H K l)
    (Tδ : ι → H →L[ℂ] H) (T : K →L[ℂ] K) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ i, ‖Tδ i‖ ≤ M) (hbound : ‖T‖ ≤ M)
    (hT : ∀ u : R.core,
      RepresentativeStrong R (fun i => Tδ i (R.repr i u)) (T (u : K)))
    {v : ι → H} {x : K} (hv : RepresentativeStrong R v x) :
    RepresentativeStrong R (fun i => Tδ i (v i)) (T x) := by
  intro ε hε
  have hpos : 0 < M+1 := by linarith
  have heps : 0 < ε/(4*(M+1)) := by positivity
  obtain ⟨u,hu,hvu⟩ := hv (ε/(4*(M+1))) heps
  obtain ⟨t,ht,hut⟩ := hT u (ε/4) (by positivity)
  have hsmall : ∀ z : ℝ, 0 ≤ z → z < ε/(4*(M+1)) → M*z < ε/4 := by
    intro z hz hzl
    have hh := (lt_div_iff₀ (by positivity : 0 < 4*(M+1))).mp hzl
    nlinarith
  refine ⟨t,?_,?_⟩
  · have he := (T.le_of_opNorm_le hbound (x-(u : K))).trans_lt
      (hsmall _ (norm_nonneg _) hu)
    rw [map_sub] at he
    have hh := norm_add_le (T x-T (u : K)) (T (u : K)-(t : K))
    rw [sub_add_sub_cancel] at hh
    linarith
  · filter_upwards [hvu,hut] with i hi hj
    have he := ((Tδ i).le_of_opNorm_le (hb i) (v i-R.repr i u)).trans_lt
      (hsmall _ (norm_nonneg _) hi)
    rw [map_sub] at he
    have hh := norm_add_le (Tδ i (v i)-Tδ i (R.repr i u))
      (Tδ i (R.repr i u)-R.repr i t)
    rw [sub_add_sub_cancel] at hh
    linarith

theorem representative_operator_extension (R : RepresentativeCore ι H K l)
    [NeBot l] [CompleteSpace K]
    (Tδ : ι → H →L[ℂ] H) (T : R.core → K) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ i, ‖Tδ i‖ ≤ M)
    (hT : ∀ u, RepresentativeStrong R (fun i => Tδ i (R.repr i u)) (T u)) :
    ∃ Tbar : K →L[ℂ] K, ‖Tbar‖ ≤ M ∧ (∀ u : R.core, Tbar (u : K)=T u) ∧
      ∀ (v : ι → H) (x : K), RepresentativeStrong R v x →
        RepresentativeStrong R (fun i => Tδ i (v i)) (Tbar x) := by
  obtain ⟨T₀,hT₀⟩ := representative_core_limit_linear R Tδ T hT
  have hnorm : ∀ u, ‖T₀ u‖ ≤ M*‖R.core.subtype u‖ := by
    intro u
    rw [hT₀]
    exact representative_core_limit_bound R Tδ T M hb hT u
  have hdense : DenseRange R.core.subtype := by
    exact R.dense.denseRange_val
  let Tbar := T₀.extendOfNorm R.core.subtype
  have heq : ∀ u : R.core, Tbar (u : K)=T u := by
    intro u
    change T₀.extendOfNorm R.core.subtype (R.core.subtype u)=T u
    rw [LinearMap.extendOfNorm_eq hdense ⟨M,hnorm⟩,hT₀]
  have hbound : ‖Tbar‖ ≤ M := LinearMap.opNorm_extendOfNorm_le hdense hM hnorm
  refine ⟨Tbar,hbound,heq,?_⟩
  intro v x hv
  apply representative_bounded_operator_action R Tδ Tbar M hM hb hbound ?_ hv
  intro u
  rw [heq]
  exact hT u

/-- Ordered composition of representative limits. Neither the finite
operators nor their limit operators are required to commute. -/
theorem representative_operator_composition (R : RepresentativeCore ι H K l)
    (Tδ Sδ : ι → H →L[ℂ] H) (T S : K →L[ℂ] K)
    (M N : ℝ) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hTb : ∀ i, ‖Tδ i‖ ≤ M) (hSb : ∀ i, ‖Sδ i‖ ≤ N)
    (hTbound : ‖T‖ ≤ M) (hSbound : ‖S‖ ≤ N)
    (hT : ∀ u : R.core, RepresentativeStrong R (fun i => Tδ i (R.repr i u)) (T (u : K)))
    (hS : ∀ u : R.core, RepresentativeStrong R (fun i => Sδ i (R.repr i u)) (S (u : K)))
    {v : ι → H} {x : K} (hv : RepresentativeStrong R v x) :
    RepresentativeStrong R (fun i => Sδ i (Tδ i (v i))) (S (T x)) := by
  exact representative_bounded_operator_action R Sδ S N hN hSb hSbound hS
    (representative_bounded_operator_action R Tδ T M hM hTb hTbound hT hv)

/-- Every clause of the named representative lemma, stated for arbitrary
nontrivial parameter filters and arbitrary dense Hilbert-space cores.
Gram convergence is the explicit contextual hypothesis preceding the
lemma. No six-vertex clustering assertion is assumed or proved here. -/
structure ChiralRepresentativeLimits (R : RepresentativeCore ι H K l) : Prop where
  extension : ∀ (Tδ : ι → H →L[ℂ] H) (T : R.core → K) (M : ℝ), 0 ≤ M →
    (∀ i, ‖Tδ i‖ ≤ M) →
    (∀ u, RepresentativeStrong R (fun i => Tδ i (R.repr i u)) (T u)) →
    ∃ Tbar : K →L[ℂ] K, ‖Tbar‖ ≤ M ∧ (∀ u : R.core, Tbar (u : K)=T u) ∧
      ∀ (v : ι → H) (x : K), RepresentativeStrong R v x →
        RepresentativeStrong R (fun i => Tδ i (v i)) (Tbar x)
  composition : ∀ (Tδ Sδ : ι → H →L[ℂ] H) (T S : K →L[ℂ] K)
    (M N : ℝ), 0 ≤ M → 0 ≤ N →
    (∀ i, ‖Tδ i‖ ≤ M) → (∀ i, ‖Sδ i‖ ≤ N) → ‖T‖ ≤ M → ‖S‖ ≤ N →
    (∀ u : R.core, RepresentativeStrong R (fun i => Tδ i (R.repr i u)) (T (u : K))) →
    (∀ u : R.core, RepresentativeStrong R (fun i => Sδ i (R.repr i u)) (S (u : K))) →
    ∀ (v : ι → H) (x : K), RepresentativeStrong R v x →
      RepresentativeStrong R (fun i => Sδ i (Tδ i (v i))) (S (T x))
  criterion : ∀ (v : ι → H) (x : K),
    (∀ u : R.core, Tendsto (fun i => ⟪v i,R.repr i u⟫_ℂ) l (𝓝 ⟪x,(u : K)⟫_ℂ)) →
    Tendsto (fun i => ‖v i‖) l (𝓝 ‖x‖) → RepresentativeStrong R v x

/-- Lemma 6.2, including extension, arbitrary strong families, ordered
composition, and the pairings-plus-norm criterion. -/
theorem chiral_representatives (R : RepresentativeCore ι H K l)
    [NeBot l] [CompleteSpace K] : ChiralRepresentativeLimits R where
  extension := representative_operator_extension R
  composition := fun Tδ Sδ T S M N hM hN hTb hSb hTbound hSbound hT hS v x hv =>
    representative_operator_composition R Tδ Sδ T S M N hM hN hTb hSb hTbound hSbound hT hS hv
  criterion := fun v x hp hn => representative_strong_of_pairings_norm R hp hn

end SixVertex
