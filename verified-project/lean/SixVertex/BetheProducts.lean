import SixVertex.BetheScalars
import Mathlib.Data.Finset.NoncommProd

namespace SixVertex

section Products

variable {I R : Type*} [Monoid R]

/-- A finite product of mutually commuting creation operators, without
assuming that the ambient operator algebra is commutative. -/
noncomputable def creationProduct (B : I → R) (hB : ∀ x y, Commute (B x) (B y))
    (U : Finset I) : R := U.noncommProd B (fun x _ y _ _ => hB x y)

@[simp] theorem creationProduct_empty (B : I → R) (hB : ∀ x y, Commute (B x) (B y)) :
    creationProduct B hB ∅ = 1 := rfl

theorem creationProduct_insert [DecidableEq I]
    (B : I → R) (hB : ∀ x y, Commute (B x) (B y)) (U : Finset I) (u : I) (hu : u ∉ U) :
    creationProduct B hB (insert u U) = B u * creationProduct B hB U := by
  exact Finset.noncommProd_insert_of_notMem U u B _ hu

theorem creationProduct_erase [DecidableEq I]
    (B : I → R) (hB : ∀ x y, Commute (B x) (B y)) (U : Finset I) (u : I) (hu : u ∈ U) :
    B u * creationProduct B hB (U.erase u) = creationProduct B hB U := by
  exact Finset.mul_noncommProd_erase U hu B _

theorem creationProduct_commute (B : I → R) (hB : ∀ x y, Commute (B x) (B y))
    (U : Finset I) (u : I) : Commute (B u) (creationProduct B hB U) := by
  exact Finset.noncommProd_commute U B _ (B u) (fun x _ => hB u x)

theorem creationProduct_list [DecidableEq I]
    (B : I → R) (hB : ∀ x y, Commute (B x) (B y)) (U : List I) (hU : U.Nodup) :
    creationProduct B hB U.toFinset = (U.map B).prod := by
  exact Finset.noncommProd_toFinset U B _ hU

end Products

section DiagonalNormalOrder

variable {I R : Type*} [DecidableEq I] [Ring R] [Algebra ℂ R]

/-- The unchanged term in a normal-ordered diagonal action. -/
noncomputable def diagonalMain (F : I → I → ℂ) (D B : I → R)
    (hB : ∀ x y, Commute (B x) (B y)) (U : Finset I) (v : I) : R :=
  (∏ u ∈ U, F v u) • (creationProduct B hB U * D v)

/-- Contributions replacing one original argument. -/
noncomputable def diagonalReplacements (F G : I → I → ℂ) (D B : I → R)
    (hB : ∀ x y, Commute (B x) (B y)) (U : Finset I) (v : I) : R :=
  ∑ p ∈ U, (G v p * ∏ u ∈ U.erase p, F p u) •
    (B v * creationProduct B hB (U.erase p) * D p)

theorem diagonalReplacements_insert (F G : I → I → ℂ) (D B : I → R)
    (hB : ∀ x y, Commute (B x) (B y)) (U : Finset I) (v u : I) (hu : u ∉ U) :
    diagonalReplacements F G D B hB (insert u U) v =
      (G v u * ∏ w ∈ U, F u w) • (B v * creationProduct B hB U * D u) +
      ∑ p ∈ U, (G v p * (F p u * ∏ w ∈ U.erase p, F p w)) •
        (B v * (B u * creationProduct B hB (U.erase p)) * D p) := by
  unfold diagonalReplacements
  rw [Finset.sum_insert hu, Finset.erase_insert hu]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  have hpu : p ≠ u := by intro h; subst p; exact hu hp
  have hue : u ∉ U.erase p := fun h => hu (Finset.mem_of_mem_erase h)
  rw [Finset.erase_insert_of_ne hpu.symm, Finset.prod_insert hue, creationProduct_insert B hB _ _ hue]

/-- Normal ordering over an arbitrary finite spectral set. The hypotheses
are the two-entry exchange relation and its scalar cocycle, restricted to
one ambient set of regular arguments. No commutativity of R is assumed. -/
theorem diagonal_normal_order (F G : I → I → ℂ) (D B : I → R)
    (hB : ∀ x y, Commute (B x) (B y)) (S : Finset I)
    (hex : ∀ v ∈ S, ∀ u ∈ S, v ≠ u →
      D v * B u = F v u • (B u * D v) + G v u • (B v * D u))
    (hc : ∀ v ∈ S, ∀ u ∈ S, ∀ p ∈ S, v ≠ u → v ≠ p → u ≠ p →
      F v u * G v p + G v u * G u p = G v p * F p u)
    (U : Finset I) (hU : U ⊆ S) (v : I) (hv : v ∈ S) (hvU : v ∉ U) :
    D v * creationProduct B hB U =
      diagonalMain F D B hB U v + diagonalReplacements F G D B hB U v := by
  induction U using Finset.induction_on generalizing v with
  | empty => simp [diagonalMain, diagonalReplacements]
  | @insert u U hu ih =>
    have huS : u ∈ S := hU (Finset.mem_insert_self u U)
    have hUS : U ⊆ S := fun x hx => hU (Finset.mem_insert_of_mem hx)
    have hvu : v ≠ u := by intro he; subst v; exact hvU (Finset.mem_insert_self u U)
    have hvU' : v ∉ U := fun h => hvU (Finset.mem_insert_of_mem h)
    have hvErase : ∀ p ∈ U, v ≠ p := fun p hp he => hvU' (he ▸ hp)
    have huErase : ∀ p ∈ U, u ≠ p := fun p hp he => hu (he ▸ hp)
    rw [creationProduct_insert B hB U u hu, ← mul_assoc, hex v hv u huS hvu]
    simp only [add_mul, smul_mul_assoc, mul_assoc]
    rw [ih hUS v hv hvU', ih hUS u huS hu]
    rw [diagonalReplacements_insert F G D B hB U v u hu]
    unfold diagonalMain
    rw [Finset.prod_insert hu, creationProduct_insert B hB U u hu]
    simp only [diagonalReplacements, mul_add, smul_add, mul_smul_comm,
      Finset.mul_sum, Finset.smul_sum, smul_smul, ← mul_assoc]
    have hsum :
        (∑ p ∈ U, (F v u * (G v p * ∏ w ∈ U.erase p, F p w)) •
          (B u * (B v * creationProduct B hB (U.erase p) * D p))) +
        (∑ p ∈ U, (G v u * (G u p * ∏ w ∈ U.erase p, F p w)) •
          (B v * (B u * creationProduct B hB (U.erase p) * D p))) =
        ∑ p ∈ U, (G v p * (F p u * ∏ w ∈ U.erase p, F p w)) •
          (B v * (B u * creationProduct B hB (U.erase p)) * D p) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      have hbuv : B u * B v = B v * B u := (hB u v).eq
      simp only [← mul_assoc, hbuv, ← add_smul]
      congr 1
      have hh := hc v hv u huS p (hUS hp) hvu (hvErase p hp) (huErase p hp)
      linear_combination (∏ w ∈ U.erase p, F p w) * hh
    -- The two terms removing p combine by the scalar cocycle.
    simp only [← mul_assoc] at hsum
    rw [← hsum]
    abel

/-- Evaluation of a normal-ordered diagonal entry on a common eigenvector,
written in the symmetric insert-and-remove form of the paper. -/
theorem diagonal_action (F G K : I → I → ℂ) (D B : I → R)
    (hB : ∀ x y, Commute (B x) (B y)) (a : I → ℂ) (Ω : R)
    (U : Finset I) (v : I) (hvU : v ∉ U)
    (hN : D v * creationProduct B hB U =
      diagonalMain F D B hB U v + diagonalReplacements F G D B hB U v)
    (hVac : ∀ p ∈ insert v U, D p * Ω = a p • Ω)
    (hK : K v v = 1) (hKF : ∀ p ∈ U, K v p * F p v = G v p) :
    D v * (creationProduct B hB U * Ω) =
      ∑ p ∈ insert v U, (a p * K v p * ∏ u ∈ (insert v U).erase p, F p u) •
        (creationProduct B hB ((insert v U).erase p) * Ω) := by
  rw [← mul_assoc, hN]
  simp only [add_mul, diagonalMain, diagonalReplacements, smul_mul_assoc,
    Finset.sum_mul, mul_assoc]
  rw [Finset.sum_insert hvU, Finset.erase_insert hvU]
  have hv : v ∈ insert v U := Finset.mem_insert_self _ _
  rw [hVac v hv, mul_smul_comm, smul_smul, hK, one_mul]
  congr 1
  · congr 1
    ring
  · apply Finset.sum_congr rfl
    intro p hp
    have hpv : p ≠ v := fun he => hvU (he ▸ hp)
    have hvErase : v ∉ U.erase p := fun he => hvU (Finset.mem_of_mem_erase he)
    rw [hVac p (Finset.mem_insert_of_mem hp)]
    simp only [mul_smul_comm, smul_smul]
    rw [Finset.erase_insert_of_ne hpv.symm, Finset.prod_insert hvErase,
      creationProduct_insert B hB _ _ hvErase]
    simp only [mul_assoc]
    congr 1
    have hh := hKF p hp
    linear_combination -(a p * ∏ u ∈ U.erase p, F p u) * hh

end DiagonalNormalOrder

end SixVertex
