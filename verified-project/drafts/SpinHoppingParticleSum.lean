import SixVertex.FreeSectorHopping
import SixVertex.PhysicalBondSites
import SixVertex.SpinSitePermutation

namespace SixVertex
noncomputable section

theorem swapSpinSites_comm {L particles : ℕ} (q : ParticleConfigurations L particles) (a b : Fin L) :
    swapSpinSites q a b=swapSpinSites q b a := by
  apply Subtype.ext
  simp only [swapSpinSites,Equiv.swap_comm]

/-- Exact sum over occupied physical sites,using the proved particle enumeration. -/
theorem sum_occupiedIndex_filter {L particles : ℕ} (q : ParticleConfigurations L particles)
    (f : Fin L → ℂ) :
    (∑ a : Fin L,if rowSpinAt L q.val a=1 then f a else 0)=∑ j,f (occupiedIndex q j) := by
  classical
  have h := Equiv.sum_comp ((occupiedSites L q.val).orderIsoOfFin
    ((occupiedSites_card L q.val).trans q.property)).toEquiv
      (fun a : occupiedSites L q.val => f a.val)
  change (∑ j,f (occupiedIndex q j))=∑ a : occupiedSites L q.val,f a.val at h
  rw [Finset.sum_coe_sort] at h
  rw [h]
  simp only [occupiedSites,Finset.sum_filter]

/-- Literal periodic-site formula for the exact actual sector matrix. -/
theorem complexSectorHamiltonian_freeFermion_site_mulVec (n particles : ℕ)
    (v : ParticleConfigurations (n+2) particles → ℂ) (q : ParticleConfigurations (n+2) particles) :
    (complexSectorHamiltonian (Real.pi/2) (1/2) n particles).mulVec v q=
      ∑ k : Fin (n+2),if rowSpinAt (n+2) q.val (k-1)≠rowSpinAt (n+2) q.val k
        then -(1/2 : ℂ)*v (swapSpinSites q (k-1) k) else 0 := by
  rw [complexSectorHamiltonian_mulVec_eq_full,homogeneousLinkHamiltonian_freeFermion_site_mulVec]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs
  · exact congrArg (fun z : ℂ => -(1/2 : ℂ)*z)
      (physicalSectorExtension_apply v (swapSpinSites q (k-1) k))
  · rfl

/-- Reindex the ACTUAL spin-sector hopping sum into one right and one
left move per occupied particle. Empty sectors are included. -/
theorem complexSectorHamiltonian_freeFermion_particle_mulVec (n particles : ℕ)
    (v : ParticleConfigurations (n+2) particles → ℂ) (q : ParticleConfigurations (n+2) particles) :
    (complexSectorHamiltonian (Real.pi/2) (1/2) n particles).mulVec v q=
      -(1/2 : ℂ)*(∑ j : Fin particles,
        ((if rowSpinAt (n+2) q.val (occupiedIndex q j+1)=0 then v (swapSpinSites q (occupiedIndex q j) (occupiedIndex q j+1)) else 0)+
        (if rowSpinAt (n+2) q.val (occupiedIndex q j-1)=0 then v (swapSpinSites q (occupiedIndex q j) (occupiedIndex q j-1)) else 0))) := by
  classical
  let R := fun a : Fin (n+2) => if rowSpinAt (n+2) q.val a=1 ∧ rowSpinAt (n+2) q.val (a+1)=0
    then v (swapSpinSites q a (a+1)) else 0
  let T := fun a : Fin (n+2) => if rowSpinAt (n+2) q.val a=1 ∧ rowSpinAt (n+2) q.val (a-1)=0
    then v (swapSpinSites q a (a-1)) else 0
  have hp (k : Fin (n+2)) :
      (if rowSpinAt (n+2) q.val (k-1)≠rowSpinAt (n+2) q.val k
        then -(1/2 : ℂ)*v (swapSpinSites q (k-1) k) else 0)=-(1/2 : ℂ)*(R (k-1)+T k) := by
    dsimp [R,T]
    rw [sub_add_cancel,swapSpinSites_comm q k (k-1)]
    generalize rowSpinAt (n+2) q.val (k-1)=a
    generalize rowSpinAt (n+2) q.val k=b
    fin_cases a <;> fin_cases b <;> norm_num
  have hr : (∑ k : Fin (n+2),R (k-1))=∑ k : Fin (n+2),R k := by
    simpa only [finRotate_symm_apply] using Equiv.sum_comp (finRotate (n+2)).symm R
  rw [complexSectorHamiltonian_freeFermion_site_mulVec]
  simp_rw [hp]
  rw [← Finset.mul_sum,Finset.sum_add_distrib,hr]
  have hR : (∑ a : Fin (n+2),R a)=∑ j : Fin particles,
      if rowSpinAt (n+2) q.val (occupiedIndex q j+1)=0
      then v (swapSpinSites q (occupiedIndex q j) (occupiedIndex q j+1)) else 0 := by
    simpa only [R,ite_and] using sum_occupiedIndex_filter q
      (fun a => if rowSpinAt (n+2) q.val (a+1)=0 then v (swapSpinSites q a (a+1)) else 0)
  have hT : (∑ a : Fin (n+2),T a)=∑ j : Fin particles,
      if rowSpinAt (n+2) q.val (occupiedIndex q j-1)=0
      then v (swapSpinSites q (occupiedIndex q j) (occupiedIndex q j-1)) else 0 := by
    simpa only [T,ite_and] using sum_occupiedIndex_filter q
      (fun a => if rowSpinAt (n+2) q.val (a-1)=0 then v (swapSpinSites q a (a-1)) else 0)
  rw [hR,hT,← Finset.sum_add_distrib]

end
end SixVertex
