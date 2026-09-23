import PoincareConjecture.ParallelImplementation.BarycentricMembership
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.BarycentricStarContractible
open PoincareConjecture.ParallelImplementation.FinitePLRealization
open scoped BigOperators
theorem positive_vertex_star_contractible
    {V : Type*} [Fintype V] [DecidableEq V] (K : FiniteAbstractComplex V)
    (v : V) (hv : ({v} : Finset V) ∈ K.faces) :
    ContractibleSpace {x : V → ℝ // x ∈ (realization K).space ∧ 0 < x v} :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let e : V → ℝ := barycentricVertex v
  let A : Set (V → ℝ) := {x | x ∈ (realization K).space ∧ 0 < x v}
  have he_mem : e ∈ (realization K).space := by
    apply (PoincareConjecture.ParallelImplementation.BarycentricMembership.mem_realization_iff_barycentric
      K e).2
    refine ⟨?_, ?_, ?_⟩
    · intro u
      by_cases huv : u = v
      · subst u
        simp [e, barycentricVertex]
      · simp [e, barycentricVertex, huv]
    · simp [e, barycentricVertex]
    · have hsupp : (Finset.univ.filter fun u => 0 < e u) = {v} := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        by_cases huv : u = v
        · subst u
          simp [e, barycentricVertex]
        · have he0 : e u = 0 := by simp [e, barycentricVertex, huv]
          rw [he0]
          simp [huv]
      rw [hsupp]
      exact hv
  have he_pos : 0 < e v := by simp [e, barycentricVertex]
  have hA : StarConvex ℝ e A := by
    intro x hx a b ha hb hab
    let z : V → ℝ := a • e + b • x
    change z ∈ A
    have hdata :=
      (PoincareConjecture.ParallelImplementation.BarycentricMembership.mem_realization_iff_barycentric
        K x).mp hx.1
    have hxn : ∀ u, 0 ≤ x u := hdata.1
    have hxs : (∑ u, x u) = 1 := hdata.2.1
    let Sx : Finset V := Finset.univ.filter fun u => 0 < x u
    have hxf : Sx ∈ K.faces := by simpa [Sx] using hdata.2.2
    have he_nonneg : ∀ u, 0 ≤ e u := by
      intro u
      by_cases huv : u = v
      · subst u
        simp [e, barycentricVertex]
      · simp [e, barycentricVertex, huv]
    have he_sum : (∑ u, e u) = 1 := by simp [e, barycentricVertex]
    have hz_nonneg : ∀ u, 0 ≤ z u := by
      intro u
      change 0 ≤ a * e u + b * x u
      exact add_nonneg (mul_nonneg ha (he_nonneg u)) (mul_nonneg hb (hxn u))
    have hz_sum : (∑ u, z u) = 1 := by
      calc
        (∑ u, z u) = ∑ u, (a * e u + b * x u) := by
          apply Finset.sum_congr rfl
          intro u hu
          simp [z, Pi.add_apply, Pi.smul_apply]
        _ = (∑ u, a * e u) + ∑ u, b * x u := Finset.sum_add_distrib
        _ = a * (∑ u, e u) + b * (∑ u, x u) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum]
        _ = 1 := by simpa [he_sum, hxs] using hab
    have hzv : 0 < z v := by
      by_cases hb0 : b = 0
      · have ha1 : a = 1 := by linarith
        simp [z, e, barycentricVertex, hb0, ha1]
      · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
        have hmul : 0 < b * x v := mul_pos hbpos hx.2
        have hpos : 0 < a + b * x v := by linarith [ha, hmul]
        simpa [z, e, barycentricVertex] using hpos
    let Sz : Finset V := Finset.univ.filter fun u => 0 < z u
    have hsub : Sz ⊆ Sx := by
      intro u hu
      have hzu : 0 < z u := (Finset.mem_filter.mp hu).2
      by_cases huv : u = v
      · subst u
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx.2⟩
      · have hmul : 0 < b * x u := by
          simpa [z, e, barycentricVertex, Pi.add_apply, Pi.smul_apply, huv] using hzu
        have hxune : x u ≠ 0 := by
          intro hxzero
          rw [hxzero] at hmul
          simp at hmul
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, lt_of_le_of_ne (hxn u) (Ne.symm hxune)⟩
    have hzne : Sz.Nonempty :=
      ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzv⟩⟩
    have hzface : Sz ∈ K.faces := (K.isRelLowerSet_faces hxf).2 hsub hzne
    have hz_mem : z ∈ (realization K).space := by
      apply (PoincareConjecture.ParallelImplementation.BarycentricMembership.mem_realization_iff_barycentric
        K z).2
      exact ⟨hz_nonneg, hz_sum, by simpa [Sz] using hzface⟩
    exact ⟨hz_mem, hzv⟩
  have hAne : A.Nonempty := ⟨e, by exact ⟨he_mem, he_pos⟩⟩
  exact hA.contractibleSpace hAne
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.BarycentricStarContractible
