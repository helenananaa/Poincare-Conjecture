import PoincareConjecture.ParallelImplementation.FinitePLRealization
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.BarycentricMembership
open PoincareConjecture.ParallelImplementation.FinitePLRealization
open scoped BigOperators
theorem mem_realization_iff_barycentric
    {V : Type*} [Fintype V] [DecidableEq V]
    (K : FiniteAbstractComplex V) (x : V → ℝ) :
    x ∈ (realization K).space ↔
      (∀ v, 0 ≤ x v) ∧ (∑ v, x v) = 1 ∧
      (Finset.univ.filter (fun v => 0 < x v)) ∈ K.faces :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  constructor
  · intro hx
    rcases Geometry.SimplicialComplex.mem_space_iff.mp hx with ⟨t, ht, hx⟩
    rcases realized_face_originates K ht with ⟨s, hs, rfl⟩
    change x ∈ convexHull ℝ (↑(s.image barycentricVertex) : Set (V → ℝ)) at hx
    rw [mem_convexHull_iff_exists_fintype] at hx
    rcases hx with ⟨ι, _, w, z, hw0, hw1, hz, hxsum⟩
    have hz' : ∀ i, z i ∈ s.image barycentricVertex := by
      intro i
      exact Finset.mem_coe.mp (hz i)
    choose f hf using fun i => Finset.mem_image.mp (hz' i)
    have hcoord (v : V) : x v = ∑ i, w i * (barycentricVertex (f i)) v := by
      have heq := congrArg (fun y : V → ℝ => y v) hxsum
      simpa [hf, smul_eq_mul] using heq.symm
    have hnonneg : ∀ v, 0 ≤ x v := by
      intro v
      rw [hcoord]
      apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg (hw0 i) (by
        simp only [barycentricVertex, Pi.single_apply]
        split_ifs <;> norm_num)
    have hsum : (∑ v, x v) = 1 := by
      simp_rw [hcoord]
      rw [Finset.sum_comm]
      simp [barycentricVertex, Pi.single_apply, mul_ite, hw1]
    let S := Finset.univ.filter fun v => 0 < x v
    have hSne : S.Nonempty := by
      have hpos : 0 < x := (Fintype.sum_pos_iff_of_nonneg hnonneg).mp (by rw [hsum]; norm_num)
      have hex : ∃ v, 0 < x v := (Pi.lt_def.mp hpos).2
      rcases hex with ⟨v, hv⟩
      exact ⟨v, by simp [S, hv]⟩
    have hsub : S ⊆ s := by
      intro v hv
      have hvpos : 0 < x v := (Finset.mem_filter.mp hv).2
      rw [hcoord] at hvpos
      have hpos : 0 < fun i => w i * (barycentricVertex (f i)) v :=
        (Fintype.sum_pos_iff_of_nonneg (fun i =>
          mul_nonneg (hw0 i) (by
            simp only [barycentricVertex, Pi.single_apply]
            split_ifs <;> norm_num))).mp hvpos
      have hex : ∃ i, 0 < w i * (barycentricVertex (f i)) v := (Pi.lt_def.mp hpos).2
      rcases hex with ⟨i, hi⟩
      have hfi : f i = v := by
        by_contra hne
        simp [barycentricVertex, hne] at hi
      exact hfi ▸ (hf i).1
    have hSface : S ∈ K.faces := (K.isRelLowerSet_faces hs).2 hsub hSne
    exact ⟨hnonneg, hsum, hSface⟩
  · rintro ⟨hnonneg, hsum, hface⟩
    let S := Finset.univ.filter fun v => 0 < x v
    have hpos : 0 < x := (Fintype.sum_pos_iff_of_nonneg hnonneg).mp (by rw [hsum]; norm_num)
    have hex : ∃ v, 0 < x v := (Pi.lt_def.mp hpos).2
    rcases hex with ⟨v₀, hv₀⟩
    have hv₀S : v₀ ∈ S := by simp [S, hv₀]
    let z : V → (V → ℝ) := fun v =>
      if hv : 0 < x v then barycentricVertex v else barycentricVertex v₀
    have hz : ∀ v, z v ∈ (↑(S.image barycentricVertex) : Set (V → ℝ)) := by
      intro v
      by_cases hv : 0 < x v
      · apply Finset.mem_coe.mpr
        rw [Finset.mem_image]
        exact ⟨v, by simp [S, hv], by simp [z, hv]⟩
      · apply Finset.mem_coe.mpr
        rw [Finset.mem_image]
        exact ⟨v₀, by simp [S, hv₀], by simp [z, hv]⟩
    have hcomb : (∑ v, x v • z v) = x := by
      have hterm (v : V) : x v • z v = Pi.single v (x v) := by
        ext u
        by_cases hv : 0 < x v
        · simp [z, hv, barycentricVertex, Pi.single_apply]
        · have hxv : x v = 0 := le_antisymm (le_of_not_gt hv) (hnonneg v)
          simp [z, hxv, barycentricVertex, Pi.single_apply]
      calc
        (∑ v, x v • z v) = ∑ v, Pi.single v (x v) := by simp_rw [hterm]
        _ = x := by
          ext u
          simp [Pi.single_apply]
    have hconv : x ∈ convexHull ℝ (↑(S.image barycentricVertex) : Set (V → ℝ)) := by
      apply mem_convexHull_of_exists_fintype (w := fun v : V => x v) (z := z)
      · exact hnonneg
      · exact hsum
      · exact hz
      · exact hcomb
    exact (realization K).convexHull_subset_space (abstract_face_realizes K hface) hconv
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.BarycentricMembership
