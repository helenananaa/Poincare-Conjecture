import PoincareConjecture.ParallelImplementation.BarycentricLinkCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.BarycentricLinkReconstruction
open PoincareConjecture.ParallelImplementation.FinitePLRealization
open scoped BigOperators
theorem reconstruct_from_link_coordinates
    {V : Type*} [Fintype V] [DecidableEq V] (K : FiniteAbstractComplex V)
    (v : V) (hv : ({v} : Finset V) ∈ K.faces)
    (y : V → ℝ) (hy0 : ∀ w, 0 ≤ y w) (hy1 : (∑ w, y w) = 1)
    (hylink : (Finset.univ.filter (fun w => 0 < y w)) ∈ (abstractLink K {v} hv).faces)
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    let x : V → ℝ := fun w => if w = v then t else (1 - t) * y w
    x ∈ (realization K).space ∧ x v = t ∧
      (fun w => if w = v then 0 else x w / (1 - x v)) = y :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let x : V → ℝ := fun w => if w = v then t else (1 - t) * y w
  let S : Finset V := Finset.univ.filter (fun w => 0 < y w)
  change x ∈ (realization K).space ∧ x v = t ∧
    (fun w => if w = v then 0 else x w / (1 - x v)) = y
  change S.Nonempty ∧ Disjoint S ({v} : Finset V) ∧ S ∪ {v} ∈ K.faces at hylink
  rcases hylink with ⟨hSne, hSdisjoint, hSface⟩
  have hv_notS : v ∉ S := by
    intro hvS
    have hv_single : v ∈ ({v} : Finset V) := Finset.mem_singleton_self v
    exact (Finset.disjoint_left.mp hSdisjoint) hvS hv_single
  have hyv_notpos : ¬ 0 < y v := by
    intro hyv
    apply hv_notS
    simp [S, hyv]
  have hyv : y v = 0 := le_antisymm (le_of_not_gt hyv_notpos) (hy0 v)
  have hxv : x v = t := by simp [x]
  have hsum_erase_y : (∑ w ∈ Finset.univ.erase v, y w) = 1 := by
    have hsplit := Finset.univ.sum_erase_add y (Finset.mem_univ v)
    rw [hy1, hyv] at hsplit
    linarith
  have hsum_erase_x : (∑ w ∈ Finset.univ.erase v, x w) =
      (1 - t) * (∑ w ∈ Finset.univ.erase v, y w) := by
    calc
      (∑ w ∈ Finset.univ.erase v, x w) =
          ∑ w ∈ Finset.univ.erase v, (1 - t) * y w := by
        apply Finset.sum_congr rfl
        intro w hw
        have hwv : w ≠ v := (Finset.mem_erase.mp hw).1
        simp [x, hwv]
      _ = (1 - t) * (∑ w ∈ Finset.univ.erase v, y w) := by
        rw [← Finset.mul_sum]
  have hsumx : (∑ w, x w) = 1 := by
    rw [← Finset.univ.sum_erase_add x (Finset.mem_univ v), hxv,
      hsum_erase_x, hsum_erase_y]
    ring
  have hsupport : (Finset.univ.filter (fun w => 0 < x w)) = S ∪ {v} := by
    ext w
    by_cases hw : w = v
    · subst w
      simp [x, ht]
    · have hscale : 0 < 1 - t := by linarith
      simp [S, x, hw, mul_pos_iff_of_pos_left hscale]
  have hxmem : x ∈ (realization K).space := by
    apply (BarycentricMembership.mem_realization_iff_barycentric K x).mpr
    refine ⟨?_, hsumx, ?_⟩
    · intro w
      by_cases hw : w = v
      · simp [x, hw, ht.le]
      · simp [x, hw, mul_nonneg (sub_nonneg.mpr ht1.le) (hy0 w)]
    · simpa [hsupport] using hSface
  refine ⟨hxmem, hxv, ?_⟩
  funext w
  by_cases hw : w = v
  · subst w
    simp [hyv]
  · rw [hxv]
    simp only [if_neg hw]
    have hden : 1 - t ≠ 0 := ne_of_gt (by linarith : 0 < 1 - t)
    simp only [x, hw]
    field_simp [hden]
    simp only [if_false]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.BarycentricLinkReconstruction
