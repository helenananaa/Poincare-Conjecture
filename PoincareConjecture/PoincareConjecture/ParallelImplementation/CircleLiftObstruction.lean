import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.CircleLiftObstruction
open scoped unitInterval Topology
/-- A genuine circle crossing cannot be returned through a zero-phase path
in a simply connected space. No winding-number or nontrivial-loop premise. -/
theorem not_simplyConnected_of_circle_crossing
    {M : Type*} [TopologicalSpace M] {a b : M}
    (c : M → AddCircle (1 : ℝ)) (hc : Continuous c)
    (crossing : Path a b) (back : Path b a)
    (hcross : ∀ t : unitInterval, c (crossing t) = ((t : ℝ) : AddCircle (1 : ℝ)))
    (hback : ∀ t : unitInterval, c (back t) = 0) :
    ¬ SimplyConnectedSpace M :=
/- SWARM_PROOF_BEGIN -/
by
  intro hsim
  let cov := AddCircle.isCoveringMap_coe (1 : ℝ)
  let f : C(M, AddCircle (1 : ℝ)) := ⟨c, hc⟩
  let γ₀ : C(unitInterval, AddCircle (1 : ℝ)) := f.comp crossing.toContinuousMap
  let γ₁ : C(unitInterval, AddCircle (1 : ℝ)) := f.comp back.symm.toContinuousMap
  have hrel : γ₀.HomotopicRel γ₁ {0, 1} := by
    simpa [γ₀, γ₁, f] using
      (ContinuousMap.HomotopicRel.comp_continuousMap
        (SimplyConnectedSpace.paths_homotopic crossing back.symm) f)
  have hstart₀ : γ₀ 0 = ((0 : ℝ) : AddCircle (1 : ℝ)) := by
    simpa [γ₀, f] using hcross 0
  have hstart₁ : γ₁ 0 = ((0 : ℝ) : AddCircle (1 : ℝ)) := by
    simpa [γ₁, f, Path.symm] using hback 1
  have hlift₀ : (fun t : unitInterval => (t : ℝ)) =
      cov.liftPath γ₀ 0 hstart₀ := by
    apply (cov.eq_liftPath_iff hstart₀).2
    refine ⟨continuous_subtype_val, ?_, rfl⟩
    ext t
    change ((t : ℝ) : AddCircle (1 : ℝ)) = c (crossing t)
    exact (hcross t).symm
  have hlift₁ : (fun _ : unitInterval => (0 : ℝ)) =
      cov.liftPath γ₁ 0 hstart₁ := by
    apply (cov.eq_liftPath_iff hstart₁).2
    refine ⟨continuous_const, ?_, rfl⟩
    ext t
    simp [γ₁, f, Path.symm, hback]
  have hend := cov.liftPath_apply_one_eq_of_homotopicRel hrel 0 hstart₀ hstart₁
  rw [← hlift₀, ← hlift₁] at hend
  norm_num at hend
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.CircleLiftObstruction
