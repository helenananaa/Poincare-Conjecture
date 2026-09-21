import MorganTianLib.Ch02.SurgeryCap.PuncturedCap
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Sphere
open Set Riemannian TopologicalSpace
open scoped ContDiff Manifold Topology
noncomputable section
namespace MorganTianLib.SurgeryCap
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Math.** Euclidean three-space with the origin removed. -/
def capPuncturedSpace : Opens E3 := ⟨{x | x ≠ 0}, isOpen_ne⟩

/-- **Math.** Construct the polar diffeomorphism with its actual radius and direction maps. -/
theorem exists_cap_polar_diffeomorph :
    ∃ phi : Diffeomorph PuncturedCapModel (𝓡 3) PuncturedCap ↥capPuncturedSpace ∞,
      (∀ p : PuncturedCap, (phi p : E3) = (p.2 : ℝ) • (p.1 : E3)) ∧
      (∀ x : ↥capPuncturedSpace, ((phi.symm x).2 : ℝ) = ‖(x : E3)‖) ∧
      (∀ x : ↥capPuncturedSpace, ((phi.symm x).1 : E3) = ‖(x : E3)‖⁻¹ • (x : E3)) := by
/- SWARM_PROOF_BEGIN -/
  letI : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
  let polarEquiv : PuncturedCap ≃ ↥capPuncturedSpace := {
    toFun p := ⟨(p.2 : ℝ) • (p.1 : E3), by
      change (p.2 : ℝ) • (p.1 : E3) ≠ 0
      exact smul_ne_zero (ne_of_gt p.2.property)
        (Metric.ne_of_mem_sphere p.1.property one_ne_zero)⟩
    invFun x := ⟨⟨‖(x : E3)‖⁻¹ • (x : E3), by
        rw [mem_sphere_zero_iff_norm]
        have hx : (x : E3) ≠ 0 := by
          have hx' := x.property
          change (x : E3) ≠ 0 at hx'
          exact hx'
        simp [norm_smul, norm_inv, hx]⟩,
      ⟨‖(x : E3)‖, by
        have hx : (x : E3) ≠ 0 := by
          have hx' := x.property
          change (x : E3) ≠ 0 at hx'
          exact hx'
        exact (norm_pos_iff.mpr hx)⟩⟩
    left_inv p := by
      apply Prod.ext
      · apply Subtype.ext
        have hp : ‖(p.1 : E3)‖ = 1 := by simpa using p.1.property
        have hr : 0 < (p.2 : ℝ) := p.2.property
        simp [norm_smul, abs_of_pos hr, hp, smul_smul, hr.ne']
      · apply Subtype.ext
        have hp : ‖(p.1 : E3)‖ = 1 := by simpa using p.1.property
        have hr : 0 < (p.2 : ℝ) := p.2.property
        simp [norm_smul, abs_of_pos hr, hp, smul_smul, hr.ne']
    right_inv x := by
      apply Subtype.ext
      have hx : (x : E3) ≠ 0 := by
        have hx' := x.property
        change (x : E3) ≠ 0 at hx'
        exact hx'
      simp [norm_smul, norm_inv, hx, smul_smul]
  }
  let phi : Diffeomorph PuncturedCapModel (𝓡 3) PuncturedCap ↥capPuncturedSpace ∞ := {
    toEquiv := polarEquiv
    contMDiff_toFun := by
      rw [← ContMDiff.subtypeVal_comp_iff capPuncturedSpace polarEquiv]
      change ContMDiff PuncturedCapModel 𝓘(ℝ, E3) ∞
        (fun p : PuncturedCap => (p.2 : ℝ) • (p.1 : E3))
      exact
        (contMDiff_subtype_val.comp contMDiff_snd).smul
          (contMDiff_coe_sphere.comp contMDiff_fst)
    contMDiff_invFun := by
      have hnorm : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞
          (fun x : ↥capPuncturedSpace => ‖(x : E3)‖) := by
        intro x
        rw [contMDiffAt_subtype_iff]
        have hx := x.property
        change (x : E3) ≠ 0 at hx
        exact (contDiffAt_norm ℝ (n := ∞) (x := (x : E3)) hx).contMDiffAt
      have hnorm_inv : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞
          (fun x : ↥capPuncturedSpace => ‖(x : E3)‖⁻¹) := by
        intro x
        exact (hnorm x).inv₀ (by
          have hx := x.property
          change (x : E3) ≠ 0 at hx
          exact norm_ne_zero_iff.mpr hx)
      have hdir0 : ContMDiff (𝓡 3) 𝓘(ℝ, E3) ∞
          (fun x : ↥capPuncturedSpace => ‖(x : E3)‖⁻¹ • (x : E3)) :=
        hnorm_inv.smul contMDiff_subtype_val
      have hdir : ContMDiff (𝓡 3) (𝓡 2) ∞
          (Set.codRestrict (fun x : ↥capPuncturedSpace =>
            ‖(x : E3)‖⁻¹ • (x : E3)) _ (fun x => (polarEquiv.symm x).1.property)) := by
        apply hdir0.codRestrict_sphere (E := E3) (n := 2)
      have hradius : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞
          (fun x : ↥capPuncturedSpace => ‖(x : E3)‖) := hnorm
      have hradius' : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞
          (fun x : ↥capPuncturedSpace =>
            (⟨‖(x : E3)‖, (polarEquiv.symm x).2.property⟩ : ↥positiveReal)) := by
        rw [← ContMDiff.subtypeVal_comp_iff positiveReal]
        exact hradius
      dsimp [polarEquiv]
      exact hdir.prodMk hradius'
  }
  refine ⟨phi, ?_, ?_, ?_⟩ <;> intro z <;> rfl
/- SWARM_PROOF_END -/
end MorganTianLib.SurgeryCap
