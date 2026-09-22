import PoincareConjecture.ProofContract.V1.Obligations
import PoincareConjecture.ProofContract.Proofs.CoordinateBallExists
import PoincareConjecture.ProofContract.Proofs.OpenAnnulus
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Topology
open scoped Topology Manifold ContDiff
/-- A genuine bicollar with the prescribed boundary parametrization. -/
theorem coordinate_boundary_bicollar {M : ClosedThreeManifold.{u}} (b : CoordinateBall M) :
    ∃ (U : TopologicalSpace.Opens M)
      (e : (Sphere2 × Set.Ioo (1/2 : ℝ) (3/2 : ℝ)) ≃ₜ U),
      (∀ x : M, x ∈ U ↔ ∃ z : Euclidean3,
        (1/2 : ℝ) < ‖z‖ ∧ ‖z‖ < (3/2 : ℝ) ∧ b.parametrization z = x) ∧
      ∀ (s : Sphere2) (r : Set.Ioo (1/2 : ℝ) (3/2 : ℝ)),
        (e (s,r) : M) = b.parametrization ((r:ℝ) • (s:Euclidean3)) :=
/- SWARM_PROOF_BEGIN -/
by
  let A : Set Euclidean3 := {x : Euclidean3 |
    (1 / 2 : ℝ) < ‖x‖ ∧ ‖x‖ < (3 / 2 : ℝ)}
  have hAopen : IsOpen A := by
    change IsOpen {x : Euclidean3 |
      (1 / 2 : ℝ) < ‖x‖ ∧ ‖x‖ < (3 / 2 : ℝ)}
    exact (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  have hsource : A ⊆ b.parametrization.source := by
    intro z hz
    apply b.contains_two
    have hz' : ‖z‖ < (3 / 2 : ℝ) := hz.2
    simpa [Metric.mem_closedBall] using (show ‖z‖ ≤ (2 : ℝ) by linarith)
  let U : TopologicalSpace.Opens M :=
    ⟨b.parametrization '' A,
      b.parametrization.isOpen_image_of_subset_source hAopen hsource⟩
  let f : A → Sphere2 × Set.Ioo (1 / 2 : ℝ) (3 / 2 : ℝ) := fun x =>
    (⟨‖(x : Euclidean3)‖⁻¹ • (x : Euclidean3), by
        rw [Metric.mem_sphere, dist_zero_right]
        have hx : 0 < ‖(x : Euclidean3)‖ := lt_trans (by norm_num) x.property.1
        simp [norm_smul, abs_of_pos (inv_pos.mpr hx), hx.ne']⟩,
      ⟨‖(x : Euclidean3)‖, x.property⟩)
  let g : (Sphere2 × Set.Ioo (1 / 2 : ℝ) (3 / 2 : ℝ)) → A := fun p =>
    ⟨(p.2 : ℝ) • (p.1 : Euclidean3), by
      have hs : ‖(p.1 : Euclidean3)‖ = 1 := by
        simpa [Metric.mem_sphere, dist_zero_right] using p.1.property
      have hp : 0 < (p.2 : ℝ) := lt_trans (by norm_num) p.2.2.1
      change (1 / 2 : ℝ) < ‖(p.2 : ℝ) • (p.1 : Euclidean3)‖ ∧
        ‖(p.2 : ℝ) • (p.1 : Euclidean3)‖ < (3 / 2 : ℝ)
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hp, hs]
      simp only [mul_one]
      exact p.2.2⟩
  have hfg : Function.LeftInverse g f := by
    intro x
    apply Subtype.ext
    dsimp [f, g]
    have hx : 0 < ‖(x : Euclidean3)‖ := lt_trans (by norm_num) x.property.1
    simp [smul_smul, hx.ne']
  have hgf : Function.RightInverse g f := by
    intro p
    apply Prod.ext
    · apply Subtype.ext
      dsimp [f, g]
      have hs : ‖(p.1 : Euclidean3)‖ = 1 := by
        simpa [Metric.mem_sphere, dist_zero_right] using p.1.property
      have hp : 0 < (p.2 : ℝ) := lt_trans (by norm_num) p.2.2.1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hp, hs]
      rw [mul_one, smul_smul, inv_mul_cancel₀ hp.ne', one_smul]
    · apply Subtype.ext
      dsimp [f, g]
      have hs : ‖(p.1 : Euclidean3)‖ = 1 := by
        simpa [Metric.mem_sphere, dist_zero_right] using p.1.property
      have hp : 0 < (p.2 : ℝ) := lt_trans (by norm_num) p.2.2.1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hp, hs]
      simp only [mul_one]
  have hf : Continuous f := by
    dsimp [f]
    have hn : Continuous (fun x : A => ‖(x : Euclidean3)‖) :=
      continuous_subtype_val.norm
    have hni : Continuous (fun x : A => ‖(x : Euclidean3)‖⁻¹) :=
      hn.inv₀ (fun x => (lt_trans (by norm_num) x.property.1).ne')
    exact (hni.smul continuous_subtype_val).subtype_mk _ |>.prodMk (hn.subtype_mk _)
  have hg : Continuous g := by
    dsimp [g]
    exact ((continuous_subtype_val.comp continuous_snd).smul
      (continuous_subtype_val.comp continuous_fst)).subtype_mk _
  let eA : (Sphere2 × Set.Ioo (1 / 2 : ℝ) (3 / 2 : ℝ)) ≃ₜ A :=
    { toEquiv :=
        { toFun := g
          invFun := f
          left_inv := hgf
          right_inv := hfg }
      continuous_toFun := hg
      continuous_invFun := hf }
  let hchart : A ≃ₜ U :=
    b.parametrization.homeomorphOfImageSubsetSource hsource (by rfl)
  let e : (Sphere2 × Set.Ioo (1 / 2 : ℝ) (3 / 2 : ℝ)) ≃ₜ U :=
    eA.trans hchart
  refine ⟨U, e, ?_, ?_⟩
  · intro x
    change x ∈ b.parametrization '' A ↔ _
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz.1, hz.2, rfl⟩
    · rintro ⟨z, hz₁, hz₂, hzx⟩
      exact ⟨z, ⟨hz₁, hz₂⟩, hzx⟩
  · intro s r
    change b.parametrization ((r : ℝ) • (s : Euclidean3)) = _
    rfl
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
