import PoincareConjecture.ProofContract.Refinement20260927.EuclideanMollifierReuse
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.RefinedCylinderRestrictionEstimate
open PoincareConjecture.ProofContract.Refinement20260927
theorem cylinder_restriction_estimate : CylinderRestrictionEstimateStatement :=
/- SWARM_PROOF_BEGIN -/
open PoincareConjecture.ProofContract.V1 in
open scoped Topology Manifold ContDiff in by
  intro n f g s p i eps hf hg heps hbound
  letI : Fact (Module.finrank ℝ Euclidean3 = 2+1) := ⟨by simp [Euclidean3]⟩
  let coeSphere : Sphere2 → Euclidean3 := Subtype.val
  have hcoe : ContMDiff ((modelWithCornersSelf ℝ SphereModel)) (modelWithCornersSelf ℝ Euclidean3)
      (WithTop.some (⊤ : WithTop ℕ)) coeSphere := contMDiff_coe_sphere
  have hcoeD : MDifferentiableAt ((modelWithCornersSelf ℝ SphereModel)) (modelWithCornersSelf ℝ Euclidean3) coeSphere p :=
    (hcoe.mdifferentiable (by decide)) p
  let vec : Euclidean3 := mvfderiv ((modelWithCornersSelf ℝ SphereModel)) coeSphere p (sphereEnergyFrame p i)
  let lift : Euclidean3 → CylinderAmbient := fun z => (s,z)
  let A : Euclidean3 →L[ℝ] CylinderAmbient := ContinuousLinearMap.inr ℝ ℝ Euclidean3
  have hl : HasFDerivAt lift A p.val := by
    convert (hasFDerivAt_const s p.val).prodMk (hasFDerivAt_id p.val) using 1 <;> rfl
  have chainVector (k : CylinderAmbient → ApproxAmbient n)
      (hk : DifferentiableAt ℝ k (s,p.val)) :
      ambientSliceVector (fun z => k (s,z.val)) p i = fderiv ℝ k (s,p.val) (0,vec) := by
    have hklift := hk.hasFDerivAt.comp p.val hl
    have hmd := mfderiv_comp_apply (I := (modelWithCornersSelf ℝ SphereModel)) (I' := (modelWithCornersSelf ℝ Euclidean3))
      (I'' := (modelWithCornersSelf ℝ (ApproxAmbient n))) (f := coeSphere) (g := k ∘ lift) (x := p)
      hklift.differentiableAt.mdifferentiableAt hcoeD (sphereEnergyFrame p i)
    have hmEq : mfderiv (modelWithCornersSelf ℝ Euclidean3) (modelWithCornersSelf ℝ (ApproxAmbient n)) (k ∘ lift) p.val =
        (fderiv ℝ k (s,p.val)).comp A := by
      rw [mfderiv_eq_fderiv]
      exact hklift.fderiv
    rw [hmEq] at hmd
    convert hmd using 1 <;>
      simp only [ambientSliceVector,mvfderiv,NormedSpace.fromTangentSpace,
        ContinuousLinearMap.comp_apply,Function.comp_def,coeSphere,lift,A] <;> rfl
  have hsliceF := chainVector f hf
  have hsliceG := chainVector g hg
  have hframe : (MorganTianLib.unitRoundSphereMetric.inner p)
      (sphereEnergyFrame p i) (sphereEnergyFrame p i) = 1 := by
    simpa [sphereEnergyFrame] using
      (Riemannian.Tensor.smoothOrthoFrame_orthonormal_at_center
        MorganTianLib.unitRoundSphereMetric p i i)
  have hmetric : MorganTianLib.unitRoundSphereMetric.metricInner p
      (sphereEnergyFrame p i) (sphereEnergyFrame p i) = 1 := by
    rw [Riemannian.RiemannianMetric.metricInner_apply]
    exact hframe
  have hinner : inner ℝ vec vec = 1 := by
    change Riemannian.DCInducedForm
      (Riemannian.DCEuclideanMetric (F := Euclidean3)) coeSphere p
      (sphereEnergyFrame p i) (sphereEnergyFrame p i) = 1 at hmetric
    rw [Riemannian.DCInducedForm_apply,Riemannian.DCEuclideanMetric_apply] at hmetric
    convert hmetric using 1 <;> rfl
  have hnorm : ‖vec‖ = 1 := by
    have hsquare : ‖vec‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq]
      exact hinner
    nlinarith [norm_nonneg vec, sq_nonneg (‖vec‖ - 1)]
  have hfull : ‖((0 : ℝ), vec)‖ = 1 := by
    simp [Prod.norm_def, hnorm]
  calc
    ‖ambientSliceVector (fun z => f (s, z.val)) p i -
        ambientSliceVector (fun z => g (s, z.val)) p i‖ =
        ‖(fderiv ℝ f (s, p.val) - fderiv ℝ g (s, p.val)) (0, vec)‖ := by
          rw [hsliceF, hsliceG]
          simp
    _ ≤ ‖fderiv ℝ f (s, p.val) - fderiv ℝ g (s, p.val)‖ * ‖(0, vec)‖ :=
      (fderiv ℝ f (s, p.val) - fderiv ℝ g (s, p.val)).le_opNorm (0, vec)
    _ = ‖fderiv ℝ f (s, p.val) - fderiv ℝ g (s, p.val)‖ := by rw [hfull]; ring
    _ ≤ eps := hbound
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RefinedCylinderRestrictionEstimate
