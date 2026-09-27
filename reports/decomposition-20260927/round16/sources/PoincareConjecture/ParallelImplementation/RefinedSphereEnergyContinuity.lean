import PoincareConjecture.ProofContract.Refinement20260927.IntrinsicSphereEnergy
import MorganTianLib.Ch01.OrthoFrame
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.RefinedSphereEnergyContinuity
open PoincareConjecture.ProofContract.Refinement20260927
theorem sphere_energy_continuity : SphereEnergyContinuityStatement.{u} :=
/- SWARM_PROOF_BEGIN -/
open PoincareConjecture.ProofContract.V1 MorganTianLib Riemannian.Tensor in
open scoped Topology Manifold ContDiff BigOperators Bundle in
by
  classical
  letI : Nonempty Sphere2 := sphereEnergySphere_nonempty
  letI : NeZero (Module.finrank ℝ SphereModel) := ⟨by simp [SphereModel]⟩
  letI : Riemannian.HasMetric (modelWithCornersSelf ℝ SphereModel) Sphere2 :=
    ⟨unitRoundSphereMetric⟩
  intro M g f hf
  let X := ℝ × Sphere2
  let I₁ := modelWithCornersSelf ℝ ℝ
  let I₂ := modelWithCornersSelf ℝ SphereModel
  let I₃ := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))
  let Iₓ := I₁.prod I₂
  let smoothOrder : WithTop (WithTop ℕ) := WithTop.some (⊤ : WithTop ℕ)
  have hf' : ContMDiff Iₓ I₃ smoothOrder f := by
    simpa [Iₓ, I₁, I₂, I₃, SphereModel, smoothOrder] using hf
  apply continuous_iff_continuousAt.mpr
  intro q
  let α : Sphere2 := q.2
  have hframeNbhd : smoothOrthoFrameNbhd (I := I₂) α ∈ nhds α :=
    smoothOrthoFrameNbhd_mem_nhds (I := I₂) α
  have hnear : Filter.Eventually (fun z : X =>
      z.2 ∈ smoothOrthoFrameNbhd (I := I₂) α) (nhds q) := by
    exact continuous_snd.continuousAt.preimage_mem_nhds hframeNbhd
  let frame (i : Fin (Module.finrank ℝ SphereModel)) (p : Sphere2) :
      TangentSpace I₂ p := smoothOrthoFrame unitRoundSphereMetric α i p
  let frameSection (i : Fin (Module.finrank ℝ SphereModel)) (p : Sphere2) :
      TangentBundle I₂ Sphere2 := ⟨p, frame i p⟩
  have hframeSection (i : Fin (Module.finrank ℝ SphereModel)) :
      ContMDiff I₂ (I₂.prod (modelWithCornersSelf ℝ SphereModel)) smoothOrder (frameSection i) := by
    change ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))))
      (WithTop.some (⊤ : WithTop ℕ)) (frameSection i)
    simpa [frameSection, frame] using
      (contMDiff_smoothOrthoFrame_section unitRoundSphereMetric α i)
  let zeroSection : ℝ → TangentBundle I₁ ℝ :=
    Bundle.zeroSection ℝ (TangentSpace I₁ : ℝ → Type _)
  have hzeroSection :
      ContMDiff I₁ (I₁.prod (modelWithCornersSelf ℝ ℝ)) smoothOrder zeroSection := by
    change ContMDiff (modelWithCornersSelf ℝ ℝ)
      ((modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ ℝ))
      (WithTop.some (⊤ : WithTop ℕ)) zeroSection
    simpa [zeroSection] using
      (Bundle.contMDiff_zeroSection ℝ (TangentSpace I₁ : ℝ → Type _))
  let sourceSection (i : Fin (Module.finrank ℝ SphereModel)) (z : X) :
      TangentBundle Iₓ X :=
    (equivTangentBundleProd I₁ ℝ I₂ Sphere2).symm
      (zeroSection z.1, frameSection i z.2)
  have hsourceSection (i : Fin (Module.finrank ℝ SphereModel)) :
      ContMDiff Iₓ (Iₓ.prod (modelWithCornersSelf ℝ (ℝ × SphereModel))) smoothOrder
        (sourceSection i) := by
    dsimp [sourceSection]
    exact (contMDiff_equivTangentBundleProd_symm
        (I := I₁) (M := ℝ) (I' := I₂) (M' := Sphere2) (n := smoothOrder)).comp
      ((hzeroSection.comp contMDiff_fst).prodMk
        ((hframeSection i).comp contMDiff_snd))
  have hsourceSection_apply (i : Fin (Module.finrank ℝ SphereModel)) (z : X) :
      sourceSection i z = ⟨z, (0, frame i z.2)⟩ := by
    simp [sourceSection, equivTangentBundleProd, zeroSection, frameSection]
  let targetSection (i : Fin (Module.finrank ℝ SphereModel)) (z : X) :
      TangentBundle I₃ M := tangentMap Iₓ I₃ f (sourceSection i z)
  have htargetSection (i : Fin (Module.finrank ℝ SphereModel)) :
      ContMDiff Iₓ (I₃.prod (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))) smoothOrder
        (targetSection i) := by
    exact (hf'.contMDiff_tangentMap (m := smoothOrder) (n := smoothOrder) le_rfl).comp
      (hsourceSection i)
  let vec (i : Fin (Module.finrank ℝ SphereModel)) (z : X) :
      TangentSpace I₃ (f z) :=
    mfderiv Iₓ I₃ f z ((0, frame i z.2))
  have htargetSection_eq (i : Fin (Module.finrank ℝ SphereModel)) :
      (fun z : X => (⟨f z, vec i z⟩ : TangentBundle I₃ M)) = targetSection i := by
    funext z
    change (⟨f z, vec i z⟩ : TangentBundle I₃ M) =
      tangentMap Iₓ I₃ f (sourceSection i z)
    rw [hsourceSection_apply]
    simp [vec, tangentMap]
  let term (i : Fin (Module.finrank ℝ SphereModel)) (z : X) : ℝ :=
    g.metricInner (f z) (vec i z) (vec i z)
  have hterm (i : Fin (Module.finrank ℝ SphereModel)) :
      ContMDiff Iₓ (modelWithCornersSelf ℝ ℝ) smoothOrder (term i) := by
    letI : Riemannian.HasMetric I₃ M := ⟨g⟩
    letI : Bundle.RiemannianBundle (TangentSpace I₃ : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    letI : ∀ x : M, NormedAddCommGroup (TangentSpace I₃ x) :=
      fun x => (g.toRiemannianMetric.toCore x).toNormedAddCommGroupOfTopology
        (g.toRiemannianMetric.continuousAt x) (g.toRiemannianMetric.isVonNBounded x)
    letI : ∀ x : M, InnerProductSpace ℝ (TangentSpace I₃ x) :=
      fun x => InnerProductSpace.ofCoreOfTopology (g.toRiemannianMetric.toCore x)
        (g.toRiemannianMetric.continuousAt x) (g.toRiemannianMetric.isVonNBounded x)
    letI : IsContMDiffRiemannianBundle I₃ smoothOrder
        (EuclideanSpace ℝ (Fin 3)) (TangentSpace I₃) :=
      ⟨⟨g.inner, g.contMDiff, by intro x v w; rfl⟩⟩
    have hsec : ContMDiff Iₓ (I₃.prod (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))) smoothOrder
        (fun z : X => (⟨f z, vec i z⟩ : TangentBundle I₃ M)) := by
      rw [htargetSection_eq]
      exact htargetSection i
    have h := ContMDiff.inner_bundle (IB := I₃) (n := smoothOrder)
      (F := EuclideanSpace ℝ (Fin 3)) (E := TangentSpace I₃)
      (IM := Iₓ) (M := ℝ × Sphere2) (B := M)
      (b := fun z : ℝ × Sphere2 => f z) (v := vec i) (w := vec i) hsec hsec
    have hnormEq (z : ℝ × Sphere2) : term i z = ‖vec i z‖ ^ 2 := by
      change g.metricInner (f z) (vec i z) (vec i z) = _
      rw [Riemannian.RiemannianMetric.metricInner_apply]
      change inner ℝ (vec i z) (vec i z) = _
      exact real_inner_self_eq_norm_sq _
    have hfun : term i = fun z : ℝ × Sphere2 => ‖vec i z‖ ^ 2 := by
      funext z
      exact hnormEq z
    rw [hfun]
    simpa [vec] using h
  let localEnergy (z : X) : ℝ :=
    (1 / 2 : ℝ) * ∑ i : Fin (Module.finrank ℝ SphereModel), term i z
  have hlocalEnergy : Continuous localEnergy := by
    change Continuous (fun z : X => (1 / 2 : ℝ) *
      ∑ i : Fin (Module.finrank ℝ SphereModel), term i z)
    apply Continuous.mul continuous_const
    exact continuous_finsetSum _ fun i _ => (hterm i).continuous
  have hslice (z : X) (i : Fin (Module.finrank ℝ SphereModel)) :
      mfderiv I₂ I₃ (fun p : Sphere2 => f (z.1, p)) z.2 (frame i z.2) =
        mfderiv Iₓ I₃ f z ((0, frame i z.2)) := by
    cases z with
    | mk t p =>
      let ι : Sphere2 → X := fun x => (t, x)
      have hι : ContMDiff I₂ Iₓ smoothOrder ι := by
        exact contMDiff_const.prodMk contMDiff_id
      have hfMD : MDifferentiable Iₓ I₃ f := hf'.mdifferentiable (by simp [smoothOrder])
      have hιMD : MDifferentiable I₂ Iₓ ι := hι.mdifferentiable (by simp [smoothOrder])
      have hcomp := mfderiv_comp_apply (f := ι) (g := f) (x := p)
        (by simpa [ι] using hfMD (t, p)) (hιMD p) (frame i p)
      have hincl_apply :
          mfderiv I₂ Iₓ ι p (frame i p) = (0, frame i p) := by
        rw [mfderiv_prod_right]
        rfl
      rw [hincl_apply] at hcomp
      have hfun : f ∘ ι = (fun x : Sphere2 => f (t, x)) := by
        funext x
        rfl
      rw [hfun] at hcomp
      simpa [ι] using hcomp
  have hlocalEq (z : X) (hz : z.2 ∈ smoothOrthoFrameNbhd (I := I₂) α) :
      sphereEnergyDensity M g (fun p => f (z.1, p)) z.2 = localEnergy z := by
    rw [sphereEnergyDensity_local_frame M g (fun p => f (z.1, p)) α z.2 hz]
    dsimp [localEnergy, term, vec]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [hslice z i]
  apply ((hlocalEnergy.continuousAt : ContinuousAt localEnergy q)).congr
  filter_upwards [hnear] with z hz
  exact (hlocalEq z hz).symm
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RefinedSphereEnergyContinuity
