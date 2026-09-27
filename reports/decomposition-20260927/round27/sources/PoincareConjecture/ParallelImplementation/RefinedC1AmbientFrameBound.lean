import PoincareConjecture.ProofContract.Refinement20260927.C1ReferenceLeaves
import MorganTianLib.Ch01.OrthoFrame
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.RefinedC1AmbientFrameBound
open PoincareConjecture.ProofContract.Refinement20260927
theorem c1_ambient_frame_bound : C1AmbientFrameBoundStatement :=
/- SWARM_PROOF_BEGIN -/
by
  open PoincareConjecture.ProofContract.V1 MorganTianLib Riemannian.Tensor Bundle in
  open scoped Topology Manifold ContDiff BigOperators Bundle in
  classical
  letI : Nonempty Sphere2 := sphereEnergySphere_nonempty
  letI : NeZero (Module.finrank ℝ SphereModel) := ⟨by simp [SphereModel]⟩
  letI : Riemannian.HasMetric (modelWithCornersSelf ℝ SphereModel) Sphere2 :=
    ⟨unitRoundSphereMetric⟩
  intro n f hf
  let X := ℝ × Sphere2
  let I₁ := modelWithCornersSelf ℝ ℝ
  let I₂ := modelWithCornersSelf ℝ SphereModel
  let Iₙ := modelWithCornersSelf ℝ (ApproxAmbient n)
  let Iₓ := I₁.prod I₂
  let smoothOrder : WithTop (WithTop ℕ) := WithTop.some (⊤ : WithTop ℕ)
  have hf' : ContMDiff Iₓ Iₙ 1 f := by
    simpa [Iₓ, I₁, I₂, SphereModel, SweepModel, X] using hf
  have hframeNbhd (α : Sphere2) :
      smoothOrthoFrameNbhd (I := I₂) α ∈ nhds α :=
    smoothOrthoFrameNbhd_mem_nhds (I := I₂) α
  let frame (α : Sphere2) (i : Fin (Module.finrank ℝ SphereModel)) (p : Sphere2) :
      TangentSpace I₂ p := smoothOrthoFrame unitRoundSphereMetric α i p
  let frameSection (α : Sphere2) (i : Fin (Module.finrank ℝ SphereModel)) (p : Sphere2) :
      TangentBundle I₂ Sphere2 := ⟨p, frame α i p⟩
  have hframeSection (α : Sphere2) (i : Fin (Module.finrank ℝ SphereModel)) :
      ContMDiff I₂ (I₂.prod (modelWithCornersSelf ℝ SphereModel)) smoothOrder
        (frameSection α i) := by
    change ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))))
      (WithTop.some (⊤ : WithTop ℕ)) (frameSection α i)
    simpa [frameSection, frame, I₂, SphereModel] using
      (contMDiff_smoothOrthoFrame_section unitRoundSphereMetric α i)
  let zeroSection : ℝ → TangentBundle I₁ ℝ :=
    Bundle.zeroSection ℝ (TangentSpace I₁ : ℝ → Type _)
  have hzeroSection :
      ContMDiff I₁ (I₁.prod (modelWithCornersSelf ℝ ℝ)) smoothOrder zeroSection := by
    change ContMDiff (modelWithCornersSelf ℝ ℝ)
      ((modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ ℝ))
      (WithTop.some (⊤ : WithTop ℕ)) zeroSection
    simpa [zeroSection, I₁] using
      (Bundle.contMDiff_zeroSection ℝ (TangentSpace I₁ : ℝ → Type _))
  let sourceSection (α : Sphere2) (i : Fin (Module.finrank ℝ SphereModel)) (z : X) :
      TangentBundle Iₓ X :=
    (equivTangentBundleProd I₁ ℝ I₂ Sphere2).symm
      (zeroSection z.1, frameSection α i z.2)
  have hsourceSection (α : Sphere2) (i : Fin (Module.finrank ℝ SphereModel)) :
      ContMDiff Iₓ (Iₓ.prod (modelWithCornersSelf ℝ (ℝ × SphereModel))) smoothOrder
        (sourceSection α i) := by
    dsimp [sourceSection]
    exact (contMDiff_equivTangentBundleProd_symm
        (I := I₁) (M := ℝ) (I' := I₂) (M' := Sphere2) (n := smoothOrder)).comp
      ((hzeroSection.comp contMDiff_fst).prodMk
        ((hframeSection α i).comp contMDiff_snd))
  have hsourceSection_apply (α : Sphere2) (i : Fin (Module.finrank ℝ SphereModel)) (z : X) :
      sourceSection α i z = ⟨z, (0, frame α i z.2)⟩ := by
    simp [sourceSection, equivTangentBundleProd, zeroSection, frameSection]
  let targetSection (α : Sphere2) (i : Fin (Module.finrank ℝ SphereModel)) (z : X) :
      TangentBundle Iₙ (ApproxAmbient n) :=
    tangentMap Iₓ Iₙ f (sourceSection α i z)
  have htargetSection_continuous (α : Sphere2) (i : Fin (Module.finrank ℝ SphereModel)) :
      Continuous (targetSection α i) := by
    have htangent : Continuous (tangentMap Iₓ Iₙ f) :=
      hf'.continuous_tangentMap (by norm_num)
    exact htangent.comp (hsourceSection α i).continuous
  let vec (α : Sphere2) (i : Fin (Module.finrank ℝ SphereModel)) (z : X) :
      TangentSpace Iₙ (f z) := mfderiv Iₓ Iₙ f z ((0, frame α i z.2))
  have htargetSection_eq (α : Sphere2) (i : Fin (Module.finrank ℝ SphereModel)) :
      (fun z : X => (⟨f z, vec α i z⟩ : TangentBundle Iₙ (ApproxAmbient n))) =
        targetSection α i := by
    funext z
    change (⟨f z, vec α i z⟩ : TangentBundle Iₙ (ApproxAmbient n)) =
      tangentMap Iₓ Iₙ f (sourceSection α i z)
    rw [hsourceSection_apply]
    simp [vec, tangentMap]
  have hvec_continuous (α : Sphere2) (i : Fin (Module.finrank ℝ SphereModel)) :
      Continuous (fun z : X => (vec α i z : ApproxAmbient n)) := by
    have hcoord : Continuous (fun z : X =>
        (tangentBundleModelSpaceHomeomorph Iₙ (targetSection α i z)).2) :=
      continuous_snd.comp
        ((tangentBundleModelSpaceHomeomorph Iₙ).continuous.comp
          (htargetSection_continuous α i))
    have heq (z : X) :
        (tangentBundleModelSpaceHomeomorph Iₙ (targetSection α i z)).2 =
          (vec α i z : ApproxAmbient n) := by
      rw [← htargetSection_eq α i]
      simp [tangentBundleModelSpaceHomeomorph_coe, TotalSpace.toProd]
    convert hcoord using 1
    funext z
    exact heq z
  let localTrace (α : Sphere2) (z : X) : ℝ :=
    ∑ i : Fin (Module.finrank ℝ SphereModel), ‖vec α i z‖ ^ 2
  have hlocalTrace_continuous (α : Sphere2) : Continuous (localTrace α) := by
    change Continuous (fun z : X =>
      ∑ i : Fin (Module.finrank ℝ SphereModel), ‖vec α i z‖ ^ 2)
    apply continuous_finsetSum
    intro i hi
    have hn : Continuous (fun z : X => ‖vec α i z‖) := by
      convert (continuous_norm.comp (hvec_continuous α i)) using 1
      ext z
      exact norm_tangentSpace_vectorSpace (x := f z) (v := vec α i z)
    convert hn.pow 2 using 1
    ext z
    rfl
  have hslice (z : X) (v : TangentSpace I₂ z.2) :
      mfderiv I₂ Iₙ (fun p : Sphere2 => f (z.1, p)) z.2 v =
        mfderiv Iₓ Iₙ f z (0, v) := by
    cases z with
    | mk t p =>
      let ι : Sphere2 → X := fun x => (t, x)
      have hι : ContMDiff I₂ Iₓ smoothOrder ι :=
        contMDiff_const.prodMk contMDiff_id
      have hfMD : MDifferentiable Iₓ Iₙ f := hf'.mdifferentiable (by norm_num)
      have hιMD : MDifferentiable I₂ Iₓ ι := hι.mdifferentiable (by simp [smoothOrder])
      have hcomp := mfderiv_comp_apply (f := ι) (g := f) (x := p)
        (by simpa [ι] using hfMD (t, p)) (hιMD p) v
      have hincl_apply : mfderiv I₂ Iₓ ι p v = (0, v) := by
        rw [mfderiv_prod_right]
        rfl
      rw [hincl_apply] at hcomp
      have hfun : f ∘ ι = (fun x : Sphere2 => f (t, x)) := by
        funext x
        rfl
      rw [hfun] at hcomp
      simpa [ι] using hcomp
  let pointTrace (z : ℝ × Sphere2) : ℝ :=
    ∑ i : Fin (Module.finrank ℝ SphereModel),
      ‖ambientSliceVector (fun p => f (z.1, p)) z.2 i‖ ^ 2
  have htrace_eq (α : Sphere2) (z : ℝ × Sphere2)
      (hz : z.2 ∈ smoothOrthoFrameNbhd (I := I₂) α) :
      pointTrace z = localTrace α z := by
    let D : TangentSpace I₂ z.2 →L[ℝ] TangentSpace Iₙ (f (z.1, z.2)) :=
      mfderiv I₂ Iₙ (fun p : Sphere2 => f (z.1, p)) z.2
    let B : TangentSpace I₂ z.2 →ₗ[ℝ] TangentSpace I₂ z.2 →ₗ[ℝ] ℝ :=
      LinearMap.mk₂ ℝ (fun v w => inner ℝ (D v) (D w))
        (by intro v w x; simp [inner_add_left])
        (by intro c v w; simp [inner_smul_left])
        (by intro v w x; simp [inner_add_right])
        (by intro c v w; simp [inner_smul_right])
    have hdiag :
        (∑ i : Fin (Module.finrank ℝ SphereModel),
          B (smoothOrthoFrame unitRoundSphereMetric z.2 i z.2)
            (smoothOrthoFrame unitRoundSphereMetric z.2 i z.2)) =
        ∑ i : Fin (Module.finrank ℝ SphereModel),
          B (smoothOrthoFrame unitRoundSphereMetric α i z.2)
            (smoothOrthoFrame unitRoundSphereMetric α i z.2) := by
      exact (sum_diagonal_smoothOrthoFrame_eq_std (I := I₂) z.2 B).trans
        (sum_diagonal_smoothOrthoFrame_at_nbhd_eq_std (I := I₂) α hz B).symm
    have hleft : pointTrace z =
        ∑ i : Fin (Module.finrank ℝ SphereModel),
          B (sphereEnergyFrame z.2 i) (sphereEnergyFrame z.2 i) := by
      change (∑ i : Fin (Module.finrank ℝ SphereModel),
          ‖ambientSliceVector (fun p => f (z.1, p)) z.2 i‖ ^ 2) = _
      apply Finset.sum_congr rfl
      intro i hi
      change ‖ambientSliceVector (fun p => f (z.1,p)) z.2 i‖ ^ 2 =
        inner ℝ (D (sphereEnergyFrame z.2 i)) (D (sphereEnergyFrame z.2 i))
      rw [real_inner_self_eq_norm_sq]
      apply congrArg (fun t : ℝ => t ^ 2)
      exact (norm_tangentSpace_vectorSpace (x := f (z.1,z.2))
        (v := D (sphereEnergyFrame z.2 i))).symm
    have hright : localTrace α z =
        ∑ i : Fin (Module.finrank ℝ SphereModel),
          B (frame α i z.2) (frame α i z.2) := by
      change (∑ i : Fin (Module.finrank ℝ SphereModel), ‖vec α i z‖ ^ 2) = _
      apply Finset.sum_congr rfl
      intro i hi
      change ‖mfderiv Iₓ Iₙ f z (0, frame α i z.2)‖ ^ 2 =
        inner ℝ (D (frame α i z.2)) (D (frame α i z.2))
      rw [← hslice z (frame α i z.2)]
      exact (real_inner_self_eq_norm_sq _).symm
    rw [hleft, hright]
    exact hdiag
  let trace : X → ℝ := pointTrace
  have htrace_continuous : Continuous trace := by
    apply continuous_iff_continuousAt.mpr
    intro q
    let α : Sphere2 := q.2
    have hnear : Filter.Eventually (fun z : X =>
        z.2 ∈ smoothOrthoFrameNbhd (I := I₂) α) (nhds q) := by
      exact continuous_snd.continuousAt.preimage_mem_nhds (hframeNbhd α)
    apply ((hlocalTrace_continuous α).continuousAt : ContinuousAt (localTrace α) q).congr
    filter_upwards [hnear] with z hz
    exact (htrace_eq α z hz).symm
  let K : Set X := Set.Icc (0 : ℝ) 1 ×ˢ Set.univ
  have hKcompact : IsCompact K := isCompact_Icc.prod isCompact_univ
  have hKnonempty : K.Nonempty := by
    obtain ⟨p⟩ := (inferInstance : Nonempty Sphere2)
    refine ⟨(0, p), ?_⟩
    simp only [K, Set.mem_prod, Set.mem_Icc, Set.mem_univ]
    exact ⟨⟨le_rfl, by norm_num⟩, trivial⟩
  obtain ⟨z₀, hz₀, hmax⟩ := hKcompact.exists_isMaxOn hKnonempty
    htrace_continuous.continuousOn
  let B : ℝ := trace z₀
  have hB_nonneg : 0 ≤ B := by
    dsimp [B, trace, pointTrace]
    apply Finset.sum_nonneg
    intro i hi
    exact sq_nonneg _
  have htrace_le (z : X) (hz : z ∈ K) : trace z ≤ B := by
    exact hmax hz
  refine ⟨Real.sqrt B, Real.sqrt_nonneg B, ?_⟩
  intro s p i
  have hsK : ((s : ℝ), p) ∈ K := by
    change ((s : ℝ) ∈ Set.Icc (0 : ℝ) 1) ∧ p ∈ Set.univ
    simpa [SweepParameter] using And.intro s.property (Set.mem_univ p)
  have hpow :
      ‖ambientSliceVector (fun z => f (s, z)) p i‖ ^ 2 ≤ B := by
    have hsingle := Finset.single_le_sum
      (s := (Finset.univ : Finset (Fin (Module.finrank ℝ SphereModel))))
      (f := fun j => ‖ambientSliceVector (fun z => f (s, z)) p j‖ ^ 2)
      (fun j hj => sq_nonneg _) (Finset.mem_univ i)
    have hsum :
        (∑ j : Fin (Module.finrank ℝ SphereModel),
          ‖ambientSliceVector (fun z => f (s, z)) p j‖ ^ 2) = trace (s, p) := rfl
    rw [hsum] at hsingle
    exact hsingle.trans (htrace_le (s, p) hsK)
  have hnorm : 0 ≤ ‖ambientSliceVector (fun z => f (s, z)) p i‖ := norm_nonneg _
  exact (Real.le_sqrt hnorm hB_nonneg).2 hpow
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RefinedC1AmbientFrameBound
