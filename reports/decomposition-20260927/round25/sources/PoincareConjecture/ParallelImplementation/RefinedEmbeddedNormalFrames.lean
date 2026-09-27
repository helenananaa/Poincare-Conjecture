import PoincareConjecture.ProofContract.Refinement20260927.EmbeddedNormalFrames
import LeeLib.Ch02.NormalBundle
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.RefinedEmbeddedNormalFrames
open PoincareConjecture.ProofContract.Refinement20260927
theorem embedded_normal_frames : EmbeddedNormalFrameStatement.{u} :=
/- SWARM_PROOF_BEGIN -/
by
  unfold EmbeddedNormalFrameStatement
  intro N n e p
  let f : ContMDiffMap
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (ApproxAmbient n)) N.toTopCat (ApproxAmbient n) (↑(⊤ : ℕ∞)) :=
        ⟨e.map, e.smooth⟩
  obtain ⟨v, hn, Y, hopen, hp, hY, hYon, hYnorm, hYspan⟩ :=
    LeeLib.Ch02.exists_orthonormalFrame_normalSpace
      (LeeLib.Ch02.euclideanMetric (ApproxAmbient n)) f e.injective_deriv p
  let chart : OpenPartialHomeomorph N NormalTangent :=
    chartAt PoincareConjecture.ProofContract.V1.Euclidean3 p
  let base : OpenPartialHomeomorph N NormalTangent := chart.restrOpen v hopen
  have hsource_sub : base.source ⊆ v := by
    intro q hq
    change q ∈ chart.source ∩ v at hq
    exact hq.2
  have hchart_source : base.source ⊆ chart.source := by
    intro q hq
    change q ∈ chart.source ∩ v at hq
    exact hq.1
  have htarget_sub : base.target ⊆ chart.target := by
    intro z hz
    change z ∈ chart.target ∩ chart.symm ⁻¹' v at hz
    exact hz.1
  have hpbase : p ∈ base.source := by
    change p ∈ chart.source ∩ v
    exact ⟨mem_chart_source _ p, hp⟩
  have hsymm : ContMDiffOn ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))) ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))) (↑(⊤ : ℕ∞)) base.symm base.target := by
    simpa only [base, OpenPartialHomeomorph.coe_restrOpen_symm] using
      (contMDiffOn_chart_symm (x := p)).mono htarget_sub
  have hbaseMD : base.MDifferentiable ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))) ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))) := by
    constructor
    · intro q hq
      have h0 := (mdifferentiable_chart (I := (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))) (H := PoincareConjecture.ProofContract.V1.Euclidean3) (x := p)).1 q (hchart_source hq)
      have hm := h0.mono hchart_source
      simpa only [base, OpenPartialHomeomorph.coe_restrOpen] using hm
    · intro z hz
      have hz0 := (mdifferentiable_chart (I := (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))) (H := PoincareConjecture.ProofContract.V1.Euclidean3) (x := p)).2 z (htarget_sub hz)
      have hm := hz0.mono htarget_sub
      simpa only [base, OpenPartialHomeomorph.coe_restrOpen_symm] using hm
  let frame : Fin (Module.finrank ℝ (ApproxAmbient n) - Module.finrank ℝ NormalTangent) → N → ApproxAmbient n :=
    fun i q => Y i q
  have htrivCoord (i : Fin (Module.finrank ℝ (ApproxAmbient n) - Module.finrank ℝ NormalTangent))
      (q0 q : N) :
      (trivializationAt (ApproxAmbient n) (Bundle.Pullback f (TangentSpace (modelWithCornersSelf ℝ (ApproxAmbient n)))) q0
        (⟨q, Y i q⟩ : Bundle.TotalSpace (ApproxAmbient n) (Bundle.Pullback f (TangentSpace (modelWithCornersSelf ℝ (ApproxAmbient n)))))).2 = Y i q := by
    rw [LeeLib.Ch02.trivializationAt_pullback]
    rw [Bundle.Trivialization.pullback_apply]
    rw [Bundle.Pullback.lift_mk]
    exact congrArg Prod.snd
      (trivializationAt_model_space_apply
        (p := ⟨e.map q, Y i q⟩) (x := e.map q0))
  have hvec (i : Fin (Module.finrank ℝ (ApproxAmbient n) - Module.finrank ℝ NormalTangent)) :
      ContMDiffOn ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))) ((modelWithCornersSelf ℝ (ApproxAmbient n))) (↑(⊤ : ℕ∞)) (fun q => Y i q) v := by
    intro q hq
    have hsmooth := hY i q hq
    rw [Bundle.contMDiffWithinAt_section] at hsmooth
    have heq : (fun x => (trivializationAt (ApproxAmbient n)
        (Bundle.Pullback f (TangentSpace (modelWithCornersSelf ℝ (ApproxAmbient n)))) q
        (⟨x, Y i x⟩ : Bundle.TotalSpace (ApproxAmbient n)
          (Bundle.Pullback f (TangentSpace (modelWithCornersSelf ℝ (ApproxAmbient n)))))).2) = fun x => Y i x := by
      funext x
      exact htrivCoord i q x
    simpa only [heq] using hsmooth
  have hcont (i : Fin (Module.finrank ℝ (ApproxAmbient n) - Module.finrank ℝ NormalTangent)) :
      ContinuousOn (frame i) base.source := by
    simpa [frame] using (hvec i).continuousOn.mono hsource_sub
  have hsmoothFrame (i : Fin (Module.finrank ℝ (ApproxAmbient n) - Module.finrank ℝ NormalTangent)) :
      ContDiffOn ℝ (↑(⊤ : ℕ∞)) (frame i ∘ base.symm) base.target := by
    have hcoord : ContMDiffOn ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))) ((modelWithCornersSelf ℝ (ApproxAmbient n))) (↑(⊤ : ℕ∞))
        ((fun q => Y i q) ∘ base.symm) base.target :=
      (hvec i).comp hsymm (by
        intro z hz
        have hs : base.symm z ∈ base.source := base.map_target hz
        exact hsource_sub hs)
    simpa [frame, Function.comp_def] using hcoord.contDiffOn
  have hembsmooth : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (e.map ∘ base.symm) base.target := by
    have hem : ContMDiffOn ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))) ((modelWithCornersSelf ℝ (ApproxAmbient n))) (↑(⊤ : ℕ∞)) e.map Set.univ :=
      e.smooth.contMDiffOn
    have hcoord : ContMDiffOn ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))) ((modelWithCornersSelf ℝ (ApproxAmbient n))) (↑(⊤ : ℕ∞))
        (e.map ∘ base.symm) base.target :=
      hem.comp hsymm (by intro z hz; simp)
    exact hcoord.contDiffOn
  have hmem_eq (q : N) (y : ApproxAmbient n) :
      (show (Bundle.Pullback f (TangentSpace (modelWithCornersSelf ℝ (ApproxAmbient n)))) q from y) ∈
        LeeLib.Ch02.normalSpace (LeeLib.Ch02.euclideanMetric (ApproxAmbient n)) f q ↔
      y ∈ embeddedNormalSpace e q := by
    constructor
    · intro hy
      rw [embeddedNormalSpace, Submodule.mem_orthogonal]
      intro z hz
      have hnorm := (LeeLib.Ch02.mem_normalSpace).mp hy
      have hz' : z ∈ LeeLib.Ch02.tangentRange f q := by
        change ∃ x, (mfderiv ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))) (modelWithCornersSelf ℝ (ApproxAmbient n)) e.map q) x = z
        rcases hz with ⟨x, hx⟩
        exact ⟨x, hx⟩
      have hzero := hnorm z hz'
      have hzero' : inner ℝ y z = 0 := by
        change (innerSL ℝ y) z = 0
        exact hzero
      change inner ℝ z y = 0
      rw [real_inner_comm]
      exact hzero'
    · intro hy
      apply (LeeLib.Ch02.mem_normalSpace).mpr
      intro z hz
      have hz' : z ∈ LinearMap.range (mfderiv ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))) (modelWithCornersSelf ℝ (ApproxAmbient n)) e.map q).toLinearMap := by
        change ∃ x, (mfderiv ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))) (modelWithCornersSelf ℝ (ApproxAmbient n)) e.map q) x = z
        change ∃ x, (mfderiv ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))) (modelWithCornersSelf ℝ (ApproxAmbient n)) e.map q) x = z at hz
        exact hz
      rw [embeddedNormalSpace, Submodule.mem_orthogonal] at hy
      have hzero := hy z hz'
      have hzero' : inner ℝ y z = 0 := by
        rw [real_inner_comm]
        exact hzero
      change inner ℝ y z = 0
      exact hzero'
  have hnormal (q : N) (hq : q ∈ v)
      (i : Fin (Module.finrank ℝ (ApproxAmbient n) - Module.finrank ℝ NormalTangent)) :
      frame i q ∈ embeddedNormalSpace e q :=
    (hmem_eq q (frame i q)).mp (hYnorm q hq i)
  have hor (q : N) (hq : q ∈ v) : Orthonormal ℝ (fun i => frame i q) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hh := hYon q hq i j
    change (innerSL ℝ (frame i q)) (frame j q) = _
    exact hh
  let ambientAddMonoid : AddCommMonoid (ApproxAmbient n) := inferInstance
  let ambientModule : @Module ℝ (ApproxAmbient n) inferInstance ambientAddMonoid := inferInstance
  let frameSpan : N → Submodule ℝ (ApproxAmbient n) := fun q =>
    @Submodule.span ℝ (ApproxAmbient n) inferInstance ambientAddMonoid ambientModule
      (Set.range fun i => frame i q)
  have hspans (q : N) (hq : q ∈ v) :
      Submodule.span ℝ (Set.range fun i => frame i q) = embeddedNormalSpace e q := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro y hy
      rcases hy with ⟨i, rfl⟩
      exact hnormal q hq i
    · intro y hy
      letI : AddCommGroup ((Bundle.Pullback f (TangentSpace (modelWithCornersSelf ℝ (ApproxAmbient n)))) q) :=
        LeeLib.Ch02.Pullback.addCommGroup (f := f) q
      letI : Module ℝ ((Bundle.Pullback f (TangentSpace (modelWithCornersSelf ℝ (ApproxAmbient n)))) q) :=
        LeeLib.Ch02.Pullback.module (f := f) q
      have hlee : (show (Bundle.Pullback f (TangentSpace (modelWithCornersSelf ℝ (ApproxAmbient n)))) q from y) ∈
          LeeLib.Ch02.normalSpace (LeeLib.Ch02.euclideanMetric (ApproxAmbient n)) f q := by
        apply (LeeLib.Ch02.mem_normalSpace).mpr
        intro z hz
        have hz' : z ∈ LeeLib.Ch02.tangentRange f q := by
          change ∃ x, (mfderiv ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))) (modelWithCornersSelf ℝ (ApproxAmbient n)) e.map q) x = z
          rcases hz with ⟨x, hx⟩
          exact ⟨x, hx⟩
        rw [embeddedNormalSpace, Submodule.mem_orthogonal] at hy
        have hzero := hy z hz'
        have hzero' : inner ℝ y z = 0 := by
          rw [real_inner_comm]
          exact hzero
        change (innerSL ℝ y) z = 0
        exact hzero'
      have hsrc : (show (Bundle.Pullback f (TangentSpace (modelWithCornersSelf ℝ (ApproxAmbient n)))) q from y) ∈
          Submodule.span ℝ (Set.range fun i => Y i q) := by
        rw [hYspan q hq]
        exact hlee
      have hadd (a b : (Bundle.Pullback f (TangentSpace (modelWithCornersSelf ℝ (ApproxAmbient n)))) q) :
          (show ApproxAmbient n from a + b) =
            (show ApproxAmbient n from a) + (show ApproxAmbient n from b) := rfl
      have hsmul (c : ℝ) (a : (Bundle.Pullback f (TangentSpace (modelWithCornersSelf ℝ (ApproxAmbient n)))) q) :
          (show ApproxAmbient n from c • a) = c • (show ApproxAmbient n from a) := rfl
      have hzero :
          (show ApproxAmbient n from (0 : (Bundle.Pullback f (TangentSpace (modelWithCornersSelf ℝ (ApproxAmbient n)))) q)) = 0 := rfl
      have hconv (w : (Bundle.Pullback f (TangentSpace (modelWithCornersSelf ℝ (ApproxAmbient n)))) q)
          (hw : w ∈ Submodule.span ℝ (Set.range fun i => Y i q)) :
          (show ApproxAmbient n from w) ∈ frameSpan q := by
        induction hw using Submodule.span_induction with
        | mem z hz =>
            rcases hz with ⟨i, hi⟩
            subst z
            have hgen : frame i q ∈ frameSpan q := by
              dsimp [frameSpan]
              exact @Submodule.subset_span ℝ (ApproxAmbient n) inferInstance
                ambientAddMonoid ambientModule (Set.range fun j => frame j q) (frame i q) ⟨i, rfl⟩
            exact hgen
        | zero =>
            rw [hzero]
            exact @Submodule.zero_mem ℝ (ApproxAmbient n) inferInstance
              ambientAddMonoid (module_M := ambientModule) (frameSpan q)
        | add a b ha hb hia hib =>
            rw [hadd]
            exact @Submodule.add_mem ℝ (ApproxAmbient n) inferInstance
              ambientAddMonoid ambientModule (frameSpan q) a b hia hib
        | smul c a ha hia =>
            rw [hsmul]
            exact @Submodule.smul_mem ℝ (ApproxAmbient n) inferInstance
              ambientAddMonoid ambientModule (frameSpan q) a c hia
      exact hconv _ hsrc
  have hbaseP : base p ∈ base.target := base.map_source hpbase
  have hembMD : MDifferentiableAt ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))) ((modelWithCornersSelf ℝ (ApproxAmbient n))) e.map p := by
    exact (e.smooth.mdifferentiable (by norm_num)).mdifferentiableAt
  have hembAt : MDifferentiableAt ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))) ((modelWithCornersSelf ℝ (ApproxAmbient n))) e.map (base.symm (base p)) := by
    simpa only [base.left_inv hpbase] using hembMD
  have hinvAt : MDifferentiableAt ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))) ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))) base.symm (base p) :=
    hbaseMD.symm.mdifferentiableAt hbaseP
  let A : TangentSpace ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))) p →L[ℝ] ApproxAmbient n :=
    mfderiv ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))) (modelWithCornersSelf ℝ (ApproxAmbient n)) e.map p
  let B : NormalTangent →L[ℝ] TangentSpace ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))) p :=
    mfderiv ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))) ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))) base.symm (base p)
  let linear : NormalTangent →L[ℝ] ApproxAmbient n := A.comp B
  have hlineq : mfderiv ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))) (modelWithCornersSelf ℝ (ApproxAmbient n)) (e.map ∘ base.symm) (base p) = linear := by
    dsimp [linear, A, B]
    rw [mfderiv_comp _ hembAt hinvAt]
    rw [base.left_inv hpbase]
  have hlinear_fac : linear = A.comp B := rfl
  have hcompMD : MDifferentiableAt ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))) ((modelWithCornersSelf ℝ (ApproxAmbient n))) (e.map ∘ base.symm) (base p) := MDifferentiableAt.comp (f := base.symm) (g := e.map) (x := base p) hembAt hinvAt
  have hderiv : HasFDerivAt (e.map ∘ base.symm) linear (base p) := by
    rw [← hlineq]
    exact hcompMD.hasMFDerivAt.hasFDerivAt
  have hAinj : Function.Injective A := e.injective_deriv p
  have hBinj : Function.Injective B := (hbaseMD.symm.mfderiv hbaseP).injective
  have hBsurj : Function.Surjective B := (hbaseMD.symm.mfderiv hbaseP).surjective
  have hlinear_inj : Function.Injective linear := by
    intro x y hxy
    change A (B x) = A (B y) at hxy
    exact hBinj (hAinj hxy)
  have hrange : LinearMap.range linear.toLinearMap = LinearMap.range A.toLinearMap := by
    rw [hlinear_fac]
    ext y
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨B x, ?_⟩
      calc
        A (B x) = (A.comp B) x := (ContinuousLinearMap.comp_apply A B x).symm
        _ = y := hx
    · rintro ⟨x, hx⟩
      obtain ⟨z, hz⟩ := hBsurj x
      refine ⟨z, ?_⟩
      calc
        (A.comp B) z = A (B z) := ContinuousLinearMap.comp_apply A B z
        _ = A x := by rw [hz]
        _ = y := hx
  have hcenter : embeddedNormalSpace e p = NormalFiber linear := by
    change (LinearMap.range A.toLinearMap)ᗮ = (LinearMap.range linear.toLinearMap)ᗮ
    rw [hrange]
  refine ⟨{
    baseChart := base
    point_source := hpbase
    smooth_base_inverse := hsymm
    smooth_embedding := hembsmooth
    linear := linear
    linear_injective := hlinear_inj
    embedding_deriv := hderiv
    center_normal := hcenter
    count := Module.finrank ℝ (ApproxAmbient n) - Module.finrank ℝ NormalTangent
    frame := frame
    continuous_frame := hcont
    smooth_frame := hsmoothFrame
    orthonormal := by
      intro q hq
      exact hor q (hsource_sub hq)
    spans := by
      intro q hq
      exact hspans q (hsource_sub hq)
  }⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RefinedEmbeddedNormalFrames
