import MorganTianLib.Ch02.SurgeryCap.SphereAmbient
open Set Riemannian
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
noncomputable section
namespace MorganTianLib.SurgeryCap
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- **Math.** Smoothness, tangency and bracket naturality for actual sphere fields. -/
theorem sphereAmbientField_smooth_tangent_bracket :
    (∀ X : SmoothVectorField (𝓡 2) EpsilonNeckSphere,
      ContMDiff (𝓡 2) (𝓡 3) ∞ (sphereAmbientField X)) ∧
    (∀ (X : SmoothVectorField (𝓡 2) EpsilonNeckSphere) (p : EpsilonNeckSphere),
      inner ℝ (p : E3) (sphereAmbientField X p) = 0) ∧
    ∀ (X Y : SmoothVectorField (𝓡 2) EpsilonNeckSphere) (p : EpsilonNeckSphere),
      sphereAmbientField (bracketField X Y) p =
        mvfderiv (𝓡 2) (sphereAmbientField Y) p (X p) -
          mvfderiv (𝓡 2) (sphereAmbientField X) p (Y p) := by
/- SWARM_PROOF_BEGIN -/
  letI : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
  have hsmooth : ∀ Z : SmoothVectorField (𝓡 2) EpsilonNeckSphere,
      ContMDiff (𝓡 2) (𝓡 3) ∞ (sphereAmbientField Z) := by
    intro Z
    let f : EpsilonNeckSphere → E3 := Subtype.val
    have hf : ContMDiff (𝓡 2) (𝓡 3) ∞ f := by
      exact contMDiff_coe_sphere (E := E3) (n := 2)
    have htf : ContMDiff (𝓡 2).tangent (𝓡 3).tangent ∞
        (tangentMap (𝓡 2) (𝓡 3) f) := by
      apply hf.contMDiff_tangentMap (m := ∞) (n := ∞)
      simp
    have hZ : ContMDiff (𝓡 2) ((𝓡 2).tangent) ∞
        (fun q : EpsilonNeckSphere =>
          (⟨q, Z q⟩ : TangentBundle (𝓡 2) EpsilonNeckSphere)) := by
      exact Z.smooth
    have hcomp : ContMDiff (𝓡 2) (𝓡 3).tangent ∞
        ((tangentMap (𝓡 2) (𝓡 3) f) ∘
          (fun q : EpsilonNeckSphere =>
            (⟨q, Z q⟩ : TangentBundle (𝓡 2) EpsilonNeckSphere))) :=
      ContMDiff.comp htf hZ
    have hsnd : ContMDiff (𝓡 3).tangent (𝓡 3) ∞
        (fun q : TangentBundle (𝓡 3) E3 => q.2) :=
      contMDiff_snd_tangentBundle_modelSpace E3 (𝓡 3)
    have hres : ContMDiff (𝓡 2) (𝓡 3) ∞
        ((fun q : TangentBundle (𝓡 3) E3 => q.2) ∘
          ((tangentMap (𝓡 2) (𝓡 3) f) ∘
            (fun q : EpsilonNeckSphere =>
              (⟨q, Z q⟩ : TangentBundle (𝓡 2) EpsilonNeckSphere)))) :=
      ContMDiff.comp hsnd hcomp
    change ContMDiff (𝓡 2) (𝓡 3) ∞
      (fun q : EpsilonNeckSphere =>
        (mfderiv (𝓡 2) (𝓡 3) Subtype.val q) (Z q))
    simpa [tangentMap, f, Function.comp_def] using hres
  have hcoord : ∀ i : Fin 3,
      ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞
        (fun q : EpsilonNeckSphere => ((q : E3) i)) := by
    intro i
    let proj : E3 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) i
    have hproj : ContMDiff (𝓡 2) 𝓘(ℝ, E3 →L[ℝ] ℝ) ∞
        (fun _ : EpsilonNeckSphere => proj) := contMDiff_const
    have hcoe : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞
        (Subtype.val : EpsilonNeckSphere → E3) :=
      contMDiff_coe_sphere (E := E3) (n := 2)
    simpa [proj] using hproj.clm_apply hcoe
  have hcoord_apply : ∀ (Z : SmoothVectorField (𝓡 2) EpsilonNeckSphere)
      (i : Fin 3) (q : EpsilonNeckSphere),
      (sphereAmbientField Z q) i =
        Z.dir (fun r : EpsilonNeckSphere => ((r : E3) i)) q := by
    intro Z i q
    let proj : E3 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) i
    have hp : MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ) proj (q : E3) := by
      exact (ContinuousLinearMap.hasMFDerivAt proj).mdifferentiableAt
    have hcoe : MDifferentiableAt (𝓡 2) (𝓡 3)
        (Subtype.val : EpsilonNeckSphere → E3) q := by
      exact (contMDiff_coe_sphere (E := E3) (n := 2)).mdifferentiableAt one_ne_zero
    have hcomp := mfderiv_comp q hp hcoe
    have hproj : mfderiv (𝓡 3) 𝓘(ℝ, ℝ) proj (q : E3) = proj := by
      exact (ContinuousLinearMap.hasMFDerivAt proj).mfderiv
    have hfun : (fun r : EpsilonNeckSphere => ((r : E3) i)) =
        (proj : E3 → ℝ) ∘ (Subtype.val : EpsilonNeckSphere → E3) := by
      funext r
      simp [proj]
    unfold sphereAmbientField SmoothVectorField.dir
    rw [hfun, hcomp, hproj]
    rfl
  have hambient_apply : ∀ (Z W : SmoothVectorField (𝓡 2) EpsilonNeckSphere)
      (i : Fin 3) (q : EpsilonNeckSphere),
      (mvfderiv (𝓡 2) (sphereAmbientField Z) q (W q)) i =
        W.dir (fun r : EpsilonNeckSphere => ((sphereAmbientField Z r) i)) q := by
    intro Z W i q
    let proj : E3 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) i
    have hp : MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ) proj
        ((sphereAmbientField Z) q) := by
      exact (ContinuousLinearMap.hasMFDerivAt proj).mdifferentiableAt
    have hF : MDifferentiableAt (𝓡 2) (𝓡 3) (sphereAmbientField Z) q :=
      (hsmooth Z).mdifferentiableAt (by simp)
    have hcomp := mfderiv_comp q hp hF
    have hproj : mfderiv (𝓡 3) 𝓘(ℝ, ℝ) proj
        ((sphereAmbientField Z) q) = proj := by
      exact (ContinuousLinearMap.hasMFDerivAt proj).mfderiv
    have hfun : (fun r : EpsilonNeckSphere => ((sphereAmbientField Z r) i)) =
        (proj : E3 → ℝ) ∘ (sphereAmbientField Z) := by
      funext r
      simp [proj]
    unfold SmoothVectorField.dir
    rw [hfun, hcomp, hproj]
    rfl
  refine ⟨hsmooth, ?_, ?_⟩
  · intro X q
    have hrange : sphereAmbientField X q ∈ (ℝ ∙ (q : E3))ᗮ := by
      rw [← range_mfderiv_coe_sphere (E := E3) (n := 2) q]
      exact ⟨X q, rfl⟩
    exact (Submodule.mem_orthogonal (ℝ ∙ (q : E3))
      (sphereAmbientField X q)).1 hrange
      (q : E3) (Submodule.mem_span_singleton_self _)
  · intro X Y q
    ext i
    have hXY : (bracketField X Y).dir
        (fun r : EpsilonNeckSphere => ((r : E3) i)) q =
        X.dir (Y.dir (fun r : EpsilonNeckSphere => ((r : E3) i))) q -
          Y.dir (X.dir (fun r : EpsilonNeckSphere => ((r : E3) i))) q :=
      bracketField_dir X Y (hcoord i) q
    have hY : Y.dir (fun r : EpsilonNeckSphere => ((r : E3) i)) =
        (fun r : EpsilonNeckSphere => (sphereAmbientField Y r) i) := by
      funext r
      exact (hcoord_apply Y i r).symm
    have hX : X.dir (fun r : EpsilonNeckSphere => ((r : E3) i)) =
        (fun r : EpsilonNeckSphere => (sphereAmbientField X r) i) := by
      funext r
      exact (hcoord_apply X i r).symm
    rw [hcoord_apply (bracketField X Y) i q, hXY, hY, hX,
      PiLp.sub_apply, hambient_apply Y X i q, hambient_apply X Y i q]
/- SWARM_PROOF_END -/
end MorganTianLib.SurgeryCap
