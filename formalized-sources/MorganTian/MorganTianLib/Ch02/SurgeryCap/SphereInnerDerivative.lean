import MorganTianLib.Ch02.SurgeryCap.SphereFieldAlgebra
open Set Riemannian
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
noncomputable section
namespace MorganTianLib.SurgeryCap
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- **Math.** Inner-product differentiation for genuine sphere-domain ambient fields. -/
theorem sphere_dir_inner_rule (X : SmoothVectorField (𝓡 2) EpsilonNeckSphere)
    (f g : EpsilonNeckSphere → E3)
    (hf : ContMDiff (𝓡 2) (𝓡 3) ∞ f) (hg : ContMDiff (𝓡 2) (𝓡 3) ∞ g)
    (p : EpsilonNeckSphere) :
    X.dir (fun q => inner ℝ (f q) (g q)) p =
      inner ℝ (mvfderiv (𝓡 2) f p (X p)) (g p) +
        inner ℝ (f p) (mvfderiv (𝓡 2) g p (X p)) := by
/- SWARM_PROOF_BEGIN -/
  have hcoord_f : ∀ i : Fin 3,
      ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞
        (fun q : EpsilonNeckSphere => (f q) i) := by
    intro i
    let proj : E3 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) i
    have hproj : ContMDiff (𝓡 2) 𝓘(ℝ, E3 →L[ℝ] ℝ) ∞
        (fun _ : EpsilonNeckSphere => proj) := contMDiff_const
    simpa [proj] using hproj.clm_apply hf
  have hcoord_g : ∀ i : Fin 3,
      ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞
        (fun q : EpsilonNeckSphere => (g q) i) := by
    intro i
    let proj : E3 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) i
    have hproj : ContMDiff (𝓡 2) 𝓘(ℝ, E3 →L[ℝ] ℝ) ∞
        (fun _ : EpsilonNeckSphere => proj) := contMDiff_const
    simpa [proj] using hproj.clm_apply hg
  have hderiv_f : ∀ i : Fin 3,
      (mvfderiv (𝓡 2) f p (X p)) i =
        X.dir (fun q : EpsilonNeckSphere => (f q) i) p := by
    intro i
    let proj : E3 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) i
    have hp : MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ) proj (f p) := by
      exact (ContinuousLinearMap.hasMFDerivAt proj).mdifferentiableAt
    have hF : MDifferentiableAt (𝓡 2) (𝓡 3) f p :=
      hf.mdifferentiableAt (by simp)
    have hcomp := mfderiv_comp (I := 𝓡 2) (I' := 𝓡 3)
      (I'' := 𝓘(ℝ, ℝ)) p hp hF
    have hproj : mfderiv (𝓡 3) 𝓘(ℝ, ℝ) proj (f p) = proj := by
      exact (ContinuousLinearMap.hasMFDerivAt proj).mfderiv
    have hfun : (fun q : EpsilonNeckSphere => (f q) i) =
        (proj : E3 → ℝ) ∘ f := by
      funext q
      simp [proj]
    unfold SmoothVectorField.dir
    rw [hfun, hcomp, hproj]
    rfl
  have hderiv_g : ∀ i : Fin 3,
      (mvfderiv (𝓡 2) g p (X p)) i =
        X.dir (fun q : EpsilonNeckSphere => (g q) i) p := by
    intro i
    let proj : E3 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) i
    have hp : MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ) proj (g p) := by
      exact (ContinuousLinearMap.hasMFDerivAt proj).mdifferentiableAt
    have hG : MDifferentiableAt (𝓡 2) (𝓡 3) g p :=
      hg.mdifferentiableAt (by simp)
    have hcomp := mfderiv_comp (I := 𝓡 2) (I' := 𝓡 3)
      (I'' := 𝓘(ℝ, ℝ)) p hp hG
    have hproj : mfderiv (𝓡 3) 𝓘(ℝ, ℝ) proj (g p) = proj := by
      exact (ContinuousLinearMap.hasMFDerivAt proj).mfderiv
    have hfun : (fun q : EpsilonNeckSphere => (g q) i) =
        (proj : E3 → ℝ) ∘ g := by
      funext q
      simp [proj]
    unfold SmoothVectorField.dir
    rw [hfun, hcomp, hproj]
    rfl
  have hinner : ∀ u v : E3,
      inner ℝ u v = ∑ i : Fin 3, u i * v i := by
    intro u v
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i hi
    exact mul_comm _ _
  calc
    X.dir (fun q => inner ℝ (f q) (g q)) p =
        X.dir (fun q => ∑ i : Fin 3, (f q) i * (g q) i) p := by
          congr 2
          funext q
          exact hinner (f q) (g q)
    _ = ∑ i : Fin 3,
        X.dir (fun q => (f q) i * (g q) i) p := by
          rw [dir_sum X]
          intro i hi
          exact (hcoord_f i).mul (hcoord_g i)
    _ = ∑ i : Fin 3,
        ((f p) i * X.dir (fun q => (g q) i) p +
          (g p) i * X.dir (fun q => (f q) i) p) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [X.dir_mul p
            ((hcoord_f i).mdifferentiableAt (by simp))
            ((hcoord_g i).mdifferentiableAt (by simp))]
    _ = (∑ i : Fin 3, (mvfderiv (𝓡 2) f p (X p)) i * (g p) i) +
          ∑ i : Fin 3, (f p) i * (mvfderiv (𝓡 2) g p (X p)) i := by
          rw [Finset.sum_add_distrib, add_comm]
          congr 1
          · apply Finset.sum_congr rfl
            intro i hi
            rw [hderiv_f i]
            ring
          · apply Finset.sum_congr rfl
            intro i hi
            rw [hderiv_g i]
    _ = inner ℝ (mvfderiv (𝓡 2) f p (X p)) (g p) +
          inner ℝ (f p) (mvfderiv (𝓡 2) g p (X p)) := by
          rw [hinner, hinner]
/- SWARM_PROOF_END -/
end MorganTianLib.SurgeryCap
