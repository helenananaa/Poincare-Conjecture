import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SmoothPathSuperposition
open scoped ContDiff Topology
variable {S E F : Type*} [TopologicalSpace S] [CompactSpace S]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
def superposition (f : E → F) (hf : Continuous f) : C(S,E) → C(S,F) :=
  fun u => ⟨fun t => f (u t), hf.comp u.continuous⟩
/-- Sup-norm smoothness of actual pointwise composition on a compact parameter space. -/
theorem contDiff_superposition (f : E → F) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (superposition (S := S) f hf.continuous) :=
/- SWARM_PROOF_BEGIN -/
by
  have hSuper : ∀ (n : ℕ) {G : Type (max u_2 u_3)}
      [NormedAddCommGroup G] [NormedSpace ℝ G]
      [CompleteSpace G] (g : E → G) (hg : ContDiff ℝ n g),
      ContDiff ℝ n (superposition (S := S) g hg.continuous) := by
    intro n
    induction n with
    | zero =>
        intro G _ _ _ g hg
        simp only [Nat.cast_zero, contDiff_zero] at hg ⊢
        have hgc : Continuous g := by simpa using hg
        let q : C(E, G) := ⟨g, hgc⟩
        have heq : (fun u : C(S, E) => superposition (S := S) g hgc u) =
            fun u => q.comp u := by
          funext u
          ext t
          rfl
        change Continuous (fun u : C(S, E) => superposition (S := S) g hgc u)
        rw [heq]
        exact ContinuousMap.continuous_postcomp q
    | succ n ih =>
        intro G _ _ _ g hg
        let actAt (A : C(S, E →L[ℝ] G)) : C(S, E) →ₗ[ℝ] C(S, G) :=
          { toFun := fun v =>
              ⟨fun t => A t (v t),
                (isBoundedBilinearMap_apply.continuous.comp
                  (A.continuous.prodMk v.continuous))⟩
            map_add' := by
              intro v w
              ext t
              simp
            map_smul' := by
              intro c v
              ext t
              simp }
        let actFor (A : C(S, E →L[ℝ] G)) : C(S, E) →L[ℝ] C(S, G) :=
          (actAt A).mkContinuous ‖A‖ (by
            intro v
            apply (ContinuousMap.norm_le (f := actAt A v) (C := ‖A‖ * ‖v‖)
              (by positivity)).2
            intro t
            calc
              ‖A t (v t)‖ ≤ ‖A t‖ * ‖v t‖ := ContinuousLinearMap.le_opNorm _ _
              _ ≤ ‖A‖ * ‖v‖ := by
                exact mul_le_mul (A.norm_coe_le_norm t) (v.norm_coe_le_norm t)
                  (norm_nonneg _) (norm_nonneg _))
        let actLin : C(S, E →L[ℝ] G) →ₗ[ℝ]
            (C(S, E) →L[ℝ] C(S, G)) :=
          { toFun := actFor
            map_add' := by
              intro A B
              ext v t
              rfl
            map_smul' := by
              intro c A
              ext v t
              rfl }
        have hactFor (A : C(S, E →L[ℝ] G)) : ‖actFor A‖ ≤ ‖A‖ := by
          dsimp [actFor]
          exact LinearMap.mkContinuous_norm_le _ (norm_nonneg _) (by
            intro v
            apply (ContinuousMap.norm_le (f := actAt A v) (C := ‖A‖ * ‖v‖)
              (by positivity)).2
            intro t
            calc
              ‖A t (v t)‖ ≤ ‖A t‖ * ‖v t‖ := ContinuousLinearMap.le_opNorm _ _
              _ ≤ ‖A‖ * ‖v‖ := by
                exact mul_le_mul (A.norm_coe_le_norm t) (v.norm_coe_le_norm t)
                  (norm_nonneg _) (norm_nonneg _))
        let act : C(S, E →L[ℝ] G) →L[ℝ]
            (C(S, E) →L[ℝ] C(S, G)) :=
          actLin.mkContinuous 1 (by
            intro A
            change ‖actFor A‖ ≤ 1 * ‖A‖
            simpa using hactFor A)
        have hfd : ContDiff ℝ n (fderiv ℝ g) := by
          exact hg.fderiv_right (m := n) (by simp)
        let df : C(S, E) → C(S, E) →L[ℝ] C(S, G) := fun u =>
          act (superposition (S := S) (fderiv ℝ g) hfd.continuous u)
        have hdf : ContDiff ℝ n df := by
          exact act.contDiff.comp (ih (fderiv ℝ g) hfd)
        have hderiv : ∀ u : C(S, E),
            HasFDerivAt (superposition (S := S) g hg.continuous) (df u) u := by
          intro u
          rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
          intro c hc
          have hg1 : ContDiff ℝ 1 g := hg.of_le (by simp)
          have hDcontinuous : Continuous (fderiv ℝ g) :=
            hg1.continuous_fderiv (by norm_num)
          have hK : IsCompact (Set.range u) := isCompact_range u.continuous
          have hU :
              {p : E × E | p.1 ∈ Set.range u →
                (fderiv ℝ g p.1, fderiv ℝ g p.2) ∈
                  {q : (E →L[ℝ] G) × (E →L[ℝ] G) | dist q.1 q.2 < c}} ∈ uniformity E :=
            hK.uniformContinuousAt_of_continuousAt (fderiv ℝ g)
              (fun x _ => hDcontinuous.continuousAt) (Metric.dist_mem_uniformity hc)
          obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_uniformity_dist.mp hU
          filter_upwards [Metric.ball_mem_nhds (0 : C(S, E)) hδ] with v hv
          have hvn : ‖v‖ < δ := by
            simpa [Metric.mem_ball, dist_eq_norm] using hv
          have hpoint : ∀ t : S,
              ‖g (u t + v t) - g (u t) - fderiv ℝ g (u t) (v t)‖ ≤ c * ‖v t‖ := by
            intro t
            let x := u t
            have hclose : ∀ z ∈ Metric.ball x δ,
                ‖fderiv ℝ g z - fderiv ℝ g x‖ ≤ c := by
              intro z hz
              have hxrange : x ∈ Set.range u := ⟨t, rfl⟩
              have hdist : dist x z < δ := by
                simpa [Metric.mem_ball, dist_comm] using hz
              have hpair := hδsub hdist hxrange
              have hpair' : dist (fderiv ℝ g z) (fderiv ℝ g x) < c := by
                simpa [dist_comm] using hpair
              exact le_of_lt (by simpa [dist_eq_norm] using hpair')
            have hxball : x ∈ Metric.ball x δ := Metric.mem_ball_self hδ
            have hvball : x + v t ∈ Metric.ball x δ := by
              rw [Metric.mem_ball, dist_eq_norm]
              simpa using lt_of_le_of_lt (v.norm_coe_le_norm t) hvn
            have hmv := (convex_ball x δ).norm_image_sub_le_of_norm_fderiv_le'
              (f := g) (fun z _ => (hg1.differentiable (by norm_num)) z)
              hclose hxball hvball
            simpa [x] using hmv
          have hrem :
              ‖superposition (S := S) g hg.continuous (u + v) -
                  superposition (S := S) g hg.continuous u - df u v‖ ≤ c * ‖v‖ := by
            apply (ContinuousMap.norm_le
              (f := superposition (S := S) g hg.continuous (u + v) -
                superposition (S := S) g hg.continuous u - df u v)
              (C := c * ‖v‖) (by positivity)).2
            intro t
            calc
              ‖(superposition (S := S) g hg.continuous (u + v) -
                  superposition (S := S) g hg.continuous u - df u v) t‖ ≤
                  c * ‖v t‖ := by
                    simpa [df, act, actLin, actFor, actAt, superposition] using hpoint t
              _ ≤ c * ‖v‖ := mul_le_mul_of_nonneg_left (v.norm_coe_le_norm t) hc.le
          exact hrem
        simpa only [Nat.cast_succ] using
          (contDiff_succ_iff_hasFDerivAt (f := superposition (S := S) g hg.continuous)).2
            ⟨df, hdf, hderiv⟩
  rw [contDiff_infty]
  intro n
  let e : ULift.{max u_2 u_3, u_3} F ≃L[ℝ] F := ContinuousLinearEquiv.ulift
  let fup : E → ULift.{max u_2 u_3, u_3} F := fun x => e.symm (f x)
  have hfup : ContDiff ℝ n fup := by
    have hle : (↑n : ℕ∞ω) ≤ (∞ : ℕ∞ω) :=
      WithTop.coe_le_coe.2 (OrderTop.le_top (n : ℕ∞))
    exact e.symm.toContinuousLinearMap.contDiff.comp (hf.of_le hle)
  let eCLM : ULift.{max u_2 u_3, u_3} F →L[ℝ] F := e.toContinuousLinearMap
  let mapLin : C(S, ULift.{max u_2 u_3, u_3} F) →ₗ[ℝ] C(S, F) :=
    { toFun := fun v => ⟨fun t => eCLM (v t), eCLM.continuous.comp v.continuous⟩
      map_add' := by
        intro v w
        ext t
        simp
      map_smul' := by
        intro c v
        ext t
        simp }
  let mapCurve : C(S, ULift.{max u_2 u_3, u_3} F) →L[ℝ] C(S, F) :=
    mapLin.mkContinuous ‖eCLM‖ (by
      intro v
      apply (ContinuousMap.norm_le (f := mapLin v) (C := ‖eCLM‖ * ‖v‖)
        (by positivity)).2
      intro t
      calc
        ‖eCLM (v t)‖ ≤ ‖eCLM‖ * ‖v t‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖eCLM‖ * ‖v‖ := by
          exact mul_le_mul (le_rfl) (v.norm_coe_le_norm t) (norm_nonneg _) (norm_nonneg _))
  have hresult : ContDiff ℝ n
      (fun u : C(S, E) => mapCurve (superposition (S := S) fup hfup.continuous u)) := by
    exact mapCurve.contDiff.comp (hSuper n fup hfup)
  have heq :
      (fun u : C(S, E) => mapCurve (superposition (S := S) fup hfup.continuous u)) =
        superposition (S := S) f hf.continuous := by
    funext u
    ext t
    simp [mapCurve, mapLin, eCLM, e, fup, superposition]
  rw [← heq]
  exact hresult
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SmoothPathSuperposition
