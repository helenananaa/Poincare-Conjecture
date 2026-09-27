import PoincareConjecture.ProofContract.Refinement20260927.MetricPatchTransport
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.RefinedLocalPatchDensity
open PoincareConjecture.ProofContract.Refinement20260927
theorem local_patch_density : LocalPatchDensityStatement.{u} :=
/- SWARM_PROOF_BEGIN -/
open MorganTianLib PoincareConjecture.ProofContract.V1 Riemannian Matrix Function Set in
open scoped Manifold ContDiff Topology ENNReal Bundle BigOperators in
by
  classical
  intro M N gM gN f hf hpull
  have hlocal : ∀ {α : M} {β : N} {p : M},
      p ∈ (extChartAt (modelWithCornersSelf ℝ Euclidean3) α).source →
      f p ∈ (extChartAt (modelWithCornersSelf ℝ Euclidean3) β).source →
      ∃ D : Euclidean3 →L[ℝ] Euclidean3,
        HasFDerivAt
            (fun y : Euclidean3 => extChartAt (modelWithCornersSelf ℝ Euclidean3) β (f ((extChartAt (modelWithCornersSelf ℝ Euclidean3) α).symm y))) D
            (extChartAt (modelWithCornersSelf ℝ Euclidean3) α p) ∧
        |D.det| * chartVolumeDensity (I := (modelWithCornersSelf ℝ Euclidean3)) gN β
            (extChartAt (modelWithCornersSelf ℝ Euclidean3) β (f p)) =
          chartVolumeDensity (I := (modelWithCornersSelf ℝ Euclidean3)) gM α (extChartAt (modelWithCornersSelf ℝ Euclidean3) α p) := by
    intro α β p hpα hqβ
    let x : Euclidean3 := extChartAt (modelWithCornersSelf ℝ Euclidean3) α p
    let F : Euclidean3 → Euclidean3 := fun y => extChartAt (modelWithCornersSelf ℝ Euclidean3) β (f ((extChartAt (modelWithCornersSelf ℝ Euclidean3) α).symm y))
    let A : Euclidean3 →L[ℝ] TangentSpace (modelWithCornersSelf ℝ Euclidean3) p :=
      mfderiv (modelWithCornersSelf ℝ Euclidean3) (modelWithCornersSelf ℝ Euclidean3) (extChartAt (modelWithCornersSelf ℝ Euclidean3) α).symm x
    let B : Euclidean3 →L[ℝ] TangentSpace (modelWithCornersSelf ℝ Euclidean3) (f p) :=
      mfderiv (modelWithCornersSelf ℝ Euclidean3) (modelWithCornersSelf ℝ Euclidean3) (extChartAt (modelWithCornersSelf ℝ Euclidean3) β).symm (extChartAt (modelWithCornersSelf ℝ Euclidean3) β (f p))
    let C : TangentSpace (modelWithCornersSelf ℝ Euclidean3) (f p) →L[ℝ] Euclidean3 :=
      mfderiv (modelWithCornersSelf ℝ Euclidean3) (modelWithCornersSelf ℝ Euclidean3) (extChartAt (modelWithCornersSelf ℝ Euclidean3) β) (f p)
    let L : TangentSpace (modelWithCornersSelf ℝ Euclidean3) p →L[ℝ] TangentSpace (modelWithCornersSelf ℝ Euclidean3) (f p) :=
      mfderiv (modelWithCornersSelf ℝ Euclidean3) (modelWithCornersSelf ℝ Euclidean3) f p
    let D : Euclidean3 →L[ℝ] Euclidean3 := fderiv ℝ F x
    have hx : x ∈ (extChartAt (modelWithCornersSelf ℝ Euclidean3) α).target := by
      exact (extChartAt (modelWithCornersSelf ℝ Euclidean3) α).map_source hpα
    have hqβ' : f p ∈ (chartAt Euclidean3 β).source := by
      rw [extChartAt_source] at hqβ
      exact hqβ
    have hy : extChartAt (modelWithCornersSelf ℝ Euclidean3) β (f p) ∈ (extChartAt (modelWithCornersSelf ℝ Euclidean3) β).target := by
      exact (extChartAt (modelWithCornersSelf ℝ Euclidean3) β).map_source hqβ
    have hi : MDifferentiableAt (modelWithCornersSelf ℝ Euclidean3)
        (modelWithCornersSelf ℝ Euclidean3) (extChartAt (modelWithCornersSelf ℝ Euclidean3) α).symm x := by
      apply mdifferentiableWithinAt_univ.mp
      rw [← (modelWithCornersSelf ℝ Euclidean3).range_eq_univ]
      exact mdifferentiableWithinAt_extChartAt_symm hx
    have hf_at : MDifferentiableAt (modelWithCornersSelf ℝ Euclidean3)
        (modelWithCornersSelf ℝ Euclidean3) f p := (hf.mdifferentiable (by norm_num)) p
    have hchart : MDifferentiableAt (modelWithCornersSelf ℝ Euclidean3)
        (modelWithCornersSelf ℝ Euclidean3) (extChartAt (modelWithCornersSelf ℝ Euclidean3) β) (f p) :=
      mdifferentiableAt_extChartAt hqβ'
    have hpx : (extChartAt (modelWithCornersSelf ℝ Euclidean3) α).symm x = p := (extChartAt (modelWithCornersSelf ℝ Euclidean3) α).left_inv hpα
    have hf_x : MDifferentiableAt (modelWithCornersSelf ℝ Euclidean3)
        (modelWithCornersSelf ℝ Euclidean3) f ((extChartAt (modelWithCornersSelf ℝ Euclidean3) α).symm x) := by
      rw [hpx]
      exact hf_at
    have hchart_x : MDifferentiableAt (modelWithCornersSelf ℝ Euclidean3)
        (modelWithCornersSelf ℝ Euclidean3) (extChartAt (modelWithCornersSelf ℝ Euclidean3) β)
        (f ((extChartAt (modelWithCornersSelf ℝ Euclidean3) α).symm x)) := by
      rw [hpx]
      exact hchart
    have hcomp₁ : mfderiv (modelWithCornersSelf ℝ Euclidean3) (modelWithCornersSelf ℝ Euclidean3) (f ∘ (extChartAt (modelWithCornersSelf ℝ Euclidean3) α).symm) x =
        (mfderiv (modelWithCornersSelf ℝ Euclidean3) (modelWithCornersSelf ℝ Euclidean3) f ((extChartAt (modelWithCornersSelf ℝ Euclidean3) α).symm x)) ∘SL
          (mfderiv (modelWithCornersSelf ℝ Euclidean3) (modelWithCornersSelf ℝ Euclidean3) (extChartAt (modelWithCornersSelf ℝ Euclidean3) α).symm x) := by
      exact mfderiv_comp x hf_x hi
    have hcomp₂ : mfderiv (modelWithCornersSelf ℝ Euclidean3) (modelWithCornersSelf ℝ Euclidean3)
        ((extChartAt (modelWithCornersSelf ℝ Euclidean3) β) ∘ (f ∘ (extChartAt (modelWithCornersSelf ℝ Euclidean3) α).symm)) x =
        (mfderiv (modelWithCornersSelf ℝ Euclidean3) (modelWithCornersSelf ℝ Euclidean3) (extChartAt (modelWithCornersSelf ℝ Euclidean3) β)
          (f ((extChartAt (modelWithCornersSelf ℝ Euclidean3) α).symm x))) ∘SL
          (mfderiv (modelWithCornersSelf ℝ Euclidean3) (modelWithCornersSelf ℝ Euclidean3) (f ∘ (extChartAt (modelWithCornersSelf ℝ Euclidean3) α).symm) x) := by
      exact mfderiv_comp x hchart_x (hf_x.comp x hi)
    have hF : HasFDerivAt F (C ∘L (L ∘L A)) x := by
      have hcomp := hchart_x.hasMFDerivAt.comp x
        (hf_x.hasMFDerivAt.comp x hi.hasMFDerivAt)
      rw [hpx] at hcomp
      apply hasMFDerivAt_iff_hasFDerivAt.mp
      simpa only [F, Function.comp_def] using hcomp
    have hDval : D = C ∘L (L ∘L A) := by
      simpa [D] using hF.fderiv
    have hFD : HasFDerivAt F D x := by
      rw [hDval]
      exact hF
    have hBA : ∀ i : Fin (Module.finrank ℝ Euclidean3),
        A (Module.finBasis ℝ Euclidean3 i) =
          Riemannian.Tensor.chartBasisVecFiber α i p := by
      intro i
      have hpα' : p ∈ (chartAt Euclidean3 α).source := by
        have h := hpα
        rw [extChartAt_source] at h
        exact h
      have ht := TangentBundle.symmL_trivializationAt (𝕜 := ℝ)
        (I := (modelWithCornersSelf ℝ Euclidean3)) (x₀ := α) (x := p) hpα'
      rw [(modelWithCornersSelf ℝ Euclidean3).range_eq_univ, mfderivWithin_univ] at ht
      have hi' := congrArg (fun K => K (Module.finBasis ℝ Euclidean3 i)) ht
      have hpbase : p ∈ (trivializationAt Euclidean3 (TangentSpace (modelWithCornersSelf ℝ Euclidean3)) α).baseSet := by
        rw [trivializationAt_baseSet_eq_chartAt_source]
        exact hpα'
      rw [Bundle.Trivialization.symmL_apply _ hpbase] at hi'
      simpa [A, x, Riemannian.Tensor.chartBasisVecFiber,
        Bundle.Trivialization.symmL_apply] using hi'.symm
    have hBB : ∀ i : Fin (Module.finrank ℝ Euclidean3),
        B (Module.finBasis ℝ Euclidean3 i) =
          Riemannian.Tensor.chartBasisVecFiber β i (f p) := by
      intro i
      have ht := TangentBundle.symmL_trivializationAt (𝕜 := ℝ)
        (I := (modelWithCornersSelf ℝ Euclidean3)) (x₀ := β) (x := f p) hqβ'
      rw [(modelWithCornersSelf ℝ Euclidean3).range_eq_univ, mfderivWithin_univ] at ht
      have hi' := congrArg (fun K => K (Module.finBasis ℝ Euclidean3 i)) ht
      have hqbase : f p ∈ (trivializationAt Euclidean3 (TangentSpace (modelWithCornersSelf ℝ Euclidean3)) β).baseSet := by
        rw [trivializationAt_baseSet_eq_chartAt_source]
        exact hqβ'
      rw [Bundle.Trivialization.symmL_apply _ hqbase] at hi'
      simpa [B, Riemannian.Tensor.chartBasisVecFiber,
        Bundle.Trivialization.symmL_apply] using hi'.symm
    have hBC : B ∘L C =
        ContinuousLinearMap.id ℝ (TangentSpace (modelWithCornersSelf ℝ Euclidean3) (f p)) := by
      have hiinv := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt
        (I := (modelWithCornersSelf ℝ Euclidean3)) (x := β) hy
      rw [(modelWithCornersSelf ℝ Euclidean3).range_eq_univ, mfderivWithin_univ] at hiinv
      rw [(extChartAt (modelWithCornersSelf ℝ Euclidean3) β).left_inv hqβ] at hiinv
      simpa only [B, C] using hiinv
    have hBD : ∀ u : Euclidean3, B (D u) = L (A u) := by
      intro u
      calc
        B (D u) = B (C (L (A u))) := by rw [hDval]; rfl
        _ = (B ∘L C) (L (A u)) := rfl
        _ = L (A u) := by rw [hBC]; rfl
    let K : Euclidean3 →ₗ[ℝ] Euclidean3 →ₗ[ℝ] ℝ :=
      { toFun := fun u => (((gN.inner (f p)) (B u)).comp B).toLinearMap
        map_add' := by
          intro u v
          ext w
          simp [map_add]
        map_smul' := by
          intro c u
          ext w
          simp [map_smul] }
    have hK : ∀ u v : Euclidean3, K u v = gN.metricInner (f p) (B u) (B v) := by
      intro u v
      rfl
    have hKbasis : Matrix.of (fun i j => K (Module.finBasis ℝ Euclidean3 i)
        (Module.finBasis ℝ Euclidean3 j)) =
        Riemannian.Tensor.chartGramMatrix (I := (modelWithCornersSelf ℝ Euclidean3)) gN β (f p) := by
      ext i j
      simp only [Matrix.of_apply]
      rw [hK, hBB i, hBB j, Riemannian.Tensor.chartGramMatrix_apply,
        Riemannian.RiemannianMetric.metricInner_apply]
    have hconj := bilinGram_eq_conj (Module.finBasis ℝ Euclidean3)
      (fun i => D (Module.finBasis ℝ Euclidean3 i)) K
    have hgram : Matrix.of (fun i j => K (D (Module.finBasis ℝ Euclidean3 i))
        (D (Module.finBasis ℝ Euclidean3 j))) =
        Riemannian.Tensor.chartGramMatrix (I := (modelWithCornersSelf ℝ Euclidean3)) gM α p := by
      ext i j
      simp only [Matrix.of_apply]
      rw [hK, hBD, hBD, hBA i, hBA j]
      exact (hpull p _ _).symm
    have hmatrix : Riemannian.Tensor.chartGramMatrix (I := (modelWithCornersSelf ℝ Euclidean3)) gM α p =
        Matrix.transpose ((Module.finBasis ℝ Euclidean3).toMatrix
          (fun i => D (Module.finBasis ℝ Euclidean3 i))) *
          Riemannian.Tensor.chartGramMatrix (I := (modelWithCornersSelf ℝ Euclidean3)) gN β (f p) *
            (Module.finBasis ℝ Euclidean3).toMatrix
              (fun i => D (Module.finBasis ℝ Euclidean3 i)) := by
      rw [← hgram, hconj, hKbasis]
    have hdet :
        (LinearMap.det (D : Euclidean3 →ₗ[ℝ] Euclidean3)) ^ 2 *
            (Riemannian.Tensor.chartGramMatrix (I := (modelWithCornersSelf ℝ Euclidean3)) gN β (f p)).det =
          (Riemannian.Tensor.chartGramMatrix (I := (modelWithCornersSelf ℝ Euclidean3)) gM α p).det := by
      have hd := congrArg Matrix.det hmatrix
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd
      have hMdet :
          ((Module.finBasis ℝ Euclidean3).toMatrix
              (fun i => D (Module.finBasis ℝ Euclidean3 i))).det =
            LinearMap.det (D : Euclidean3 →ₗ[ℝ] Euclidean3) := by
        rw [show (Module.finBasis ℝ Euclidean3).toMatrix
              (fun i => D (Module.finBasis ℝ Euclidean3 i)) =
            LinearMap.toMatrix (Module.finBasis ℝ Euclidean3) (Module.finBasis ℝ Euclidean3)
              (D : Euclidean3 →ₗ[ℝ] Euclidean3) by
          ext i j
          simp [Module.Basis.toMatrix_apply, LinearMap.toMatrix_apply]]
        exact LinearMap.det_toMatrix _ _
      rw [hMdet] at hd
      nlinarith [hd]
    have hposN : 0 ≤
        (Riemannian.Tensor.chartGramMatrix (I := (modelWithCornersSelf ℝ Euclidean3)) gN β (f p)).det :=
      (Riemannian.Tensor.chartGramMatrix_det_pos (I := (modelWithCornersSelf ℝ Euclidean3)) gN β
        (by rw [trivializationAt_baseSet_eq_chartAt_source]; exact hqβ')).le
    have hsqrt :
        |LinearMap.det (D : Euclidean3 →ₗ[ℝ] Euclidean3)| *
            Real.sqrt (Riemannian.Tensor.chartGramMatrix (I := (modelWithCornersSelf ℝ Euclidean3)) gN β (f p)).det =
          Real.sqrt (Riemannian.Tensor.chartGramMatrix (I := (modelWithCornersSelf ℝ Euclidean3)) gM α p).det := by
      calc
        |LinearMap.det (D : Euclidean3 →ₗ[ℝ] Euclidean3)| *
            Real.sqrt (Riemannian.Tensor.chartGramMatrix (I := (modelWithCornersSelf ℝ Euclidean3)) gN β (f p)).det =
            Real.sqrt ((LinearMap.det (D : Euclidean3 →ₗ[ℝ] Euclidean3)) ^ 2) *
              Real.sqrt (Riemannian.Tensor.chartGramMatrix (I := (modelWithCornersSelf ℝ Euclidean3)) gN β (f p)).det := by
                rw [Real.sqrt_sq_eq_abs]
        _ = Real.sqrt ((LinearMap.det (D : Euclidean3 →ₗ[ℝ] Euclidean3)) ^ 2 *
              (Riemannian.Tensor.chartGramMatrix (I := (modelWithCornersSelf ℝ Euclidean3)) gN β (f p)).det) := by
                rw [Real.sqrt_mul (sq_nonneg _)]
        _ = Real.sqrt (Riemannian.Tensor.chartGramMatrix (I := (modelWithCornersSelf ℝ Euclidean3)) gM α p).det := by
          rw [hdet]
    have hdenN : chartVolumeDensity (I := (modelWithCornersSelf ℝ Euclidean3)) gN β
        (extChartAt (modelWithCornersSelf ℝ Euclidean3) β (f p)) =
        Real.sqrt (Riemannian.Tensor.chartGramMatrix (I := (modelWithCornersSelf ℝ Euclidean3)) gN β (f p)).det := by
      rw [chartVolumeDensity, (extChartAt (modelWithCornersSelf ℝ Euclidean3) β).left_inv hqβ]
    have hdenM : chartVolumeDensity (I := (modelWithCornersSelf ℝ Euclidean3)) gM α
        (extChartAt (modelWithCornersSelf ℝ Euclidean3) α p) =
        Real.sqrt (Riemannian.Tensor.chartGramMatrix (I := (modelWithCornersSelf ℝ Euclidean3)) gM α p).det := by
      rw [chartVolumeDensity, (extChartAt (modelWithCornersSelf ℝ Euclidean3) α).left_inv hpα]
    have hdensity : |D.det| * chartVolumeDensity (I := (modelWithCornersSelf ℝ Euclidean3)) gN β
        (extChartAt (modelWithCornersSelf ℝ Euclidean3) β (f p)) =
      chartVolumeDensity (I := (modelWithCornersSelf ℝ Euclidean3)) gM α (extChartAt (modelWithCornersSelf ℝ Euclidean3) α p) := by
      rw [hdenN, hdenM]
      simpa [D, ContinuousLinearMap.det] using hsqrt
    exact ⟨D, by simpa [F, x] using hFD, hdensity⟩
  intro alpha beta p hpα hqβ
  exact @hlocal alpha beta p hpα hqβ
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RefinedLocalPatchDensity
