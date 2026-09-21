import MorganTianLib.Ch01.RiemannianJacobian
import MorganTianLib.Ch01.FrameChartDeterminant
import Mathlib.Geometry.Manifold.Diffeomorph

open Set MeasureTheory Riemannian Matrix Function
open scoped ContDiff Manifold Topology ENNReal Bundle BigOperators

noncomputable section
namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [MeasurableSpace E] [BorelSpace E]
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E H'}
  [I.Boundaryless] [J.Boundaryless]
  {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace H' N] [IsManifold I ∞ M] [IsManifold J ∞ N]
  [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]
  [SecondCountableTopology M] [SecondCountableTopology N] [Nonempty M] [Nonempty N]
  [SigmaCompactSpace M] [SigmaCompactSpace N] [T2Space M] [T2Space N]

/-- **Math.** A metric-pullback diffeomorphism preserves the canonical Riemannian measure. -/
theorem riemannianMeasure_image_of_pullback_metric
    (mu : Measure E) [mu.IsAddHaarMeasure]
    (gM : RiemannianMetric I M) (gN : RiemannianMetric J N)
    (phi : Diffeomorph I J M N ∞)
    (hpull : ∀ p : M, ∀ v w : TangentSpace I p,
      gM.metricInner p v w = gN.metricInner (phi p)
        (mfderiv I J phi p v) (mfderiv I J phi p w))
    {s : Set M} (hs : MeasurableSet s) :
    riemannianMeasure (I := J) gN mu (phi '' s) = riemannianMeasure (I := I) gM mu s := by
/- SWARM_PROOF_BEGIN -/
  classical
  have hlocal : ∀ {α : M} {β : N} {p : M},
      p ∈ (extChartAt I α).source →
      phi p ∈ (extChartAt J β).source →
      ∃ D : E →L[ℝ] E,
        HasFDerivAt
            (fun y : E => extChartAt J β (phi ((extChartAt I α).symm y))) D
            (extChartAt I α p) ∧
        |D.det| * chartVolumeDensity (I := J) gN β
            (extChartAt J β (phi p)) =
          chartVolumeDensity (I := I) gM α (extChartAt I α p) := by
    intro α β p hpα hqβ
    let x : E := extChartAt I α p
    let F : E → E := fun y => extChartAt J β (phi ((extChartAt I α).symm y))
    let A : E →L[ℝ] TangentSpace I p :=
      mfderiv 𝓘(ℝ, E) I (extChartAt I α).symm x
    let B : E →L[ℝ] TangentSpace J (phi p) :=
      mfderiv 𝓘(ℝ, E) J (extChartAt J β).symm (extChartAt J β (phi p))
    let C : TangentSpace J (phi p) →L[ℝ] E :=
      mfderiv J 𝓘(ℝ, E) (extChartAt J β) (phi p)
    let L : TangentSpace I p →L[ℝ] TangentSpace J (phi p) :=
      mfderiv I J phi p
    let D : E →L[ℝ] E := fderiv ℝ F x
    have hx : x ∈ (extChartAt I α).target := by
      exact (extChartAt I α).map_source hpα
    have hqβ' : phi p ∈ (chartAt H' β).source := by
      rw [extChartAt_source] at hqβ
      exact hqβ
    have hy : extChartAt J β (phi p) ∈ (extChartAt J β).target := by
      exact (extChartAt J β).map_source hqβ
    have hi : MDiffAt (extChartAt I α).symm x := by
      apply mdifferentiableWithinAt_univ.mp
      rw [← I.range_eq_univ]
      exact mdifferentiableWithinAt_extChartAt_symm hx
    have hphi : MDiffAt phi p := (phi.mdifferentiable (by norm_num)) p
    have hchart : MDiffAt (extChartAt J β) (phi p) :=
      mdifferentiableAt_extChartAt hqβ'
    have hpx : (extChartAt I α).symm x = p := (extChartAt I α).left_inv hpα
    have hphi_x : MDiffAt phi ((extChartAt I α).symm x) := by
      rw [hpx]
      exact hphi
    have hchart_x : MDiffAt (extChartAt J β)
        (phi ((extChartAt I α).symm x)) := by
      rw [hpx]
      exact hchart
    have hcomp₁ : mfderiv 𝓘(ℝ, E) J (phi ∘ (extChartAt I α).symm) x =
        (mfderiv I J phi ((extChartAt I α).symm x)) ∘SL
          (mfderiv 𝓘(ℝ, E) I (extChartAt I α).symm x) := by
      exact mfderiv_comp x hphi_x hi
    have hcomp₂ : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
        ((extChartAt J β) ∘ (phi ∘ (extChartAt I α).symm)) x =
        (mfderiv J 𝓘(ℝ, E) (extChartAt J β)
          (phi ((extChartAt I α).symm x))) ∘SL
          (mfderiv 𝓘(ℝ, E) J (phi ∘ (extChartAt I α).symm) x) := by
      exact mfderiv_comp x hchart_x (hphi_x.comp x hi)
    have hF : HasFDerivAt F (C ∘L (L ∘L A)) x := by
      have hcomp := hchart_x.hasMFDerivAt.comp x
        (hphi_x.hasMFDerivAt.comp x hi.hasMFDerivAt)
      rw [hpx] at hcomp
      apply hasMFDerivAt_iff_hasFDerivAt.mp
      simpa only [F, Function.comp_def] using hcomp
    have hDval : D = C ∘L (L ∘L A) := by
      simpa [D] using hF.fderiv
    have hFD : HasFDerivAt F D x := by
      rw [hDval]
      exact hF
    have hBA : ∀ i : Fin (Module.finrank ℝ E),
        A (Module.finBasis ℝ E i) =
          Riemannian.Tensor.chartBasisVecFiber α i p := by
      intro i
      have hpα' : p ∈ (chartAt H α).source := by
        have h := hpα
        rw [extChartAt_source] at h
        exact h
      have ht := TangentBundle.symmL_trivializationAt (𝕜 := ℝ)
        (I := I) (x₀ := α) (x := p) hpα'
      rw [I.range_eq_univ, mfderivWithin_univ] at ht
      have hi' := congrArg (fun K => K (Module.finBasis ℝ E i)) ht
      have hpbase : p ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
        rw [trivializationAt_baseSet_eq_chartAt_source]
        exact hpα'
      rw [Bundle.Trivialization.symmL_apply _ hpbase] at hi'
      simpa [A, x, Riemannian.Tensor.chartBasisVecFiber,
        Bundle.Trivialization.symmL_apply] using hi'.symm
    have hBB : ∀ i : Fin (Module.finrank ℝ E),
        B (Module.finBasis ℝ E i) =
          Riemannian.Tensor.chartBasisVecFiber β i (phi p) := by
      intro i
      have ht := TangentBundle.symmL_trivializationAt (𝕜 := ℝ)
        (I := J) (x₀ := β) (x := phi p) hqβ'
      rw [J.range_eq_univ, mfderivWithin_univ] at ht
      have hi' := congrArg (fun K => K (Module.finBasis ℝ E i)) ht
      have hqbase : phi p ∈ (trivializationAt E (TangentSpace J) β).baseSet := by
        rw [trivializationAt_baseSet_eq_chartAt_source]
        exact hqβ'
      rw [Bundle.Trivialization.symmL_apply _ hqbase] at hi'
      simpa [B, Riemannian.Tensor.chartBasisVecFiber,
        Bundle.Trivialization.symmL_apply] using hi'.symm
    have hBC : B ∘L C =
        ContinuousLinearMap.id ℝ (TangentSpace J (phi p)) := by
      have hiinv := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt
        (I := J) (x := β) hy
      rw [J.range_eq_univ, mfderivWithin_univ] at hiinv
      rw [(extChartAt J β).left_inv hqβ] at hiinv
      simpa only [B, C] using hiinv
    have hBD : ∀ u : E, B (D u) = L (A u) := by
      intro u
      calc
        B (D u) = B (C (L (A u))) := by rw [hDval]; rfl
        _ = (B ∘L C) (L (A u)) := rfl
        _ = L (A u) := by rw [hBC]; rfl
    let K : E →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
      { toFun := fun u => (((gN.inner (phi p)) (B u)).comp B).toLinearMap
        map_add' := by
          intro u v
          ext w
          simp [map_add]
        map_smul' := by
          intro c u
          ext w
          simp [map_smul] }
    have hK : ∀ u v : E, K u v = gN.metricInner (phi p) (B u) (B v) := by
      intro u v
      rfl
    have hKbasis : Matrix.of (fun i j => K (Module.finBasis ℝ E i)
        (Module.finBasis ℝ E j)) =
        Riemannian.Tensor.chartGramMatrix (I := J) gN β (phi p) := by
      ext i j
      simp only [Matrix.of_apply]
      rw [hK, hBB i, hBB j, Riemannian.Tensor.chartGramMatrix_apply,
        Riemannian.RiemannianMetric.metricInner_apply]
    have hconj := bilinGram_eq_conj (Module.finBasis ℝ E)
      (fun i => D (Module.finBasis ℝ E i)) K
    have hgram : Matrix.of (fun i j => K (D (Module.finBasis ℝ E i))
        (D (Module.finBasis ℝ E j))) =
        Riemannian.Tensor.chartGramMatrix (I := I) gM α p := by
      ext i j
      simp only [Matrix.of_apply]
      rw [hK, hBD, hBD, hBA i, hBA j]
      exact (hpull p _ _).symm
    have hmatrix : Riemannian.Tensor.chartGramMatrix (I := I) gM α p =
        ((Module.finBasis ℝ E).toMatrix
          (fun i => D (Module.finBasis ℝ E i)))ᵀ *
          Riemannian.Tensor.chartGramMatrix (I := J) gN β (phi p) *
            (Module.finBasis ℝ E).toMatrix
              (fun i => D (Module.finBasis ℝ E i)) := by
      rw [← hgram, hconj, hKbasis]
    have hdet :
        (LinearMap.det (D : E →ₗ[ℝ] E)) ^ 2 *
            (Riemannian.Tensor.chartGramMatrix (I := J) gN β (phi p)).det =
          (Riemannian.Tensor.chartGramMatrix (I := I) gM α p).det := by
      have hd := congrArg Matrix.det hmatrix
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd
      have hMdet :
          ((Module.finBasis ℝ E).toMatrix
              (fun i => D (Module.finBasis ℝ E i))).det =
            LinearMap.det (D : E →ₗ[ℝ] E) := by
        rw [show (Module.finBasis ℝ E).toMatrix
              (fun i => D (Module.finBasis ℝ E i)) =
            LinearMap.toMatrix (Module.finBasis ℝ E) (Module.finBasis ℝ E)
              (D : E →ₗ[ℝ] E) by
          ext i j
          simp [Module.Basis.toMatrix_apply, LinearMap.toMatrix_apply]]
        exact LinearMap.det_toMatrix _ _
      rw [hMdet] at hd
      nlinarith [hd]
    have hposN : 0 ≤
        (Riemannian.Tensor.chartGramMatrix (I := J) gN β (phi p)).det :=
      (Riemannian.Tensor.chartGramMatrix_det_pos (I := J) gN β
        (by rw [trivializationAt_baseSet_eq_chartAt_source]; exact hqβ')).le
    have hsqrt :
        |LinearMap.det (D : E →ₗ[ℝ] E)| *
            Real.sqrt (Riemannian.Tensor.chartGramMatrix (I := J) gN β (phi p)).det =
          Real.sqrt (Riemannian.Tensor.chartGramMatrix (I := I) gM α p).det := by
      calc
        |LinearMap.det (D : E →ₗ[ℝ] E)| *
            Real.sqrt (Riemannian.Tensor.chartGramMatrix (I := J) gN β (phi p)).det =
            Real.sqrt ((LinearMap.det (D : E →ₗ[ℝ] E)) ^ 2) *
              Real.sqrt (Riemannian.Tensor.chartGramMatrix (I := J) gN β (phi p)).det := by
                rw [Real.sqrt_sq_eq_abs]
        _ = Real.sqrt ((LinearMap.det (D : E →ₗ[ℝ] E)) ^ 2 *
              (Riemannian.Tensor.chartGramMatrix (I := J) gN β (phi p)).det) := by
                rw [Real.sqrt_mul (sq_nonneg _)]
        _ = Real.sqrt (Riemannian.Tensor.chartGramMatrix (I := I) gM α p).det := by
          rw [hdet]
    have hdenN : chartVolumeDensity (I := J) gN β
        (extChartAt J β (phi p)) =
        Real.sqrt (Riemannian.Tensor.chartGramMatrix (I := J) gN β (phi p)).det := by
      rw [chartVolumeDensity, (extChartAt J β).left_inv hqβ]
    have hdenM : chartVolumeDensity (I := I) gM α
        (extChartAt I α p) =
        Real.sqrt (Riemannian.Tensor.chartGramMatrix (I := I) gM α p).det := by
      rw [chartVolumeDensity, (extChartAt I α).left_inv hpα]
    have hdensity : |D.det| * chartVolumeDensity (I := J) gN β
        (extChartAt J β (phi p)) =
      chartVolumeDensity (I := I) gM α (extChartAt I α p) := by
      rw [hdenN, hdenM]
      simpa [D, ContinuousLinearMap.det] using hsqrt
    exact ⟨D, by simpa [F, x] using hFD, hdensity⟩
  let PM : ℕ → Set M := fun i => chartPiece (I := I) (M := M) i
  let QN : ℕ → Set N := fun j => chartPiece (I := J) (M := N) j
  let α : ℕ → M := fun i => chartCover (I := I) (M := M) i
  let β : ℕ → N := fun j => chartCover (I := J) (M := N) j
  let A : ℕ → Set M := fun i => s ∩ PM i
  let B : ℕ → ℕ → Set M := fun i j => A i ∩ phi ⁻¹' QN j
  let U : ℕ → ℕ → Set E := fun i j =>
    chartPreimage (I := I) (α i) (B i j)
  let S : ℕ → ℕ → Set N := fun i j => phi '' B i j
  have hphi_meas : Measurable (phi : M → N) := by
    exact (phi.toHomeomorph.toMeasurableEquiv).measurable
  have hAmeas : ∀ i, MeasurableSet (A i) := by
    intro i
    exact hs.inter (by
      simpa [PM] using measurableSet_chartPiece (I := I) (M := M) i)
  have hBmeas : ∀ i j, MeasurableSet (B i j) := by
    intro i j
    have hQ : MeasurableSet (QN j) := by
      simpa [QN] using measurableSet_chartPiece (I := J) (M := N) j
    exact (hAmeas i).inter (hQ.preimage hphi_meas)
  have hUmeas : ∀ i j, MeasurableSet (U i j) := by
    intro i j
    exact measurableSet_chartPreimage (I := I) (M := M) (α i) (hBmeas i j)
  have hSmeas : ∀ i j, MeasurableSet (S i j) := by
    intro i j
    change MeasurableSet ((phi : M → N) '' B i j)
    exact (phi.toHomeomorph.toMeasurableEquiv).measurableSet_image.mpr (hBmeas i j)
  have hBsubα : ∀ i j, B i j ⊆ (extChartAt I (α i)).source := by
    intro i j p hp
    exact (by
      have hpA : p ∈ A i := hp.1
      have hpP : p ∈ PM i := hpA.2
      simpa [PM, α] using chartPiece_subset (I := I) (M := M) i hpP)
  have hSsubβ : ∀ i j, S i j ⊆ (extChartAt J (β j)).source := by
    intro i j q hq
    obtain ⟨p, hp, rfl⟩ := hq
    have hpQ : phi p ∈ QN j := hp.2
    simpa [QN, β] using chartPiece_subset (I := J) (M := N) j hpQ
  have hUsubtarget : ∀ i j, U i j ⊆ (extChartAt I (α i)).target := by
    intro i j
    exact chartPreimage_subset_target (I := I) (α i) (B i j)
  have hpiece : ∀ i j,
      riemannianMeasure (I := J) gN mu (S i j) =
        ∫⁻ v in U i j, ENNReal.ofReal
          (chartVolumeDensity (I := I) gM (α i) v) ∂mu := by
    intro i j
    let f : E → N := fun v => phi ((extChartAt I (α i)).symm v)
    let F : E → E := fun v => extChartAt J (β j) (f v)
    let D : E → E →L[ℝ] E := fun v => fderiv ℝ F v
    have hcover : chartPreimage (I := J) (β j) (S i j) =
        (fun v => extChartAt J (β j) (f v)) '' U i j := by
      ext y
      simp only [chartPreimage, mem_inter_iff, mem_preimage, mem_image]
      constructor
      · rintro ⟨⟨p, hp, hpy⟩, hyt⟩
        have hpα : p ∈ (extChartAt I (α i)).source := hBsubα i j hp
        have hpβ : phi p ∈ (extChartAt J (β j)).source := hSsubβ i j ⟨p, hp, rfl⟩
        have hv : extChartAt I (α i) p ∈ (extChartAt I (α i)).target :=
          (extChartAt I (α i)).map_source hpα
        have hcoord : (extChartAt I (α i)).symm
            (extChartAt I (α i) p) = p :=
          (extChartAt I (α i)).left_inv hpα
        have hy : extChartAt J (β j) (phi p) = y := by
          rw [hpy, (extChartAt J (β j)).right_inv hyt]
        refine ⟨extChartAt I (α i) p, ?_, ?_⟩
        · have hp' : (extChartAt I (α i)).symm
              (extChartAt I (α i) p) ∈ B i j := by
            rw [hcoord]
            exact hp
          exact ⟨hp', hv⟩
        · simp only [f, hcoord, hy]
      · rintro ⟨v, ⟨hp, hvt⟩, rfl⟩
        have hpα : (extChartAt I (α i)).symm v ∈
            (extChartAt I (α i)).source :=
          (extChartAt I (α i)).map_target hvt
        have hpβ : phi ((extChartAt I (α i)).symm v) ∈
            (extChartAt J (β j)).source :=
          hSsubβ i j ⟨(extChartAt I (α i)).symm v, hp, rfl⟩
        refine ⟨?_, (extChartAt J (β j)).map_source hpβ⟩
        refine ⟨(extChartAt I (α i)).symm v, hp, ?_⟩
        simpa only [f] using ((extChartAt J (β j)).left_inv hpβ).symm
    have hinj : InjOn (fun v => extChartAt J (β j) (f v)) (U i j) := by
      intro v hv w hw heq
      have hpv : (extChartAt I (α i)).symm v ∈ B i j := hv.1
      have hpw : (extChartAt I (α i)).symm w ∈ B i j := hw.1
      have hpvβ : phi ((extChartAt I (α i)).symm v) ∈
          (extChartAt J (β j)).source := hSsubβ i j ⟨_, hpv, rfl⟩
      have hpwβ : phi ((extChartAt I (α i)).symm w) ∈
          (extChartAt J (β j)).source := hSsubβ i j ⟨_, hpw, rfl⟩
      have hphi_eq : phi ((extChartAt I (α i)).symm v) =
          phi ((extChartAt I (α i)).symm w) :=
        (extChartAt J (β j)).injOn hpvβ hpwβ heq
      have hp_eq : (extChartAt I (α i)).symm v =
          (extChartAt I (α i)).symm w := phi.toHomeomorph.injective hphi_eq
      rw [← (extChartAt I (α i)).right_inv hv.2,
        ← (extChartAt I (α i)).right_inv hw.2, hp_eq]
    have hderiv : ∀ v ∈ U i j,
        HasFDerivWithinAt (fun w => extChartAt J (β j) (f w)) (D v) (U i j) v := by
      intro v hv
      let p := (extChartAt I (α i)).symm v
      have hp : p ∈ B i j := hv.1
      have hpα : p ∈ (extChartAt I (α i)).source := hBsubα i j hp
      have hpβ : phi p ∈ (extChartAt J (β j)).source := hSsubβ i j ⟨p, hp, rfl⟩
      obtain ⟨Dv, hDv, _⟩ := hlocal hpα hpβ
      have hpoint : extChartAt I (α i) p = v :=
        (extChartAt I (α i)).right_inv hv.2
      rw [hpoint] at hDv
      have hDv' : HasFDerivAt (fun w => extChartAt J (β j) (f w)) Dv v := by
        simpa [f, F, p] using hDv
      have hD_eq : D v = Dv := by
        change fderiv ℝ F v = Dv
        simpa [F, f] using hDv'.fderiv
      rw [hD_eq]
      exact hDv'.hasFDerivWithinAt
    rw [riemannianMeasure_eq_lintegral_jacobian mu gN (β j)
      (hUmeas i j) (hSmeas i j) (hSsubβ i j) hcover hinj hderiv]
    refine setLIntegral_congr_fun (hUmeas i j) ?_
    intro v hv
    let p := (extChartAt I (α i)).symm v
    have hp : p ∈ B i j := hv.1
    have hpα : p ∈ (extChartAt I (α i)).source := hBsubα i j hp
    have hpβ : phi p ∈ (extChartAt J (β j)).source := hSsubβ i j ⟨p, hp, rfl⟩
    obtain ⟨D0, hD0, hden⟩ := hlocal hpα hpβ
    have hpoint : extChartAt I (α i) p = v :=
      (extChartAt I (α i)).right_inv hv.2
    have hD_eq : D v = D0 := by
      change fderiv ℝ F v = D0
      rw [← hpoint]
      simpa [F, f] using hD0.fderiv
    have hfval : f v = phi p := by
      simp [f, p, hpoint]
    change ENNReal.ofReal (|(D v).det| *
      chartVolumeDensity (I := J) gN (β j) (extChartAt J (β j) (f v))) =
      ENNReal.ofReal (chartVolumeDensity (I := I) gM (α i) v)
    rw [hD_eq, hfval, hden, hpoint]
  have hBunion : ∀ i, (⋃ j, B i j) = A i := by
    intro i
    simp only [B]
    rw [← inter_iUnion, ← preimage_iUnion, show (⋃ j, QN j) = (univ : Set N) by
      simpa [QN] using iUnion_chartPiece (I := J) (M := N), preimage_univ,
      inter_univ]
  have hAunion : (⋃ i, A i) = s := by
    simp only [A]
    rw [← inter_iUnion, show (⋃ i, PM i) = (univ : Set M) by
      simpa [PM] using iUnion_chartPiece (I := I) (M := M), inter_univ]
  have hBdisj : ∀ i, Pairwise (Disjoint on fun j => B i j) := by
    intro i j k hjk
    have hq := pairwise_disjoint_chartPiece (I := J) (M := N) hjk
    have hq' : Disjoint (QN j) (QN k) := by simpa [QN] using hq
    exact (hq'.preimage phi).mono
      (fun p hp => hp.2) (fun p hp => hp.2)
  have hAdisj : Pairwise (Disjoint on A) := by
    intro i k hik
    have hp := pairwise_disjoint_chartPiece (I := I) (M := M) hik
    have hp' : Disjoint (PM i) (PM k) := by simpa [PM] using hp
    exact hp'.mono (fun p hp => hp.2) (fun p hp => hp.2)
  have hUunion : ∀ i, (⋃ j, U i j) =
      chartPreimage (I := I) (α i) (A i) := by
    intro i
    simp only [U, chartPreimage]
    rw [← iUnion_inter, ← preimage_iUnion, hBunion i]
  have hUdisj : ∀ i, Pairwise (Disjoint on fun j => U i j) := by
    intro i j k hjk
    have hb := hBdisj i hjk
    exact (hb.preimage (extChartAt I (α i)).symm).mono
      (fun v hv => hv.1) (fun v hv => hv.1)
  have hSunion : ∀ i, (⋃ j, S i j) = phi '' A i := by
    intro i
    simp only [S]
    rw [← image_iUnion, hBunion i]
  have hTmeas : ∀ i, MeasurableSet (⋃ j, S i j) := by
    intro i
    exact MeasurableSet.iUnion (hSmeas i)
  have hTdisj : Pairwise (Disjoint on fun i => ⋃ j, S i j) := by
    intro i k hik
    change Disjoint (⋃ j, S i j) (⋃ j, S k j)
    rw [hSunion i, hSunion k]
    exact (hAdisj hik).image (u := (univ : Set M))
      (fun _ _ _ _ h => phi.toHomeomorph.injective h)
      (fun _ _ => mem_univ _) (fun _ _ => mem_univ _)
  have hSdisj : ∀ i, Pairwise (Disjoint on fun j => S i j) := by
    intro i j k hjk
    exact (hBdisj i hjk).image
      (fun _ _ _ _ h => phi.toHomeomorph.injective h)
      (fun _ hp => hp.1) (fun _ hp => hp.1)
  have hStotal : (⋃ i, ⋃ j, S i j) = phi '' s := by
    rw [show (⋃ i, ⋃ j, S i j) = ⋃ i, phi '' A i by
      apply iUnion_congr
      exact hSunion, ← image_iUnion, hAunion]
  have hsource : ∀ i,
      riemannianMeasure (I := I) gM mu (A i) =
        ∫⁻ v in chartPreimage (I := I) (α i) (A i),
          ENNReal.ofReal (chartVolumeDensity (I := I) gM (α i) v) ∂mu := by
    intro i
    apply riemannianMeasure_apply_chart mu gM (α i) (hAmeas i)
    intro p hp
    have hpP : p ∈ PM i := hp.2
    simpa [PM, α] using chartPiece_subset (I := I) (M := M) i hpP
  calc
    riemannianMeasure (I := J) gN mu (phi '' s) =
        riemannianMeasure (I := J) gN mu (⋃ i, ⋃ j, S i j) := by rw [hStotal]
    _ = ∑' i, riemannianMeasure (I := J) gN mu (⋃ j, S i j) :=
      measure_iUnion hTdisj hTmeas
    _ = ∑' i, ∑' j, riemannianMeasure (I := J) gN mu (S i j) :=
      tsum_congr (fun i => measure_iUnion (hSdisj i) (hSmeas i))
    _ = ∑' i, ∑' j, ∫⁻ v in U i j,
          ENNReal.ofReal (chartVolumeDensity (I := I) gM (α i) v) ∂mu :=
      tsum_congr (fun i => tsum_congr (fun j => hpiece i j))
    _ = ∑' i, ∫⁻ v in chartPreimage (I := I) (α i) (A i),
          ENNReal.ofReal (chartVolumeDensity (I := I) gM (α i) v) ∂mu :=
      tsum_congr (fun i => (lintegral_iUnion (fun j => hUmeas i j)
        (hUdisj i) _).symm.trans (by rw [hUunion i]))
    _ = ∑' i, riemannianMeasure (I := I) gM mu (A i) :=
      tsum_congr (fun i => (hsource i).symm)
    _ = riemannianMeasure (I := I) gM mu s := by
      rw [← hAunion]
      exact (measure_iUnion hAdisj hAmeas).symm
/- SWARM_PROOF_END -/

end MorganTianLib
