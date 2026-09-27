import PoincareConjecture.ProofContract.Refinement20260927.MetricPatchTransport
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.RefinedOpenPatchAssembly
open PoincareConjecture.ProofContract.Refinement20260927
theorem open_patch_assembly : OpenPatchAssemblyStatement.{u} :=
/- SWARM_PROOF_BEGIN -/
open PoincareConjecture.ProofContract.V1 MorganTianLib Set MeasureTheory Function in
open scoped Manifold ContDiff Topology ENNReal BigOperators in
by
  classical
  letI : NeZero (Module.finrank ℝ Euclidean3) := ⟨by simp [Euclidean3]⟩
  let μ : Measure Euclidean3 := volume
  let I : ModelWithCorners ℝ Euclidean3 Euclidean3 := modelWithCornersSelf ℝ Euclidean3
  let J : ModelWithCorners ℝ Euclidean3 Euclidean3 := modelWithCornersSelf ℝ Euclidean3
  intro M N gM gN f he hcert s hs
  have hlocal : ∀ {α : M} {β : N} {p : M},
      p ∈ (extChartAt I α).source →
      f p ∈ (extChartAt J β).source →
      ∃ D : Euclidean3 →L[ℝ] Euclidean3,
        HasFDerivAt
            (fun y : Euclidean3 => extChartAt J β (f ((extChartAt I α).symm y))) D
            (extChartAt I α p) ∧
        |D.det| * chartVolumeDensity (I := J) gN β
            (extChartAt J β (f p)) =
          chartVolumeDensity (I := I) gM α (extChartAt I α p) := by
    intro α β p hpα hqβ
    exact hcert α β p hpα hqβ
  let PM : ℕ → Set M := fun i => chartPiece (I := I) (M := M) i
  let QN : ℕ → Set N := fun j => chartPiece (I := J) (M := N) j
  let α : ℕ → M := fun i => chartCover (I := I) (M := M) i
  let β : ℕ → N := fun j => chartCover (I := J) (M := N) j
  let A : ℕ → Set M := fun i => s ∩ PM i
  let B : ℕ → ℕ → Set M := fun i j => A i ∩ f ⁻¹' QN j
  let U : ℕ → ℕ → Set Euclidean3 := fun i j =>
    chartPreimage (I := I) (α i) (B i j)
  let S : ℕ → ℕ → Set N := fun i j => f '' B i j
  have hf_meas : Measurable (f : M → N) := by
    exact he.continuous.measurable
  have hAmeas : ∀ i, MeasurableSet (A i) := by
    intro i
    exact hs.inter (by
      simpa [PM] using measurableSet_chartPiece (I := I) (M := M) i)
  have hBmeas : ∀ i j, MeasurableSet (B i j) := by
    intro i j
    have hQ : MeasurableSet (QN j) := by
      simpa [QN] using measurableSet_chartPiece (I := J) (M := N) j
    exact (hAmeas i).inter (hQ.preimage hf_meas)
  have hUmeas : ∀ i j, MeasurableSet (U i j) := by
    intro i j
    exact measurableSet_chartPreimage (I := I) (M := M) (α i) (hBmeas i j)
  have hSmeas : ∀ i j, MeasurableSet (S i j) := by
    intro i j
    change MeasurableSet ((f : M → N) '' B i j)
    exact he.measurableEmbedding.measurableSet_image.mpr (hBmeas i j)
  have hBsubα : ∀ i j, B i j ⊆ (extChartAt I (α i)).source := by
    intro i j p hp
    exact (by
      have hpA : p ∈ A i := hp.1
      have hpP : p ∈ PM i := hpA.2
      simpa [PM, α] using chartPiece_subset (I := I) (M := M) i hpP)
  have hSsubβ : ∀ i j, S i j ⊆ (extChartAt J (β j)).source := by
    intro i j q hq
    obtain ⟨p, hp, rfl⟩ := hq
    have hpQ : f p ∈ QN j := hp.2
    simpa [QN, β] using chartPiece_subset (I := J) (M := N) j hpQ
  have hUsubtarget : ∀ i j, U i j ⊆ (extChartAt I (α i)).target := by
    intro i j
    exact chartPreimage_subset_target (I := I) (α i) (B i j)
  have hpiece : ∀ i j,
      riemannianMeasure (I := J) gN μ (S i j) =
        ∫⁻ v in U i j, ENNReal.ofReal
          (chartVolumeDensity (I := I) gM (α i) v) ∂μ := by
    intro i j
    let fcoord : Euclidean3 → N := fun v => f ((extChartAt I (α i)).symm v)
    let F : Euclidean3 → Euclidean3 := fun v => extChartAt J (β j) (fcoord v)
    let D : Euclidean3 → Euclidean3 →L[ℝ] Euclidean3 := fun v => fderiv ℝ F v
    have hcover : chartPreimage (I := J) (β j) (S i j) =
        (fun v => extChartAt J (β j) (fcoord v)) '' U i j := by
      ext y
      simp only [chartPreimage, mem_inter_iff, mem_preimage, mem_image]
      constructor
      · rintro ⟨⟨p, hp, hpy⟩, hyt⟩
        have hpα : p ∈ (extChartAt I (α i)).source := hBsubα i j hp
        have hpβ : f p ∈ (extChartAt J (β j)).source := hSsubβ i j ⟨p, hp, rfl⟩
        have hv : extChartAt I (α i) p ∈ (extChartAt I (α i)).target :=
          (extChartAt I (α i)).map_source hpα
        have hcoord : (extChartAt I (α i)).symm
            (extChartAt I (α i) p) = p :=
          (extChartAt I (α i)).left_inv hpα
        have hy : extChartAt J (β j) (f p) = y := by
          rw [hpy, (extChartAt J (β j)).right_inv hyt]
        refine ⟨extChartAt I (α i) p, ?_, ?_⟩
        · have hp' : (extChartAt I (α i)).symm
              (extChartAt I (α i) p) ∈ B i j := by
            rw [hcoord]
            exact hp
          exact ⟨hp', hv⟩
        · simp only [fcoord, hcoord, hy]
      · rintro ⟨v, ⟨hp, hvt⟩, rfl⟩
        have hpα : (extChartAt I (α i)).symm v ∈
            (extChartAt I (α i)).source :=
          (extChartAt I (α i)).map_target hvt
        have hpβ : f ((extChartAt I (α i)).symm v) ∈
            (extChartAt J (β j)).source :=
          hSsubβ i j ⟨(extChartAt I (α i)).symm v, hp, rfl⟩
        refine ⟨?_, (extChartAt J (β j)).map_source hpβ⟩
        refine ⟨(extChartAt I (α i)).symm v, hp, ?_⟩
        simpa only [fcoord] using ((extChartAt J (β j)).left_inv hpβ).symm
    have hinj : InjOn (fun v => extChartAt J (β j) (fcoord v)) (U i j) := by
      intro v hv w hw heq
      have hpv : (extChartAt I (α i)).symm v ∈ B i j := hv.1
      have hpw : (extChartAt I (α i)).symm w ∈ B i j := hw.1
      have hpvβ : f ((extChartAt I (α i)).symm v) ∈
          (extChartAt J (β j)).source := hSsubβ i j ⟨_, hpv, rfl⟩
      have hpwβ : f ((extChartAt I (α i)).symm w) ∈
          (extChartAt J (β j)).source := hSsubβ i j ⟨_, hpw, rfl⟩
      have hf_eq : f ((extChartAt I (α i)).symm v) =
          f ((extChartAt I (α i)).symm w) :=
        (extChartAt J (β j)).injOn hpvβ hpwβ heq
      have hp_eq : (extChartAt I (α i)).symm v =
          (extChartAt I (α i)).symm w := he.injective hf_eq
      rw [← (extChartAt I (α i)).right_inv hv.2,
        ← (extChartAt I (α i)).right_inv hw.2, hp_eq]
    have hderiv : ∀ v ∈ U i j,
        HasFDerivWithinAt (fun w => extChartAt J (β j) (fcoord w)) (D v) (U i j) v := by
      intro v hv
      let p := (extChartAt I (α i)).symm v
      have hp : p ∈ B i j := hv.1
      have hpα : p ∈ (extChartAt I (α i)).source := hBsubα i j hp
      have hpβ : f p ∈ (extChartAt J (β j)).source := hSsubβ i j ⟨p, hp, rfl⟩
      obtain ⟨Dv, hDv, _⟩ := hlocal hpα hpβ
      have hpoint : extChartAt I (α i) p = v :=
        (extChartAt I (α i)).right_inv hv.2
      rw [hpoint] at hDv
      have hDv' : HasFDerivAt (fun w => extChartAt J (β j) (fcoord w)) Dv v := by
        simpa [fcoord, F, p] using hDv
      have hD_eq : D v = Dv := by
        change fderiv ℝ F v = Dv
        simpa [F, fcoord] using hDv'.fderiv
      rw [hD_eq]
      exact hDv'.hasFDerivWithinAt
    rw [riemannianMeasure_eq_lintegral_jacobian μ gN (β j)
      (hUmeas i j) (hSmeas i j) (hSsubβ i j) hcover hinj hderiv]
    refine setLIntegral_congr_fun (hUmeas i j) ?_
    intro v hv
    let p := (extChartAt I (α i)).symm v
    have hp : p ∈ B i j := hv.1
    have hpα : p ∈ (extChartAt I (α i)).source := hBsubα i j hp
    have hpβ : f p ∈ (extChartAt J (β j)).source := hSsubβ i j ⟨p, hp, rfl⟩
    obtain ⟨D0, hD0, hden⟩ := hlocal hpα hpβ
    have hpoint : extChartAt I (α i) p = v :=
      (extChartAt I (α i)).right_inv hv.2
    have hD_eq : D v = D0 := by
      change fderiv ℝ F v = D0
      rw [← hpoint]
      simpa [F, fcoord] using hD0.fderiv
    have hfval : fcoord v = f p := by
      simp [fcoord, p]
    change ENNReal.ofReal (|(D v).det| *
      chartVolumeDensity (I := J) gN (β j) (extChartAt J (β j) (fcoord v))) =
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
  have hBdisj : ∀ i j k, j ≠ k → Disjoint (B i j) (B i k) := by
    intro i j k hjk
    have hq := pairwise_disjoint_chartPiece (I := J) (M := N) hjk
    have hq' : Disjoint (QN j) (QN k) := by simpa [QN] using hq
    exact (hq'.preimage f).mono
      (fun p hp => hp.2) (fun p hp => hp.2)
  have hAdisj : ∀ i k, i ≠ k → Disjoint (A i) (A k) := by
    intro i k hik
    have hp := pairwise_disjoint_chartPiece (I := I) (M := M) hik
    have hp' : Disjoint (PM i) (PM k) := by simpa [PM] using hp
    exact hp'.mono (fun p hp => hp.2) (fun p hp => hp.2)
  have hUunion : ∀ i, (⋃ j, U i j) =
      chartPreimage (I := I) (α i) (A i) := by
    intro i
    simp only [U, chartPreimage]
    rw [← iUnion_inter, ← preimage_iUnion, hBunion i]
  have hUdisj : ∀ i j k, j ≠ k → Disjoint (U i j) (U i k) := by
    intro i j k hjk
    have hb := hBdisj i j k hjk
    exact (hb.preimage (extChartAt I (α i)).symm).mono
      (fun v hv => hv.1) (fun v hv => hv.1)
  have hSunion : ∀ i, (⋃ j, S i j) = f '' A i := by
    intro i
    simp only [S]
    rw [← image_iUnion, hBunion i]
  have hTmeas : ∀ i, MeasurableSet (⋃ j, S i j) := by
    intro i
    exact MeasurableSet.iUnion (hSmeas i)
  have hTdisj : ∀ i k, i ≠ k → Disjoint (⋃ j, S i j) (⋃ j, S k j) := by
    intro i k hik
    rw [hSunion i, hSunion k]
    exact (hAdisj i k hik).image (u := (univ : Set M))
      (fun _ _ _ _ h => he.injective h)
      (fun _ _ => mem_univ _) (fun _ _ => mem_univ _)
  have hSdisj : ∀ i j k, j ≠ k → Disjoint (S i j) (S i k) := by
    intro i j k hjk
    exact (hBdisj i j k hjk).image
      (fun _ _ _ _ h => he.injective h)
      (fun _ hp => hp.1) (fun _ hp => hp.1)
  have hStotal : (⋃ i, ⋃ j, S i j) = f '' s := by
    rw [show (⋃ i, ⋃ j, S i j) = ⋃ i, f '' A i by
      apply iUnion_congr
      exact hSunion, ← image_iUnion, hAunion]
  have hsource : ∀ i,
      riemannianMeasure (I := I) gM μ (A i) =
        ∫⁻ v in chartPreimage (I := I) (α i) (A i),
          ENNReal.ofReal (chartVolumeDensity (I := I) gM (α i) v) ∂μ := by
    intro i
    apply riemannianMeasure_apply_chart μ gM (α i) (hAmeas i)
    intro p hp
    have hpP : p ∈ PM i := hp.2
    simpa [PM, α] using chartPiece_subset (I := I) (M := M) i hpP
  calc
    riemannianMeasure (I := J) gN μ (f '' s) =
        riemannianMeasure (I := J) gN μ (⋃ i, ⋃ j, S i j) := by rw [hStotal]
    _ = ∑' i, riemannianMeasure (I := J) gN μ (⋃ j, S i j) :=
      measure_iUnion (fun i k hik => hTdisj i k hik) hTmeas
    _ = ∑' i, ∑' j, riemannianMeasure (I := J) gN μ (S i j) :=
      tsum_congr (fun i => measure_iUnion (fun j k hjk => hSdisj i j k hjk) (hSmeas i))
    _ = ∑' i, ∑' j, ∫⁻ v in U i j,
          ENNReal.ofReal (chartVolumeDensity (I := I) gM (α i) v) ∂μ :=
      tsum_congr (fun i => tsum_congr (fun j => hpiece i j))
    _ = ∑' i, ∫⁻ v in chartPreimage (I := I) (α i) (A i),
          ENNReal.ofReal (chartVolumeDensity (I := I) gM (α i) v) ∂μ :=
      tsum_congr (fun i => (lintegral_iUnion (fun j => hUmeas i j)
        (fun j k hjk => hUdisj i j k hjk) _).symm.trans (by rw [hUunion i]))
    _ = ∑' i, riemannianMeasure (I := I) gM μ (A i) :=
      tsum_congr (fun i => (hsource i).symm)
    _ = riemannianMeasure (I := I) gM μ s := by
      rw [← hAunion]
      exact (measure_iUnion hAdisj hAmeas).symm
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RefinedOpenPatchAssembly
