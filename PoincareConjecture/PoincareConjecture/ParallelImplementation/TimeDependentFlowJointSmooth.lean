import MorganTianLib.Ch03.RicciFlow.TimeDependentGaugeFlow
import DoCarmoLib.Riemannian.Geodesic.GenericFlowJoint
import DoCarmoLib.Riemannian.Geodesic.BumpExtension
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.TimeDependentFlowJointSmooth
open MorganTianLib Riemannian Set
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
theorem exists_short_joint_smooth_spatialFlow
    [CompactSpace M]
    {V : SmoothTimeDependentVectorField (I := I) (M := M)}
    {t₀ : ℝ} (B : TimeDependentFlowBox (I := I) (M := M) V t₀) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ B.eta ∧
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞
        (fun q : M × ℝ => B.spatialFlow q.1 q.2)
        ((Set.univ : Set M) ×ˢ Set.Ioo (-ε) ε) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  by_cases hM : Nonempty M
  · let J : ModelWithCorners ℝ (E × ℝ) (ModelProd H ℝ) := I.prod 𝓘(ℝ, ℝ)
    let N := M × ℝ
    have hlocal : ∀ p : M, ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
        ∃ d : ℝ, 0 < d ∧ d ≤ B.eta ∧
          ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞
            (fun q : M × ℝ => B.spatialFlow q.1 q.2)
            (U ×ˢ Set.Ioo (-d) d) := by
      intro p
      let x₀ : N := (p, t₀)
      let φ := extChartAt J x₀
      let z₀ : E × ℝ := φ x₀
      let X : Riemannian.SmoothVectorField J N := V.suspension
      let τ := trivializationAt (E × ℝ) (TangentSpace J) x₀
      let c : N → E × ℝ := fun q => (τ ⟨q, X q⟩).2
      let f : (E × ℝ) → (E × ℝ) := fun y => c (φ.symm y)
      have hc : ContMDiffOn J 𝓘(ℝ, E × ℝ) ∞ c τ.baseSet := by
        exact (Bundle.Trivialization.contMDiffOn_section_baseSet_iff τ).mp
          X.smooth.contMDiffOn
      have hsymm : ContMDiffOn 𝓘(ℝ, E × ℝ) J ∞ φ.symm φ.target :=
        contMDiffOn_extChartAt_symm x₀
      have hmaps : MapsTo φ.symm φ.target τ.baseSet := by
        intro y hy
        have hmap : φ.symm y ∈ φ.source := φ.map_target hy
        change φ.symm y ∈ τ.baseSet
        rw [trivializationAt_baseSet_eq_chartAt_source]
        rw [extChartAt_source (I := J) x₀] at hmap
        exact hmap
      have hf : ContDiffOn ℝ ∞ f φ.target := by
        have h := hc.comp hsymm hmaps
        exact contMDiffOn_iff_contDiffOn.mp h
      have hcoord : ∀ q : N, q ∈ τ.baseSet →
          c q = tangentCoordChange J q x₀ q (X q) := by
        intro q hq
        have hq' : q ∈ (chartAt (ModelProd H ℝ) x₀).source := by
          rwa [trivializationAt_baseSet_eq_chartAt_source] at hq
        have hτsymm : τ.symm q (tangentCoordChange J q x₀ q (X q)) =
            tangentCoordChange J x₀ q q (tangentCoordChange J q x₀ q (X q)) := by
          calc
            τ.symm q (tangentCoordChange J q x₀ q (X q)) =
                τ.symmL ℝ q (tangentCoordChange J q x₀ q (X q)) :=
              (Bundle.Trivialization.symmL_apply (R := ℝ) τ hq'
                (tangentCoordChange J q x₀ q (X q))).symm
            _ = tangentCoordChange J x₀ q q (tangentCoordChange J q x₀ q (X q)) :=
              congrArg (fun A : (E × ℝ) →L[ℝ] (E × ℝ) =>
                A (tangentCoordChange J q x₀ q (X q)))
                (TangentBundle.symmL_trivializationAt_eq_core
                  (I := J) (b₀ := x₀) (b := q) hq')
        have hcomp : tangentCoordChange J x₀ q q
            (tangentCoordChange J q x₀ q (X q)) = X q := by
          have hqext : q ∈ (extChartAt J x₀).source := by
            rw [extChartAt_source (I := J) x₀]
            exact hq'
          have hqself : q ∈ (extChartAt J q).source :=
            mem_extChartAt_source (I := J) q
          have htriple : q ∈ (extChartAt J q).source ∩
              (extChartAt J x₀).source ∩ (extChartAt J q).source :=
            ⟨⟨hqself, hqext⟩, hqself⟩
          rw [tangentCoordChange_comp (I := J) (w := q) (x := x₀)
            (y := q) (z := q) (h := htriple)]
          exact tangentCoordChange_self (I := J) (mem_extChartAt_source (I := J) q)
        have hv : X q = τ.symm q (tangentCoordChange J q x₀ q (X q)) :=
          hτsymm.trans hcomp |>.symm
        have happ := τ.apply_mk_symm hq
          (tangentCoordChange J q x₀ q (X q))
        dsimp [c]
        change (τ ⟨q, X q⟩).2 = tangentCoordChange J q x₀ q (X q)
        have hp : τ ⟨q, X q⟩ = (q, tangentCoordChange J q x₀ q (X q)) := by
          calc
            τ ⟨q, X q⟩ =
                τ ⟨q, τ.symm q (tangentCoordChange J q x₀ q (X q))⟩ :=
              congrArg (fun v => τ ⟨q, v⟩) hv
            _ = (q, tangentCoordChange J q x₀ q (X q)) := happ
        exact congrArg Prod.snd hp
      obtain ⟨fext, a, ha, haφ, hfext, hext⟩ :=
        Riemannian.exists_contDiff_eqOn_closedBall_of_contDiffOn
          (isOpen_extChartAt_target (I := J) x₀) hf (mem_extChartAt_target x₀)
      obtain ⟨r, δ, Ψ, hr, hδ, hflow, hΨ⟩ :=
        Riemannian.GenericFlow.exists_local_flow_joint_contDiff fext hfext z₀
      have hdf : Continuous (fderiv ℝ fext) := hfext.continuous_fderiv (by simp)
      obtain ⟨C, hC⟩ :=
        (isCompact_closedBall z₀ a).exists_bound_of_continuousOn hdf.continuousOn
      have hC0 : 0 ≤ C := le_trans
        (norm_nonneg (fderiv ℝ fext z₀)) (hC z₀ (Metric.mem_closedBall_self ha.le))
      let K : NNReal := ⟨C, hC0⟩
      have hLip : LipschitzOnWith K fext (Metric.closedBall z₀ a) := by
        apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
        · intro y hy
          exact (hfext.differentiable (by simp)).differentiableAt
        · intro y hy
          exact_mod_cast hC y hy
        · exact convex_closedBall _ _
      let qmap : M → N := fun q => (q, t₀)
      let start : M → E × ℝ := fun q => φ (qmap q)
      have hφAt : ContinuousAt φ x₀ :=
        (contMDiffAt_extChartAt (I := J) (n := ∞) (x := x₀)).continuousAt
      have hqmap : ContinuousAt qmap p :=
        (continuous_id.prodMk continuous_const).continuousAt
      have hstartAt : ContinuousAt start p := by
        exact ContinuousAt.comp (g := φ) (f := qmap) (x := p) hφAt hqmap
      have hstart0 : start p = z₀ := rfl
      let Ψeval : (E × ℝ) × ℝ → E × ℝ := fun y => Ψ y.1 y.2
      have hΨopen : IsOpen (Metric.ball z₀ r ×ˢ Ioo (-δ) δ) :=
        Metric.isOpen_ball.prod isOpen_Ioo
      have hΨmem : (z₀, (0 : ℝ)) ∈ Metric.ball z₀ r ×ˢ Ioo (-δ) δ := by
        exact ⟨Metric.mem_ball_self hr, ⟨neg_lt_zero.mpr hδ, hδ⟩⟩
      have hΨAt : ContinuousAt Ψeval (z₀, 0) :=
        hΨ.continuousOn.continuousAt (hΨopen.mem_nhds hΨmem)
      have hΨ0 : Ψeval (z₀, 0) = z₀ := (hflow z₀ (Metric.mem_ball_self hr)).1
      have hΨnear : Ψeval ⁻¹' Metric.ball z₀ a ∈ 𝓝 (z₀, 0) := by
        have hnear := hΨAt.preimage_mem_nhds
          (Metric.ball_mem_nhds (Ψeval (z₀, 0)) ha)
        simpa only [hΨ0] using hnear
      obtain ⟨Z₀, S₀, hZ₀open, hz₀Z₀, hS₀open, h0S₀, hΨsmall⟩ :=
        (mem_nhds_prod_iff'.mp hΨnear)
      let gB : M × ℝ → N := fun y => B.Φ (y.1, t₀) y.2
      let A : M × ℝ → (N × ℝ) := fun y => ((y.1, t₀), y.2)
      have hA : Continuous A :=
        (continuous_fst.prodMk continuous_const).prodMk continuous_snd
      have hAmap : MapsTo A
          ((Set.univ : Set M) ×ˢ Ioo (-B.eta) B.eta)
          (B.U ×ˢ Ioo (-B.eta) B.eta) := by
        rintro ⟨q, s⟩ ⟨-, hs⟩
        change (q, t₀) ∈ B.U ∧ s ∈ Ioo (-B.eta) B.eta
        exact ⟨B.slice_subset (by simp), hs⟩
      have hgBOn : ContinuousOn gB
          ((Set.univ : Set M) ×ˢ Ioo (-B.eta) B.eta) := by
        exact B.continuousOn.comp hA.continuousOn hAmap
      have hDopen : IsOpen ((Set.univ : Set M) ×ˢ Ioo (-B.eta) B.eta) :=
        isOpen_univ.prod isOpen_Ioo
      have hDmem : (p, (0 : ℝ)) ∈
          (Set.univ : Set M) ×ˢ Ioo (-B.eta) B.eta := by
        exact ⟨mem_univ p, ⟨neg_lt_zero.mpr B.eta_pos, B.eta_pos⟩⟩
      have hgBAt : ContinuousAt gB (p, 0) :=
        hgBOn.continuousAt (hDopen.mem_nhds hDmem)
      have hgB0 : gB (p, 0) = x₀ := by
        change B.Φ (p, t₀) 0 = (p, t₀)
        exact B.apply_zero (p, t₀) (B.slice_subset (by simp))
      have hφgBAt : ContinuousAt (fun y => φ (gB y)) (p, 0) :=
        ContinuousAt.comp_of_eq (g := φ) (f := gB) (x := (p, 0))
          hφAt hgBAt hgB0
      have hφgB0 : φ (gB (p, 0)) = z₀ := by rw [hgB0]
      have hBsrcN : gB ⁻¹' φ.source ∈ 𝓝 (p, 0) := by
        have hxsrc : x₀ ∈ φ.source := by
          change x₀ ∈ (extChartAt J x₀).source
          exact mem_extChartAt_source (I := J) x₀
        exact hgBAt.preimage_mem_nhds
          ((isOpen_extChartAt_source (I := J) x₀).mem_nhds
            (by simpa [hgB0] using hxsrc))
      have hBcoordN : (fun y => φ (gB y)) ⁻¹' Metric.ball z₀ a ∈ 𝓝 (p, 0) := by
        rw [← hφgB0]
        exact hφgBAt.preimage_mem_nhds
          (Metric.ball_mem_nhds (φ (gB (p, 0))) ha)
      have hBgoodN :
          (gB ⁻¹' φ.source ∩ (fun y => φ (gB y)) ⁻¹' Metric.ball z₀ a) ∈ 𝓝 (p, 0) :=
        Filter.inter_mem hBsrcN hBcoordN
      obtain ⟨UB, TB, hUBopen, hpUB, hTBopen, h0TB, hBgood⟩ :=
        (mem_nhds_prod_iff'.mp hBgoodN)
      let Uchart : Set M := qmap ⁻¹' φ.source
      have hUchartopen : IsOpen Uchart := (isOpen_extChartAt_source (I := J) x₀).preimage
        (continuous_id.prodMk continuous_const)
      have hpUchart : p ∈ Uchart := by
        change x₀ ∈ (extChartAt J x₀).source
        exact mem_extChartAt_source (I := J) x₀
      let Ustart : Set M := start ⁻¹' (Z₀ ∩ Metric.ball z₀ r)
      have hstartN : start ⁻¹' (Z₀ ∩ Metric.ball z₀ r) ∈ 𝓝 p := by
        exact hstartAt.preimage_mem_nhds
          ((hZ₀open.inter Metric.isOpen_ball).mem_nhds (by
            rw [hstart0]
            exact ⟨hz₀Z₀, Metric.mem_ball_self hr⟩))
      obtain ⟨Ustart, hUstart, hUstartopen, hpUstart⟩ := mem_nhds_iff.mp hstartN
      let U : Set M := UB ∩ Ustart ∩ Uchart
      have hUopen : IsOpen U := (hUBopen.inter hUstartopen).inter hUchartopen
      have hpU : p ∈ U := ⟨⟨hpUB, hpUstart⟩, hpUchart⟩
      let S : Set ℝ := TB ∩ S₀ ∩ Ioo (-δ) δ ∩ Ioo (-B.eta) B.eta
      have hSopen : IsOpen S :=
        ((hTBopen.inter hS₀open).inter isOpen_Ioo).inter isOpen_Ioo
      have h0S : (0 : ℝ) ∈ S := by
        exact ⟨⟨⟨h0TB, h0S₀⟩,
          ⟨neg_lt_zero.mpr hδ, hδ⟩⟩,
          ⟨neg_lt_zero.mpr B.eta_pos, B.eta_pos⟩⟩
      obtain ⟨ρ, hρ, hρS⟩ := Metric.mem_nhds_iff.mp (hSopen.mem_nhds h0S)
      let d : ℝ := min (ρ / 2) (B.eta / 2)
      have hdpos : 0 < d := by
        dsimp [d]
        exact lt_min (by linarith [hρ]) (by linarith [B.eta_pos])
      have hdeta : d ≤ B.eta := by
        dsimp [d]
        exact (min_le_right _ _).trans (by linarith [B.eta_pos])
      have htimeS : ∀ s ∈ Ioo (-d) d, s ∈ S := by
        intro s hs
        apply hρS
        rw [Metric.mem_ball, Real.dist_eq, sub_zero]
        have hsabs : |s| < d := abs_lt.mpr hs
        have hdρ : d < ρ := by
          dsimp [d]
          have : ρ / 2 < ρ := half_lt_self hρ
          exact lt_of_le_of_lt (min_le_left _ _) this
        exact lt_trans hsabs hdρ
      have hcoordODE {γ : ℝ → N}
          (hγ : IsMIntegralCurveOn γ (fun q => X q) (Ioo (-B.eta) B.eta))
          {s : ℝ} (hs : s ∈ Ioo (-B.eta) B.eta) (hsrc : γ s ∈ φ.source) :
          HasDerivWithinAt (fun u => φ (γ u)) (c (γ s))
            (Ioo (-B.eta) B.eta) s := by
        have hsrc' : γ s ∈ (chartAt (ModelProd H ℝ) x₀).source := by
          rw [← extChartAt_source (I := J) x₀]
          exact hsrc
        rw [hasDerivWithinAt_iff_hasFDerivWithinAt,
          ← hasMFDerivWithinAt_iff_hasFDerivWithinAt]
        apply (HasMFDerivWithinAt.comp s
          (hasMFDerivWithinAt_extChartAt (I := J) hsrc') (hγ s hs)
          (Set.subset_preimage_image _ _)).congr_mfderiv
        rw [mfderiv_chartAt_eq_tangentCoordChange hsrc']
        have hcval : c (γ s) =
            tangentCoordChange J (γ s) x₀ (γ s) (X (γ s)) := by
          apply hcoord
          rwa [trivializationAt_baseSet_eq_chartAt_source]
        rw [hcval]
        rw [ContinuousLinearMap.ext_iff]
        intro a
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
          map_smul,
          ← one_apply_eq_self
            (F := TangentSpace 𝓘(ℝ, ℝ) s →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) s) a,
          ← ContinuousLinearMap.smulRight_apply]
        rfl
      have hBcoordEq : ∀ q ∈ U, ∀ s ∈ Ioo (-d) d,
          gB (q, s) = φ.symm (Ψ (start q) s) := by
        intro q hq s hs
        have hqB : q ∈ UB := hq.1.1
        have hqStart : q ∈ Ustart := hq.1.2
        have hqChart : q ∈ Uchart := hq.2
        have hsS := htimeS s hs
        have hsTB : s ∈ TB := hsS.1.1.1
        have hsS₀ : s ∈ S₀ := hsS.1.1.2
        have hsδ : s ∈ Ioo (-δ) δ := hsS.1.2
        have hsBη : s ∈ Ioo (-B.eta) B.eta := hsS.2
        have hBgoodAt : (gB (q, s) ∈ φ.source) ∧
            φ (gB (q, s)) ∈ Metric.ball z₀ a := by
          have hmem : (q, s) ∈ UB ×ˢ TB := ⟨hqB, hsTB⟩
          exact hBgood hmem
        have hBsrc : gB (q, s) ∈ φ.source := hBgoodAt.1
        have hBball : φ (gB (q, s)) ∈ Metric.ball z₀ a := hBgoodAt.2
        have hstart : start q ∈ Z₀ ∩ Metric.ball z₀ r := hUstart hqStart
        have hΨball : Ψeval (start q, s) ∈ Metric.ball z₀ a := hΨsmall ⟨hstart.1, hsS₀⟩
        have hΨstart : start q ∈ Metric.ball z₀ r := hstart.2
        have htimeδ : s ∈ Ioo (-δ) δ := hsδ
        have hBtime : s ∈ Ioo (-B.eta) B.eta := hsBη
        let u : ℝ → E × ℝ := fun t => φ (gB (q, t))
        let v : ℝ → E × ℝ := fun t => Ψ (start q) t
        have huODE : ∀ t ∈ Ioo (-d) d, HasDerivAt u (fext (u t)) t := by
          intro t ht
          have hts := htimeS t ht
          have hBgoodAt : (gB (q, t) ∈ φ.source) ∧
              φ (gB (q, t)) ∈ Metric.ball z₀ a := by
            have hmem : (q, t) ∈ UB ×ˢ TB := ⟨hqB, hts.1.1.1⟩
            exact hBgood hmem
          have hsource : gB (q, t) ∈ φ.source := hBgoodAt.1
          have hcoordball : φ (gB (q, t)) ∈ Metric.ball z₀ a := hBgoodAt.2
          have hderiv := (hcoordODE
            (B.integral_curve (q, t₀) (B.slice_subset (by simp)))
            (by exact hts.2) hsource).hasDerivAt
              (Ioo_mem_nhds hts.2.1 hts.2.2)
          have hcoordvalue : c (gB (q, t)) = fext (u t) := by
            have hce : f (u t) = c (gB (q, t)) := by
              dsimp [f, u]
              rw [φ.left_inv hsource]
            calc
              c (gB (q, t)) = f (u t) := hce.symm
              _ = fext (u t) :=
                (hext (x := u t) (Metric.ball_subset_closedBall hcoordball)).symm
          simpa [u, gB, hcoordvalue] using hderiv
        have hvODE : ∀ t ∈ Ioo (-d) d, HasDerivAt v (fext (v t)) t := by
          intro t ht
          have hts := htimeS t ht
          have hdt : t ∈ Ioo (-δ) δ := hts.1.2
          have hflowt := (hflow (start q) hΨstart).2 t hdt
          simpa [v] using hflowt
        have huBall : ∀ t ∈ Ioo (-d) d, u t ∈ Metric.closedBall z₀ a := by
          intro t ht
          have hts := htimeS t ht
          have hb : φ (gB (q, t)) ∈ Metric.ball z₀ a := by
            have hmem : (q, t) ∈ UB ×ˢ TB := ⟨hqB, hts.1.1.1⟩
            exact (hBgood hmem).2
          exact Metric.ball_subset_closedBall hb
        have hvBall : ∀ t ∈ Ioo (-d) d, v t ∈ Metric.closedBall z₀ a := by
          intro t ht
          have hts := htimeS t ht
          have hb : Ψeval (start q, t) ∈ Metric.ball z₀ a :=
            hΨsmall ⟨hstart.1, hts.1.1.2⟩
          simpa [v, Ψeval] using Metric.ball_subset_closedBall hb
        have hucont : ContinuousOn u (Ioo (-d) d) := by
          exact continuousOn_of_forall_continuousAt fun t ht => (huODE t ht).continuousAt
        have hvcont : ContinuousOn v (Ioo (-d) d) := by
          exact continuousOn_of_forall_continuousAt fun t ht => (hvODE t ht).continuousAt
        have hinitial : u 0 = v 0 := by
          change φ (B.Φ (q, t₀) 0) = Ψ (start q) 0
          rw [B.apply_zero (q, t₀) (B.slice_subset (by simp))]
          exact ((hflow (start q) hΨstart).1).symm
        have hODEeq : EqOn u v (Ioo (-d) d) := by
          apply ODE_solution_unique_of_mem_Ioo (v := fun _ => fext)
            (s := fun _ => Metric.closedBall z₀ a) (K := K) (a := -d) (b := d) (t₀ := 0)
          · intro t ht
            exact hLip
          · exact ⟨by linarith [hdpos], hdpos⟩
          · intro t ht
            exact ⟨huODE t ht, huBall t ht⟩
          · intro t ht
            exact ⟨hvODE t ht, hvBall t ht⟩
          · exact hinitial
        have heqcoord := hODEeq hs
        have hpoint : gB (q, s) = φ.symm (Ψ (start q) s) := by
          calc
            gB (q, s) = φ.symm (φ (gB (q, s))) :=
              (φ.left_inv hBsrc).symm
            _ = φ.symm (Ψ (start q) s) := by
              exact congrArg φ.symm (by simpa [u, v] using heqcoord)
        exact hpoint
      let D : Set (M × ℝ) := U ×ˢ Ioo (-d) d
      let G : M × ℝ → M := fun y => (φ.symm (Ψ (start y.1) y.2)).1
      have hbaseMap : ContMDiff (I.prod 𝓘(ℝ, ℝ)) J ∞
          (fun y : M × ℝ => (y.1, t₀)) := by
        exact contMDiff_fst.prodMk contMDiff_const
      have hbaseMaps : MapsTo (fun y : M × ℝ => (y.1, t₀)) D
          (chartAt (ModelProd H ℝ) x₀).source := by
        intro y hy
        have hqchart : qmap y.1 ∈ φ.source := hy.1.2
        change (y.1, t₀) ∈ (extChartAt J x₀).source at hqchart
        rw [← extChartAt_source (I := J) x₀]
        exact hqchart
      have hcoordStart : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E × ℝ) ∞
          (fun y : M × ℝ => φ (y.1, t₀)) D := by
        exact (contMDiffOn_extChartAt (I := J) (x := x₀)).comp
          hbaseMap.contMDiffOn hbaseMaps
      have hinput : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, (E × ℝ) × ℝ) ∞
          (fun y : M × ℝ => (φ (y.1, t₀), y.2)) D := by
        exact hcoordStart.prodMk_space contMDiff_snd.contMDiffOn
      have hψcont : ContMDiffOn 𝓘(ℝ, (E × ℝ) × ℝ) 𝓘(ℝ, E × ℝ) ∞
          Ψeval ((Metric.ball z₀ r) ×ˢ Ioo (-δ) δ) := hΨ.contMDiffOn
      have hinputMaps : MapsTo (fun y : M × ℝ => (φ (y.1, t₀), y.2)) D
          ((Metric.ball z₀ r) ×ˢ Ioo (-δ) δ) := by
        intro y hy
        have hyU : y.1 ∈ U := hy.1
        have hyS := hy.2
        have hyStart : start y.1 ∈ Z₀ ∩ Metric.ball z₀ r := by
          exact hUstart hyU.1.2
        have hsS := htimeS y.2 hyS
        exact ⟨hyStart.2, hsS.1.2⟩
      have hψcompose : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E × ℝ) ∞
          (fun y : M × ℝ => Ψ (φ (y.1, t₀)) y.2) D := by
        have h := hψcont.comp hinput hinputMaps
        exact h.congr fun y hy => rfl
      have hψtarget : ∀ y ∈ D,
          Ψ (φ (y.1, t₀)) y.2 ∈ φ.target := by
        intro y hy
        have hyU : y.1 ∈ U := hy.1
        have hyStart : start y.1 ∈ Z₀ ∩ Metric.ball z₀ r := hUstart hyU.1.2
        have hsS := htimeS y.2 hy.2
        have hΨball : Ψeval (start y.1, y.2) ∈ Metric.ball z₀ a :=
          hΨsmall (show (start y.1, y.2) ∈ Z₀ ×ˢ S₀ from
            ⟨hyStart.1, hsS.1.1.2⟩)
        have hb := hΨball
        exact haφ (Metric.ball_subset_closedBall hb)
      have hsymmCompose : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) J ∞
          (fun y : M × ℝ => φ.symm (Ψ (φ (y.1, t₀)) y.2)) D :=
        (contMDiffOn_extChartAt_symm x₀).comp hψcompose hψtarget
      have hG : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ G D := by
        have hfst : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞
            (@Prod.fst M ℝ) Set.univ := contMDiffOn_fst
        exact hfst.comp hsymmCompose (by intro y hy; exact mem_univ _)
      have hG_eq : EqOn (fun y : M × ℝ => B.spatialFlow y.1 y.2) G D := by
        intro y hy
        change (B.Φ (y.1, t₀) y.2).1 = _
        exact congrArg Prod.fst (hBcoordEq y.1 hy.1 y.2 hy.2)
      have hG' := hG.congr hG_eq
      refine ⟨U, hUopen, hpU, d, hdpos, hdeta, ?_⟩
      exact hG'
    choose U hUopen hpU d hdpos hdeta hlocal using hlocal
    obtain ⟨s, hscover⟩ := (isCompact_univ : IsCompact (Set.univ : Set M)).elim_finite_subcover
      U hUopen (by intro p hp; exact mem_iUnion.mpr ⟨p, hpU p⟩)
    have hsne : s.Nonempty := by
      by_contra hne
      have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have : (Set.univ : Set M) ⊆ (∅ : Set M) := by
        simpa [hempty] using hscover
      rcases hM with ⟨p⟩
      have := this (mem_univ p)
      simpa using this
    let ε : ℝ := (s.image d).min' (hsne.image d)
    have hεpos : 0 < ε := by
      have hmem : ε ∈ s.image d := Finset.min'_mem _ _
      obtain ⟨p, hp, hpeq⟩ := Finset.mem_image.mp hmem
      rw [← hpeq]
      exact hdpos p
    have hεeta : ε ≤ B.eta := by
      obtain ⟨p, hp, -⟩ :=
        Finset.mem_image.mp (Finset.min'_mem (s.image d) (hsne.image d))
      exact (Finset.min'_le (s.image d) (d p)
        (Finset.mem_image.mpr ⟨p, hp, rfl⟩)).trans (hdeta p)
    have hGlobal : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞
        (fun q : M × ℝ => B.spatialFlow q.1 q.2)
        ((Set.univ : Set M) ×ˢ Ioo (-ε) ε) := by
      apply contMDiffOn_of_locally_contMDiffOn
      intro y hy
      obtain ⟨p, hp, hyU⟩ := mem_iUnion₂.mp (hscover hy.1)
      have hεd : ε ≤ d p := by
        exact Finset.min'_le (s.image d) (d p) (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
      refine ⟨U p ×ˢ Ioo (-d p) (d p), (hUopen p).prod isOpen_Ioo, ?_, ?_⟩
      · exact ⟨hyU, ⟨by linarith [hy.2.1], by linarith [hy.2.2]⟩⟩
      · apply (hlocal p).mono
        intro z hz
        exact hz.2
    exact ⟨ε, hεpos, hεeta, hGlobal⟩
  · let ε : ℝ := B.eta / 2
    refine ⟨ε, by dsimp [ε]; linarith [B.eta_pos], by dsimp [ε]; linarith [B.eta_pos], ?_⟩
    intro q hq
    exact False.elim (hM ⟨q.1⟩)
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.TimeDependentFlowJointSmooth
