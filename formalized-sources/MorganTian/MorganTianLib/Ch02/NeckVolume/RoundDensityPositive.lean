import MorganTianLib.Ch02.NeckVolume.RoundDensityModel

open Set MeasureTheory Riemannian Bundle Function
open scoped ContDiff Manifold Topology ENNReal Bundle RealInnerProductSpace
noncomputable section
namespace MorganTianLib

set_option maxHeartbeats 800000 in
/-- **Math.** The sphere--axis coordinate density is continuous and strictly positive
on the actual sphere chart target, without reference to any neck length. -/
theorem roundCylinderCoordinateDensity_continuous_pos (alpha : EpsilonNeckSphere) :
    ContinuousOn (roundCylinderCoordinateDensity alpha) (extChartAt (𝓡 2) alpha).target ∧
      ∀ u ∈ (extChartAt (𝓡 2) alpha).target, 0 < roundCylinderCoordinateDensity alpha u := by
/- SWARM_PROOF_BEGIN -/
  classical
  constructor
  · let e := trivializationAt (EuclideanSpace ℝ (Fin 2)) (TangentSpace (𝓡 2)) alpha
    let base := e.baseSet
    have hsection : ∀ q : EuclideanSpace ℝ (Fin 2),
        ContMDiffOn (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) ∞
          (fun p : EpsilonNeckSphere =>
            (⟨p, e.symm p q⟩ : TangentBundle (𝓡 2) EpsilonNeckSphere)) base := by
      intro q
      let b := Module.finBasis ℝ (EuclideanSpace ℝ (Fin 2))
      let c : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2))) → ℝ :=
        fun k => (b.repr q) k
      let S : (p : EpsilonNeckSphere) → TangentSpace (𝓡 2) p := fun p =>
        ∑ k, c k • Riemannian.Tensor.chartBasisVecFiber alpha k p
      have hS : ContMDiffOn (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) ∞
          (fun p => (⟨p, S p⟩ : TangentBundle (𝓡 2) EpsilonNeckSphere)) base := by
        apply ContMDiffOn.sum_section
        intro k hk
        exact (contMDiffOn_const.smul_section
          (Riemannian.Tensor.chartBasisVec_contMDiffOn alpha k)).congr fun p hp => by
          rfl
      have hEq : ∀ p ∈ base, S p = e.symm p q := by
        intro p hp
        have hq : (∑ k, c k • b k) = q := b.sum_repr q
        calc
          S p = ∑ k, c k • (e.symmL ℝ p) (b k) := by
            apply Finset.sum_congr rfl
            intro k hk
            dsimp [Riemannian.Tensor.chartBasisVecFiber]
            rw [e.symmL_apply hp]
          _ = (e.symmL ℝ p) (∑ k, c k • b k) := by
            rw [map_sum]
            apply Finset.sum_congr rfl
            intro k hk
            rw [map_smul]
          _ = e.symm p q := by rw [hq, e.symmL_apply hp]
      change ContMDiffOn (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) ∞
        (fun p => (⟨p, e.symm p q⟩ : TangentBundle (𝓡 2) EpsilonNeckSphere)) base
      apply e.contMDiffOn_section_baseSet_iff.mpr
      exact e.contMDiffOn_section_baseSet_iff.mp
        (hS.congr fun p hp =>
          congrArg (fun v => (⟨p, v⟩ : TangentBundle (𝓡 2) EpsilonNeckSphere))
            (hEq p hp).symm)
    have hentry : ∀ q r : EuclideanSpace ℝ (Fin 2),
        ContinuousOn (fun p : EpsilonNeckSphere =>
          roundSphereMetric.metricInner p (e.symm p q) (e.symm p r)) base := by
      intro q r
      have hpair : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞
          (fun p : EpsilonNeckSphere =>
            roundSphereMetric.metricInner p (e.symm p q) (e.symm p r)) base := by
        intro p hp
        exact roundSphereMetric.metricInner_contMDiffWithinAt
          (hsection q p hp) (hsection r p hp)
      exact hpair.continuousOn
    have hGram : ContinuousOn (roundCylinderCoordinateGram alpha)
        (extChartAt (𝓡 2) alpha).target := by
      rw [continuousOn_pi]
      intro i
      rw [continuousOn_pi]
      intro j
      let split := fun k => EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
        (Module.finBasis ℝ (EuclideanSpace ℝ (Fin 3)) k)
      have hs : ContinuousOn
          (fun u : EuclideanSpace ℝ (Fin 2) =>
            roundSphereMetric.metricInner ((extChartAt (𝓡 2) alpha).symm u)
              (e.symm ((extChartAt (𝓡 2) alpha).symm u) (split i).1)
              (e.symm ((extChartAt (𝓡 2) alpha).symm u) (split j).1))
          (extChartAt (𝓡 2) alpha).target := by
        simpa [Function.comp_def] using
          (hentry (split i).1 (split j).1).comp
            (continuousOn_extChartAt_symm (I := 𝓡 2) alpha)
            (by
              intro (u : EuclideanSpace ℝ (Fin 2)) hu
              change (extChartAt (𝓡 2) alpha).symm u ∈ e.baseSet
              rw [trivializationAt_baseSet_eq_chartAt_source]
              rw [← extChartAt_source (𝓡 2)]
              exact (extChartAt (𝓡 2) alpha).map_target hu)
      have ha : ContinuousOn (fun _ : EuclideanSpace ℝ (Fin 2) =>
          inner ℝ (split i).2 (split j).2) (extChartAt (𝓡 2) alpha).target :=
        continuousOn_const
      have hadd := hs.add ha
      change ContinuousOn
        (fun u : EuclideanSpace ℝ (Fin 2) =>
          roundSphereMetric.metricInner ((extChartAt (𝓡 2) alpha).symm u)
            (e.symm ((extChartAt (𝓡 2) alpha).symm u) (split i).1)
            (e.symm ((extChartAt (𝓡 2) alpha).symm u) (split j).1) +
            inner ℝ (split i).2 (split j).2)
        (extChartAt (𝓡 2) alpha).target
      exact hadd
    have hdet : ContinuousOn (fun u => (roundCylinderCoordinateGram alpha u).det)
        (extChartAt (𝓡 2) alpha).target := by
      rw [continuousOn_iff_continuous_restrict]
      exact Continuous.matrix_det (continuousOn_iff_continuous_restrict.mp hGram)
    change ContinuousOn (fun u => Real.sqrt (roundCylinderCoordinateGram alpha u).det)
      (extChartAt (𝓡 2) alpha).target
    exact Real.continuous_sqrt.continuousOn.comp hdet (fun _ _ => Set.mem_univ _)
  · intro u hu
    let p := (extChartAt (𝓡 2) alpha).symm u
    let e := trivializationAt (EuclideanSpace ℝ (Fin 2)) (TangentSpace (𝓡 2)) alpha
    have hp : p ∈ e.baseSet := by
      dsimp [p, e]
      rw [← extChartAt_source (𝓡 2)]
      exact (extChartAt (𝓡 2) alpha).map_target hu
    let ell := e.linearEquivAt ℝ p hp
    let splitL :=
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)).toLinearEquiv
    let prodL := LinearEquiv.prodCongr ell.symm
      (LinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 1)))
    let L := splitL.trans prodL
    let split := fun i => EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
      (Module.finBasis ℝ (EuclideanSpace ℝ (Fin 3)) i)
    let v : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) →
        TangentSpace (𝓡 2) p := fun i => ell.symm (split i).1
    let w : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) →
        EuclideanSpace ℝ (Fin 1) := fun i => (split i).2
    let A : Matrix (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))))
        (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) ℝ := Matrix.of fun i j =>
      roundSphereMetric.metricInner p (v i) (v j) + inner ℝ (w i) (w j)
    have hA : A.PosDef := by
      rw [Matrix.posDef_iff_dotProduct_mulVec]
      constructor
      · apply Matrix.IsHermitian.ext
        intro i j
        change star (roundSphereMetric.metricInner p (v j) (v i) + inner ℝ (w j) (w i)) =
          roundSphereMetric.metricInner p (v i) (v j) + inner ℝ (w i) (w j)
        simp only [StarAddMonoid.star_add, TrivialStar.star_trivial]
        rw [roundSphereMetric.metricInner_comm, real_inner_comm]
      · intro x hx
        let sv : TangentSpace (𝓡 2) p := ∑ i, x i • v i
        let sw : EuclideanSpace ℝ (Fin 1) := ∑ i, x i • w i
        have hquad : dotProduct (star x) (Matrix.mulVec A x) =
            roundSphereMetric.metricInner p sv sv + inner ℝ sw sw := by
          simp only [Matrix.mulVec, dotProduct, A, Matrix.of_apply, Pi.star_apply,
            starRingEnd_apply, conj_trivial, mul_one]
          have hmetric : roundSphereMetric.metricInner p sv sv =
              ∑ i, ∑ j, x i * x j *
                roundSphereMetric.metricInner p (v i) (v j) := by
            change roundSphereMetric.metricInner p (∑ i, x i • v i) (∑ i, x i • v i) = _
            rw [metricInner_sum_smul_left]
            apply Finset.sum_congr rfl
            intro i hi
            rw [metricInner_sum_smul_right]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
          have hinner : inner ℝ sw sw =
              ∑ i, ∑ j, x i * x j * inner ℝ (w i) (w j) := by
            calc
              inner ℝ sw sw = ∑ i, inner ℝ (x i • w i) sw := by
                change inner ℝ (∑ i, x i • w i) sw = _
                rw [sum_inner]
              _ = ∑ i, x i * inner ℝ (w i) sw := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [inner_smul_left]
                simp
              _ = ∑ i, x i * (∑ j, x j * inner ℝ (w i) (w j)) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [inner_sum]
                apply congrArg (fun z => x i * z)
                apply Finset.sum_congr rfl
                intro j hj
                rw [inner_smul_right]
              _ = ∑ i, ∑ j, x i * x j * inner ℝ (w i) (w j) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j hj
                ring
          rw [hmetric, hinner]
          simp only [TrivialStar.star_trivial]
          calc
            (∑ i, x i * ∑ j, (roundSphereMetric.metricInner p (v i) (v j) +
                inner ℝ (w i) (w j)) * x j) =
                ∑ i, ∑ j, x i * x j *
                  (roundSphereMetric.metricInner p (v i) (v j) + inner ℝ (w i) (w j)) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j hj
              ring
            _ = (∑ i, ∑ j, x i * x j *
                roundSphereMetric.metricInner p (v i) (v j)) +
                (∑ i, ∑ j, x i * x j * inner ℝ (w i) (w j)) := by
              simp_rw [mul_add, Finset.sum_add_distrib]
        have hsum :
            (∑ i, x i • (Module.finBasis ℝ (EuclideanSpace ℝ (Fin 3))) i) ≠ 0 := by
          intro hzero
          have hcoeff := (Fintype.linearIndependent_iff.mp
            (Module.finBasis ℝ (EuclideanSpace ℝ (Fin 3))).linearIndependent) x hzero
          exact hx (funext hcoeff)
        have hpair : (sv, sw) ≠ (0, 0) := by
          have hLsum : L
                (∑ i, x i • (Module.finBasis ℝ (EuclideanSpace ℝ (Fin 3))) i) =
              (sv, sw) := by
            change prodL (splitL
                (∑ i, x i • (Module.finBasis ℝ (EuclideanSpace ℝ (Fin 3))) i)) =
              (∑ i, x i • ell.symm (split i).1, ∑ i, x i • (split i).2)
            rw [map_sum]
            simp_rw [splitL.map_smul]
            rw [map_sum]
            simp_rw [prodL.map_smul]
            apply Prod.ext
            · change (AddMonoidHom.fst _ _)
                  (∑ i, x i • prodL (splitL
                    ((Module.finBasis ℝ (EuclideanSpace ℝ (Fin 3))) i))) = _
              rw [map_sum]
              simp only [Prod.smul_fst]
              rfl
            · change (AddMonoidHom.snd _ _)
                  (∑ i, x i • prodL (splitL
                    ((Module.finBasis ℝ (EuclideanSpace ℝ (Fin 3))) i))) = _
              rw [map_sum]
              simp only [Prod.smul_snd]
              rfl
          intro hzero
          apply hsum
          apply L.injective
          calc
            L (∑ i, x i • (Module.finBasis ℝ (EuclideanSpace ℝ (Fin 3))) i) =
                (sv, sw) := hLsum
            _ = (0, 0) := hzero
            _ = L 0 := (L.map_zero).symm
        rw [hquad]
        by_cases hv : sv = 0
        · have hw : sw ≠ 0 := fun hw => hpair (Prod.ext hv hw)
          exact (real_inner_self_pos.mpr hw).trans_le
            (le_add_of_nonneg_left (roundSphereMetric.metricInner_self_nonneg p sv))
        · exact (roundSphereMetric.metricInner_self_pos p sv hv).trans_le
            (le_add_of_nonneg_right (real_inner_self_nonneg (x := sw)))
    have hEq : roundCylinderCoordinateGram alpha u = A := by
      ext i j
      simp [roundCylinderCoordinateGram, A, p, e, ell, split, v, w,
        Bundle.Trivialization.linearEquivAt_symm_apply]
    change 0 < Real.sqrt (roundCylinderCoordinateGram alpha u).det
    rw [hEq]
    exact Real.sqrt_pos.mpr hA.det_pos
/- SWARM_PROOF_END -/

end MorganTianLib
