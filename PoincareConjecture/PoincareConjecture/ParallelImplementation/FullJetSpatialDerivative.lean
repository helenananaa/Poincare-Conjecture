import PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet
import PoincareConjecture.ParallelImplementation.C2HolderPointwiseLimit
import PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.FullJetSpatialDerivative
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet
open scoped ContDiff Topology BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Uniform full-jet difference bounds produce the ACTUAL spatial derivative
as another zero-trace full parabolic jet. No norm convergence or derivative
jet witness is assumed. -/
theorem exists_actual_spatial_derivative_jet
    (T alpha : ℝ) (hT : 0 < T) (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (z : FullJet T) (hz : z ∈ fullParabolicJetSet T alpha hT.le)
    (i : Fin 3) (C : ℝ) (hC : 0 ≤ C)
    (hquot : ∀ h : ℝ, h ≠ 0 → ‖finiteSpatialDifferenceJet z i h‖ ≤ C) :
    ∃ dz : FullJet T,
      dz ∈ fullParabolicJetSet T alpha hT.le ∧ ‖dz‖ ≤ C ∧
      ∀ p : Slab T, dz.1.1.1.1 p = z.1.1.1.2.1 p (EuclideanSpace.single i 1) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let E6 := EuclideanSpace ℝ (Fin 6)
  let e : E3 := EuclideanSpace.single i 1
  let h (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  let q (n : ℕ) : FullJet T := finiteSpatialDifferenceJet z i (h n)

  have hspaceZ : z.1.1 ∈ PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicC2HolderSet T alpha := hz.1
  have htimeZ : (z.1.1.1.1, z.1.2) ∈ PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph.slabTimeDerivativeGraph T := hz.2.1
  have htimeIncZ : ∀ p : PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.Pair T,
      z.2 p = (PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
        (z.1.2 p.1.1 - z.1.2 p.1.2) := hz.2.2.1
  have hinitialZ : ∀ x : E3,
      z.1.1.1.1 (⟨0, le_rfl, hT.le⟩, x) = 0 := hz.2.2.2

  have hpos (n : ℕ) : 0 < h n := by
    dsimp [h]
    positivity
  have hne (n : ℕ) : h n ≠ 0 := ne_of_gt (hpos n)
  have hseq0 : Filter.Tendsto h Filter.atTop (𝓝 0) := by
    change Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (𝓝 0)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hseqPos : Filter.Tendsto h Filter.atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within h hseq0
      (Filter.Eventually.of_forall fun n => hpos n)

  have hfinite (n : ℕ) :=
    finite_spatial_difference_full_jet T alpha hT.le z hspaceZ htimeZ htimeIncZ
      i (h n) (hne n)
  have hqValue (n : ℕ) (p : Slab T) :
      (q n).1.1.1.1 p = (h n)⁻¹ •
        (z.1.1.1.1 (PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient.shiftPoint p i (h n)) - z.1.1.1.1 p) := (hfinite n).1 p
  have hqGrad (n : ℕ) (p : Slab T) :
      (q n).1.1.1.2.1 p = (h n)⁻¹ •
        (z.1.1.1.2.1 (PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient.shiftPoint p i (h n)) - z.1.1.1.2.1 p) := (hfinite n).2.1 p
  have hqHolder (n : ℕ) : (q n).1.1 ∈ PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicC2HolderSet T alpha :=
    (hfinite n).2.2.2.2.2.2.2.1
  have hqTime (n : ℕ) : ((q n).1.1.1.1, (q n).1.2) ∈
      PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph.slabTimeDerivativeGraph T := (hfinite n).2.2.2.2.2.2.2.2.1
  have hqTimeInc (n : ℕ) : ∀ p : PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.Pair T,
      (q n).2 p = (PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
        ((q n).1.2 p.1.1 - (q n).1.2 p.1.2) := (hfinite n).2.2.2.2.2.2.2.2.2.1
  have hqNorm (n : ℕ) : ‖q n‖ ≤ C := hquot (h n) (hne n)

  have hqFull (n : ℕ) : q n ∈ fullParabolicJetSet T alpha hT.le := by
    change (q n).1.1 ∈ PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicC2HolderSet T alpha ∧
      ((q n).1.1.1.1, (q n).1.2) ∈ PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph.slabTimeDerivativeGraph T ∧
      (∀ p : PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.Pair T, (q n).2 p =
        (PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
          ((q n).1.2 p.1.1 - (q n).1.2 p.1.2)) ∧
      ∀ x : E3, (q n).1.1.1.1 (⟨0, le_rfl, hT.le⟩, x) = 0
    refine ⟨hqHolder n, hqTime n, hqTimeInc n, ?_⟩
    intro x
    rw [hqValue n (⟨0, le_rfl, hT.le⟩, x)]
    simp only [PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient.shiftPoint]
    rw [hinitialZ, hinitialZ]
    simp

  have hqHessNorm (n : ℕ) : ‖(q n).1.1.1.2.2‖ ≤ C := by
    have hle : ‖(q n).1.1.1.2.2‖ ≤ ‖q n‖ := by
      calc
        ‖(q n).1.1.1.2.2‖ ≤ ‖(q n).1.1.1.2‖ := by
          change ‖(q n).1.1.1.2.2‖ ≤ max ‖(q n).1.1.1.2.1‖ ‖(q n).1.1.1.2.2‖
          exact le_max_right _ _
        _ ≤ ‖(q n).1.1.1‖ := by
          change ‖(q n).1.1.1.2‖ ≤ max ‖(q n).1.1.1.1‖ ‖(q n).1.1.1.2‖
          exact le_max_right _ _
        _ ≤ ‖(q n).1.1‖ := by
          change ‖(q n).1.1.1‖ ≤ max ‖(q n).1.1.1‖ ‖(q n).1.1.2‖
          exact le_max_left _ _
        _ ≤ ‖(q n).1‖ := by
          change ‖(q n).1.1‖ ≤ max ‖(q n).1.1‖ ‖(q n).1.2‖
          exact le_max_left _ _
        _ ≤ ‖q n‖ := by
          change ‖(q n).1‖ ≤ max ‖(q n).1‖ ‖(q n).2‖
          exact le_max_left _ _
    exact hle.trans (hqNorm n)
  have hqTimeNorm (n : ℕ) : ‖(q n).1.2‖ ≤ C := by
    have hle : ‖(q n).1.2‖ ≤ ‖q n‖ := by
      calc
        ‖(q n).1.2‖ ≤ ‖(q n).1‖ := by
          change ‖(q n).1.2‖ ≤ max ‖(q n).1.1‖ ‖(q n).1.2‖
          exact le_max_right _ _
        _ ≤ ‖q n‖ := by
          change ‖(q n).1‖ ≤ max ‖(q n).1‖ ‖(q n).2‖
          exact le_max_left _ _
    exact hle.trans (hqNorm n)
  have hqValueNorm (n : ℕ) : ‖(q n).1.1.1.1‖ ≤ C := by
    have hle : ‖(q n).1.1.1.1‖ ≤ ‖q n‖ := by
      calc
        ‖(q n).1.1.1.1‖ ≤ ‖(q n).1.1.1‖ := by
          change ‖(q n).1.1.1.1‖ ≤ max ‖(q n).1.1.1.1‖ ‖(q n).1.1.1.2‖
          exact le_max_left _ _
        _ ≤ ‖(q n).1.1‖ := by
          change ‖(q n).1.1.1‖ ≤ max ‖(q n).1.1.1‖ ‖(q n).1.1.2‖
          exact le_max_left _ _
        _ ≤ ‖(q n).1‖ := by
          change ‖(q n).1.1‖ ≤ max ‖(q n).1.1‖ ‖(q n).1.2‖
          exact le_max_left _ _
        _ ≤ ‖q n‖ := by
          change ‖(q n).1‖ ≤ max ‖(q n).1‖ ‖(q n).2‖
          exact le_max_left _ _
    exact hle.trans (hqNorm n)
  have hqGradNorm (n : ℕ) : ‖(q n).1.1.1.2.1‖ ≤ C := by
    have hle : ‖(q n).1.1.1.2.1‖ ≤ ‖q n‖ := by
      calc
        ‖(q n).1.1.1.2.1‖ ≤ ‖(q n).1.1.1.2‖ := by
          change ‖(q n).1.1.1.2.1‖ ≤ max ‖(q n).1.1.1.2.1‖ ‖(q n).1.1.1.2.2‖
          exact le_max_left _ _
        _ ≤ ‖(q n).1.1.1‖ := by
          change ‖(q n).1.1.1.2‖ ≤ max ‖(q n).1.1.1.1‖ ‖(q n).1.1.1.2‖
          exact le_max_right _ _
        _ ≤ ‖(q n).1.1‖ := by
          change ‖(q n).1.1.1‖ ≤ max ‖(q n).1.1.1‖ ‖(q n).1.1.2‖
          exact le_max_left _ _
        _ ≤ ‖(q n).1‖ := by
          change ‖(q n).1.1‖ ≤ max ‖(q n).1.1‖ ‖(q n).1.2‖
          exact le_max_left _ _
        _ ≤ ‖q n‖ := by
          change ‖(q n).1‖ ≤ max ‖(q n).1‖ ‖(q n).2‖
          exact le_max_left _ _
    exact hle.trans (hqNorm n)
  have hqHincNorm (n : ℕ) : ‖(q n).1.1.2‖ ≤ C := by
    have hle : ‖(q n).1.1.2‖ ≤ ‖q n‖ := by
      calc
        ‖(q n).1.1.2‖ ≤ ‖(q n).1.1‖ := by
          change ‖(q n).1.1.2‖ ≤ max ‖(q n).1.1.1‖ ‖(q n).1.1.2‖
          exact le_max_right _ _
        _ ≤ ‖(q n).1‖ := by
          change ‖(q n).1.1‖ ≤ max ‖(q n).1.1‖ ‖(q n).1.2‖
          exact le_max_left _ _
        _ ≤ ‖q n‖ := by
          change ‖(q n).1‖ ≤ max ‖(q n).1‖ ‖(q n).2‖
          exact le_max_left _ _
    exact hle.trans (hqNorm n)
  have hqTincNorm (n : ℕ) : ‖(q n).2‖ ≤ C := by
    calc
      ‖(q n).2‖ ≤ ‖q n‖ := by
        change ‖(q n).2‖ ≤ max ‖(q n).1‖ ‖(q n).2‖
        exact le_max_right _ _
      _ ≤ C := hqNorm n

  have hRhoPos (p : PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.Pair T) : 0 < PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho p.1.1 p.1.2 := by
    have hspaceTime : (p.1.1).1 ≠ (p.1.2).1 ∨ (p.1.1).2 ≠ (p.1.2).2 := by
      by_contra h
      push Not at h
      apply p.2
      apply Prod.ext
      · exact h.1
      · exact h.2
    unfold PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho
    rcases hspaceTime with ht | hx
    · have htval : ((p.1.1).1 : ℝ) ≠ ((p.1.2).1 : ℝ) := by
        intro hval
        apply ht
        exact Subtype.ext hval
      exact add_pos_of_nonneg_of_pos (norm_nonneg _)
        (Real.sqrt_pos.2 (abs_pos.mpr (sub_ne_zero.mpr htval)))
    · exact add_pos_of_pos_of_nonneg
        (norm_pos_iff.mpr (sub_ne_zero.mpr hx)) (Real.sqrt_nonneg _)
  have hqTimeDiff (n : ℕ) (p q' : Slab T) :
      ‖(q n).1.2 p - (q n).1.2 q'‖ ≤
        C * PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho p q' ^ alpha := by
    by_cases hpq : p = q'
    · subst q'
      simp [PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho, ha.ne']
    · let pq : PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.Pair T := ⟨(p, q'), hpq⟩
      have hrho : 0 < PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho p q' := hRhoPos pq
      have hpowa : 0 < PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho p q' ^ alpha := Real.rpow_pos_of_pos hrho alpha
      have hrel := hqTimeInc n pq
      have hdiff : (q n).1.2 p - (q n).1.2 q' =
          PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho p q' ^ alpha • (q n).2 pq := by
        calc
          _ = PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho p q' ^ alpha •
                ((PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho p q' ^ alpha)⁻¹ •
                  ((q n).1.2 p - (q n).1.2 q')) := by
                  rw [smul_smul, mul_inv_cancel₀ hpowa.ne', one_smul]
          _ = PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho p q' ^ alpha • (q n).2 pq := by rw [← hrel]
      calc
        ‖(q n).1.2 p - (q n).1.2 q'‖ =
            PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho p q' ^ alpha * ‖(q n).2 pq‖ := by
              rw [hdiff, norm_smul, Real.norm_of_nonneg hpowa.le]
        _ ≤ PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho p q' ^ alpha * ‖(q n).2‖ :=
          mul_le_mul_of_nonneg_left ((q n).2.norm_coe_le_norm pq) hpowa.le
        _ ≤ PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho p q' ^ alpha * C :=
          mul_le_mul_of_nonneg_left (hqTincNorm n) hpowa.le
        _ = C * PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho p q' ^ alpha := by ring

  let W := (E3 →L[ℝ] E3 →L[ℝ] EuclideanSpace ℝ (Fin 6)) ×
    EuclideanSpace ℝ (Fin 6)
  let J (n : ℕ) : C(Slab T, W) :=
    ⟨fun p => ((q n).1.1.1.2.2 p, (q n).1.2 p),
      ( (q n).1.1.1.2.2.continuous).prodMk ((q n).1.2.continuous)⟩
  let m (d : ℝ) : ℝ := C * (d + Real.sqrt d) ^ alpha
  have hm : Filter.Tendsto m (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt m 0 := by
      dsimp [m]
      exact continuousAt_const.mul
        ((continuousAt_id.add Real.continuous_sqrt.continuousAt).rpow_const
          (Or.inr ha.le))
    simpa [m, Real.sqrt_zero, ha.ne'] using hc.tendsto
  have hRhoLe (p q' : Slab T) :
      PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho p q' ≤ dist p q' + Real.sqrt (dist p q') := by
    have hprod : dist p q' = max (dist p.1 q'.1) (dist p.2 q'.2) := by
      exact Prod.dist_eq
    have hx : ‖p.2 - q'.2‖ ≤ dist p q' := by
      rw [hprod, dist_eq_norm]
      exact le_max_right _ _
    have ht : |(p.1 : ℝ) - (q'.1 : ℝ)| ≤ dist p q' := by
      have htimeDist : dist p.1 q'.1 = |(p.1 : ℝ) - (q'.1 : ℝ)| := by
        simp only [Subtype.dist_eq, dist_eq_norm, Real.norm_eq_abs]
      calc
        |(p.1 : ℝ) - (q'.1 : ℝ)| = dist p.1 q'.1 := htimeDist.symm
        _ ≤ max (dist p.1 q'.1) (dist p.2 q'.2) := le_max_left _ _
        _ = dist p q' := hprod.symm
    unfold PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho
    exact add_le_add hx (Real.sqrt_le_sqrt ht)
  have hJmod (n : ℕ) (p q' : Slab T) :
      dist (J n p) (J n q') ≤ m (dist p q') := by
    simp only [J, Prod.dist_eq]
    refine max_le ?_ ?_
    · calc
        dist ((q n).1.1.1.2.2 p) ((q n).1.1.1.2.2 q') =
            ‖(q n).1.1.1.2.2 p - (q n).1.1.1.2.2 q'‖ := by rw [dist_eq_norm]
        _ ≤ ‖(q n).1.1.2‖ * PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho p q' ^ alpha :=
          (PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolic_C2_holder_jet_complete T alpha ha).2 (q n).1.1
            (hqHolder n) p q'
        _ ≤ C * PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho p q' ^ alpha :=
          mul_le_mul_of_nonneg_right (hqHincNorm n)
            (Real.rpow_nonneg (by unfold PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho; positivity) _)
        _ ≤ m (dist p q') := by
          dsimp [m]
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (by unfold PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho; positivity)
              (hRhoLe p q') ha.le) hC
    · calc
        dist ((q n).1.2 p) ((q n).1.2 q') =
            ‖(q n).1.2 p - (q n).1.2 q'‖ := by rw [dist_eq_norm]
        _ ≤ C * PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho p q' ^ alpha := hqTimeDiff n p q'
        _ ≤ m (dist p q') := by
          dsimp [m]
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (by unfold PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho; positivity)
              (hRhoLe p q') ha.le) hC
  have hJEquicont : Equicontinuous (fun n p => J n p) :=
    Metric.equicontinuous_of_continuity_modulus m hm (fun n p => J n p) (by
      intro p q' n
      exact hJmod n p q')

  let S : Set C(Slab T, W) := Set.range J
  have hSEquicont : Equicontinuous ((↑) : S → Slab T → W) := by
    let idx (f : S) : ℕ := Classical.choose (Set.mem_range.mp f.2)
    have hraw := hJEquicont.comp idx
    convert hraw using 1
    funext f p
    have heq : J (idx f) = (f : C(Slab T, W)) :=
      Classical.choose_spec (Set.mem_range.mp f.2)
    change (f : C(Slab T, W)) p = J (idx f) p
    rw [← heq]
  let compactFamily : Set (Set (Slab T)) := {K | IsCompact K}
  have hFEmbedding : Topology.IsClosedEmbedding
      (UniformOnFun.ofFun compactFamily ∘
        (fun f : C(Slab T, W) => (f : Slab T → W))) := by
    have hClosed : IsClosed
        (Set.range (ContinuousMap.toUniformOnFunIsCompact :
          C(Slab T, W) → UniformOnFun (Slab T) W {K | IsCompact K})) := by
      rw [ContinuousMap.range_toUniformOnFunIsCompact]
      exact UniformOnFun.isClosed_setOf_continuous
        CompactlyCoherentSpace.isCoherentWith
    have hEmbedding : Topology.IsClosedEmbedding
        (ContinuousMap.toUniformOnFunIsCompact :
          C(Slab T, W) → UniformOnFun (Slab T) W {K | IsCompact K}) :=
      ⟨ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isEmbedding, hClosed⟩
    change Topology.IsClosedEmbedding
      (ContinuousMap.toUniformOnFunIsCompact :
        C(Slab T, W) → UniformOnFun (Slab T) W compactFamily)
    exact hEmbedding
  have hpointCompact : ∀ K ∈ compactFamily, ∀ p ∈ K,
      ∃ Q : Set W, IsCompact Q ∧ ∀ f ∈ S, (f : Slab T → W) p ∈ Q := by
    intro K hK p hp
    refine ⟨Metric.closedBall (0 : W) C, isCompact_closedBall _ _, ?_⟩
    rintro f ⟨n, rfl⟩
    have hval : ‖(q n).1.1.1.2.2 p‖ ≤ C :=
      (q n).1.1.1.2.2.norm_coe_le_norm p |>.trans (hqHessNorm n)
    have htime : ‖(q n).1.2 p‖ ≤ C :=
      (q n).1.2.norm_coe_le_norm p |>.trans (hqTimeNorm n)
    have hnorm : ‖J n p‖ ≤ C := by
      apply (norm_prod_le_iff).2
      exact ⟨hval, htime⟩
    exact Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hnorm)
  have hcompact : IsCompact (closure S) := by
    exact ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (𝔖_compact := fun K hK => hK) hFEmbedding
      (s_eqcont := fun K hK => hSEquicont.equicontinuousOn K)
      (s_pointwiseCompact := hpointCompact)

  rcases hcompact.tendsto_subseq (fun n => subset_closure ⟨n, rfl⟩) with
    ⟨lim, hlim, φ, hφ, hconv⟩
  have hconvCompact :=
    (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hconv)
  let Hfun (p : Slab T) : E3 →L[ℝ] E3 →L[ℝ] E6 := (lim p).1
  let tfun (p : Slab T) : E6 := (lim p).2
  have hHcont : Continuous Hfun := by
    exact continuous_fst.comp lim.continuous
  have htCont : Continuous tfun := by
    exact continuous_snd.comp lim.continuous
  have hpairPt (p : Slab T) :
      Filter.Tendsto (fun n => J (φ n) p) Filter.atTop (𝓝 (lim p)) := by
    have h := hconvCompact {p} isCompact_singleton
    exact h.tendsto_at (Set.mem_singleton p)
  have hHpt (p : Slab T) :
      Filter.Tendsto (fun n => (q (φ n)).1.1.1.2.2 p) Filter.atTop (𝓝 (Hfun p)) := by
    have h := (continuous_fst.continuousAt.tendsto.comp (hpairPt p))
    simpa [Function.comp_def, J, Hfun, q] using h
  have htPt (p : Slab T) :
      Filter.Tendsto (fun n => (q (φ n)).1.2 p) Filter.atTop (𝓝 (tfun p)) := by
    have h := (continuous_snd.continuousAt.tendsto.comp (hpairPt p))
    simpa [Function.comp_def, J, tfun, q] using h
  have hHbound (p : Slab T) : ‖Hfun p‖ ≤ C := by
    have htend := continuous_norm.continuousAt.tendsto.comp (hHpt p)
    have hmem : ‖Hfun p‖ ∈ Set.Iic C :=
      isClosed_Iic.mem_of_tendsto htend (Filter.Eventually.of_forall fun n =>
        (q (φ n)).1.1.1.2.2.norm_coe_le_norm p |>.trans (hqHessNorm (φ n)))
    exact hmem
  have htbound (p : Slab T) : ‖tfun p‖ ≤ C := by
    have htend := continuous_norm.continuousAt.tendsto.comp (htPt p)
    have hmem : ‖tfun p‖ ∈ Set.Iic C :=
      isClosed_Iic.mem_of_tendsto htend (Filter.Eventually.of_forall fun n =>
        (q (φ n)).1.2.norm_coe_le_norm p |>.trans (hqTimeNorm (φ n)))
    exact hmem

  let ufun (p : Slab T) : E6 := z.1.1.1.2.1 p e
  let gfun (p : Slab T) : E3 →L[ℝ] E6 := z.1.1.1.2.2 p e
  have huCont : Continuous ufun := by
    change Continuous (fun p => z.1.1.1.2.1 p e)
    fun_prop
  have hgCont : Continuous gfun := by
    change Continuous (fun p => z.1.1.1.2.2 p e)
    fun_prop
  have hvaluePt (t : Set.Icc (0 : ℝ) T) (x : E3) :
      Filter.Tendsto (fun n => (q (φ n)).1.1.1.1 (t, x)) Filter.atTop (𝓝 (ufun (t, x))) := by
    let f : E3 → E6 := fun y => z.1.1.1.1 (t, y)
    have hline := (hspaceZ.1 t).1 x |>.hasLineDerivAt e
    have hlim := hline.tendsto_slope_zero_right.comp hseqPos
    have hEq (n : ℕ) : (q n).1.1.1.1 (t, x) =
        (h n)⁻¹ • (f (x + h n • e) - f x) := by
      rw [hqValue n (t, x)]
      rfl
    have hlim' : Filter.Tendsto (fun n => (q (φ n)).1.1.1.1 (t, x)) Filter.atTop
        (𝓝 (z.1.1.1.2.1 (t, x) e)) := by
      have hlimSub := hlim.comp hφ.tendsto_atTop
      apply Filter.Tendsto.congr' (Filter.Eventually.of_forall fun n => ?_) hlimSub
      simpa only [Function.comp_def, f] using (hEq (φ n)).symm
    simpa [ufun] using hlim'
  have hgradPt (t : Set.Icc (0 : ℝ) T) (x : E3) :
      Filter.Tendsto (fun n => (q (φ n)).1.1.1.2.1 (t, x)) Filter.atTop
        (𝓝 (gfun (t, x))) := by
    let f : E3 → E3 →L[ℝ] E6 := fun y => z.1.1.1.2.1 (t, y)
    have hline := (hspaceZ.1 t).2 x |>.hasLineDerivAt e
    have hlim := hline.tendsto_slope_zero_right.comp hseqPos
    have hEq (n : ℕ) : (q n).1.1.1.2.1 (t, x) =
        (h n)⁻¹ • (f (x + h n • e) - f x) := by
      rw [hqGrad n (t, x)]
      rfl
    have hlim' : Filter.Tendsto (fun n => (q (φ n)).1.1.1.2.1 (t, x)) Filter.atTop
        (𝓝 (z.1.1.1.2.2 (t, x) e)) := by
      have hlimSub := hlim.comp hφ.tendsto_atTop
      apply Filter.Tendsto.congr' (Filter.Eventually.of_forall fun n => ?_) hlimSub
      simpa only [Function.comp_def, f] using (hEq (φ n)).symm
    simpa [gfun] using hlim'

  have hufunBound (p : Slab T) : ‖ufun p‖ ≤ C := by
    have hpt := hvaluePt p.1 p.2
    have hnorm := continuous_norm.continuousAt.tendsto.comp hpt
    have hmem : ‖ufun p‖ ∈ Set.Iic C := isClosed_Iic.mem_of_tendsto hnorm
      (Filter.Eventually.of_forall fun n =>
        (q (φ n)).1.1.1.1.norm_coe_le_norm p |>.trans (hqValueNorm (φ n)))
    exact hmem
  have hgfunBound (p : Slab T) : ‖gfun p‖ ≤ C := by
    have hpt := hgradPt p.1 p.2
    have hnorm := continuous_norm.continuousAt.tendsto.comp hpt
    have hmem : ‖gfun p‖ ∈ Set.Iic C := isClosed_Iic.mem_of_tendsto hnorm
      (Filter.Eventually.of_forall fun n =>
        (q (φ n)).1.1.1.2.1.norm_coe_le_norm p |>.trans (hqGradNorm (φ n)))
    exact hmem

  have pairwiseBound {X Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      (f : X → Y) (B : ℝ) (hB : ∀ p, ‖f p‖ ≤ B) :
      ∀ p q' : X, dist (f p) (f q') ≤ 2 * B := by
    intro p q'
    rw [dist_eq_norm]
    calc
      ‖f p - f q'‖ ≤ ‖f p‖ + ‖f q'‖ := norm_sub_le _ _
      _ ≤ B + B := add_le_add (hB p) (hB q')
      _ = 2 * B := by ring

  let u : Slab T →ᵇ E6 := BoundedContinuousFunction.mkOfBound
    ⟨ufun, huCont⟩ (2 * C)
      (@pairwiseBound (Slab T) E6 _ _ ufun C hufunBound)
  let g : Slab T →ᵇ (E3 →L[ℝ] E6) := BoundedContinuousFunction.mkOfBound
    ⟨gfun, hgCont⟩ (2 * C)
      (@pairwiseBound (Slab T) (E3 →L[ℝ] E6) _ _ gfun C hgfunBound)
  let H : Slab T →ᵇ (E3 →L[ℝ] E3 →L[ℝ] E6) :=
    BoundedContinuousFunction.mkOfBound ⟨Hfun, hHcont⟩ (2 * C)
      (@pairwiseBound (Slab T) (E3 →L[ℝ] E3 →L[ℝ] E6) _ _ Hfun C hHbound)
  let dt : Slab T →ᵇ E6 :=
    BoundedContinuousFunction.mkOfBound ⟨tfun, htCont⟩ (2 * C)
      (@pairwiseBound (Slab T) E6 _ _ tfun C htbound)

  have hHdiffLimit (p q' : Slab T) :
      ‖Hfun p - Hfun q'‖ ≤ C * PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho p q' ^ alpha := by
    have hsub := (hHpt p).sub (hHpt q')
    have hnorm := continuous_norm.continuousAt.tendsto.comp hsub
    have hmem : ‖Hfun p - Hfun q'‖ ∈ Set.Iic (C * PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho p q' ^ alpha) :=
      isClosed_Iic.mem_of_tendsto hnorm
        (Filter.Eventually.of_forall fun n =>
          (PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolic_C2_holder_jet_complete T alpha ha).2
            (q (φ n)).1.1 (hqHolder (φ n)) p q' |>.trans
            (mul_le_mul_of_nonneg_right (hqHincNorm (φ n))
              (Real.rpow_nonneg (by unfold PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho; positivity) _)))
    exact hmem
  have htDiffLimit (p q' : Slab T) :
      ‖tfun p - tfun q'‖ ≤ C * PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho p q' ^ alpha := by
    have hsub := (htPt p).sub (htPt q')
    have hnorm := continuous_norm.continuousAt.tendsto.comp hsub
    have hmem : ‖tfun p - tfun q'‖ ∈ Set.Iic (C * PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho p q' ^ alpha) :=
      isClosed_Iic.mem_of_tendsto hnorm
        (Filter.Eventually.of_forall fun n => hqTimeDiff (φ n) p q')
    exact hmem

  let rhoFun (p : PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.Pair T) : ℝ := PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho p.1.1 p.1.2
  have hrhoCont : Continuous rhoFun := by
    dsimp [rhoFun]
    fun_prop [PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho]
  have hpairFst : Continuous (fun p : PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.Pair T => Hfun p.1.1) := by fun_prop
  have hpairSnd : Continuous (fun p : PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.Pair T => Hfun p.1.2) := by fun_prop
  have htimePairFst : Continuous (fun p : PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.Pair T => tfun p.1.1) := by fun_prop
  have htimePairSnd : Continuous (fun p : PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.Pair T => tfun p.1.2) := by fun_prop
  let incHfun (p : PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.Pair T) : E3 →L[ℝ] E3 →L[ℝ] E6 :=
    (rhoFun p ^ alpha)⁻¹ • (Hfun p.1.1 - Hfun p.1.2)
  let incTfun (p : PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.Pair T) : E6 :=
    (rhoFun p ^ alpha)⁻¹ • (tfun p.1.1 - tfun p.1.2)
  have hincHcont : Continuous incHfun := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hrho := hRhoPos p
    have hpowa : 0 < rhoFun p ^ alpha := Real.rpow_pos_of_pos hrho alpha
    have hcoeff : ContinuousAt (fun q : PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.Pair T => (rhoFun q ^ alpha)⁻¹) p :=
      (hrhoCont.continuousAt.rpow_const (Or.inr ha.le)).inv₀ hpowa.ne'
    exact hcoeff.smul ((hpairFst.continuousAt).sub hpairSnd.continuousAt)
  have hincTcont : Continuous incTfun := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hrho := hRhoPos p
    have hpowa : 0 < rhoFun p ^ alpha := Real.rpow_pos_of_pos hrho alpha
    have hcoeff : ContinuousAt (fun q : PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.Pair T => (rhoFun q ^ alpha)⁻¹) p :=
      (hrhoCont.continuousAt.rpow_const (Or.inr ha.le)).inv₀ hpowa.ne'
    exact hcoeff.smul ((htimePairFst.continuousAt).sub htimePairSnd.continuousAt)
  have hincHbound (p : PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.Pair T) : ‖incHfun p‖ ≤ C := by
    have hpowa : 0 < rhoFun p ^ alpha := Real.rpow_pos_of_pos (hRhoPos p) alpha
    calc
      ‖incHfun p‖ = (rhoFun p ^ alpha)⁻¹ * ‖Hfun p.1.1 - Hfun p.1.2‖ := by
        dsimp only [incHfun]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpowa)]
      _ ≤ (rhoFun p ^ alpha)⁻¹ * (C * rhoFun p ^ alpha) :=
        mul_le_mul_of_nonneg_left (hHdiffLimit p.1.1 p.1.2)
          (inv_nonneg.mpr hpowa.le)
      _ = C := by field_simp [ne_of_gt hpowa]
  have hincTbound (p : PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.Pair T) : ‖incTfun p‖ ≤ C := by
    have hpowa : 0 < rhoFun p ^ alpha := Real.rpow_pos_of_pos (hRhoPos p) alpha
    calc
      ‖incTfun p‖ = (rhoFun p ^ alpha)⁻¹ * ‖tfun p.1.1 - tfun p.1.2‖ := by
        dsimp only [incTfun]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpowa)]
      _ ≤ (rhoFun p ^ alpha)⁻¹ * (C * rhoFun p ^ alpha) :=
        mul_le_mul_of_nonneg_left (htDiffLimit p.1.1 p.1.2)
          (inv_nonneg.mpr hpowa.le)
      _ = C := by field_simp [ne_of_gt hpowa]
  let incH : PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.Pair T →ᵇ (E3 →L[ℝ] E3 →L[ℝ] E6) :=
    BoundedContinuousFunction.mkOfBound ⟨incHfun, hincHcont⟩ (2 * C)
      (@pairwiseBound
        (PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.Pair T)
        (E3 →L[ℝ] E3 →L[ℝ] E6) _ _ incHfun C hincHbound)
  let incT : PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.Pair T →ᵇ E6 :=
    BoundedContinuousFunction.mkOfBound ⟨incTfun, hincTcont⟩ (2 * C)
      (@pairwiseBound
        (PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.Pair T)
        E6 _ _ incTfun C hincTbound)

  have hgradUniform (t : Set.Icc (0 : ℝ) T) (x : E3) :
      TendstoUniformlyOn (fun n y => (q (φ n)).1.1.1.2.1 (t, y))
        (fun y => gfun (t, y)) Filter.atTop (Metric.ball x 1) := by
    let F (n : ℕ) (y : {y : E3 // y ∈ Metric.closedBall x 1}) :=
      (q (φ n)).1.1.1.2.1 (t, y.1)
    let f (y : {y : E3 // y ∈ Metric.closedBall x 1}) := gfun (t, y.1)
    have hLipschitz (n : ℕ) : LipschitzWith C.toNNReal
        (fun y : E3 => (q (φ n)).1.1.1.2.1 (t, y)) := by
      apply lipschitzWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
      · intro y
        exact ((hqFull (φ n)).1.1 t).2 y |>.differentiableAt
      · intro y
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal C hC]
        have hderiv := ((hqFull (φ n)).1.1 t).2 y
        rw [hderiv.fderiv]
        exact (q (φ n)).1.1.1.2.2.norm_coe_le_norm (t, y) |>.trans
          (hqHessNorm (φ n))
    have hmLip : Filter.Tendsto (fun d : ℝ => C * d) (𝓝 0) (𝓝 0) := by
      have hc : Continuous (fun d : ℝ => C * d) :=
        (continuous_const : Continuous (fun _ : ℝ => C)).mul continuous_id
      simpa using
        (hc.continuousAt : ContinuousAt (fun d : ℝ => C * d) 0).tendsto
    have hEqRaw : Equicontinuous
        (fun (n : ℕ) (y : E3) => (q (φ n)).1.1.1.2.1 (t, y)) :=
      Metric.equicontinuous_of_continuity_modulus (fun d : ℝ => C * d) hmLip
        (fun (n : ℕ) (y : E3) => (q (φ n)).1.1.1.2.1 (t, y)) (by
          intro y y' n
          calc
            dist ((q (φ n)).1.1.1.2.1 (t, y)) ((q (φ n)).1.1.1.2.1 (t, y')) ≤
                (C.toNNReal : ℝ) * dist y y' := (hLipschitz n).dist_le_mul y y'
            _ = C * dist y y' := by rw [Real.coe_toNNReal C hC])
    have hEq : Equicontinuous F := by
      have := (equicontinuous_restrict_iff
        (fun (n : ℕ) (y : E3) => (q (φ n)).1.1.1.2.1 (t, y))).2
          (hEqRaw.equicontinuousOn (Metric.closedBall x 1))
      convert this using 1
      funext n y
      rfl
    have hpt : Filter.Tendsto F Filter.atTop (𝓝 f) := by
      rw [tendsto_pi_nhds]
      intro y
      exact hgradPt t y.1
    have hUF := (hEq.tendsto_uniformFun_iff_pi Filter.atTop f).2 hpt
    have hUniform : TendstoUniformly F f Filter.atTop :=
      UniformFun.tendsto_iff_tendstoUniformly.mp hUF
    have hclosed : TendstoUniformlyOn
        (fun (n : ℕ) (y : E3) => (q (φ n)).1.1.1.2.1 (t, y))
        (fun (y : E3) => gfun (t, y)) Filter.atTop (Metric.closedBall x 1) := by
      rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
      simpa [F, f, Function.comp_def] using hUniform
    exact hclosed.mono Metric.ball_subset_closedBall

  have hHUniformBall (t : Set.Icc (0 : ℝ) T) (x : E3) :
      TendstoUniformlyOn (fun n y => (q (φ n)).1.1.1.2.2 (t, y))
        (fun y => Hfun (t, y)) Filter.atTop (Metric.ball x 1) := by
    let K : Set (Slab T) := Set.image (fun y : E3 => (t, y)) (Metric.closedBall x 1)
    have hK : IsCompact K :=
      (isCompact_closedBall x 1).image (continuous_const.prodMk continuous_id)
    have hUnif := (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hconv)
      K hK
    rw [Metric.tendstoUniformlyOn_iff]
    rw [Metric.tendstoUniformlyOn_iff] at hUnif
    intro ε hε
    filter_upwards [hUnif ε hε] with n hn
    intro y hy
    have hmem : (t, y) ∈ K := ⟨y, Metric.ball_subset_closedBall hy, rfl⟩
    have hpair := hn (t, y) hmem
    calc
      dist (Hfun (t, y)) ((q (φ n)).1.1.1.2.2 (t, y)) =
          dist ((lim (t, y)).1) ((J (φ n) (t, y)).1) := rfl
      _ ≤ dist (lim (t, y)) (J (φ n) (t, y)) := by
        rw [Prod.dist_eq]
        exact le_max_left _ _
      _ < ε := hpair

  have htimeUniform (x : E3) :
      TendstoUniformlyOn
        (fun n s => PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph.timeExtension
          (q (φ n)).1.2 x s)
        (PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph.timeExtension dt x)
        Filter.atTop (Set.Ioo (0 : ℝ) T) := by
    let K : Set (Slab T) := Set.image (fun s : Set.Icc (0 : ℝ) T => (s, x)) Set.univ
    have hK : IsCompact K := by
      letI : CompactSpace (Set.Icc (0 : ℝ) T) := compactSpace_Icc 0 T
      have hmap : Continuous (fun s : Set.Icc (0 : ℝ) T => (s, x)) := by fun_prop
      exact isCompact_univ.image hmap
    have hUnif := (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hconv)
      K hK
    rw [Metric.tendstoUniformlyOn_iff]
    rw [Metric.tendstoUniformlyOn_iff] at hUnif
    intro ε hε
    filter_upwards [hUnif ε hε] with n hn
    intro s hs
    let t : Set.Icc (0 : ℝ) T := ⟨s, ⟨hs.1.le, hs.2.le⟩⟩
    have hmem : (t, x) ∈ K := ⟨t, Set.mem_univ _, rfl⟩
    have hv :
        PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph.timeExtension
          (q (φ n)).1.2 x s = (q (φ n)).1.2 (t, x) := by
      simp [PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph.timeExtension,
        t, hs.1.le, hs.2.le]
    have hv' :
        PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph.timeExtension dt x s =
          dt (t, x) := by
      rw [PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph.timeExtension,
        dif_pos (show s ∈ Set.Icc (0 : ℝ) T from ⟨hs.1.le, hs.2.le⟩)]
    have hpair := hn (t, x) hmem
    have hcomponent : dist (tfun (t, x)) ((q (φ n)).1.2 (t, x)) < ε := by
      calc
        dist (tfun (t, x)) ((q (φ n)).1.2 (t, x)) =
            dist ((lim (t, x)).2) ((J (φ n) (t, x)).2) := rfl
        _ ≤ dist (lim (t, x)) (J (φ n) (t, x)) := by
          rw [Prod.dist_eq]
          exact le_max_right _ _
        _ < ε := hpair
    simpa [hv, hv', dt] using hcomponent

  have hvalueDeriv (t : Set.Icc (0 : ℝ) T) (x : E3) :
      HasFDerivAt (fun y : E3 => u (t, y)) (g (t, x)) x := by
    change HasFDerivAt (fun y : E3 => ufun (t, y)) (gfun (t, x)) x
    let s : Set E3 := Metric.ball x 1
    apply hasFDerivAt_of_tendstoUniformlyOn Metric.isOpen_ball
      (hgradUniform t x)
    · intro n y hy
      exact ((hqFull (φ n)).1.1 t).1 y
    · intro y hy
      exact hvaluePt t y
    · exact Metric.mem_ball_self (by norm_num)
  have hgradDeriv (t : Set.Icc (0 : ℝ) T) (x : E3) :
      HasFDerivAt (fun y : E3 => g (t, y)) (H (t, x)) x := by
    change HasFDerivAt (fun y : E3 => gfun (t, y)) (Hfun (t, x)) x
    apply hasFDerivAt_of_tendstoUniformlyOn Metric.isOpen_ball
      (hHUniformBall t x)
    · intro n y hy
      exact ((hqFull (φ n)).1.1 t).2 y
    · intro y hy
      exact hgradPt t y
    · exact Metric.mem_ball_self (by norm_num)
  have htimeDeriv (t : Set.Icc (0 : ℝ) T) (ht0 : 0 < (t : ℝ))
      (htT : (t : ℝ) < T) (x : E3) :
      HasDerivAt
        (PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph.timeExtension u x)
        (dt (t, x)) (t : ℝ) := by
    have hderiv : ∀ᶠ n in Filter.atTop, ∀ s ∈ Set.Ioo (0 : ℝ) T,
        HasDerivAt
          (PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph.timeExtension
            (q (φ n)).1.1.1.1 x)
          (PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph.timeExtension
            (q (φ n)).1.2 x s) s := by
      filter_upwards [Filter.Eventually.of_forall fun n => hqFull (φ n)] with n hn
      intro s hs
      let ts : Set.Icc (0 : ℝ) T := ⟨s, ⟨hs.1.le, hs.2.le⟩⟩
      have hd := hn.2.1 ts hs.1 hs.2 x
      have hv :
          PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph.timeExtension
            (q (φ n)).1.2 x s = (q (φ n)).1.2 (ts, x) := by
        simp [PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph.timeExtension,
          ts, hs.1.le, hs.2.le]
      simpa only [hv] using hd
    have hpoint : ∀ s ∈ Set.Ioo (0 : ℝ) T,
        Filter.Tendsto (fun n =>
          PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph.timeExtension
            (q (φ n)).1.1.1.1 x s) Filter.atTop
          (𝓝 (PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph.timeExtension
            u x s)) := by
      intro s hs
      let ts : Set.Icc (0 : ℝ) T := ⟨s, ⟨hs.1.le, hs.2.le⟩⟩
      have hv' :
          PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph.timeExtension
            u x s = u (ts, x) := by
        rw [PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph.timeExtension,
          dif_pos (show s ∈ Set.Icc (0 : ℝ) T from ⟨hs.1.le, hs.2.le⟩)]
      rw [hv']
      apply Filter.Tendsto.congr' (Filter.Eventually.of_forall fun n => ?_) (hvaluePt ts x)
      symm
      simp [PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph.timeExtension,
        ts, hs.1.le, hs.2.le]
    have htIoo : (t : ℝ) ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
    have hlim := hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo (htimeUniform x)
      hderiv hpoint htIoo
    simpa [PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph.timeExtension,
      Set.mem_Icc, ht0.le, htT.le] using hlim

  have hinitial : ∀ x : E3, u (⟨0, le_rfl, hT.le⟩, x) = 0 := by
    intro x
    have hzero : (fun y : E3 => z.1.1.1.1 (⟨0, le_rfl, hT.le⟩, y)) = fun _ => (0 : E6) := by
      funext y
      exact hinitialZ y
    have hconst : HasFDerivAt (fun y : E3 => z.1.1.1.1 (⟨0, le_rfl, hT.le⟩, y))
        (0 : E3 →L[ℝ] E6) x := by
      rw [hzero]
      exact hasFDerivAt_const (𝕜 := ℝ) (0 : E6) x
    have hgraph := (hspaceZ.1 ⟨0, le_rfl, hT.le⟩).1 x
    have heq := hgraph.fderiv.symm.trans hconst.fderiv
    change z.1.1.1.2.1 (⟨0, le_rfl, hT.le⟩, x) e = 0
    rw [heq]
    simp

  let dz : FullJet T := ((((u, (g, H)), incH), dt), incT)
  have hdzSpace : dz.1.1 ∈ PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicC2HolderSet T alpha := by
    change dz.1.1.1 ∈ spaceTimeC2JetSet T ∧
      ∀ p : PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.Pair T, dz.1.1.2 p =
        (PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
          (dz.1.1.1.2.2 p.1.1 - dz.1.1.1.2.2 p.1.2)
    constructor
    · intro t
      exact ⟨hvalueDeriv t, hgradDeriv t⟩
    · intro p
      rfl
  have hdzTime : (dz.1.1.1.1, dz.1.2) ∈ PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph.slabTimeDerivativeGraph T := by
    intro t ht0 htT x
    exact htimeDeriv t ht0 htT x
  have hdzTimeInc : ∀ p : PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.Pair T,
      dz.2 p = (PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
        (dz.1.2 p.1.1 - dz.1.2 p.1.2) := by
    intro p
    rfl
  have hdzMem : dz ∈ fullParabolicJetSet T alpha hT.le := by
    change dz.1.1 ∈ PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicC2HolderSet T alpha ∧
      (dz.1.1.1.1, dz.1.2) ∈ PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph.slabTimeDerivativeGraph T ∧
      (∀ p : PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.Pair T, dz.2 p = (PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
        (dz.1.2 p.1.1 - dz.1.2 p.1.2)) ∧
      ∀ x : E3, dz.1.1.1.1 (⟨0, le_rfl, hT.le⟩, x) = 0
    exact ⟨hdzSpace, hdzTime, hdzTimeInc, hinitial⟩
  have hdzNorm : ‖dz‖ ≤ C := by
    change ‖((((u, (g, H)), incH), dt), incT)‖ ≤ C
    apply (norm_prod_le_iff).2
    constructor
    · apply (norm_prod_le_iff).2
      constructor
      · apply (norm_prod_le_iff).2
        constructor
        · apply (norm_prod_le_iff).2
          constructor
          · exact (BoundedContinuousFunction.norm_le hC).2 hufunBound
          · apply (norm_prod_le_iff).2
            constructor
            · exact (BoundedContinuousFunction.norm_le hC).2 hgfunBound
            · exact (BoundedContinuousFunction.norm_le hC).2 hHbound
        · exact (BoundedContinuousFunction.norm_le hC).2 hincHbound
      · exact (BoundedContinuousFunction.norm_le hC).2 htbound
    · exact (BoundedContinuousFunction.norm_le hC).2 hincTbound
  exact ⟨dz, hdzMem, hdzNorm, fun p => rfl⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.FullJetSpatialDerivative
