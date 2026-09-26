import PoincareConjecture.ParallelImplementation.SpatialDifferenceBootstrap
import PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.FullJetSpatialC3Slices
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph
open PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet
open scoped Topology ContDiff BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Consume an actual full-jet difference bound, identify its derivative fields,
and upgrade each actual spatial time slice to C3. -/
theorem spatial_slices_contDiff_three_of_full_jet_differences
    (T alpha : ℝ) (hT : 0 ≤ T) (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (z : FullJet T)
    (hspace : z.1.1 ∈ parabolicC2HolderSet T alpha)
    (htime : (z.1.1.1.1,z.1.2) ∈ slabTimeDerivativeGraph T)
    (hinc : ∀ p : Pair T, z.2 p = (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
      (z.1.2 p.1.1 - z.1.2 p.1.2))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ (i : Fin 3) (h : ℝ), h ≠ 0 →
      ‖finiteSpatialDifferenceJet z i h‖ ≤ C) :
    ∀ t : Set.Icc (0 : ℝ) T, ContDiff ℝ 3 (fun x : E3 => z.1.1.1.1 (t,x)) :=
/- SWARM_PROOF_BEGIN -/
by
  intro t
  let w : E3 → EuclideanSpace ℝ (Fin 6) := fun x => z.1.1.1.1 (t, x)
  have hw : ContDiff ℝ 2 w := by
    change ContDiff ℝ 2 (fun x : E3 => z.1.1.1.1 (t, x))
    exact (spaceTime_C2_jet_complete T).2 z.1.1.1 hspace.1 t
  have hqdata (i : Fin 3) (h : ℝ) (hh : h ≠ 0) :=
    finite_spatial_difference_full_jet T alpha hT z hspace htime hinc i h hh
  have hbound' : ∀ (i : Fin 3) (h : ℝ), h ≠ 0 → ∀ x : E3,
      ‖SpatialDifferenceBootstrap.spatialQuotient w i h x‖ ≤ C ∧
      ‖fderiv ℝ (SpatialDifferenceBootstrap.spatialQuotient w i h) x‖ ≤ C ∧
      ‖fderiv ℝ (fderiv ℝ (SpatialDifferenceBootstrap.spatialQuotient w i h)) x‖ ≤ C := by
    intro i h hh x
    let q : FullJet T := finiteSpatialDifferenceJet z i h
    have hq := hqdata i h hh
    have hn : ‖q‖ ≤ C := by
      simpa [q] using hbound i h hh
    have hv : q.1.1.1.1 (t, x) = SpatialDifferenceBootstrap.spatialQuotient w i h x := by
      change h⁻¹ • (z.1.1.1.1 (t, x + h • PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient.spatialUnit i) -
        z.1.1.1.1 (t, x)) = _
      rfl
    have hvfun : (fun y : E3 => q.1.1.1.1 (t, y)) =
        SpatialDifferenceBootstrap.spatialQuotient w i h := by
      funext y
      change h⁻¹ • (z.1.1.1.1 (t, y + h • PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient.spatialUnit i) -
        z.1.1.1.1 (t, y)) = _
      rfl
    have hjet := hq.2.2.2.2.2.2.2.1
    have hjet' : q.1.1.1 ∈ spaceTimeC2JetSet T := hjet.1
    change (∀ t : Set.Icc (0 : ℝ) T,
      (∀ x : E3, HasFDerivAt (fun y => q.1.1.1.1 (t, y))
        (q.1.1.1.2.1 (t, x)) x) ∧
      (∀ x : E3, HasFDerivAt (fun y => q.1.1.1.2.1 (t, y))
        (q.1.1.1.2.2 (t, x)) x)) at hjet'
    have hfirst : ∀ y : E3,
        q.1.1.1.2.1 (t, y) = fderiv ℝ (SpatialDifferenceBootstrap.spatialQuotient w i h) y := by
      intro y
      have hd : HasFDerivAt (SpatialDifferenceBootstrap.spatialQuotient w i h)
          (q.1.1.1.2.1 (t, y)) y := by
        simpa only [hvfun] using (hjet' t).1 y
      exact hd.fderiv.symm
    have hv1 : (fun y : E3 => q.1.1.1.2.1 (t, y)) =
        fderiv ℝ (SpatialDifferenceBootstrap.spatialQuotient w i h) := funext hfirst
    have hsecond : ∀ y : E3,
        q.1.1.1.2.2 (t, y) =
          fderiv ℝ (fderiv ℝ (SpatialDifferenceBootstrap.spatialQuotient w i h)) y := by
      intro y
      have hd : HasFDerivAt (fderiv ℝ (SpatialDifferenceBootstrap.spatialQuotient w i h))
          (q.1.1.1.2.2 (t, y)) y := by
        simpa only [hv1] using (hjet' t).2 y
      exact hd.fderiv.symm
    have hnval : ‖q.1.1.1.1‖ ≤ ‖q‖ := by
      calc
        ‖q.1.1.1.1‖ ≤ ‖q.1.1.1‖ := by change _ ≤ max _ _; exact le_max_left _ _
        _ ≤ ‖q.1.1‖ := by change _ ≤ max _ _; exact le_max_left _ _
        _ ≤ ‖q.1‖ := by change _ ≤ max _ _; exact le_max_left _ _
        _ ≤ ‖q‖ := by change _ ≤ max _ _; exact le_max_left _ _
    have hngrad : ‖q.1.1.1.2.1‖ ≤ ‖q‖ := by
      calc
        ‖q.1.1.1.2.1‖ ≤ ‖q.1.1.1.2‖ := by change _ ≤ max _ _; exact le_max_left _ _
        _ ≤ ‖q.1.1.1‖ := by change _ ≤ max _ _; exact le_max_right _ _
        _ ≤ ‖q.1.1‖ := by change _ ≤ max _ _; exact le_max_left _ _
        _ ≤ ‖q.1‖ := by change _ ≤ max _ _; exact le_max_left _ _
        _ ≤ ‖q‖ := by change _ ≤ max _ _; exact le_max_left _ _
    have hnhess : ‖q.1.1.1.2.2‖ ≤ ‖q‖ := by
      calc
        ‖q.1.1.1.2.2‖ ≤ ‖q.1.1.1.2‖ := by change _ ≤ max _ _; exact le_max_right _ _
        _ ≤ ‖q.1.1.1‖ := by change _ ≤ max _ _; exact le_max_right _ _
        _ ≤ ‖q.1.1‖ := by change _ ≤ max _ _; exact le_max_left _ _
        _ ≤ ‖q.1‖ := by change _ ≤ max _ _; exact le_max_left _ _
        _ ≤ ‖q‖ := by change _ ≤ max _ _; exact le_max_left _ _
    refine ⟨?_, ?_, ?_⟩
    · rw [← hvfun]
      exact (q.1.1.1.1).norm_coe_le_norm (t, x) |>.trans (hnval.trans hn)
    · rw [← hfirst x]
      exact (q.1.1.1.2.1).norm_coe_le_norm (t, x) |>.trans (hngrad.trans hn)
    · rw [← hsecond x]
      exact (q.1.1.1.2.2).norm_coe_le_norm (t, x) |>.trans (hnhess.trans hn)
  have hholder' : ∀ (i : Fin 3) (h : ℝ), h ≠ 0 → ∀ x y : E3,
      ‖fderiv ℝ (fderiv ℝ (SpatialDifferenceBootstrap.spatialQuotient w i h)) x -
        fderiv ℝ (fderiv ℝ (SpatialDifferenceBootstrap.spatialQuotient w i h)) y‖ ≤
          C * ‖x-y‖ ^ alpha := by
    intro i h hh x y
    by_cases hxy : x = y
    · simp [hxy]
      positivity
    · let p : Pair T := ⟨((t, x), (t, y)), by
        intro heq
        have heq' := congrArg Prod.snd heq
        exact hxy heq'⟩
      let q : FullJet T := finiteSpatialDifferenceJet z i h
      have hq := hqdata i h hh
      have hn : ‖q‖ ≤ C := by
        simpa [q] using (hbound i h hh)
      have hjet := hq.2.2.2.2.2.2.2.1
      have hjet' : q.1.1.1 ∈ spaceTimeC2JetSet T := hjet.1
      change (∀ t : Set.Icc (0 : ℝ) T,
        (∀ x : E3, HasFDerivAt (fun y => q.1.1.1.1 (t, y))
          (q.1.1.1.2.1 (t, x)) x) ∧
        (∀ x : E3, HasFDerivAt (fun y => q.1.1.1.2.1 (t, y))
          (q.1.1.1.2.2 (t, x)) x)) at hjet'
      have hfirst : ∀ u : E3,
          q.1.1.1.2.1 (t, u) = fderiv ℝ (SpatialDifferenceBootstrap.spatialQuotient w i h) u := by
        intro u
        have hvfun : (fun v : E3 => q.1.1.1.1 (t, v)) =
            SpatialDifferenceBootstrap.spatialQuotient w i h := by
          funext v
          change h⁻¹ • (z.1.1.1.1 (t, v + h • PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient.spatialUnit i) -
            z.1.1.1.1 (t, v)) = _
          rfl
        have hd : HasFDerivAt (SpatialDifferenceBootstrap.spatialQuotient w i h)
            (q.1.1.1.2.1 (t, u)) u := by
          simpa only [hvfun] using (hjet' t).1 u
        exact hd.fderiv.symm
      have hsecond : ∀ u : E3,
          q.1.1.1.2.2 (t, u) =
            fderiv ℝ (fderiv ℝ (SpatialDifferenceBootstrap.spatialQuotient w i h)) u := by
        intro u
        have hv1 : (fun v : E3 => q.1.1.1.2.1 (t, v)) =
            fderiv ℝ (SpatialDifferenceBootstrap.spatialQuotient w i h) := funext hfirst
        have hd : HasFDerivAt (fderiv ℝ (SpatialDifferenceBootstrap.spatialQuotient w i h))
            (q.1.1.1.2.2 (t, u)) u := by
          simpa only [hv1] using (hjet' t).2 u
        exact hd.fderiv.symm
      have hqHolder : q.1.1 ∈ parabolicC2HolderSet T alpha := by
        exact hq.2.2.2.2.2.2.2.1
      have hincBound := (parabolic_C2_holder_jet_complete T alpha ha).2 q.1.1 hqHolder
        p.1.1 p.1.2
      have hqnorm : ‖q.1.1.2‖ ≤ ‖q‖ := by
        calc
          ‖q.1.1.2‖ ≤ ‖q.1.1‖ := by change _ ≤ max _ _; exact le_max_right _ _
          _ ≤ ‖q.1‖ := by change _ ≤ max _ _; exact le_max_left _ _
          _ ≤ ‖q‖ := by change _ ≤ max _ _; exact le_max_left _ _
      have hrho : parabolicRho p.1.1 p.1.2 = ‖x-y‖ := by
        simp [p, parabolicRho]
      have hboundInc : ‖q.1.1.1.2.2 (t, x) - q.1.1.1.2.2 (t, y)‖ ≤
          C * ‖x-y‖ ^ alpha := by
        have := hincBound
        rw [hrho] at this
        exact this.trans (mul_le_mul_of_nonneg_right (hqnorm.trans hn)
          (Real.rpow_nonneg (norm_nonneg _) _))
      simpa only [hsecond x, hsecond y] using hboundInc
  exact SpatialDifferenceBootstrap.contDiff_three_of_uniform_spatial_differences
    w hw C alpha hC ha ha1 hbound' hholder'
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.FullJetSpatialC3Slices
