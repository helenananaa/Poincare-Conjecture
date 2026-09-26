import PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient
import PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph
open PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient
open scoped Topology BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)

/-- Pull back a bounded continuous field along a continuous self-map. -/
def pullbackBCF {X : Type*} [TopologicalSpace X]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (τ : C(X, X)) (F : X →ᵇ V) : X →ᵇ V := F.compContinuous τ

def spatialShiftSlabMap {T : ℝ} (i : Fin 3) (h : ℝ) : C(Slab T, Slab T) where
  toFun := fun p => shiftPoint p i h
  continuous_toFun := by
    dsimp [shiftPoint]
    exact continuous_fst.prodMk (continuous_snd.add continuous_const)

theorem spatialShiftSlab_injective {T : ℝ} (i : Fin 3) (h : ℝ) :
    Function.Injective (fun p : Slab T => shiftPoint p i h) := by
  intro p q hpq
  change (p.1, p.2 + h • spatialUnit i) =
    (q.1, q.2 + h • spatialUnit i) at hpq
  have ht := congrArg (fun r : Slab T => r.1) hpq
  have hx := congrArg (fun r : Slab T => r.2) hpq
  apply Prod.ext
  · exact ht
  · exact add_right_cancel hx

def spatialShiftPairMap {T : ℝ} (i : Fin 3) (h : ℝ) : C(Pair T, Pair T) where
  toFun p := ⟨(shiftPoint p.1.1 i h, shiftPoint p.1.2 i h), by
    intro heq
    apply p.2
    exact spatialShiftSlab_injective i h heq⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact
      ((spatialShiftSlabMap i h).continuous.comp
        (continuous_fst.comp continuous_subtype_val)).prodMk
      ((spatialShiftSlabMap i h).continuous.comp
        (continuous_snd.comp continuous_subtype_val))

theorem spatialShiftPair_rho {T : ℝ} (i : Fin 3) (h : ℝ)
    (p : Pair T) :
    parabolicRho (shiftPoint p.1.1 i h) (shiftPoint p.1.2 i h) =
      parabolicRho p.1.1 p.1.2 := by
  simp [parabolicRho, shiftPoint, add_sub_add_right_eq_sub]

/-- The actual fixed-h difference of a bounded continuous field. -/
def spatialDifferenceBCF {X : Type*} [TopologicalSpace X]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (τ : C(X, X)) (F : X →ᵇ V) (h : ℝ) : X →ᵇ V :=
  h⁻¹ • (pullbackBCF τ F - F)

/-- Apply the same actual spatial quotient to every field in the parabolic jet,
including both normalized increment fields on the translated Pair. -/
def finiteSpatialDifferenceJet {T : ℝ} (z : FullJet T) (i : Fin 3) (h : ℝ) :
    FullJet T :=
  ((((spatialDifferenceBCF (spatialShiftSlabMap i h) z.1.1.1.1 h,
      (spatialDifferenceBCF (spatialShiftSlabMap i h) z.1.1.1.2.1 h,
       spatialDifferenceBCF (spatialShiftSlabMap i h) z.1.1.1.2.2 h)),
      spatialDifferenceBCF (spatialShiftPairMap i h) z.1.1.2 h),
    spatialDifferenceBCF (spatialShiftSlabMap i h) z.1.2 h),
    spatialDifferenceBCF (spatialShiftPairMap i h) z.2 h)

/-- Finite spatial difference quotients preserve the actual C2 spatial graph,
the actual time derivative graph, and both normalized increment identities.
The norm estimate is for this fixed nonzero h only; it records the expected
2/|h| loss and makes no uniform-in-h claim. -/
theorem finite_spatial_difference_full_jet
    (T alpha : ℝ) (hT : 0 ≤ T) (z : FullJet T)
    (hzSpace : z.1.1 ∈ parabolicC2HolderSet T alpha)
    (hzTime : (z.1.1.1.1, z.1.2) ∈ slabTimeDerivativeGraph T)
    (hzTimeInc : ∀ p : Pair T,
      z.2 p = (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
        (z.1.2 p.1.1 - z.1.2 p.1.2))
    (i : Fin 3) (h : ℝ) (hh : h ≠ 0) :
    let q := finiteSpatialDifferenceJet z i h
    (∀ p : Slab T,
      q.1.1.1.1 p = h⁻¹ •
        (z.1.1.1.1 (shiftPoint p i h) - z.1.1.1.1 p)) ∧
    (∀ p : Slab T,
      q.1.1.1.2.1 p = h⁻¹ •
        (z.1.1.1.2.1 (shiftPoint p i h) - z.1.1.1.2.1 p)) ∧
    (∀ p : Slab T,
      q.1.1.1.2.2 p = h⁻¹ •
        (z.1.1.1.2.2 (shiftPoint p i h) - z.1.1.1.2.2 p)) ∧
    (∀ p : Slab T,
      q.1.2 p = h⁻¹ • (z.1.2 (shiftPoint p i h) - z.1.2 p)) ∧
    (∀ p : Pair T,
      q.1.1.2 p = h⁻¹ •
        (z.1.1.2 (spatialShiftPairMap i h p) - z.1.1.2 p)) ∧
    (∀ p : Pair T,
      q.2 p = h⁻¹ • (z.2 (spatialShiftPairMap i h p) - z.2 p)) ∧
    (∀ p : Pair T,
      parabolicRho (spatialShiftPairMap i h p).1.1
        (spatialShiftPairMap i h p).1.2 = parabolicRho p.1.1 p.1.2) ∧
    q.1.1 ∈ parabolicC2HolderSet T alpha ∧
    (q.1.1.1.1, q.1.2) ∈ slabTimeDerivativeGraph T ∧
    (∀ p : Pair T,
      q.2 p = (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
        (q.1.2 p.1.1 - q.1.2 p.1.2)) ∧
    ‖q‖ ≤ (2 / |h|) * ‖z‖ :=
/- SWARM_PROOF_BEGIN -/
by
  dsimp only
  classical
  let q : FullJet T := finiteSpatialDifferenceJet z i h

  have slabSurj : Function.Surjective (fun p : Slab T => spatialShiftSlabMap i h p) := by
    intro p
    refine ⟨(p.1, p.2 - h • spatialUnit i), ?_⟩
    change shiftPoint (p.1, p.2 - h • spatialUnit i) i h = p
    simp [shiftPoint]

  have pairSurj : Function.Surjective (fun p : Pair T => spatialShiftPairMap i h p) := by
    intro p
    let a : Slab T := (p.1.1.1, p.1.1.2 - h • spatialUnit i)
    let b : Slab T := (p.1.2.1, p.1.2.2 - h • spatialUnit i)
    have hab : a ≠ b := by
      intro hab
      apply p.2
      have heq := congrArg (fun x : Slab T => shiftPoint x i h) hab
      simpa [a, b, shiftPoint] using heq
    refine ⟨⟨(a, b), hab⟩, ?_⟩
    apply Subtype.ext
    change (shiftPoint a i h, shiftPoint b i h) = p.1
    apply Prod.ext
    · simp [a, shiftPoint]
    · simp [b, shiftPoint]

  have pullbackAdd {X : Type} [TopologicalSpace X]
      {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (τ : C(X, X)) (F G : X →ᵇ V) :
      pullbackBCF τ (F + G) = pullbackBCF τ F + pullbackBCF τ G := by
    ext x
    rfl
  have pullbackSmul {X : Type} [TopologicalSpace X]
      {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (τ : C(X, X)) (r : ℝ) (F : X →ᵇ V) :
      pullbackBCF τ (r • F) = r • pullbackBCF τ F := by
    ext x
    rfl
  have slabPullbackAdd {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (F G : Slab T →ᵇ V) :
      pullbackBCF (spatialShiftSlabMap i h) (F + G) =
        pullbackBCF (spatialShiftSlabMap i h) F +
          pullbackBCF (spatialShiftSlabMap i h) G := by
    ext x
    rfl
  have pairPullbackAdd {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (F G : Pair T →ᵇ V) :
      pullbackBCF (spatialShiftPairMap i h) (F + G) =
        pullbackBCF (spatialShiftPairMap i h) F +
          pullbackBCF (spatialShiftPairMap i h) G := by
    ext x
    rfl
  have slabPullbackSmul {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (r : ℝ) (F : Slab T →ᵇ V) :
      pullbackBCF (spatialShiftSlabMap i h) (r • F) =
        r • pullbackBCF (spatialShiftSlabMap i h) F := by
    ext x
    rfl
  have pairPullbackSmul {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (r : ℝ) (F : Pair T →ᵇ V) :
      pullbackBCF (spatialShiftPairMap i h) (r • F) =
        r • pullbackBCF (spatialShiftPairMap i h) F := by
    ext x
    rfl
  have slabPullbackNorm {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (F : Slab T →ᵇ V) :
      ‖pullbackBCF (spatialShiftSlabMap i h) F‖ = ‖F‖ := by
    apply le_antisymm
    · exact BoundedContinuousFunction.norm_compContinuous_le F (spatialShiftSlabMap i h)
    · apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).2
      intro p
      obtain ⟨p', hp'⟩ := slabSurj p
      rw [← hp']
      exact (pullbackBCF (spatialShiftSlabMap i h) F).norm_coe_le_norm p'
  have pairPullbackNorm {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (F : Pair T →ᵇ V) :
      ‖pullbackBCF (spatialShiftPairMap i h) F‖ = ‖F‖ := by
    apply le_antisymm
    · exact BoundedContinuousFunction.norm_compContinuous_le F (spatialShiftPairMap i h)
    · apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).2
      intro p
      obtain ⟨p', hp'⟩ := pairSurj p
      rw [← hp']
      exact (pullbackBCF (spatialShiftPairMap i h) F).norm_coe_le_norm p'

  have differenceNorm {X : Type} [TopologicalSpace X]
      {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (τ : C(X, X))
      (hpn : ∀ F : X →ᵇ V, ‖pullbackBCF τ F‖ = ‖F‖) (F : X →ᵇ V) :
      ‖spatialDifferenceBCF τ F h‖ ≤ (2 / |h|) * ‖F‖ := by
    calc
      ‖spatialDifferenceBCF τ F h‖ = |h⁻¹| * ‖pullbackBCF τ F - F‖ := by
        simp [spatialDifferenceBCF, norm_smul, Real.norm_eq_abs]
      _ ≤ |h⁻¹| * (‖pullbackBCF τ F‖ + ‖F‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (abs_nonneg _)
      _ = (2 / |h|) * ‖F‖ := by
        rw [hpn F, abs_inv]
        ring

  have hspace : z.1.1 ∈ parabolicC2HolderSet T alpha := hzSpace
  have hspaceTime : z.1.1.1 ∈ spaceTimeC2JetSet T := hspace.1

  have hqSpaceTime : q.1.1.1 ∈ spaceTimeC2JetSet T := by
    change ∀ t : Set.Icc (0 : ℝ) T,
      (∀ x : E3, HasFDerivAt (fun y => q.1.1.1.1 (t, y))
        (q.1.1.1.2.1 (t, x)) x) ∧
      (∀ x : E3, HasFDerivAt (fun y => q.1.1.1.2.1 (t, y))
        (q.1.1.1.2.2 (t, x)) x)
    intro t
    have hjet := hspaceTime t
    constructor
    · intro x
      let c : E3 := h • spatialUnit i
      have htrans : HasFDerivAt (fun y : E3 => z.1.1.1.1 (t, y + c))
          (z.1.1.1.2.1 (t, x + c)) x := by
        have hinner : HasFDerivAt (fun y : E3 => c + y)
            (ContinuousLinearMap.id ℝ E3) x := by
          simpa using (hasFDerivAt_id x).const_add c
        have ht := HasFDerivAt.comp (f := fun y : E3 => c + y) (x := x)
          (hjet.1 (c + x)) hinner
        simpa [Function.comp_def, add_comm, ContinuousLinearMap.comp_id] using ht
      have hbase := hjet.1 x
      change HasFDerivAt
        (fun y : E3 => h⁻¹ • (z.1.1.1.1 (t, y + h • spatialUnit i) -
          z.1.1.1.1 (t, y)))
        (h⁻¹ • (z.1.1.1.2.1 (t, x + h • spatialUnit i) -
          z.1.1.1.2.1 (t, x))) x
      exact (htrans.sub hbase).const_smul h⁻¹
    · intro x
      let c : E3 := h • spatialUnit i
      have htrans : HasFDerivAt (fun y : E3 => z.1.1.1.2.1 (t, y + c))
          (z.1.1.1.2.2 (t, x + c)) x := by
        have hinner : HasFDerivAt (fun y : E3 => c + y)
            (ContinuousLinearMap.id ℝ E3) x := by
          simpa using (hasFDerivAt_id x).const_add c
        have ht := HasFDerivAt.comp (f := fun y : E3 => c + y) (x := x)
          (hjet.2 (c + x)) hinner
        simpa [Function.comp_def, add_comm, ContinuousLinearMap.comp_id] using ht
      have hbase := hjet.2 x
      change HasFDerivAt
        (fun y : E3 => h⁻¹ • (z.1.1.1.2.1 (t, y + h • spatialUnit i) -
          z.1.1.1.2.1 (t, y)))
        (h⁻¹ • (z.1.1.1.2.2 (t, x + h • spatialUnit i) -
          z.1.1.1.2.2 (t, x))) x
      exact (htrans.sub hbase).const_smul h⁻¹

  have hqHessianInc : ∀ p : Pair T,
      q.1.1.2 p = (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
        (q.1.1.1.2.2 p.1.1 - q.1.1.1.2.2 p.1.2) := by
    intro p
    have hshift := hspace.2 (spatialShiftPairMap i h p)
    have hshift' : z.1.1.2 (spatialShiftPairMap i h p) =
        (parabolicRho (shiftPoint p.1.1 i h) (shiftPoint p.1.2 i h) ^ alpha)⁻¹ •
          (z.1.1.1.2.2 (shiftPoint p.1.1 i h) -
            z.1.1.1.2.2 (shiftPoint p.1.2 i h)) := by
      simpa [spatialShiftPairMap] using hshift
    have hbase := hspace.2 p
    have hrho : parabolicRho (spatialShiftPairMap i h p).1.1
        (spatialShiftPairMap i h p).1.2 = parabolicRho p.1.1 p.1.2 := by
      simpa [spatialShiftPairMap] using spatialShiftPair_rho i h p
    have hrhoShift : parabolicRho (shiftPoint p.1.1 i h) (shiftPoint p.1.2 i h) =
        parabolicRho p.1.1 p.1.2 := spatialShiftPair_rho i h p
    change h⁻¹ • (z.1.1.2 (spatialShiftPairMap i h p) - z.1.1.2 p) =
      (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
        ((h⁻¹ • (z.1.1.1.2.2 (shiftPoint p.1.1 i h) -
            z.1.1.1.2.2 p.1.1)) -
          (h⁻¹ • (z.1.1.1.2.2 (shiftPoint p.1.2 i h) -
            z.1.1.1.2.2 p.1.2)))
    rw [hshift', hbase]
    have hrhoPow :
        (parabolicRho (shiftPoint p.1.1 i h) (shiftPoint p.1.2 i h) ^ alpha)⁻¹ =
          (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ := by
      rw [hrhoShift]
    rw [hrhoPow]
    simp only [smul_sub, smul_smul]
    have hcoeff : h⁻¹ * (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ =
        (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ * h⁻¹ := mul_comm _ _
    rw [hcoeff]
    abel_nf

  have hqHolder : q.1.1 ∈ parabolicC2HolderSet T alpha := by
    change q.1.1.1 ∈ spaceTimeC2JetSet T ∧
      ∀ p : Pair T, q.1.1.2 p =
        (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
          (q.1.1.1.2.2 p.1.1 - q.1.1.1.2.2 p.1.2)
    exact ⟨hqSpaceTime, hqHessianInc⟩

  have hqTime : (q.1.1.1.1, q.1.2) ∈ slabTimeDerivativeGraph T := by
    change ∀ t : Set.Icc (0 : ℝ) T, 0 < (t : ℝ) → (t : ℝ) < T → ∀ x : E3,
      HasDerivAt (timeExtension q.1.1.1.1 x) (q.1.2 (t, x)) (t : ℝ)
    intro t ht0 htT x
    let c : E3 := h • spatialUnit i
    have hshift := hzTime t ht0 htT (x + c)
    have hbase := hzTime t ht0 htT x
    have htimeEq : (fun s : ℝ => timeExtension q.1.1.1.1 x s) =
        fun s => h⁻¹ • (timeExtension z.1.1.1.1 (x + c) s -
          timeExtension z.1.1.1.1 x s) := by
      funext s
      by_cases hs : s ∈ Set.Icc (0 : ℝ) T
      · simp [timeExtension, q, finiteSpatialDifferenceJet,
          spatialDifferenceBCF, pullbackBCF, spatialShiftSlabMap, shiftPoint,
          c, hs]
      · simp [timeExtension, hs]
    have hdiff := (hshift.sub hbase).const_smul h⁻¹
    change HasDerivAt (fun s : ℝ => h⁻¹ •
      (timeExtension z.1.1.1.1 (x + c) s - timeExtension z.1.1.1.1 x s))
      (h⁻¹ • (z.1.2 (t, x + c) - z.1.2 (t, x))) (t : ℝ) at hdiff
    have hqTimeEval : q.1.2 (t, x) =
        h⁻¹ • (z.1.2 (t, x + c) - z.1.2 (t, x)) := by
      rfl
    change HasDerivAt (fun s : ℝ => timeExtension q.1.1.1.1 x s)
      (q.1.2 (t, x)) (t : ℝ)
    rw [htimeEq, hqTimeEval]
    exact hdiff

  have hqTimeInc : ∀ p : Pair T,
      q.2 p = (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
        (q.1.2 p.1.1 - q.1.2 p.1.2) := by
    intro p
    have hshift := hzTimeInc (spatialShiftPairMap i h p)
    have hshift' : z.2 (spatialShiftPairMap i h p) =
        (parabolicRho (shiftPoint p.1.1 i h) (shiftPoint p.1.2 i h) ^ alpha)⁻¹ •
          (z.1.2 (shiftPoint p.1.1 i h) - z.1.2 (shiftPoint p.1.2 i h)) := by
      simpa [spatialShiftPairMap] using hshift
    have hbase := hzTimeInc p
    have hrho : parabolicRho (spatialShiftPairMap i h p).1.1
        (spatialShiftPairMap i h p).1.2 = parabolicRho p.1.1 p.1.2 := by
      simpa [spatialShiftPairMap] using spatialShiftPair_rho i h p
    have hrhoShift : parabolicRho (shiftPoint p.1.1 i h) (shiftPoint p.1.2 i h) =
        parabolicRho p.1.1 p.1.2 := spatialShiftPair_rho i h p
    change h⁻¹ • (z.2 (spatialShiftPairMap i h p) - z.2 p) =
      (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
        ((h⁻¹ • (z.1.2 (shiftPoint p.1.1 i h) - z.1.2 p.1.1)) -
          (h⁻¹ • (z.1.2 (shiftPoint p.1.2 i h) - z.1.2 p.1.2)))
    rw [hshift', hbase]
    have hrhoPow :
        (parabolicRho (shiftPoint p.1.1 i h) (shiftPoint p.1.2 i h) ^ alpha)⁻¹ =
          (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ := by
      rw [hrhoShift]
    rw [hrhoPow]
    simp only [smul_sub, smul_smul]
    have hcoeff : h⁻¹ * (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ =
        (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ * h⁻¹ := mul_comm _ _
    rw [hcoeff]
    abel_nf

  have hvalNorm : ‖z.1.1.1.1‖ ≤ ‖z‖ := by
    calc
      ‖z.1.1.1.1‖ ≤ ‖z.1.1.1‖ := by
        change ‖z.1.1.1.1‖ ≤ max ‖z.1.1.1.1‖ ‖z.1.1.1.2‖
        exact le_max_left _ _
      _ ≤ ‖z.1.1‖ := by
        change ‖z.1.1.1‖ ≤ max ‖z.1.1.1‖ ‖z.1.1.2‖
        exact le_max_left _ _
      _ ≤ ‖z.1‖ := by
        change ‖z.1.1‖ ≤ max ‖z.1.1‖ ‖z.1.2‖
        exact le_max_left _ _
      _ ≤ ‖z‖ := by
        change ‖z.1‖ ≤ max ‖z.1‖ ‖z.2‖
        exact le_max_left _ _
  have hgradNorm : ‖z.1.1.1.2.1‖ ≤ ‖z‖ := by
    calc
      ‖z.1.1.1.2.1‖ ≤ ‖z.1.1.1.2‖ := by
        change ‖z.1.1.1.2.1‖ ≤ max ‖z.1.1.1.2.1‖ ‖z.1.1.1.2.2‖
        exact le_max_left _ _
      _ ≤ ‖z.1.1.1‖ := by
        change ‖z.1.1.1.2‖ ≤ max ‖z.1.1.1.1‖ ‖z.1.1.1.2‖
        exact le_max_right _ _
      _ ≤ ‖z.1.1‖ := by
        change ‖z.1.1.1‖ ≤ max ‖z.1.1.1‖ ‖z.1.1.2‖
        exact le_max_left _ _
      _ ≤ ‖z.1‖ := by
        change ‖z.1.1‖ ≤ max ‖z.1.1‖ ‖z.1.2‖
        exact le_max_left _ _
      _ ≤ ‖z‖ := by
        change ‖z.1‖ ≤ max ‖z.1‖ ‖z.2‖
        exact le_max_left _ _
  have hhessNorm : ‖z.1.1.1.2.2‖ ≤ ‖z‖ := by
    calc
      ‖z.1.1.1.2.2‖ ≤ ‖z.1.1.1.2‖ := by
        change ‖z.1.1.1.2.2‖ ≤ max ‖z.1.1.1.2.1‖ ‖z.1.1.1.2.2‖
        exact le_max_right _ _
      _ ≤ ‖z.1.1.1‖ := by
        change ‖z.1.1.1.2‖ ≤ max ‖z.1.1.1.1‖ ‖z.1.1.1.2‖
        exact le_max_right _ _
      _ ≤ ‖z.1.1‖ := by
        change ‖z.1.1.1‖ ≤ max ‖z.1.1.1‖ ‖z.1.1.2‖
        exact le_max_left _ _
      _ ≤ ‖z.1‖ := by
        change ‖z.1.1‖ ≤ max ‖z.1.1‖ ‖z.1.2‖
        exact le_max_left _ _
      _ ≤ ‖z‖ := by
        change ‖z.1‖ ≤ max ‖z.1‖ ‖z.2‖
        exact le_max_left _ _
  have hhessIncNorm : ‖z.1.1.2‖ ≤ ‖z‖ := by
    calc
      ‖z.1.1.2‖ ≤ ‖z.1.1‖ := by
        change ‖z.1.1.2‖ ≤ max ‖z.1.1.1‖ ‖z.1.1.2‖
        exact le_max_right _ _
      _ ≤ ‖z.1‖ := by
        change ‖z.1.1‖ ≤ max ‖z.1.1‖ ‖z.1.2‖
        exact le_max_left _ _
      _ ≤ ‖z‖ := by
        change ‖z.1‖ ≤ max ‖z.1‖ ‖z.2‖
        exact le_max_left _ _
  have htimeNorm : ‖z.1.2‖ ≤ ‖z‖ := by
    calc
      ‖z.1.2‖ ≤ ‖z.1‖ := by
        change ‖z.1.2‖ ≤ max ‖z.1.1‖ ‖z.1.2‖
        exact le_max_right _ _
      _ ≤ ‖z‖ := by
        change ‖z.1‖ ≤ max ‖z.1‖ ‖z.2‖
        exact le_max_left _ _
  have htimeIncNorm : ‖z.2‖ ≤ ‖z‖ := by
    change ‖z.2‖ ≤ max ‖z.1‖ ‖z.2‖
    exact le_max_right _ _
  have hqNorm : ‖q‖ ≤ (2 / |h|) * ‖z‖ := by
    apply (norm_prod_le_iff).2
    constructor
    · apply (norm_prod_le_iff).2
      constructor
      · apply (norm_prod_le_iff).2
        constructor
        · apply (norm_prod_le_iff).2
          constructor
          · exact (differenceNorm (spatialShiftSlabMap i h) slabPullbackNorm
              z.1.1.1.1).trans (mul_le_mul_of_nonneg_left hvalNorm (by positivity))
          · apply (norm_prod_le_iff).2
            constructor
            · exact (differenceNorm (spatialShiftSlabMap i h) slabPullbackNorm
                z.1.1.1.2.1).trans
                  (mul_le_mul_of_nonneg_left hgradNorm (by positivity))
            · exact (differenceNorm (spatialShiftSlabMap i h) slabPullbackNorm
                z.1.1.1.2.2).trans
                  (mul_le_mul_of_nonneg_left hhessNorm (by positivity))
        · exact (differenceNorm (spatialShiftPairMap i h) pairPullbackNorm
            z.1.1.2).trans
              (mul_le_mul_of_nonneg_left hhessIncNorm (by positivity))
      · exact (differenceNorm (spatialShiftSlabMap i h) slabPullbackNorm
          z.1.2).trans (mul_le_mul_of_nonneg_left htimeNorm (by positivity))
    · exact (differenceNorm (spatialShiftPairMap i h) pairPullbackNorm
        z.2).trans (mul_le_mul_of_nonneg_left htimeIncNorm (by positivity))

  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hqHolder, hqTime, hqTimeInc, hqNorm⟩
  · intro p
    rfl
  · intro p
    rfl
  · intro p
    rfl
  · intro p
    rfl
  · intro p
    rfl
  · intro p
    rfl
  · intro p
    change parabolicRho (shiftPoint p.1.1 i h) (shiftPoint p.1.2 i h) = _
    exact spatialShiftPair_rho i h p
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet
