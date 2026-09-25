import PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
import PoincareConjecture.ParallelImplementation.AffineRightInverseFixedPoint
import PoincareConjecture.ParallelImplementation.AffineInverseQuadraticGradient
import PoincareConjecture.ParallelImplementation.AffineInverseHessianNonlinearity
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SpatialHolderToParabolicForcing
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph
open scoped Topology BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance standardGroup0 : NormedAddCommGroup (E3 →L[ℝ] E3) := inferInstance
local instance standardSpace0 : NormedSpace ℝ (E3 →L[ℝ] E3) := inferInstance
local instance standardGroup1 : NormedAddCommGroup (E3 →L[ℝ] E6) := inferInstance
local instance standardSpace1 : NormedSpace ℝ (E3 →L[ℝ] E6) := inferInstance
local instance standardGroup2 : NormedAddCommGroup ((E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
local instance standardSpace2 : NormedSpace ℝ ((E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
local instance standardGroup3 : NormedAddCommGroup ((E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
local instance standardSpace3 : NormedSpace ℝ ((E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
local instance standardGroup4 : NormedAddCommGroup ((E3 →L[ℝ] E3) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
local instance standardSpace4 : NormedSpace ℝ ((E3 →L[ℝ] E3) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
local instance standardGroup5 : NormedAddCommGroup ((E3 →L[ℝ] E3) →L[ℝ] (E3 →L[ℝ] E3) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
local instance standardSpace5 : NormedSpace ℝ ((E3 →L[ℝ] E3) →L[ℝ] (E3 →L[ℝ] E3) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
theorem exists_stationary_parabolic_forcing
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T alpha K : ℝ) (ha : 0 < alpha) (hK : 0 ≤ K)
    (f : E3 →ᵇ V) (hf : ∀ x y : E3, ‖f x-f y‖ ≤ K*‖x-y‖^alpha) :

    ∃ F : ForcingJet V T, F ∈ forcingGraph V T alpha ∧
      (∀ p : Slab T, F.1 p=f p.2) ∧ ‖F‖ ≤ max ‖f‖ K :=
/- SWARM_PROOF_BEGIN -/
by
  let spatialProjection : ContinuousMap (Slab T) E3 :=
    ⟨fun p => p.2, continuous_snd⟩
  let g : Slab T →ᵇ V := f.compContinuous spatialProjection
  have hg (p : Slab T) : g p = f p.2 := rfl
  have hspatial (p q : Slab T) :
      ‖p.2-q.2‖ ≤ parabolicRho p q := by
    unfold parabolicRho
    exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have hholder : ∀ p q : Slab T,
      ‖g p-g q‖ ≤ K*parabolicRho p q^alpha := by
    intro p q
    rw [hg p, hg q]
    calc
      ‖f p.2-f q.2‖ ≤ K*‖p.2-q.2‖^alpha := hf p.2 q.2
      _ ≤ K*parabolicRho p q^alpha :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (norm_nonneg _) (hspatial p q) ha.le) hK

  have hpair : Continuous (fun p : Pair T => (p.1 : Slab T × Slab T)) :=
    continuous_subtype_val
  have hleft : Continuous (fun p : Pair T => p.1.1) :=
    continuous_fst.comp hpair
  have hright : Continuous (fun p : Pair T => p.1.2) :=
    continuous_snd.comp hpair
  have htime : Continuous (fun x : Slab T => (x.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hspace : Continuous (fun x : Slab T => x.2) :=
    continuous_snd
  have hrho_cont : Continuous (fun p : Pair T => parabolicRho p.1.1 p.1.2) := by
    unfold parabolicRho
    exact (continuous_norm.comp ((hspace.comp hleft).sub (hspace.comp hright))).add
      (Real.continuous_sqrt.comp
        (continuous_abs.comp ((htime.comp hleft).sub (htime.comp hright))))
  have hrho_pos (p : Pair T) : 0 < parabolicRho p.1.1 p.1.2 := by
    have htimeOrSpace :
        (p.1.1.1 : ℝ) ≠ (p.1.2.1 : ℝ) ∨ p.1.1.2 ≠ p.1.2.2 := by
      by_contra h
      push Not at h
      apply p.2
      apply Prod.ext
      · exact Subtype.ext h.1
      · exact h.2
    unfold parabolicRho
    rcases htimeOrSpace with ht | hx
    · exact add_pos_of_nonneg_of_pos (norm_nonneg _)
        (Real.sqrt_pos.2 (abs_pos.mpr (sub_ne_zero.mpr ht)))
    · exact add_pos_of_pos_of_nonneg
        (norm_pos_iff.mpr (sub_ne_zero.mpr hx)) (Real.sqrt_nonneg _)
  let rhoPow : Pair T → ℝ := fun p => parabolicRho p.1.1 p.1.2 ^ alpha
  have hrhoPow_cont : Continuous rhoPow := by
    apply continuous_iff_continuousAt.mpr
    intro p
    dsimp [rhoPow]
    exact hrho_cont.continuousAt.rpow_const
      (Or.inl (ne_of_gt (hrho_pos p)))
  have hrhoPow_pos (p : Pair T) : 0 < rhoPow p :=
    Real.rpow_pos_of_pos (hrho_pos p) alpha
  have hrhoPowInv_cont : Continuous (fun p : Pair T => (rhoPow p)⁻¹) :=
    hrhoPow_cont.inv₀ fun p => (hrhoPow_pos p).ne'
  let raw : Pair T → V := fun p =>
    (rhoPow p)⁻¹ • (g p.1.1-g p.1.2)
  have hraw_cont : Continuous raw := by
    dsimp [raw]
    exact continuous_smul.comp
      (hrhoPowInv_cont.prodMk ((g.continuous.comp hleft).sub
        (g.continuous.comp hright)))
  have hraw_bound : ∀ p : Pair T, ‖raw p‖ ≤ K := by
    intro p
    have hp := hrhoPow_pos p
    calc
      ‖raw p‖ = (rhoPow p)⁻¹ * ‖g p.1.1-g p.1.2‖ := by
        simp only [raw, norm_smul,
          Real.norm_of_nonneg (inv_nonneg.mpr hp.le)]
      _ ≤ (rhoPow p)⁻¹ * (K * rhoPow p) :=
        mul_le_mul_of_nonneg_left (hholder p.1.1 p.1.2)
          (inv_nonneg.mpr hp.le)
      _ = K * ((rhoPow p)⁻¹ * rhoPow p) := by ring
      _ = K := by rw [inv_mul_cancel₀ hp.ne']; simp
  let increments : Pair T →ᵇ V :=
    BoundedContinuousFunction.ofNormedAddCommGroup raw hraw_cont K hraw_bound
  have hincrements_norm : ‖increments‖ ≤ K := by
    change ‖BoundedContinuousFunction.ofNormedAddCommGroup
      raw hraw_cont K hraw_bound‖ ≤ K
    exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
      hraw_cont hK hraw_bound
  let F : ForcingJet V T := (g, increments)
  have hgraph : F ∈ forcingGraph V T alpha := by
    change ∀ p : Pair T, F.2 p =
      (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
        (F.1 p.1.1-F.1 p.1.2)
    intro p
    change raw p =
      (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
        (g p.1.1-g p.1.2)
    rfl
  have hvalue (p : Slab T) : F.1 p = f p.2 := hg p
  have hnorm_g : ‖g‖ ≤ ‖f‖ :=
    BoundedContinuousFunction.norm_compContinuous_le f spatialProjection
  refine ⟨F, hgraph, hvalue, ?_⟩
  change max ‖g‖ ‖increments‖ ≤ max ‖f‖ K
  exact max_le
    (hnorm_g.trans (le_max_left ‖f‖ K))
    (hincrements_norm.trans (le_max_right ‖f‖ K))
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SpatialHolderToParabolicForcing
