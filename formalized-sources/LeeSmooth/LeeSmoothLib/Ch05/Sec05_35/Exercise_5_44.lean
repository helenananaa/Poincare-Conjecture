import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import LeeSmoothLib.Ch05.Sec05_35.Definition_5_35_extra_2
import LeeSmoothLib.Ch05.Sec05_35.Proposition_5_41
-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff Topology
open Manifold
open Set Filter

noncomputable section

universe uM

section

variable {n : ℕ} [NeZero n]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
variable [IsManifold (𝓡∂ n) ∞ M]

/-- The derivative of a real-valued boundary defining function in the tangent direction `v`,
viewed in the canonical tangent-space model `ℝ`. -/
def boundary_defining_derivative {p : M} (f : M → ℝ) (v : TangentSpace (𝓡∂ n) p) : ℝ :=
  NormedSpace.fromTangentSpace (f p) (mfderiv (𝓡∂ n) 𝓘(ℝ) f p v)

/-- A boundary defining function at a boundary point vanishes exactly on the local boundary,
is positive on the local interior, is smooth at the chosen point, and has nonzero differential
there.  The regularity clause is essential: cubing a valid normal coordinate preserves its local
zero set and sign but makes its differential vanish at the boundary. -/
def IsBoundaryDefiningFunctionAt (p : M) (f : M → ℝ) : Prop :=
  p ∈ (𝓡∂ n).boundary M ∧
    ContMDiffAt (𝓡∂ n) 𝓘(ℝ) ∞ f p ∧
    (∃ v, boundary_defining_derivative (n := n) (p := p) f v ≠ 0) ∧
    ∃ s : Set M, IsOpen s ∧ p ∈ s ∧
      (∀ x ∈ s, x ∈ (𝓡∂ n).boundary M ↔ f x = 0) ∧
      ∀ x ∈ s, x ∈ (𝓡∂ n).interior M ↔ 0 < f x

local notation "BoundaryDefiningAt" => @IsBoundaryDefiningFunctionAt n _ M _ _

/-- A boundary defining function vanishes at the boundary point where it is defined. -/
-- Proof sketch: use the local characterization of the boundary as the zero set of the function and
-- evaluate it at the distinguished boundary point.
theorem IsBoundaryDefiningFunctionAt.eq_zero {p : M} {f : M → ℝ}
    (hf : BoundaryDefiningAt p f) : f p = 0 := by
  obtain ⟨hp, _, _, s, _, hps, hzero, _⟩ := hf
  exact (hzero p hps).1 hp

private lemma boundaryDefining_comp_isLocalMinOn
    {p : M} {f : M → ℝ} (hf : BoundaryDefiningAt p f)
    {J : Set ℝ} {γ : ℝ → M} (h0 : (0 : ℝ) ∈ J) (hγ0 : γ 0 = p)
    (hγ : ContMDiffOn 𝓘(ℝ) (𝓡∂ n) ∞ γ J) :
    IsLocalMinOn (f ∘ γ) J 0 := by
  obtain ⟨hp, _, _, s, hs, hps, hzero, hpos⟩ := hf
  have hcont : ContinuousWithinAt γ J 0 :=
    hγ.continuousOn.continuousWithinAt h0
  have hpre : γ ⁻¹' s ∈ 𝓝[J] (0 : ℝ) := by
    apply hcont.preimage_mem_nhdsWithin
    simpa [hγ0] using hs.mem_nhds hps
  have hf0 : f p = 0 := (hzero p hps).1 hp
  show ∀ᶠ t in 𝓝[J] (0 : ℝ), (f ∘ γ) 0 ≤ (f ∘ γ) t
  filter_upwards [hpre] with t ht
  rw [Function.comp_apply, Function.comp_apply, hγ0, hf0]
  rcases (𝓡∂ n).isInteriorPoint_or_isBoundaryPoint (γ t) with htInt | htBd
  · exact (hpos (γ t) ht).1 htInt |>.le
  · exact le_of_eq ((hzero (γ t) ht).1 htBd).symm

private lemma boundaryDefiningDerivative_eq_fderivWithin_comp
    {p : M} {f : M → ℝ} {J : Set ℝ} {γ : ℝ → M}
    {v : TangentSpace (𝓡∂ n) p}
    (hf : ContMDiffAt (𝓡∂ n) 𝓘(ℝ) ∞ f p)
    (h0 : (0 : ℝ) ∈ J) (hJ : UniqueMDiffWithinAt 𝓘(ℝ) J 0)
    (hγ : ContMDiffOn 𝓘(ℝ) (𝓡∂ n) ∞ γ J) (hγ0 : γ 0 = p)
    (hγv : hγ0 ▸ curve_velocityWithin (𝓡∂ n) γ J 0 = v) :
    boundary_defining_derivative f v = (fderivWithin ℝ (f ∘ γ) J 0) 1 := by
  subst p
  have hcomp := composite_curve_velocity (F := f) (γ := γ) hJ
    (hf.mdifferentiableAt (by simp))
    (hγ.mdifferentiableOn (by simp) 0 h0)
  unfold boundary_defining_derivative
  rw [← hγv, ← hcomp]
  unfold curve_velocityWithin
  rw [mfderivWithin_eq_fderivWithin]
  unfold NormedSpace.fromTangentSpace
  rfl

private lemma boundaryDefiningDerivative_nonneg_of_inwardCurve
    {p : M} {f : M → ℝ} (hf : BoundaryDefiningAt p f)
    {v : TangentSpace (𝓡∂ n) p} (hv : HasInwardCurveVelocity p v) :
    0 ≤ boundary_defining_derivative f v := by
  rcases hv with ⟨_, ε, hε, γ, hγ, hγ0, hγv⟩
  have hmin := boundaryDefining_comp_isLocalMinOn hf
    (show (0 : ℝ) ∈ Ico 0 ε by exact ⟨le_rfl, hε⟩) hγ0 hγ
  have hnonneg := hmin.fderivWithin_nonneg (one_mem_posTangentConeAt_Ico hε)
  rw [boundaryDefiningDerivative_eq_fderivWithin_comp hf.2.1
    (show (0 : ℝ) ∈ Ico 0 ε by exact ⟨le_rfl, hε⟩)
    (uniqueMDiffWithinAt_Ico_zero hε) hγ hγ0 hγv]
  exact hnonneg

private lemma boundaryDefiningDerivative_nonpos_of_outwardCurve
    {p : M} {f : M → ℝ} (hf : BoundaryDefiningAt p f)
    {v : TangentSpace (𝓡∂ n) p} (hv : HasOutwardCurveVelocity p v) :
    boundary_defining_derivative f v ≤ 0 := by
  rcases hv with ⟨_, ε, hε, γ, hγ, hγ0, hγv⟩
  have hmin := boundaryDefining_comp_isLocalMinOn hf
    (show (0 : ℝ) ∈ Ioc (-ε) 0 by exact ⟨neg_lt_zero.mpr hε, le_rfl⟩) hγ0 hγ
  have hnonneg := hmin.fderivWithin_nonneg (neg_one_mem_posTangentConeAt_Ioc hε)
  have hneg :
      (fderivWithin ℝ (f ∘ γ) (Ioc (-ε) 0) 0) (-1) =
        -(fderivWithin ℝ (f ∘ γ) (Ioc (-ε) 0) 0) 1 := by
    simpa only [map_neg, map_one]
  rw [hneg] at hnonneg
  rw [boundaryDefiningDerivative_eq_fderivWithin_comp hf.2.1
    (show (0 : ℝ) ∈ Ioc (-ε) 0 by exact ⟨neg_lt_zero.mpr hε, le_rfl⟩)
    (uniqueMDiffWithinAt_Ioc_zero hε) hγ hγ0 hγv]
  linarith

private lemma boundaryDefiningDerivative_eq_zero_of_boundaryTangent
    {p : M} {f : M → ℝ} (hf : BoundaryDefiningAt p f)
    {v : TangentSpace (𝓡∂ n) p} (hv : IsBoundaryTangentVector p v) :
    boundary_defining_derivative f v = 0 := by
  rcases hv with ⟨ε, hε, γ, hγ, _, hγ0, hγv⟩
  have hmin := boundaryDefining_comp_isLocalMinOn hf
    (show (0 : ℝ) ∈ Ioo (-ε) ε by exact ⟨neg_lt_zero.mpr hε, hε⟩) hγ0 hγ
  have hzero := hmin.fderivWithin_eq_zero
    (one_mem_posTangentConeAt_Ioo hε) (neg_one_mem_posTangentConeAt_Ioo hε)
  rw [boundaryDefiningDerivative_eq_fderivWithin_comp hf.2.1
    (show (0 : ℝ) ∈ Ioo (-ε) ε by exact ⟨neg_lt_zero.mpr hε, hε⟩)
    (isOpen_Ioo.uniqueMDiffWithinAt ⟨neg_lt_zero.mpr hε, hε⟩) hγ hγ0 hγv]
  exact hzero

private lemma exists_pos_boundaryDefiningDerivative_eq_mul_boundaryCoordinate
    {p : M} {f : M → ℝ} (hf : BoundaryDefiningAt p f) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : TangentSpace (𝓡∂ n) p,
      boundary_defining_derivative f v =
        c * boundary_coordinate_component (chartAt (EuclideanHalfSpace n) p) p v := by
  let e := chartAt (EuclideanHalfSpace n) p
  have he : e ∈ atlas (EuclideanHalfSpace n) M := chart_mem_atlas _ p
  have hpe : p ∈ e.source := mem_chart_source _ p
  let C : TangentSpace (𝓡∂ n) p →L[ℝ] ℝ :=
    (EuclideanSpace.proj (0 : Fin n)).comp
      (mfderiv (𝓡∂ n) (𝓡 n) (e.extend (𝓡∂ n)) p)
  let L : TangentSpace (𝓡∂ n) p →L[ℝ] ℝ :=
    (NormedSpace.fromTangentSpace (f p)).toContinuousLinearMap.comp
      (mfderiv (𝓡∂ n) 𝓘(ℝ) f p)
  have hC (v : TangentSpace (𝓡∂ n) p) :
      C v = boundary_coordinate_component e p v := rfl
  have hL (v : TangentSpace (𝓡∂ n) p) :
      L v = boundary_defining_derivative f v := rfl
  obtain ⟨z, hz⟩ := hf.2.2.1
  have hzcoord : boundary_coordinate_component e p z ≠ 0 := by
    intro hzcoord
    have hztan : IsBoundaryTangentVector p z :=
      (tangent_to_boundary_iff_boundary_coordinate_component_eq_zero hf.1 he hpe).2 hzcoord
    exact hz (boundaryDefiningDerivative_eq_zero_of_boundaryTangent hf hztan)
  let c : ℝ := boundary_defining_derivative f z / boundary_coordinate_component e p z
  have hcpos : 0 < c := by
    rcases boundary_vector_trichotomy hf.1 he hpe (v := z) with hztan | hzin | hzout
    · exact (hz (boundaryDefiningDerivative_eq_zero_of_boundaryTangent hf hztan)).elim
    · have hzderiv_pos : 0 < boundary_defining_derivative f z :=
        lt_of_le_of_ne
          (boundaryDefiningDerivative_nonneg_of_inwardCurve hf hzin.hasInwardCurveVelocity)
          hz.symm
      have hzcoord_pos : 0 < boundary_coordinate_component e p z :=
        (inward_pointing_iff_boundary_coordinate_component_pos hf.1 he hpe).1 hzin
      exact div_pos hzderiv_pos hzcoord_pos
    · have hzderiv_neg : boundary_defining_derivative f z < 0 :=
        lt_of_le_of_ne
          (boundaryDefiningDerivative_nonpos_of_outwardCurve hf hzout.hasOutwardCurveVelocity) hz
      have hzcoord_neg : boundary_coordinate_component e p z < 0 :=
        (outward_pointing_iff_boundary_coordinate_component_neg hf.1 he hpe).1 hzout
      exact div_pos_of_neg_of_neg hzderiv_neg hzcoord_neg
  refine ⟨c, hcpos, ?_⟩
  intro v
  let u : TangentSpace (𝓡∂ n) p := C z • v - C v • z
  have hucoord : boundary_coordinate_component e p u = 0 := by
    rw [← hC]
    simp [u]
    <;> ring
  have hutan : IsBoundaryTangentVector p u :=
    (tangent_to_boundary_iff_boundary_coordinate_component_eq_zero hf.1 he hpe).2 hucoord
  have huderiv : boundary_defining_derivative f u = 0 :=
    boundaryDefiningDerivative_eq_zero_of_boundaryTangent hf hutan
  have huderiv' :
      boundary_coordinate_component e p z * boundary_defining_derivative f v -
        boundary_coordinate_component e p v * boundary_defining_derivative f z = 0 := by
    have huderivL : L u = 0 := by simpa only [hL] using huderiv
    have huL : L u = C z • L v - C v • L z := by simp [u]
    rw [huL, hC z, hC v, hL v, hL z] at huderivL
    simpa only [smul_eq_mul] using huderivL
  dsimp [c]
  field_simp
  nlinarith

/-- Exercise 5.44 (1): a tangent vector at a boundary point is inward-pointing exactly when the
boundary defining function has positive derivative on that vector. -/
-- Proof sketch: pass to a boundary chart in which the manifold is identified with a half-space and
-- the boundary defining function is a local defining equation for the boundary. In these
-- coordinates, both sides measure the sign of the same normal component.
theorem inwardPointing_iff_boundaryDefiningDerivative_pos {p : M} {f : M → ℝ}
    (hf : BoundaryDefiningAt p f) (v : TangentSpace (𝓡∂ n) p) :
    IsInwardPointing p v ↔ 0 < boundary_defining_derivative f v := by
  obtain ⟨c, hc, hderiv⟩ :=
    exists_pos_boundaryDefiningDerivative_eq_mul_boundaryCoordinate hf
  let e := chartAt (EuclideanHalfSpace n) p
  have he : e ∈ atlas (EuclideanHalfSpace n) M := chart_mem_atlas _ p
  have hpe : p ∈ e.source := mem_chart_source _ p
  rw [hderiv v]
  constructor
  · intro hv
    exact mul_pos hc
      ((inward_pointing_iff_boundary_coordinate_component_pos hf.1 he hpe).1 hv)
  · intro hv
    apply (inward_pointing_iff_boundary_coordinate_component_pos hf.1 he hpe).2
    nlinarith

/-- Exercise 5.44 (2): a tangent vector at a boundary point is outward-pointing exactly when the
boundary defining function has negative derivative on that vector. -/
-- Proof sketch: use the same boundary-chart comparison as in the inward-pointing case; the normal
-- derivative changes sign precisely when the normal component of the tangent vector is negative.
theorem outwardPointing_iff_boundaryDefiningDerivative_neg {p : M} {f : M → ℝ}
    (hf : BoundaryDefiningAt p f) (v : TangentSpace (𝓡∂ n) p) :
    IsOutwardPointing p v ↔ boundary_defining_derivative f v < 0 := by
  obtain ⟨c, hc, hderiv⟩ :=
    exists_pos_boundaryDefiningDerivative_eq_mul_boundaryCoordinate hf
  let e := chartAt (EuclideanHalfSpace n) p
  have he : e ∈ atlas (EuclideanHalfSpace n) M := chart_mem_atlas _ p
  have hpe : p ∈ e.source := mem_chart_source _ p
  rw [hderiv v]
  constructor
  · intro hv
    exact mul_neg_of_pos_of_neg hc
      ((outward_pointing_iff_boundary_coordinate_component_neg hf.1 he hpe).1 hv)
  · intro hv
    apply (outward_pointing_iff_boundary_coordinate_component_neg hf.1 he hpe).2
    nlinarith

/-- Exercise 5.44 (3): a tangent vector at a boundary point is tangent to the boundary exactly when
the boundary defining function has zero derivative on that vector. -/
-- Proof sketch: in boundary coordinates, both conditions say that the normal component of the
-- tangent vector vanishes, so the derivative of the defining function in that direction is zero.
theorem tangentToBoundary_iff_boundaryDefiningDerivative_eq_zero {p : M} {f : M → ℝ}
    (hf : BoundaryDefiningAt p f) (v : TangentSpace (𝓡∂ n) p) :
    IsBoundaryTangentVector p v ↔
      boundary_defining_derivative f v = 0 := by
  obtain ⟨c, hc, hderiv⟩ :=
    exists_pos_boundaryDefiningDerivative_eq_mul_boundaryCoordinate hf
  let e := chartAt (EuclideanHalfSpace n) p
  have he : e ∈ atlas (EuclideanHalfSpace n) M := chart_mem_atlas _ p
  have hpe : p ∈ e.source := mem_chart_source _ p
  rw [hderiv v]
  constructor
  · intro hv
    rw [(tangent_to_boundary_iff_boundary_coordinate_component_eq_zero hf.1 he hpe).1 hv,
      mul_zero]
  · intro hv
    apply (tangent_to_boundary_iff_boundary_coordinate_component_eq_zero hf.1 he hpe).2
    nlinarith

end
