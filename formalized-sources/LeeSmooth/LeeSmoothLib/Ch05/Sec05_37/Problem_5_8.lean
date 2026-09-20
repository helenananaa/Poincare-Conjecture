import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Instances.Sphere
import LeeSmoothLib.Ch01.Sec01.Definition_1_extra_1
import LeeSmoothLib.Ch01.Sec01_03.Definition_1_3_extra_1
import LeeSmoothLib.Ch01.Sec01_06.Definition_1_6_extra_2
import LeeSmoothLib.Ch02.Sec02_12.Problem_2_4
import LeeSmoothLib.Ch05.Sec05_29.Theorem_5_8.Common
import LeeSmoothLib.Ch05.Sec05_36.Definition_5_36_extra_2
import LeeSmoothLib.Ch05.Sec05_36.Definition_5_36_extra_4
import LeeSmoothLib.Ch05.Sec05_36.Proposition_5_46
import LeeSmoothLib.Ch05.Sec05_36.Theorem_5_51
-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped ContDiff Manifold Topology

noncomputable section

universe uE uM

-- Semantic recall note: no `lean_leansearch` tool was available in this environment; local
-- repository and mathlib inspection verified the standard sphere manifold instance from
-- `Mathlib.Geometry.Manifold.Instances.Sphere`, with ambient dimension written as `Fin (n + 1)`.

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M]

local notation "dimM" => Module.finrank ℝ E
local notation "boundarySphere" =>
  Metric.sphere (0 : EuclideanSpace ℝ (Fin ((dimM - 1) + 1))) 1

/-- Helper for Problem 5-8: an ordered basis packages the ambient continuous linear identification
between `ℝ^dimM` and `E`. -/
noncomputable def basis_model_continuousLinearEquiv
    (b : Module.Basis (Fin dimM) ℝ E) :
    EuclideanSpace ℝ (Fin dimM) ≃L[ℝ] E :=
  let e : E ≃ₗ[ℝ] Fin dimM → ℝ := b.equivFun
  (EuclideanSpace.equiv (Fin dimM) ℝ).trans e.symm.toContinuousLinearEquiv

/-- Helper for Problem 5-8: an ordered basis gives a fixed diffeomorphism from `ℝ^dimM` to the
ambient model space `E`. -/
noncomputable def basis_model_diffeomorph
    (b : Module.Basis (Fin dimM) ℝ E) :
    EuclideanSpace ℝ (Fin dimM) ≃ₘ[ℝ] E :=
  (basis_model_continuousLinearEquiv b).toDiffeomorph

/-- Helper for Problem 5-8: transport the ambient charted-space structure on `M` from model space
`E` to the Euclidean model `ℝ^dimM` using a fixed basis chart on `E`. -/
noncomputable abbrev basis_model_chartedSpace
    (b : Module.Basis (Fin dimM) ℝ E) :
    ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M := by
  let eModel : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin dimM)) :=
    (basis_model_diffeomorph b).symm.toHomeomorph.toOpenPartialHomeomorph
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin dimM)) E :=
    eModel.singletonChartedSpace (by
      ext x
      simp [eModel])
  exact ChartedSpace.comp (EuclideanSpace ℝ (Fin dimM)) E M

/-- Helper for Problem 5-8: conjugating an `E`-smooth chart transition by the fixed basis model
change produces a Euclidean-smooth transition. -/
lemma basis_model_transition_mem_contDiffGroupoid
    (b : Module.Basis (Fin dimM) ℝ E)
    {e : OpenPartialHomeomorph E E}
    (he : e ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (modelWithCornersSelf ℝ E)) :
    let eModel : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin dimM)) :=
      (basis_model_diffeomorph b).symm.toHomeomorph.toOpenPartialHomeomorph
    (eModel.symm.trans e).trans eModel ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 dimM) := by
  let eModel : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin dimM)) :=
    (basis_model_diffeomorph b).symm.toHomeomorph.toOpenPartialHomeomorph
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid] at he ⊢
  have he_left : ContDiffOn ℝ (⊤ : WithTop ℕ∞) (e : E → E) e.source := by
    simpa using he.1
  have he_right : ContDiffOn ℝ (⊤ : WithTop ℕ∞) (e.symm : E → E) e.target := by
    simpa using he.2
  have heModel_contDiff :
      ContDiff ℝ (⊤ : WithTop ℕ∞) (eModel : E → EuclideanSpace ℝ (Fin dimM)) := by
    -- The basis chart is the inverse of a fixed continuous linear equivalence `ℝ^n ≃L E`.
    simpa [eModel, basis_model_diffeomorph, basis_model_continuousLinearEquiv] using
      (basis_model_continuousLinearEquiv b).symm.toContinuousLinearMap.contDiff
  have heModel_symm_contDiff :
      ContDiff ℝ (⊤ : WithTop ℕ∞) (eModel.symm : EuclideanSpace ℝ (Fin dimM) → E) := by
    -- Its inverse is the original continuous linear equivalence `ℝ^n ≃L E`.
    simpa [eModel, basis_model_diffeomorph, basis_model_continuousLinearEquiv] using
      (basis_model_continuousLinearEquiv b).toContinuousLinearMap.contDiff
  have hsource :
      eModel.symm ⁻¹' e.source = ((eModel.symm.trans e).trans eModel).source := by
    -- The global basis chart has full source and target, so the transported source is just the
    -- preimage of the old source under `eModel.symm`.
    ext x
    simp [eModel]
  have htarget :
      eModel.symm ⁻¹' e.target = ((eModel.symm.trans e).trans eModel).target := by
    -- The same simplification holds for the transported target.
    ext x
    simp [eModel]
  constructor
  · -- Compose the original `E`-smooth transition with the fixed Euclidean coordinate changes.
    have hmid :
        ContDiffOn ℝ (⊤ : WithTop ℕ∞)
          (fun x : EuclideanSpace ℝ (Fin dimM) ↦ e (eModel.symm x))
          (eModel.symm ⁻¹' e.source) := by
      refine he_left.comp heModel_symm_contDiff.contDiffOn ?_
      intro x hx
      simpa using hx
    have hfinal :
        ContDiffOn ℝ (⊤ : WithTop ℕ∞)
          (fun x : EuclideanSpace ℝ (Fin dimM) ↦ eModel (e (eModel.symm x)))
          (eModel.symm ⁻¹' e.source) := by
      refine (heModel_contDiff.contDiffOn : ContDiffOn ℝ (⊤ : WithTop ℕ∞) eModel Set.univ).comp
        hmid ?_
      intro x hx
      simp [Set.mem_univ, eModel]
    simpa [hsource, eModel, Function.comp, OpenPartialHomeomorph.trans_source] using! hfinal
  · -- The same conjugation argument applies to the inverse transition.
    have hmid :
        ContDiffOn ℝ (⊤ : WithTop ℕ∞)
          (fun x : EuclideanSpace ℝ (Fin dimM) ↦ e.symm (eModel.symm x))
          (eModel.symm ⁻¹' e.target) := by
      refine he_right.comp heModel_symm_contDiff.contDiffOn ?_
      intro x hx
      simpa using hx
    have hfinal :
        ContDiffOn ℝ (⊤ : WithTop ℕ∞)
          (fun x : EuclideanSpace ℝ (Fin dimM) ↦ eModel (e.symm (eModel.symm x)))
          (eModel.symm ⁻¹' e.target) := by
      refine (heModel_contDiff.contDiffOn : ContDiffOn ℝ (⊤ : WithTop ℕ∞) eModel Set.univ).comp
        hmid ?_
      intro x hx
      simp [Set.mem_univ, eModel]
    simpa [htarget, eModel, Function.comp, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc] using!
      hfinal

/-- Helper for Problem 5-8: after transporting the ambient charts through a basis of `E`, the
manifold `M` carries the expected Euclidean smooth structure. -/
lemma basis_model_isManifold
    (b : Module.Basis (Fin dimM) ℝ E) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M :=
      basis_model_chartedSpace b
    IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) M := by
  let eModel : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin dimM)) :=
    (basis_model_diffeomorph b).symm.toHomeomorph.toOpenPartialHomeomorph
  have heModel_source : eModel.source = Set.univ := by
    -- The basis model change is global because it comes from a diffeomorphism.
    ext x
    simp [eModel]
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin dimM)) E :=
    eModel.singletonChartedSpace heModel_source
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M :=
    basis_model_chartedSpace b
  have hGroupoid : HasGroupoid M (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 dimM)) := by
    refine ⟨?_⟩
    rintro _ _ ⟨f, hf, c, hc, rfl⟩ ⟨f', hf', c', hc', rfl⟩
    have hcEq : c = eModel := by
      simpa [eModel] using
        eModel.singletonChartedSpace_mem_atlas_eq (h := heModel_source) c hc
    have hc'Eq : c' = eModel := by
      simpa [eModel] using
        eModel.singletonChartedSpace_mem_atlas_eq (h := heModel_source) c' hc'
    subst c
    subst c'
    -- Every transported transition is the old smooth transition conjugated by the fixed basis
    -- chart.
    have hcompat_old :
        f.symm.trans f' ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (modelWithCornersSelf ℝ E) :=
      HasGroupoid.compatible hf hf'
    simpa [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc, eModel] using
      basis_model_transition_mem_contDiffGroupoid b hcompat_old
  let _ : HasGroupoid M (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 dimM)) := hGroupoid
  exact IsManifold.mk' (𝓡 dimM) (⊤ : WithTop ℕ∞) M

/-- Helper for Problem 5-8: the preferred transported chart is the original preferred chart
followed by the global basis coordinate map. -/
lemma basis_model_chartAt_eq
    (b : Module.Basis (Fin dimM) ℝ E) (x : M) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M :=
      basis_model_chartedSpace b
    let eModel : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin dimM)) :=
      (basis_model_diffeomorph b).symm.toHomeomorph.toOpenPartialHomeomorph
    chartAt (EuclideanSpace ℝ (Fin dimM)) x = (chartAt E x).trans eModel := by
  rfl

/-- Helper for Problem 5-8: the identity from the transported Euclidean model back to the original
`E`-model is smooth. -/
lemma basis_model_identity_contMDiff_to_original
    (b : Module.Basis (Fin dimM) ℝ E) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M :=
      basis_model_chartedSpace b
    let _ : IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) M :=
      basis_model_isManifold b
    ContMDiff (𝓡 dimM) (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞)
      (id : M → M) := by
  let V := EuclideanSpace ℝ (Fin dimM)
  let _ : ChartedSpace V M := basis_model_chartedSpace b
  let _ : IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) M := basis_model_isManifold b
  rw [contMDiff_iff_target]
  refine ⟨continuous_id, ?_⟩
  intro y
  have hnew :
      ContMDiffOn (𝓡 dimM) (𝓡 dimM) (⊤ : WithTop ℕ∞)
        (extChartAt (𝓡 dimM) y) (chartAt V y).source :=
    contMDiffOn_extChartAt
  have hcomp :=
    (basis_model_continuousLinearEquiv b).toContinuousLinearMap.contDiff.contMDiff.comp_contMDiffOn
      hnew
  refine hcomp.congr ?_
  intro x hx
  simp [Function.comp, basis_model_chartAt_eq (M := M) b y,
    basis_model_diffeomorph, basis_model_continuousLinearEquiv]

/-- Helper for Problem 5-8: the identity from the original `E`-model into the transported
Euclidean basis model is smooth. -/
lemma basis_model_identity_contMDiff_from_original
    (b : Module.Basis (Fin dimM) ℝ E) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M :=
      basis_model_chartedSpace b
    let _ : IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) M :=
      basis_model_isManifold b
    ContMDiff (modelWithCornersSelf ℝ E) (𝓡 dimM) (⊤ : WithTop ℕ∞)
      (id : M → M) := by
  let V := EuclideanSpace ℝ (Fin dimM)
  let _ : ChartedSpace V M := basis_model_chartedSpace b
  let _ : IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) M := basis_model_isManifold b
  rw [contMDiff_iff_target]
  refine ⟨continuous_id, ?_⟩
  intro y
  have hold :
      ContMDiffOn (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E)
        (⊤ : WithTop ℕ∞) (extChartAt (modelWithCornersSelf ℝ E) y)
        (chartAt E y).source :=
    contMDiffOn_extChartAt
  have hcomp :=
    (basis_model_continuousLinearEquiv b).symm.toContinuousLinearMap.contDiff.contMDiff.comp_contMDiffOn
      hold
  simpa [Function.comp, basis_model_chartAt_eq (M := M) b y,
    basis_model_diffeomorph, basis_model_continuousLinearEquiv] using hcomp

/-- Helper for Problem 5-8: an ambient smooth chart for the original `E`-model remains a maximal
atlas chart after composing with the fixed basis identification to `ℝ^dimM`. -/
lemma basis_model_chart_mem_maximalAtlas
    (b : Module.Basis (Fin dimM) ℝ E)
    {chart : OpenPartialHomeomorph M E}
    (hchart :
      chart ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M :=
      basis_model_chartedSpace b
    let _ : IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) M :=
      basis_model_isManifold b
    let eModel : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin dimM)) :=
      (basis_model_diffeomorph b).symm.toHomeomorph.toOpenPartialHomeomorph
    chart.trans eModel ∈ IsManifold.maximalAtlas (𝓡 dimM) (⊤ : WithTop ℕ∞) M := by
  let eModel : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin dimM)) :=
    (basis_model_diffeomorph b).symm.toHomeomorph.toOpenPartialHomeomorph
  have heModel_source : eModel.source = Set.univ := by
    -- The fixed basis chart is globally defined.
    ext x
    simp [eModel]
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin dimM)) E :=
    eModel.singletonChartedSpace heModel_source
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M :=
    basis_model_chartedSpace b
  let _ : IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) M :=
    basis_model_isManifold b
  rw [IsManifold.mem_maximalAtlas_iff]
  intro c hc
  rcases hc with ⟨f, hf, c', hc', rfl⟩
  have hc'Eq : c' = eModel := by
    simpa [eModel] using
      eModel.singletonChartedSpace_mem_atlas_eq (h := heModel_source) c' hc'
  subst c'
  have hleft_old : chart.symm.trans f ∈
      contDiffGroupoid (⊤ : WithTop ℕ∞) (modelWithCornersSelf ℝ E) := by
    exact (IsManifold.mem_maximalAtlas_iff.mp hchart) f hf |>.1
  have hright_old : f.symm.trans chart ∈
      contDiffGroupoid (⊤ : WithTop ℕ∞) (modelWithCornersSelf ℝ E) := by
    exact (IsManifold.mem_maximalAtlas_iff.mp hchart) f hf |>.2
  constructor
  · -- Transport left compatibility from the original ambient atlas.
    simpa [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc, eModel] using
      basis_model_transition_mem_contDiffGroupoid b hleft_old
  · -- Transport right compatibility from the original ambient atlas.
    simpa [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc, eModel] using
      basis_model_transition_mem_contDiffGroupoid b hright_old

/-- Helper for Problem 5-8: the witness chart of a regular coordinate ball is defined on the ball
itself because it is defined on the closure. -/
lemma regular_coordinate_ball_subset_source {B : Set M}
    (hB : IsRegularCoordinateBall E B) :
    ∃ chart : OpenPartialHomeomorph M E,
      chart ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M ∧
        B ⊆ chart.source ∧
        ∃ r r' : ℝ,
          0 < r ∧
            r < r' ∧
            chart '' B = Metric.ball (0 : E) r ∧
            chart '' closure B = Metric.closedBall (0 : E) r ∧
            chart.target = Metric.ball (0 : E) r' := by
  rcases hB with ⟨chart, hchart, hclosure, r, r', hr, hrr', himage, hclosure_image, htarget⟩
  refine ⟨chart, hchart, ?_, r, r', hr, hrr', himage, hclosure_image, htarget⟩
  -- Every point of `B` lies in `closure B`, and the witness chart is defined on the closure.
  intro x hx
  exact hclosure (subset_closure hx)

/-- Helper for Problem 5-8: the closed Euclidean ball corresponding to a regular coordinate ball
lies inside the target of the witnessing chart. -/
lemma regular_coordinate_ball_closedBall_subset_target {B : Set M}
    (hB : IsRegularCoordinateBall E B) :
    ∃ chart : OpenPartialHomeomorph M E,
      chart ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M ∧
        ∃ r r' : ℝ,
          0 < r ∧
            r < r' ∧
            Metric.closedBall (0 : E) r ⊆ chart.target ∧
            chart '' B = Metric.ball (0 : E) r ∧
            chart '' closure B = Metric.closedBall (0 : E) r ∧
            chart.target = Metric.ball (0 : E) r' := by
  rcases hB with ⟨chart, hchart, hclosure, r, r', hr, hrr', himage, hclosure_image, htarget⟩
  refine ⟨chart, hchart, r, r', hr, hrr', ?_, himage, hclosure_image, htarget⟩
  -- The closed ball is the chart image of `closure B`, and chart images of source points land in
  -- the chart target.
  rw [← hclosure_image]
  exact Set.image_subset_iff.mpr fun x hx ↦ chart.map_source (hclosure hx)

/-- Helper for Problem 5-8: a regular coordinate ball is open. -/
lemma regular_coordinate_ball_is_open {B : Set M}
    (hB : IsRegularCoordinateBall E B) :
    IsOpen B := by
  rcases hB with ⟨chart, hchart, hclosure, r, r', hr, hrr', himage, hclosure_image, htarget⟩
  have hsubset : B ⊆ chart.source := fun x hx ↦ hclosure (subset_closure hx)
  have hsymm_image : B = chart.symm '' Metric.ball (0 : E) r := by
    ext x
    constructor
    · intro hx
      refine ⟨chart x, ?_, ?_⟩
      · rw [← himage]
        exact ⟨x, hx, rfl⟩
      · simpa [chart.left_inv (hsubset hx)]
    · rintro ⟨y, hy, rfl⟩
      have hy_image : y ∈ chart '' B := by
        simpa [himage] using hy
      rcases hy_image with ⟨x, hx, rfl⟩
      simpa [chart.left_inv (hsubset hx)] using hx
  -- View `B` as the inverse-chart image of the open Euclidean ball and use that the inverse chart
  -- is an open map on the target.
  rw [hsymm_image]
  refine chart.isOpen_image_symm_of_subset_target Metric.isOpen_ball ?_
  intro y hy
  rw [htarget]
  rw [Metric.mem_ball] at hy ⊢
  exact lt_trans hy hrr'

/-- Helper for Problem 5-8: the complement of a regular coordinate ball is closed. -/
lemma regular_coordinate_ball_compl_isClosed {B : Set M}
    (hB : IsRegularCoordinateBall E B) :
    IsClosed (Set.compl B) := by
  -- This is the complement of the open regular coordinate ball.
  exact (regular_coordinate_ball_is_open hB).isClosed_compl

/-- Helper for Problem 5-8: because a regular coordinate ball is open, the frontier of its
complement is exactly `closure B \ B`. -/
lemma regular_coordinate_ball_compl_frontier_eq_closure_diff {B : Set M}
    (hB : IsRegularCoordinateBall E B) :
    frontier (Set.compl B) = closure B \ B := by
  -- Route correction: avoid rewriting both closure terms of `frontier_eq_closure_inter_closure`.
  -- The complement has the same frontier, and an open set has frontier `closure \ interior`.
  calc
    frontier (Set.compl B) = frontier B := by
      exact frontier_compl B
    _ = closure B \ interior B := by rw [← closure_diff_interior]
    _ = closure B \ B := by rw [(regular_coordinate_ball_is_open hB).interior_eq]

/-- Helper for Problem 5-8: because a regular coordinate ball is open, the frontier of its
complement lies in that complement. -/
lemma regular_coordinate_ball_compl_frontier_subset_compl {B : Set M}
    (hB : IsRegularCoordinateBall E B) :
    frontier (Set.compl B) ⊆ Set.compl B := by
  rw [regular_coordinate_ball_compl_frontier_eq_closure_diff hB]
  intro x hx
  exact hx.2

/-- Helper for Problem 5-8: the spherical frontier of a regular coordinate ball is exactly the
image under the witnessing chart of `closure B \\ B`. -/
lemma regular_coordinate_ball_frontier_image_eq_sphere {B : Set M}
    (hB : IsRegularCoordinateBall E B) :
    ∃ chart : OpenPartialHomeomorph M E,
      chart ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M ∧
        ∃ r r' : ℝ,
          0 < r ∧
            r < r' ∧
            chart '' (closure B \ B) = Metric.sphere (0 : E) r ∧
            chart '' B = Metric.ball (0 : E) r ∧
            chart '' closure B = Metric.closedBall (0 : E) r ∧
            chart.target = Metric.ball (0 : E) r' := by
  rcases hB with ⟨chart, hchart, hclosure, r, r', hr, hrr', himage, hclosure_image, htarget⟩
  have hInj : Set.InjOn chart (closure B) := chart.injOn.mono hclosure
  have hfrontier_image :
      chart '' (closure B \ B) = chart '' closure B \ chart '' B :=
    hInj.image_diff_subset subset_closure
  refine ⟨chart, hchart, r, r', hr, hrr', ?_, himage, hclosure_image, htarget⟩
  -- The chart sends the geometric frontier to the difference between the closed and open balls.
  rw [hfrontier_image, hclosure_image, himage, Metric.closedBall_diff_ball]

/-- Helper for Problem 5-8: in ambient dimension `0`, the frontier `closure B \ B` is empty,
because its chart image would be a positive-radius sphere in a subsingleton space. -/
lemma regular_coordinate_ball_frontier_eq_empty_of_dim_zero {B : Set M}
    (hB : IsRegularCoordinateBall E B) (hdim0 : dimM = 0) :
    closure B \ B = ∅ := by
  rcases regular_coordinate_ball_frontier_image_eq_sphere hB with
    ⟨chart, hchart, r, r', hr, hrr', hfrontier_image, himage, hclosure_image, htarget⟩
  haveI : Subsingleton E := Module.finrank_zero_iff.1 hdim0
  have hsphere : Metric.sphere (0 : E) r = ∅ :=
    Metric.sphere_eq_empty_of_subsingleton (ne_of_gt hr)
  ext x
  constructor
  · intro hx
    have hx_image : chart x ∈ Metric.sphere (0 : E) r := by
      rw [← hfrontier_image]
      exact ⟨x, hx, rfl⟩
    simpa [hsphere] using hx_image
  · intro hx
    simpa using hx

/-- Helper for Problem 5-8: in the witnessing chart of a regular coordinate ball, the local image
of the complement `M \ B` is exactly the exterior of the corresponding open Euclidean ball inside
the chart target. -/
lemma regular_coordinate_ball_compl_chart_image_eq_ball_exterior {B : Set M}
    (hB : IsRegularCoordinateBall E B) :
    ∃ chart : OpenPartialHomeomorph M E,
      chart ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M ∧
        ∃ r r' : ℝ,
          0 < r ∧
            r < r' ∧
            chart '' ((Set.compl B) ∩ chart.source) = chart.target \ Metric.ball (0 : E) r ∧
            chart '' B = Metric.ball (0 : E) r ∧
            chart '' closure B = Metric.closedBall (0 : E) r ∧
            chart.target = Metric.ball (0 : E) r' := by
  rcases hB with ⟨chart, hchart, hclosure, r, r', hr, hrr', himage, hclosure_image, htarget⟩
  have hsubset : B ⊆ chart.source := fun x hx ↦ hclosure (subset_closure hx)
  have himage_diff :
      chart '' (chart.source \ B) = chart '' chart.source \ chart '' B :=
    chart.injOn.image_diff_subset hsubset
  refine ⟨chart, hchart, r, r', hr, hrr', ?_, himage, hclosure_image, htarget⟩
  -- Inside the witness chart, removing `B` from the source becomes removing the smaller open ball
  -- from the chart target.
  calc
    chart '' ((Set.compl B) ∩ chart.source)
        = chart '' (chart.source \ B) := by
            ext y
            constructor
            · rintro ⟨x, hx, rfl⟩
              exact ⟨x, ⟨hx.2, hx.1⟩, rfl⟩
            · rintro ⟨x, hx, rfl⟩
              exact ⟨x, ⟨hx.2, hx.1⟩, rfl⟩
    _ = chart '' chart.source \ chart '' B := himage_diff
    _ = chart.target \ Metric.ball (0 : E) r := by
          rw [chart.image_source_eq_target, himage]

/-- Helper for Problem 5-8: for a fixed witness chart of a regular coordinate ball, a frontier
point of `B` lands in the shell describing the complement branch of that chart. -/
lemma regular_coordinate_ball_witness_frontier_point_mem_ball_exterior
    {B : Set M} {chart : OpenPartialHomeomorph M E} {r : ℝ}
    (hclosure : closure B ⊆ chart.source)
    (hcomplImage :
      chart '' ((Set.compl B) ∩ chart.source) = chart.target \ Metric.ball (0 : E) r)
    {x : M} (hx : x ∈ closure B \ B) :
    chart x ∈ chart.target \ Metric.ball (0 : E) r := by
  have hx_source : x ∈ chart.source := hclosure hx.1
  have hx_compl : x ∈ Set.compl B := hx.2
  -- The frontier point already lies in the complement branch of the witness chart.
  have hx_image : chart x ∈ chart '' ((Set.compl B) ∩ chart.source) := by
    exact ⟨x, ⟨hx_compl, hx_source⟩, rfl⟩
  rwa [hcomplImage] at hx_image

/-- Helper for Problem 5-8: for a fixed witness chart of a regular coordinate ball, a frontier
point of `B` lands on the corresponding radius-`r` sphere. -/
lemma regular_coordinate_ball_witness_frontier_point_mem_sphere
    {B : Set M} {chart : OpenPartialHomeomorph M E} {r : ℝ}
    (hclosure : closure B ⊆ chart.source)
    (himage : chart '' B = Metric.ball (0 : E) r)
    (hclosure_image : chart '' closure B = Metric.closedBall (0 : E) r)
    {x : M} (hx : x ∈ closure B \ B) :
    chart x ∈ Metric.sphere (0 : E) r := by
  have hx_source : x ∈ chart.source := hclosure hx.1
  have hx_closedBall : chart x ∈ Metric.closedBall (0 : E) r := by
    rw [← hclosure_image]
    exact ⟨x, hx.1, rfl⟩
  have hx_not_ball : chart x ∉ Metric.ball (0 : E) r := by
    intro hx_ball
    have hx_image : chart x ∈ chart '' B := by
      simpa [himage] using hx_ball
    rcases hx_image with ⟨y, hy, hxy⟩
    have hy_source : y ∈ chart.source := hclosure (subset_closure hy)
    have hEq : y = x := by
      apply_fun chart.symm at hxy
      simpa [chart.left_inv hx_source, chart.left_inv hy_source] using hxy
    exact hx.2 (hEq ▸ hy)
  -- A point in the closed ball but not in the open ball lies on the sphere.
  have hx_shell : chart x ∈ Metric.closedBall (0 : E) r \ Metric.ball (0 : E) r :=
    ⟨hx_closedBall, hx_not_ball⟩
  simpa [Metric.closedBall_diff_ball] using hx_shell

/-- Helper for Problem 5-8: after composing an ambient chart with a second chart, the original
local image description is simply restricted by the second chart source. -/
lemma trans_chart_image_eq_inter_source_of_image_eq
    {S : Set M} {T : Set E}
    {chart : OpenPartialHomeomorph M E}
    {e : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin dimM))}
    (himage : chart '' (S ∩ chart.source) = T) :
    chart '' (S ∩ (chart.trans e).source) = T ∩ e.source := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx_source : x ∈ chart.source := by
      simpa [OpenPartialHomeomorph.trans_source] using hx.2.1
    have hyT : chart x ∈ T := by
      rw [← himage]
      exact ⟨x, ⟨hx.1, hx_source⟩, rfl⟩
    have hy_source : chart x ∈ e.source := by
      simpa [OpenPartialHomeomorph.trans_source] using hx.2.2
    exact ⟨hyT, hy_source⟩
  · intro hy
    rw [← himage] at hy
    rcases hy.1 with ⟨x, hx, rfl⟩
    refine ⟨x, ?_, rfl⟩
    refine ⟨hx.1, ?_⟩
    simpa [OpenPartialHomeomorph.trans_source, hx.2] using hy.2

/-- Helper for Problem 5-8: if a Euclidean half-slice already lies in a smaller ambient open set,
the same set can be viewed as a half-slice of that smaller open set. -/
lemma euclideanHalfSlice_inter_eq_of_subset
    {k : ℕ} {hk : 0 < k} {hkn : k ≤ dimM}
    {U V : Set (EuclideanSpace ℝ (Fin dimM))}
    {c : Fin (dimM - k) → ℝ}
    (hsub : Set.euclideanHalfSlice U k hk hkn c ⊆ V) :
    Set.euclideanHalfSlice U k hk hkn c =
      Set.euclideanHalfSlice (U ∩ V) k hk hkn c := by
  ext x
  constructor
  · intro hx
    have hxV : x ∈ V := hsub hx
    rcases hx with ⟨hxSlice, hxNonneg⟩
    rcases hxSlice with ⟨hxU, hxTail⟩
    exact ⟨⟨⟨hxU, hxV⟩, hxTail⟩, hxNonneg⟩
  · intro hx
    rcases hx with ⟨hxSlice, hxNonneg⟩
    rcases hxSlice with ⟨hxUV, hxTail⟩
    exact ⟨⟨hxUV.1, hxTail⟩, hxNonneg⟩

/-- Helper for Problem 5-8: once an `E`-chart identifies the local image of `S` with `T`, any
boundary slice chart for `T` can be pulled back through that chart to a boundary slice chart
for `S`. -/
lemma trans_isBoundarySliceChart_of_local_image
    [ChartedSpace (EuclideanSpace ℝ (Fin dimM)) E]
    [IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) E]
    [ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M]
    [IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) M]
    {S : Set M} {T : Set E}
    {chart : OpenPartialHomeomorph M E}
    {e : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin dimM))}
    (htrans :
      chart.trans e ∈ IsManifold.maximalAtlas (𝓡 dimM) (⊤ : WithTop ℕ∞) M)
    (hlocal : chart '' (S ∩ (chart.trans e).source) = T ∩ e.source)
    (hsub : T ⊆ chart.target)
    (he : e.IsBoundarySliceChart T dimM) :
    (chart.trans e).IsBoundarySliceChart S dimM := by
  rcases he.2 with ⟨hk, hkn, c, hc⟩
  refine ⟨htrans, ?_⟩
  rw [Set.IsHalfSliceInChart, Set.IsEuclideanHalfSlice]
  refine ⟨hk, hkn, c, ?_⟩
  have hHalfSlice_subset :
      Set.euclideanHalfSlice e.target dimM hk hkn c ⊆ e.symm ⁻¹' chart.target := by
    -- Every point of the old half-slice comes from a point of `T`, hence from the old chart
    -- target, so the composed target can be intersected down to `chart.trans e`.
    intro z hz
    rw [← hc] at hz
    rcases hz with ⟨y, hy, rfl⟩
    simpa [hy.2] using hsub hy.1
  -- Route correction: transport the Euclidean half-slice through exactly one chart composition,
  -- then intersect the old target with the new trans-target instead of unfolding larger APIs.
  calc
    (chart.trans e) '' (S ∩ (chart.trans e).source)
        = e '' (chart '' (S ∩ (chart.trans e).source)) := by
            ext z
            constructor
            · rintro ⟨x, hx, rfl⟩
              exact ⟨chart x, ⟨x, hx, rfl⟩, by simp [OpenPartialHomeomorph.trans_apply]⟩
            · rintro ⟨y, ⟨x, hx, rfl⟩, hz⟩
              refine ⟨x, hx, ?_⟩
              simpa [OpenPartialHomeomorph.trans_apply] using hz
    _ = e '' (T ∩ e.source) := by rw [hlocal]
    _ = Set.euclideanHalfSlice e.target dimM hk hkn c := hc
    _ = Set.euclideanHalfSlice (e.target ∩ e.symm ⁻¹' chart.target) dimM hk hkn c := by
          exact euclideanHalfSlice_inter_eq_of_subset hHalfSlice_subset
    _ = Set.euclideanHalfSlice ((chart.trans e).target) dimM hk hkn c := by
          rw [OpenPartialHomeomorph.trans_target]

/-- Helper for Problem 5-8: an open subset of `ℝ^n` is tautologically a full-dimensional
Euclidean slice of itself. -/
lemma full_dimensional_euclideanSlice_self
    (U : Set (EuclideanSpace ℝ (Fin dimM))) :
    U.IsEuclideanSlice U dimM := by
  -- In full dimension there are no tail coordinates to constrain.
  refine ⟨le_rfl, fun i ↦ False.elim (by simpa [Nat.sub_self] using i.is_lt), ?_⟩
  ext x
  constructor
  · intro hx
    refine ⟨hx, ?_⟩
    intro i
    exact False.elim (by simpa [Nat.sub_self] using i.is_lt)
  · intro hx
    exact hx.1

/-- Helper for Problem 5-8: any full-dimensional Euclidean slice is the whole ambient open set,
because there are no tail coordinates left to constrain. -/
lemma euclideanSlice_full_dimensional_eq
    (U : Set (EuclideanSpace ℝ (Fin dimM))) (hk : dimM ≤ dimM)
    (c : Fin (dimM - dimM) → ℝ) :
    Set.euclideanSlice U dimM hk c = U := by
  -- The defining tail-coordinate equations are vacuous because `Fin (dimM - dimM)` is empty.
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    refine ⟨hx, ?_⟩
    intro i
    exact False.elim (by simpa [Nat.sub_self] using i.is_lt)

/-- Helper for Problem 5-8: a point outside `closure B` already has a full-dimensional slice chart
for the complement `M \ B`. -/
lemma exterior_point_has_full_sliceChart_for_compl {B : Set M} {x : M}
    [ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M]
    [IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) M]
    (hx : x ∈ (closure B)ᶜ) :
    ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin dimM)),
      x ∈ e.source ∧ e.IsSliceChart (Set.compl B) dimM := by
  let U : Set M := (closure B)ᶜ
  have hU_open : IsOpen U := isClosed_closure.isOpen_compl
  let e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin dimM)) :=
    (chartAt (EuclideanSpace ℝ (Fin dimM)) x).restr U
  have hx_source : x ∈ e.source := by
    -- Restrict the ambient chart to the open neighborhood disjoint from `closure B`.
    change x ∈ ((chartAt (EuclideanSpace ℝ (Fin dimM)) x).restr U).source
    rw [(chartAt (EuclideanSpace ℝ (Fin dimM)) x).restr_source' U hU_open]
    exact ⟨mem_chart_source (EuclideanSpace ℝ (Fin dimM)) x, hx⟩
  refine ⟨e, hx_source, ?_⟩
  refine ⟨?_, ?_⟩
  · -- Restricting a maximal-atlas chart to an ambient open subset preserves smoothness.
    change ((chartAt (EuclideanSpace ℝ (Fin dimM)) x).restr U) ∈
        IsManifold.maximalAtlas (𝓡 dimM) (⊤ : WithTop ℕ∞) M
    exact restr_mem_maximalAtlas
      (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 dimM))
      (IsManifold.chart_mem_maximalAtlas x)
      hU_open
  · have hsource_subset_compl : e.source ⊆ Set.compl B := by
      intro y hy
      change y ∈ ((chartAt (EuclideanSpace ℝ (Fin dimM)) x).restr U).source at hy
      rw [(chartAt (EuclideanSpace ℝ (Fin dimM)) x).restr_source' U hU_open] at hy
      intro hyB
      exact hy.2 (subset_closure hyB)
    have hinter : Set.compl B ∩ e.source = e.source := by
      ext y
      constructor
      · intro hy
        exact hy.2
      · intro hy
        exact ⟨hsource_subset_compl hy, hy⟩
    -- On this restricted source, the complement fills the whole chart patch.
    refine ⟨le_rfl, fun i ↦ False.elim (by simpa [Nat.sub_self] using i.is_lt), ?_⟩
    calc
      e '' (Set.compl B ∩ e.source) = e '' e.source := by rw [hinter]
      _ = e.target := e.image_source_eq_target
      _ = Set.euclideanSlice e.target dimM le_rfl
            (fun i ↦ False.elim (by simpa [Nat.sub_self] using i.is_lt)) := by
            symm
            exact euclideanSlice_full_dimensional_eq e.target le_rfl
              (fun i ↦ False.elim (by simpa [Nat.sub_self] using i.is_lt))

/-- Helper for Problem 5-8: once the frontier points of `closure B \ B` are known to admit
boundary slice charts, the whole complement `M \ B` satisfies the local slice condition with
boundary by splitting into the exterior of `closure B` and the frontier itself. -/
lemma regular_coordinate_ball_compl_satisfiesLocalSliceConditionWithBoundary {B : Set M}
    [ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M]
    [IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) M]
    (hB : IsRegularCoordinateBall E B)
    (hfrontier :
      ∀ x ∈ closure B \ B,
        ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin dimM)),
          x ∈ e.source ∧ e.IsBoundarySliceChart (Set.compl B) dimM) :
    Set.SatisfiesLocalSliceConditionWithBoundary dimM (Set.compl B) dimM := by
  refine ⟨?_⟩
  intro x hx
  by_cases hxClosure : x ∈ closure B
  · -- Frontier points use the boundary-slice charts supplied by the shell analysis.
    rcases hfrontier x ⟨hxClosure, hx⟩ with ⟨e, hxSource, he⟩
    exact ⟨e, hxSource, Or.inr he⟩
  · -- Points outside `closure B` already lie in the interior branch of the complement.
    rcases exterior_point_has_full_sliceChart_for_compl (E := E) (M := M) (B := B)
        (x := x) (show x ∈ (closure B)ᶜ from hxClosure) with
      ⟨e, hxSource, he⟩
    exact ⟨e, hxSource, Or.inl he⟩

-- The bridge from `Set.SatisfiesLocalSliceConditionWithBoundary` to a smooth manifold-with-
-- boundary structure plus smooth embedding is the canonical Chapter 5 theorem
-- `local_slice_criterion_for_embedded_submanifold_with_boundary`; no local wrapper is kept here.

/-- Helper for Problem 5-8: a point on a positive-radius sphere rules out the zero-dimensional
ambient model, because a zero-dimensional finite-dimensional normed space is subsingleton. -/
lemma sphere_point_forces_positive_dim
    {r : ℝ} (hr : 0 < r) {y : E}
    (hy_sphere : y ∈ Metric.sphere (0 : E) r) :
    0 < dimM := by
  by_contra hdim
  have hdim0 : dimM = 0 := Nat.eq_zero_of_not_pos hdim
  haveI : Subsingleton E := Module.finrank_zero_iff.1 hdim0
  have hsphere : Metric.sphere (0 : E) r = ∅ :=
    Metric.sphere_eq_empty_of_subsingleton (ne_of_gt hr)
  simpa [hsphere] using hy_sphere

/-- Helper for Problem 5-8: a Euclidean linear automorphism defines a smooth transition in the
top regularity groupoid. -/
lemma euclidean_linear_equiv_mem_contDiffGroupoid
    {m : ℕ}
    {L : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m)} :
    L.toHomeomorph.toOpenPartialHomeomorph ∈
      contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 m) := by
  -- Linear automorphisms of Euclidean space are smooth together with their inverses.
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid]
  constructor
  · simpa [modelWithCornersSelf_coe] using L.contDiff.contDiffOn
  · simpa [modelWithCornersSelf_coe] using L.symm.contDiff.contDiffOn

/-- Helper for Problem 5-8: the global orthonormal-coordinate chart on `E` is a maximal-atlas
chart for every transported basis-model Euclidean structure. -/
lemma orthonormal_chart_mem_maximalAtlas_in_basis_model
    (b : Module.Basis (Fin dimM) ℝ E) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin dimM)) E :=
      basis_model_chartedSpace b
    let _ : IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) E :=
      basis_model_isManifold b
    ∃ eOrtho : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin dimM)),
      eOrtho ∈ IsManifold.maximalAtlas (𝓡 dimM) (⊤ : WithTop ℕ∞) E := by
  let eOrtho : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin dimM)) :=
    (basis_model_diffeomorph b).symm.toHomeomorph.toOpenPartialHomeomorph
  refine ⟨eOrtho, ?_⟩
  have hId :
      (OpenPartialHomeomorph.refl E) ∈
        IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) E := by
    -- The ambient identity chart is smooth in the original `E`-model atlas.
    simpa using!
      (contDiffGroupoid (⊤ : WithTop ℕ∞) (modelWithCornersSelf ℝ E)).id_mem_maximalAtlas
  -- Route correction: obtain the transported Euclidean chart by pushing the ambient identity
  -- chart through the fixed basis model change, instead of rebuilding a new atlas argument.
  simpa [eOrtho] using
    (basis_model_chart_mem_maximalAtlas (M := E) b
      (chart := OpenPartialHomeomorph.refl E) hId)

/-- Helper for Problem 5-8: in full ambient dimension, the Euclidean half-slice condition simply
requires the last coordinate to be nonnegative. -/
lemma full_dimensional_halfslice_eq_last_coordinate_nonneg
    {m : ℕ} (V : Set (EuclideanSpace ℝ (Fin (m + 1)))) :
    ∃ c : Fin ((m + 1) - (m + 1)) → ℝ,
      Set.euclideanHalfSlice V (m + 1) (Nat.succ_pos _) le_rfl c =
        {z ∈ V | 0 ≤ z (Fin.last m)} := by
  refine ⟨fun i ↦ False.elim (by simpa using i.is_lt), ?_⟩
  -- In full ambient dimension the tail-coordinate constraints are vacuous, so only the last
  -- free-coordinate inequality remains.
  ext z
  constructor
  · intro hz
    refine ⟨hz.1.1, ?_⟩
    change 0 ≤ z (Fin.last m)
    simpa using! hz.2
  · intro hz
    refine ⟨⟨hz.1, ?_⟩, ?_⟩
    · intro i
      exact False.elim (by simpa using i.is_lt)
    · change 0 ≤ z (Fin.last m)
      simpa using hz.2

/-- Helper for Problem 5-8: in dimension `1`, the sign-normalizing Euclidean chart is either the
identity or global negation. -/
noncomputable def unit_exterior_ray_sign_chart (s : Bool) :
    OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)) :=
  if s then
    OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))
  else
    (ContinuousLinearEquiv.neg ℝ).toHomeomorph.toOpenPartialHomeomorph

/-- Helper for Problem 5-8: the one-dimensional sign-normalizing chart is Euclidean-smooth because
it is built from a global linear equivalence. -/
lemma unit_exterior_ray_sign_chart_mem_contDiffGroupoid (s : Bool) :
    unit_exterior_ray_sign_chart s ∈
      contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 1) := by
  cases s
  · -- In the negative branch, the chart is global negation on `ℝ¹`.
    simpa [unit_exterior_ray_sign_chart] using
      (euclidean_linear_equiv_mem_contDiffGroupoid
        (L := (ContinuousLinearEquiv.neg ℝ :
          EuclideanSpace ℝ (Fin 1) ≃L[ℝ] EuclideanSpace ℝ (Fin 1))))
  · -- In the positive branch, the chart is the identity linear automorphism.
    simpa [unit_exterior_ray_sign_chart] using!
      (euclidean_linear_equiv_mem_contDiffGroupoid
        (L := ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 1))))

/-- Helper for Problem 5-8: the one-dimensional sign-normalizing chart multiplies the unique
coordinate by the chosen boundary sign. -/
lemma unit_exterior_ray_sign_chart_apply_zero
    (s : Bool) (z : EuclideanSpace ℝ (Fin 1)) :
    unit_exterior_ray_sign_chart s z 0 = closed_unit_ball_boundary_sign s * z 0 := by
  -- In dimension `1`, the sign chart is either the identity or global negation.
  cases s <;> simp [unit_exterior_ray_sign_chart, closed_unit_ball_boundary_sign]

/-- Helper for Problem 5-8: the one-dimensional sign-normalizing chart is globally defined. -/
lemma unit_exterior_ray_sign_chart_source
    (s : Bool) :
    (unit_exterior_ray_sign_chart s).source = Set.univ := by
  -- Both the identity and global negation are everywhere-defined Euclidean automorphisms.
  cases s <;> ext z <;> simp [unit_exterior_ray_sign_chart]

/-- Helper for Problem 5-8: the one-dimensional sign-normalizing chart has full target. -/
lemma unit_exterior_ray_sign_chart_target
    (s : Bool) :
    (unit_exterior_ray_sign_chart s).target = Set.univ := by
  -- Both branches are global Euclidean automorphisms, so every target point is allowed.
  cases s <;> ext z <;> simp [unit_exterior_ray_sign_chart]

/-- Helper for Problem 5-8: after choosing the sign so the sphere point has positive signed
coordinate, the signed coordinate is exactly `1`. -/
lemma unit_exterior_ray_signed_sphere_coord_eq_one
    (s : Bool) {y : EuclideanSpace ℝ (Fin 1)}
    (hy_sphere : y ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)
    (hy_sign : 0 < closed_unit_ball_boundary_sign s * y 0) :
    closed_unit_ball_boundary_sign s * y 0 = 1 := by
  have hy_abs : |y 0| = 1 := by
    -- On the unit sphere in `ℝ¹`, the Euclidean norm is the absolute value of the unique
    -- coordinate.
    have hy_norm : ‖y‖ = 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hy_sphere
    simpa [EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs] using hy_norm
  cases s
  · -- In the negative branch, positivity means the original coordinate is negative.
    have hy_neg : y 0 < 0 := by
      simpa [closed_unit_ball_boundary_sign] using hy_sign
    have hy_coord : -(y 0) = 1 := by
      simpa [abs_of_neg hy_neg] using hy_abs
    simpa [closed_unit_ball_boundary_sign] using hy_coord
  · -- In the positive branch, positivity means the original coordinate is already positive.
    have hy_pos : 0 < y 0 := by
      simpa [closed_unit_ball_boundary_sign] using hy_sign
    have hy_coord : y 0 = 1 := by
      calc
        y 0 = |y 0| := by simpa [abs_of_pos hy_pos]
        _ = 1 := hy_abs
    simpa [closed_unit_ball_boundary_sign] using hy_coord

/-- Helper for Problem 5-8: on the sign-positive patch in `ℝ¹`, the signed coordinate agrees with
the absolute value of the unique coordinate. -/
lemma unit_exterior_ray_signed_coord_eq_abs
    (s : Bool) {x : EuclideanSpace ℝ (Fin 1)}
    (hx : 0 < closed_unit_ball_boundary_sign s * x 0) :
    closed_unit_ball_boundary_sign s * x 0 = |x 0| := by
  cases s
  · -- In the negative branch, positivity means the original coordinate is negative.
    have hx_neg : x 0 < 0 := by
      simpa [closed_unit_ball_boundary_sign] using hx
    simpa [closed_unit_ball_boundary_sign, abs_of_neg hx_neg]
  · -- In the positive branch, positivity means the original coordinate is already positive.
    have hx_pos : 0 < x 0 := by
      simpa [closed_unit_ball_boundary_sign] using hx
    simpa [closed_unit_ball_boundary_sign, abs_of_pos hx_pos]

/-- Helper for Problem 5-8: a point of `ℝ¹` outside the open unit ball has coordinate absolute
value at least `1`. -/
lemma one_le_abs_coord_of_not_mem_unit_ball
    {x : EuclideanSpace ℝ (Fin 1)}
    (hx : x ∉ Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) 1) :
    1 ≤ |x 0| := by
  by_contra hlt
  have habs_lt : |x 0| < 1 := lt_of_not_ge hlt
  have hnorm_lt : ‖x‖ < 1 := by
    simpa [EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs] using habs_lt
  exact hx (by simpa [Metric.mem_ball, dist_eq_norm] using hnorm_lt)

/-- Helper for Problem 5-8: in `ℝ¹`, coordinate absolute value at least `1` forces a point to lie
outside the open unit ball. -/
lemma not_mem_unit_ball_of_one_le_abs_coord
    {x : EuclideanSpace ℝ (Fin 1)}
    (hx : 1 ≤ |x 0|) :
    x ∉ Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) 1 := by
  intro hx_ball
  have hnorm_lt : ‖x‖ < 1 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hx_ball
  have habs_lt : |x 0| < 1 := by
    simpa [EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs] using hnorm_lt
  exact (not_lt_of_ge hx) habs_lt

/-- Helper for Problem 5-8: every point of the unit sphere in `ℝ¹` admits a sign choice whose
signed coordinate is positive. -/
lemma unit_exterior_ray_exists_positive_sign
    {y : EuclideanSpace ℝ (Fin 1)}
    (hy_sphere : y ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :
    ∃ s : Bool, 0 < closed_unit_ball_boundary_sign s * y 0 := by
  have hy_abs : |y 0| = 1 := by
    -- On the unit sphere in `ℝ¹`, the Euclidean norm is the absolute value of the unique
    -- coordinate.
    have hy_norm : ‖y‖ = 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hy_sphere
    simpa [EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs] using hy_norm
  have hy_ne : y 0 ≠ 0 := by
    intro hy_zero
    have : |y 0| = 0 := by simp [hy_zero]
    linarith [hy_abs]
  rcases lt_or_gt_of_ne hy_ne with hy_neg | hy_pos
  · -- If the coordinate is negative, use the sign-flip branch.
    refine ⟨false, ?_⟩
    simpa [closed_unit_ball_boundary_sign] using (neg_pos.mpr hy_neg)
  · -- If the coordinate is positive, use the identity branch.
    refine ⟨true, ?_⟩
    simpa [closed_unit_ball_boundary_sign] using hy_pos

/-- Helper for Problem 5-8: in ambient dimension `k + 2`, a unit-sphere point has some
coordinate whose sign can be chosen to become strictly positive. -/
lemma unit_sphere_point_exists_positive_signed_coordinate
    {k : ℕ} {y : EuclideanSpace ℝ (Fin (k + 2))}
    (hy_sphere : y ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 2))) 1) :
    ∃ i : Fin (k + 2), ∃ s : Bool, 0 < closed_unit_ball_boundary_sign s * y i := by
  have hy_ne : y ≠ 0 := by
    intro hy_zero
    have hy_norm : ‖y‖ = 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hy_sphere
    simpa [hy_zero] using hy_norm
  obtain ⟨i, hi⟩ := exists_nonzero_coordinate_of_ne_zero y hy_ne
  rcases lt_or_gt_of_ne hi with hneg | hpos
  · -- A negative coordinate becomes positive after choosing the sign-flip branch.
    refine ⟨i, false, ?_⟩
    simpa [closed_unit_ball_boundary_sign] using (neg_pos.mpr hneg)
  · -- A positive coordinate already works with the identity-sign branch.
    refine ⟨i, true, ?_⟩
    simpa [closed_unit_ball_boundary_sign] using hpos

/-- Helper for Problem 5-8: in split coordinates, the higher-dimensional exterior shell chart only
reverses the final normalized coordinate. -/
noncomputable def unit_exterior_signed_shell_flip (k : ℕ) :
    EuclideanSpace ℝ (Fin (k + 2)) ≃L[ℝ] EuclideanSpace ℝ (Fin (k + 2)) :=
  let split0 := split_at_coordinate_continuousLinearEquiv (0 : Fin (k + 2))
  (split0.trans
    ((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin (k + 1)))).prodCongr
      (ContinuousLinearEquiv.neg ℝ))).trans
    split0.symm

/-- Helper for Problem 5-8: after splitting off the distinguished output coordinate, the shell
flip keeps the tail coordinates and negates only the final scalar coordinate. -/
lemma unit_exterior_signed_shell_flip_split {k : ℕ}
    (x : EuclideanSpace ℝ (Fin (k + 2))) :
    split_at_coordinate (0 : Fin (k + 2)) (unit_exterior_signed_shell_flip k x) =
      ((split_at_coordinate (0 : Fin (k + 2)) x).1,
        -(split_at_coordinate (0 : Fin (k + 2)) x).2) := by
  -- The shell flip is the split-coordinate conjugate of `(u, t) ↦ (u, -t)`.
  simp [unit_exterior_signed_shell_flip, split_at_coordinate_continuousLinearEquiv]

/-- Helper for Problem 5-8: the shell flip is its own inverse, so the same split-coordinate
normal form also describes the inverse map. -/
lemma unit_exterior_signed_shell_flip_symm_split {k : ℕ}
    (z : EuclideanSpace ℝ (Fin (k + 2))) :
    split_at_coordinate (0 : Fin (k + 2)) ((unit_exterior_signed_shell_flip k).symm z) =
      ((split_at_coordinate (0 : Fin (k + 2)) z).1,
        -(split_at_coordinate (0 : Fin (k + 2)) z).2) := by
  -- Apply the already-normalized forward split formula to the inverse image and then cancel the
  -- shell flip by `apply_symm_apply`.
  have h :
      split_at_coordinate (0 : Fin (k + 2)) z =
        ((split_at_coordinate (0 : Fin (k + 2))
            ((unit_exterior_signed_shell_flip k).symm z)).1,
          -((split_at_coordinate (0 : Fin (k + 2))
              ((unit_exterior_signed_shell_flip k).symm z)).2)) := by
    simpa using
      (unit_exterior_signed_shell_flip_split (k := k)
        ((unit_exterior_signed_shell_flip k).symm z))
  apply Prod.ext
  · simpa using congrArg Prod.fst h.symm
  · have hsnd :
        -((split_at_coordinate (0 : Fin (k + 2))
            ((unit_exterior_signed_shell_flip k).symm z)).2) =
          (split_at_coordinate (0 : Fin (k + 2)) z).2 := by
        simpa using congrArg Prod.snd h.symm
    linarith

/-- Helper for Problem 5-8: the fixed shell flip is a smooth Euclidean transition because it is a
global continuous linear automorphism. -/
lemma unit_exterior_signed_shell_flip_mem_contDiffGroupoid (k : ℕ) :
    (unit_exterior_signed_shell_flip k).toHomeomorph.toOpenPartialHomeomorph ∈
      contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 (k + 2)) := by
  -- The shell flip is a fixed Euclidean linear automorphism, so it is smooth with smooth inverse.
  simpa using
    (euclidean_linear_equiv_mem_contDiffGroupoid
      (L := unit_exterior_signed_shell_flip k))

/-- Helper for Problem 5-8: the higher-dimensional exterior shell chart uses the ambient patch
where the retained split coordinates stay inside the unit ball and the chosen signed coordinate is
positive. -/
def unit_exterior_signed_shell_source_set
    (k : ℕ) (i : Fin (k + 2)) (s : Bool) :
    Set (EuclideanSpace ℝ (Fin (k + 2))) :=
  {x | ‖(split_at_coordinate i x).1‖ < 1 ∧
      0 < closed_unit_ball_boundary_sign s * x i}

/-- Helper for Problem 5-8: the higher-dimensional exterior shell chart lands in the ambient shell
whose normalized last coordinate can dip below `0` but still stays above the lower graph branch. -/
def unit_exterior_signed_shell_target_set
    (k : ℕ) :
    Set (EuclideanSpace ℝ (Fin (k + 2))) :=
  {z | let uz := split_at_coordinate (0 : Fin (k + 2)) z
    ‖uz.1‖ < 1 ∧ -uz.2 < Real.sqrt (1 - ‖uz.1‖ ^ 2)}

/-- Helper for Problem 5-8: the ambient source patch of the higher-dimensional shell chart is open
because it is cut out by two strict inequalities of continuous functions. -/
lemma unit_exterior_signed_shell_source_set_isOpen
    (k : ℕ) (i : Fin (k + 2)) (s : Bool) :
    IsOpen (unit_exterior_signed_shell_source_set k i s) := by
  have htail :
      Continuous
        (fun x : EuclideanSpace ℝ (Fin (k + 2)) ↦ ‖(split_at_coordinate i x).1‖) := by
    fun_prop
  have hcoord :
      Continuous
        (fun x : EuclideanSpace ℝ (Fin (k + 2)) ↦
          closed_unit_ball_boundary_sign s * x i) := by
    fun_prop
  -- The shell source is the intersection of the retained-coordinate unit ball with a strict
  -- signed-coordinate positivity patch.
  simpa [unit_exterior_signed_shell_source_set] using!
    (isOpen_lt htail continuous_const).inter (isOpen_lt continuous_const hcoord)

/-- Helper for Problem 5-8: the ambient shell target is open because both the retained-coordinate
unit-ball condition and the lower-graph inequality are strict continuous inequalities. -/
lemma unit_exterior_signed_shell_target_set_isOpen
    (k : ℕ) :
    IsOpen (unit_exterior_signed_shell_target_set k) := by
  let uz :
      EuclideanSpace ℝ (Fin (k + 2)) →
        EuclideanSpace ℝ (Fin (k + 1)) × ℝ :=
    split_at_coordinate (0 : Fin (k + 2))
  have huz : Continuous uz := split_at_coordinate_continuous (0 : Fin (k + 2))
  have htail :
      Continuous
        (fun z : EuclideanSpace ℝ (Fin (k + 2)) ↦ ‖(uz z).1‖) :=
    continuous_fst.comp huz |>.norm
  have hlower :
      Continuous
        (fun z : EuclideanSpace ℝ (Fin (k + 2)) ↦ -(uz z).2) := by
    exact (continuous_snd.comp huz).neg
  have hbranch :
      Continuous
        (fun z : EuclideanSpace ℝ (Fin (k + 2)) ↦
          Real.sqrt (1 - ‖(uz z).1‖ ^ 2)) := by
    fun_prop
  -- The target is Lee's ambient shell: strict tail-ball control plus strict lower-graph
  -- inequality.
  simpa [unit_exterior_signed_shell_target_set, uz] using!
    (isOpen_lt htail continuous_const).inter (isOpen_lt hlower hbranch)

/-- Helper for Problem 5-8: the ambient inverse graphing formula is globally continuous, since the
square-root branch is continuous on all of Euclidean space. -/
lemma closed_unit_ball_boundary_chart_inverse_extend_continuous_global
    (k : ℕ) (i : Fin (k + 2)) (s : Bool) :
    Continuous (closed_unit_ball_boundary_chart_inverse_extend k i s) := by
  let ur : EuclideanSpace ℝ (Fin (k + 2)) → EuclideanSpace ℝ (Fin (k + 1)) × ℝ :=
    split_at_coordinate (0 : Fin (k + 2))
  have hur : Continuous ur := split_at_coordinate_continuous (0 : Fin (k + 2))
  have hbranch : Continuous (closed_unit_ball_boundary_branch k s) := by
    -- The sign choice only toggles between the square-root branch and its negation.
    cases s with
    | false =>
        simpa [closed_unit_ball_boundary_branch] using!
          (show Continuous
            (fun u : EuclideanSpace ℝ (Fin (k + 1)) ↦
              -Real.sqrt (1 - ‖u‖ ^ 2)) by
            fun_prop)
    | true =>
        simpa [closed_unit_ball_boundary_branch] using!
          (show Continuous
            (fun u : EuclideanSpace ℝ (Fin (k + 1)) ↦
              Real.sqrt (1 - ‖u‖ ^ 2)) by
            fun_prop)
  have htail :
      Continuous (fun z : EuclideanSpace ℝ (Fin (k + 2)) ↦ (ur z).1) :=
    continuous_fst.comp hur
  have hcoord :
      Continuous
        (fun z : EuclideanSpace ℝ (Fin (k + 2)) ↦
          closed_unit_ball_boundary_branch k s (ur z).1 -
            closed_unit_ball_boundary_sign s * (ur z).2) := by
    -- The distinguished inverse coordinate is the graph branch minus an affine scalar term.
    exact (hbranch.comp htail).sub (continuous_const.mul (continuous_snd.comp hur))
  have hpair :
      Continuous
        (fun z : EuclideanSpace ℝ (Fin (k + 2)) ↦
          ((ur z).1,
            closed_unit_ball_boundary_branch k s (ur z).1 -
              closed_unit_ball_boundary_sign s * (ur z).2)) :=
    htail.prodMk hcoord
  -- Reinsert the chosen coordinate using the inverse split linear equivalence.
  simpa [closed_unit_ball_boundary_chart_inverse_extend, ur] using!
    (split_at_coordinate_symm_continuous (i := i)).comp hpair

/-- Helper for Problem 5-8: after undoing the shell flip, the signed distinguished coordinate of
the ambient inverse graphing formula is the lower-shell height `sqrt(1 - ‖u‖²) + t`. -/
lemma closed_unit_ball_boundary_chart_inverse_extend_signed_coordinate_after_shell_flip_symm
    (k : ℕ) (i : Fin (k + 2)) (s : Bool)
    (z : EuclideanSpace ℝ (Fin (k + 2))) :
    let uz := split_at_coordinate (0 : Fin (k + 2)) z
    closed_unit_ball_boundary_sign s *
        (closed_unit_ball_boundary_chart_inverse_extend k i s
          ((unit_exterior_signed_shell_flip k).symm z) i) =
      Real.sqrt (1 - ‖uz.1‖ ^ 2) + uz.2 := by
  let uz := split_at_coordinate (0 : Fin (k + 2)) z
  -- Rewrite the flipped shell point into the stable split form `(u, -t)`.
  have hflip :
      split_at_coordinate (0 : Fin (k + 2)) ((unit_exterior_signed_shell_flip k).symm z) =
        (uz.1, -uz.2) := by
    simpa [uz] using unit_exterior_signed_shell_flip_symm_split (k := k) z
  -- The distinguished `i`-th coordinate is the scalar reinserted by `(split_at_coordinate i).symm`.
  have hcoord :
      (closed_unit_ball_boundary_chart_inverse_extend k i s
        ((unit_exterior_signed_shell_flip k).symm z) i) =
        closed_unit_ball_boundary_branch k s uz.1 -
          closed_unit_ball_boundary_sign s * (-uz.2) := by
    simp [closed_unit_ball_boundary_chart_inverse_extend, hflip, uz,
      split_at_coordinate_symm_apply_self]
  -- The outside sign converts either graph branch into the common positive expression.
  cases s with
  | false =>
      rw [hcoord]
      simpa [uz, closed_unit_ball_boundary_branch, closed_unit_ball_boundary_sign,
        add_comm, add_left_comm, add_assoc]
  | true =>
      rw [hcoord]
      simpa [uz, closed_unit_ball_boundary_branch, closed_unit_ball_boundary_sign]

/-- Helper for Problem 5-8: the ambient inverse graphing formula globally cancels the ambient
forward graphing formula. -/
lemma closed_unit_ball_boundary_chart_inverse_extend_forward_extend
    (k : ℕ) (i : Fin (k + 2)) (s : Bool)
    (x : EuclideanSpace ℝ (Fin (k + 2))) :
    closed_unit_ball_boundary_chart_inverse_extend k i s
      (closed_unit_ball_boundary_chart_forward_extend k i s x) = x := by
  have hsplit :
      (split_at_coordinate i).symm
        ((split_at_coordinate i x).1, (split_at_coordinate i x).2) = x := by
    exact (split_at_coordinate i).left_inv x
  -- Compare the two formulas after both are written in the same split coordinates at `i`.
  cases s with
  | false =>
      simpa [closed_unit_ball_boundary_chart_inverse_extend,
        closed_unit_ball_boundary_chart_forward_extend,
        closed_unit_ball_boundary_branch, closed_unit_ball_boundary_sign,
        split_at_coordinate_snd_apply] using hsplit
  | true =>
      simpa [closed_unit_ball_boundary_chart_inverse_extend,
        closed_unit_ball_boundary_chart_forward_extend,
        closed_unit_ball_boundary_branch, closed_unit_ball_boundary_sign,
        split_at_coordinate_snd_apply] using hsplit

/-- Helper for Problem 5-8: on the signed shell source, the ambient forward formula followed by
the shell flip lands in the ambient shell target. -/
lemma unit_exterior_signed_shell_map_source
    (k : ℕ) (i : Fin (k + 2)) (s : Bool)
    {x : EuclideanSpace ℝ (Fin (k + 2))}
    (hx : x ∈ unit_exterior_signed_shell_source_set k i s) :
    unit_exterior_signed_shell_flip k
        (closed_unit_ball_boundary_chart_forward_extend k i s x) ∈
      unit_exterior_signed_shell_target_set k := by
  rcases hx with ⟨hx_norm, hx_sign⟩
  rw [unit_exterior_signed_shell_target_set]
  constructor
  · -- The shell flip preserves the retained split coordinates from the forward graphing chart.
    simpa [unit_exterior_signed_shell_flip_split,
      closed_unit_ball_boundary_chart_forward_extend_split] using hx_norm
  · -- The lower-graph inequality is exactly the signed-coordinate positivity hypothesis.
    cases s with
    | false =>
        simpa [unit_exterior_signed_shell_flip_split,
          closed_unit_ball_boundary_chart_forward_extend_split,
          closed_unit_ball_boundary_branch, closed_unit_ball_boundary_sign,
          split_at_coordinate_snd_apply] using hx_sign
    | true =>
        simpa [unit_exterior_signed_shell_flip_split,
          closed_unit_ball_boundary_chart_forward_extend_split,
          closed_unit_ball_boundary_branch, closed_unit_ball_boundary_sign,
          split_at_coordinate_snd_apply] using hx_sign

/-- Helper for Problem 5-8: on the ambient shell target, applying the flipped inverse graphing
formula returns to the signed shell source. -/
lemma unit_exterior_signed_shell_map_target
    (k : ℕ) (i : Fin (k + 2)) (s : Bool)
    {z : EuclideanSpace ℝ (Fin (k + 2))}
    (hz : z ∈ unit_exterior_signed_shell_target_set k) :
    closed_unit_ball_boundary_chart_inverse_extend k i s
        ((unit_exterior_signed_shell_flip k).symm z) ∈
      unit_exterior_signed_shell_source_set k i s := by
  let uz := split_at_coordinate (0 : Fin (k + 2)) z
  have huz : ‖uz.1‖ < 1 ∧ -uz.2 < Real.sqrt (1 - ‖uz.1‖ ^ 2) := by
    -- Unpack the shell target conditions in the split coordinates used by the flip.
    simpa [unit_exterior_signed_shell_target_set, uz] using hz
  rw [unit_exterior_signed_shell_source_set]
  constructor
  · -- The inverse graphing chart preserves the retained split coordinates, so the unit-ball
    -- condition is exactly the first shell inequality.
    simpa [closed_unit_ball_boundary_chart_inverse_extend, uz,
      unit_exterior_signed_shell_flip_symm_split] using huz.1
  · -- The signed distinguished coordinate is `sqrt(1 - ‖u‖²) + t`, which is positive by the
    -- lower-shell inequality `-t < sqrt(1 - ‖u‖²)`.
    have hcoord :
        closed_unit_ball_boundary_sign s *
            (closed_unit_ball_boundary_chart_inverse_extend k i s
              ((unit_exterior_signed_shell_flip k).symm z) i) =
          Real.sqrt (1 - ‖uz.1‖ ^ 2) + uz.2 := by
      simpa [uz] using
        closed_unit_ball_boundary_chart_inverse_extend_signed_coordinate_after_shell_flip_symm
          k i s z
    rw [hcoord]
    linarith

/-- Helper for Problem 5-8: the flipped ambient inverse graphing formula cancels the ambient
forward shell formula. -/
lemma unit_exterior_signed_shell_left_inv
    (k : ℕ) (i : Fin (k + 2)) (s : Bool)
    {x : EuclideanSpace ℝ (Fin (k + 2))}
    (hx : x ∈ unit_exterior_signed_shell_source_set k i s) :
    closed_unit_ball_boundary_chart_inverse_extend k i s
        ((unit_exterior_signed_shell_flip k).symm
          (unit_exterior_signed_shell_flip k
            (closed_unit_ball_boundary_chart_forward_extend k i s x))) = x := by
  -- The shell flip is involutive, so only the ambient graphing cancellation remains.
  simpa using
    closed_unit_ball_boundary_chart_inverse_extend_forward_extend k i s x

/-- Helper for Problem 5-8: the ambient forward shell formula recovers every point of the ambient
shell target after applying the flipped inverse graphing formula. -/
lemma unit_exterior_signed_shell_right_inv
    (k : ℕ) (i : Fin (k + 2)) (s : Bool)
    {z : EuclideanSpace ℝ (Fin (k + 2))}
    (hz : z ∈ unit_exterior_signed_shell_target_set k) :
    unit_exterior_signed_shell_flip k
        (closed_unit_ball_boundary_chart_forward_extend k i s
          (closed_unit_ball_boundary_chart_inverse_extend k i s
            ((unit_exterior_signed_shell_flip k).symm z))) = z := by
  -- Compare the normalized shell coordinates after the inverse graphing formula reconstructs the
  -- distinguished coordinate and the shell flip restores the original sign.
  apply (split_at_coordinate (0 : Fin (k + 2))).injective
  cases s with
  | false =>
      simpa [closed_unit_ball_boundary_chart_inverse_extend,
        closed_unit_ball_boundary_chart_forward_extend, unit_exterior_signed_shell_flip,
        closed_unit_ball_boundary_branch, closed_unit_ball_boundary_sign,
        split_at_coordinate_continuousLinearEquiv]
  | true =>
      simpa [closed_unit_ball_boundary_chart_inverse_extend,
        closed_unit_ball_boundary_chart_forward_extend, unit_exterior_signed_shell_flip,
        closed_unit_ball_boundary_branch, closed_unit_ball_boundary_sign,
        split_at_coordinate_continuousLinearEquiv]

/-- Helper for Problem 5-8: the ambient forward shell formula is continuous on all of Euclidean
space, hence in particular on the shell source patch. -/
lemma unit_exterior_signed_shell_continuousOn_toFun
    (k : ℕ) (i : Fin (k + 2)) (s : Bool) :
    ContinuousOn
      (fun x : EuclideanSpace ℝ (Fin (k + 2)) ↦
        unit_exterior_signed_shell_flip k
          (closed_unit_ball_boundary_chart_forward_extend k i s x))
      (unit_exterior_signed_shell_source_set k i s) := by
  -- Both pieces are globally continuous, so the shell chart is continuous on the restricted
  -- source patch.
  exact
    ((unit_exterior_signed_shell_flip k).continuous.comp
      (closed_unit_ball_boundary_chart_forward_extend_continuous k i s)).continuousOn

/-- Helper for Problem 5-8: the flipped ambient inverse graphing formula is continuous on all of
Euclidean space, hence in particular on the shell target. -/
lemma unit_exterior_signed_shell_continuousOn_invFun
    (k : ℕ) (i : Fin (k + 2)) (s : Bool) :
    ContinuousOn
      (fun z : EuclideanSpace ℝ (Fin (k + 2)) ↦
        closed_unit_ball_boundary_chart_inverse_extend k i s
          ((unit_exterior_signed_shell_flip k).symm z))
      (unit_exterior_signed_shell_target_set k) := by
  -- The ambient inverse graphing formula and the shell flip are both globally continuous.
  exact
    ((closed_unit_ball_boundary_chart_inverse_extend_continuous_global k i s).comp
      (unit_exterior_signed_shell_flip k).symm.continuous).continuousOn

/-- Helper for Problem 5-8: the higher-dimensional exterior shell chart is Lee's Chapter 2 signed
ambient graphing chart near the unit sphere, with the final normalized coordinate flipped so the
exterior branch becomes the nonnegative side. -/
noncomputable def unit_exterior_signed_shell_chart
    (k : ℕ) (i : Fin (k + 2)) (s : Bool) :
    OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (k + 2)))
      (EuclideanSpace ℝ (Fin (k + 2))) :=
  { toPartialEquiv :=
      { toFun := fun x ↦
          unit_exterior_signed_shell_flip k
            (closed_unit_ball_boundary_chart_forward_extend k i s x)
        invFun := fun z ↦
          closed_unit_ball_boundary_chart_inverse_extend k i s
            ((unit_exterior_signed_shell_flip k).symm z)
        source := unit_exterior_signed_shell_source_set k i s
        target := unit_exterior_signed_shell_target_set k
        map_source' := fun x hx ↦ unit_exterior_signed_shell_map_source k i s hx
        map_target' := fun z hz ↦ unit_exterior_signed_shell_map_target k i s hz
        left_inv' := fun x hx ↦ unit_exterior_signed_shell_left_inv k i s hx
        right_inv' := fun z hz ↦ unit_exterior_signed_shell_right_inv k i s hz }
    open_source := unit_exterior_signed_shell_source_set_isOpen k i s
    open_target := unit_exterior_signed_shell_target_set_isOpen k
    continuousOn_toFun := unit_exterior_signed_shell_continuousOn_toFun k i s
    continuousOn_invFun := unit_exterior_signed_shell_continuousOn_invFun k i s }

/-- Helper for Problem 5-8: the ambient shell chart source is exactly the signed shell patch where
the retained split coordinates stay in the open unit ball and the chosen signed coordinate is
positive. -/
lemma unit_exterior_signed_shell_chart_source
    (k : ℕ) (i : Fin (k + 2)) (s : Bool) :
    (unit_exterior_signed_shell_chart k i s).source =
      unit_exterior_signed_shell_source_set k i s := by
  -- The shell chart was defined with this explicit ambient shell source.
  simp [unit_exterior_signed_shell_chart]

/-- Helper for Problem 5-8: the distinguished output coordinate of the higher-dimensional shell
chart is the signed radial excess over the lower graph branch. -/
lemma unit_exterior_signed_shell_chart_apply_zero
    (k : ℕ) (i : Fin (k + 2)) (s : Bool)
    (x : EuclideanSpace ℝ (Fin (k + 2))) :
    (unit_exterior_signed_shell_chart k i s x) 0 =
      closed_unit_ball_boundary_sign s * x i -
        Real.sqrt (1 - ‖(split_at_coordinate i x).1‖ ^ 2) := by
  -- Read coordinate `0` from the split form of the shell chart after the final shell flip.
  calc
    (unit_exterior_signed_shell_chart k i s x) 0 =
        (split_at_coordinate (0 : Fin (k + 2))
          (unit_exterior_signed_shell_chart k i s x)).2 := by
            symm
            exact
              split_at_coordinate_snd_apply (0 : Fin (k + 2))
                (unit_exterior_signed_shell_chart k i s x)
    _ = -(closed_unit_ball_boundary_sign s *
          (closed_unit_ball_boundary_branch k s (split_at_coordinate i x).1 -
            (split_at_coordinate i x).2)) := by
          -- The shell flip leaves the retained coordinates alone and negates only the new
          -- distinguished scalar coordinate.
          simpa [unit_exterior_signed_shell_chart,
            closed_unit_ball_boundary_chart_forward_extend_split] using
            congrArg Prod.snd
              (unit_exterior_signed_shell_flip_split (k := k)
                (closed_unit_ball_boundary_chart_forward_extend k i s x))
    _ = closed_unit_ball_boundary_sign s * x i -
          Real.sqrt (1 - ‖(split_at_coordinate i x).1‖ ^ 2) := by
          -- After expanding the branch/sign choice, both sign cases reduce to the same formula.
          rw [split_at_coordinate_snd_apply]
          cases s <;>
            simp [closed_unit_ball_boundary_branch, closed_unit_ball_boundary_sign,
              sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

/-- Helper for Problem 5-8: target membership for the ambient shell chart is exactly the explicit
split-coordinate shell inequality from the source proof. -/
lemma unit_exterior_signed_shell_chart_target_mem_iff
    {k : ℕ} {i : Fin (k + 2)} {s : Bool}
    {z : EuclideanSpace ℝ (Fin (k + 2))} :
    z ∈ (unit_exterior_signed_shell_chart k i s).target ↔
      let uz := split_at_coordinate (0 : Fin (k + 2)) z
      ‖uz.1‖ < 1 ∧ -uz.2 < Real.sqrt (1 - ‖uz.1‖ ^ 2) := by
  -- The shell chart target was defined by this explicit ambient split-coordinate condition.
  simp [unit_exterior_signed_shell_chart, unit_exterior_signed_shell_target_set]

/-- Helper for Problem 5-8: undoing the shell flip preserves the retained split coordinates and
only changes the distinguished scalar coordinate. -/
lemma unit_exterior_signed_shell_flip_symm_preserves_retained_coordinates
    (k : ℕ) (z : EuclideanSpace ℝ (Fin (k + 2))) :
    (split_at_coordinate (0 : Fin (k + 2)) ((unit_exterior_signed_shell_flip k).symm z)).1 =
      (split_at_coordinate (0 : Fin (k + 2)) z).1 := by
  -- The inverse shell flip keeps the retained coordinates and only negates the scalar slot.
  simpa using congrArg Prod.fst (unit_exterior_signed_shell_flip_symm_split (k := k) z)

/-- Helper for Problem 5-8: every point of the shell-chart target already lies in the open unit
ball for the retained split coordinates, which is the inverse graphing smoothness domain. -/
lemma unit_exterior_signed_shell_chart_target_mem_unit_ball
    {k : ℕ} {i : Fin (k + 2)} {s : Bool}
    {z : EuclideanSpace ℝ (Fin (k + 2))}
    (hz : z ∈ (unit_exterior_signed_shell_chart k i s).target) :
    ‖(split_at_coordinate (0 : Fin (k + 2)) z).1‖ < 1 := by
  -- Keep only the retained-coordinate inequality from the explicit shell-target description.
  have hz' :=
    (unit_exterior_signed_shell_chart_target_mem_iff
      (k := k) (i := i) (s := s) (z := z)).mp hz
  simpa using hz'.1

/-- Helper for Problem 5-8: the fixed Euclidean coordinate swap sends the last coordinate to slot
`0`. -/
lemma swap_zero_last_linear_isometry_apply_zero
    (k : ℕ) (x : EuclideanSpace ℝ (Fin (k + 2))) :
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (Equiv.swap 0 (Fin.last (k + 1))) x) 0 = x (Fin.last (k + 1)) := by
  -- The permutation chart acts by precomposing with the chosen swap on `Fin (k + 2)`.
  simp

/-- Helper for Problem 5-8: the fixed Euclidean coordinate swap sends slot `0` to the last
coordinate. -/
lemma swap_zero_last_linear_isometry_apply_last
    (k : ℕ) (x : EuclideanSpace ℝ (Fin (k + 2))) :
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (Equiv.swap 0 (Fin.last (k + 1))) x) (Fin.last (k + 1)) = x 0 := by
  -- This is the same permutation identity, read at the last coordinate instead of at `0`.
  simp

/-- Helper for Problem 5-8: the higher-dimensional shell chart is a smooth Euclidean chart, so
its restriction and centered translate can enter the maximal atlas without reopening the formulas.
-/
lemma unit_exterior_signed_shell_chart_mem_contDiffGroupoid
    (k : ℕ) (i : Fin (k + 2)) (s : Bool) :
    (unit_exterior_signed_shell_chart k i s) ∈
      contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 (k + 2)) := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid]
  constructor
  · -- Compose the smooth ambient graphing formula with the global shell flip on the sign patch.
    have hforward :
        ContDiffOn ℝ ω
          (closed_unit_ball_boundary_chart_forward_extend k i s)
          (unit_exterior_signed_shell_source_set k i s) := by
      refine (closed_unit_ball_boundary_chart_forward_extend_contDiffOn k i s).mono ?_
      intro x hx
      exact hx.1
    have hflip :
        ContDiffOn ℝ ω
          (unit_exterior_signed_shell_flip k)
          Set.univ := by
      simpa using
        ((unit_exterior_signed_shell_flip k).contDiff.contDiffOn :
          ContDiffOn ℝ ω (unit_exterior_signed_shell_flip k) Set.univ)
    -- The forward shell chart is literally the ambient graphing map followed by the shell flip.
    simpa [unit_exterior_signed_shell_chart] using! hflip.comp hforward (by
      intro x hx
      simp)
  · -- Undoing the shell flip preserves the retained coordinates, so the inverse graphing formula
    -- stays in its open-ball smoothness domain on the shell target.
    have hflip_symm :
        ContDiffOn ℝ ω
          (fun z : EuclideanSpace ℝ (Fin (k + 2)) ↦
            (unit_exterior_signed_shell_flip k).symm z)
          (unit_exterior_signed_shell_target_set k) := by
      refine
        (((unit_exterior_signed_shell_flip k).symm.contDiff.contDiffOn :
          ContDiffOn ℝ ω
            (fun z : EuclideanSpace ℝ (Fin (k + 2)) ↦
              (unit_exterior_signed_shell_flip k).symm z)
            Set.univ)).mono ?_
      intro z hz
      simp
    -- Route correction: use the explicit target inequality plus the retained-coordinate
    -- preservation under the shell flip, instead of unfolding the whole inverse chart package.
    simpa [unit_exterior_signed_shell_chart] using!
      (closed_unit_ball_boundary_chart_inverse_extend_contDiffOn k i s).comp hflip_symm
        (by
          intro z hz
          have hz_chart :
              z ∈ (unit_exterior_signed_shell_chart k i s).target := by
            simpa [unit_exterior_signed_shell_chart] using hz
          have hz_tail :
              ‖(split_at_coordinate (0 : Fin (k + 2)) z).1‖ < 1 :=
            unit_exterior_signed_shell_chart_target_mem_unit_ball
              (i := i) (s := s) hz_chart
          simpa [unit_exterior_signed_shell_flip_symm_preserves_retained_coordinates (k := k) z]
            using hz_tail)

/-- Helper for Problem 5-8: on a signed shell patch, the distinguished shell coordinate is
nonnegative exactly on the exterior of the open unit ball. -/
lemma unit_exterior_signed_shell_chart_apply_zero_nonneg_iff
    (k : ℕ) (i : Fin (k + 2)) (s : Bool)
    {x : EuclideanSpace ℝ (Fin (k + 2))}
    (hx : x ∈ unit_exterior_signed_shell_source_set k i s) :
    0 ≤ (unit_exterior_signed_shell_chart k i s x) 0 ↔
      x ∉ Metric.ball (0 : EuclideanSpace ℝ (Fin (k + 2))) 1 := by
  let u := (split_at_coordinate i x).1
  let t := (split_at_coordinate i x).2
  let a := closed_unit_ball_boundary_sign s * x i
  have hu : ‖u‖ < 1 := by
    simpa [unit_exterior_signed_shell_source_set, u] using hx.1
  have ha : 0 < a := by
    simpa [unit_exterior_signed_shell_source_set, a] using hx.2
  have ht : t = x i := by
    simp [t, split_at_coordinate_snd_apply]
  have ha_sq : a ^ 2 = t ^ 2 := by
    rw [ht]
    cases s <;> simp [a, closed_unit_ball_boundary_sign]
  have hnorm_sq : ‖x‖ ^ 2 = ‖u‖ ^ 2 + t ^ 2 := by
    simpa [u, t] using
      split_at_coordinate_symm_norm_sq i (split_at_coordinate i x)
  have hrad : 0 ≤ 1 - ‖u‖ ^ 2 := by
    nlinarith [norm_nonneg u]
  have hsqrt_sq : (Real.sqrt (1 - ‖u‖ ^ 2)) ^ 2 = 1 - ‖u‖ ^ 2 :=
    Real.sq_sqrt hrad
  have hcoord :
      (unit_exterior_signed_shell_chart k i s x) 0 =
        a - Real.sqrt (1 - ‖u‖ ^ 2) := by
    simpa [a, u] using unit_exterior_signed_shell_chart_apply_zero k i s x
  constructor
  · intro hnonneg hxball
    have hnorm_lt : ‖x‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hxball
    have hroot_le : Real.sqrt (1 - ‖u‖ ^ 2) ≤ a := by
      linarith [hnonneg, hcoord]
    have hroot_nonneg : 0 ≤ Real.sqrt (1 - ‖u‖ ^ 2) := Real.sqrt_nonneg _
    have hsq : 1 ≤ ‖x‖ ^ 2 := by
      nlinarith [sq_nonneg (a - Real.sqrt (1 - ‖u‖ ^ 2)), ha_sq, hnorm_sq,
        hsqrt_sq]
    nlinarith [norm_nonneg x]
  · intro hout
    have hnorm_ge : 1 ≤ ‖x‖ := by
      by_contra hlt
      have hnorm_lt : ‖x‖ < 1 := lt_of_not_ge hlt
      exact hout (by simpa [Metric.mem_ball, dist_eq_norm] using hnorm_lt)
    have hroot_le : Real.sqrt (1 - ‖u‖ ^ 2) ≤ a := by
      have hroot_nonneg : 0 ≤ Real.sqrt (1 - ‖u‖ ^ 2) := Real.sqrt_nonneg _
      nlinarith [ha_sq, hnorm_sq, hsqrt_sq, norm_nonneg x]
    rw [hcoord]
    linarith

/-- Helper for Problem 5-8: a unit-sphere point in a signed shell source has zero distinguished
shell coordinate. -/
lemma unit_exterior_signed_shell_chart_apply_zero_of_mem_sphere
    (k : ℕ) (i : Fin (k + 2)) (s : Bool)
    {x : EuclideanSpace ℝ (Fin (k + 2))}
    (hx : x ∈ unit_exterior_signed_shell_source_set k i s)
    (hsphere : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 2))) 1) :
    (unit_exterior_signed_shell_chart k i s x) 0 = 0 := by
  let u := (split_at_coordinate i x).1
  let t := (split_at_coordinate i x).2
  let a := closed_unit_ball_boundary_sign s * x i
  have ha : 0 < a := by
    simpa [unit_exterior_signed_shell_source_set, a] using hx.2
  have ht : t = x i := by
    simp [t, split_at_coordinate_snd_apply]
  have ha_sq : a ^ 2 = t ^ 2 := by
    rw [ht]
    cases s <;> simp [a, closed_unit_ball_boundary_sign]
  have hnorm : ‖x‖ = 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hsphere
  have hnorm_sq : ‖x‖ ^ 2 = ‖u‖ ^ 2 + t ^ 2 := by
    simpa [u, t] using
      split_at_coordinate_symm_norm_sq i (split_at_coordinate i x)
  have hu : ‖u‖ < 1 := by
    simpa [unit_exterior_signed_shell_source_set, u] using hx.1
  have hrad : 0 ≤ 1 - ‖u‖ ^ 2 := by
    nlinarith [norm_nonneg u]
  have hsqrt_sq : (Real.sqrt (1 - ‖u‖ ^ 2)) ^ 2 = 1 - ‖u‖ ^ 2 :=
    Real.sq_sqrt hrad
  have ha_eq : a = Real.sqrt (1 - ‖u‖ ^ 2) := by
    nlinarith [Real.sqrt_nonneg (1 - ‖u‖ ^ 2)]
  rw [unit_exterior_signed_shell_chart_apply_zero, show
    closed_unit_ball_boundary_sign s * x i = a by rfl, show
    (split_at_coordinate i x).1 = u by rfl, ha_eq, sub_self]

/-- Helper for Problem 5-8: after sign-normalizing and centering a one-dimensional exterior ray at
the sphere point, the local image is exactly the standard nonnegative half-line in the restricted
chart target. -/
lemma unit_exterior_ray_chart_local_image
    (s : Bool) {U : Set (EuclideanSpace ℝ (Fin 1))} (hU_open : IsOpen U)
    {y : EuclideanSpace ℝ (Fin 1)}
    (hy_shell : y ∈ U \ Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) 1)
    (hy_sphere : y ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)
    (hy_sign : 0 < closed_unit_ball_boundary_sign s * y 0) :
    ∃ e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)),
      y ∈ e.source ∧
        e.IsBoundarySliceChart (U \ Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) 1) 1 := by
  -- Route correction: restricting only to `U` is still too large for arbitrary `U`; the witness
  -- must first shrink to a sign-positive neighborhood inside `U`, and only then be centered at
  -- `y` so the exterior ray becomes the standard half-line.
  let W : Set (EuclideanSpace ℝ (Fin 1)) :=
    U ∩ {x | 0 < closed_unit_ball_boundary_sign s * x 0}
  have hW_open : IsOpen W := by
    -- The patch keeps the given ambient neighborhood and intersects it with a strict
    -- sign-positivity condition on the unique coordinate.
    have hsign_open :
        IsOpen {x : EuclideanSpace ℝ (Fin 1) | 0 < closed_unit_ball_boundary_sign s * x 0} := by
      have hcont :
          Continuous (fun x : EuclideanSpace ℝ (Fin 1) ↦
            closed_unit_ball_boundary_sign s * x 0) := by
        fun_prop
      exact isOpen_lt continuous_const hcont
    exact hU_open.inter hsign_open
  let e0 : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)) :=
    (unit_exterior_ray_sign_chart s).restr W
  have hy_e0source : y ∈ e0.source := by
    -- The chosen sphere point lies in the restricted source because it lies in both `U` and the
    -- sign-positive patch.
    change y ∈ ((unit_exterior_ray_sign_chart s).restr W).source
    rw [(unit_exterior_ray_sign_chart s).restr_source' W hW_open]
    rw [unit_exterior_ray_sign_chart_source]
    exact ⟨by simp, ⟨hy_shell.1, hy_sign⟩⟩
  let p : e0.source := ⟨y, hy_e0source⟩
  let e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)) :=
    e0.centerAt p
  have hsource_mem_patch :
      ∀ {x : EuclideanSpace ℝ (Fin 1)}, x ∈ e.source → x ∈ W := by
    intro x hx
    -- Centering keeps the restricted source unchanged, so source points are exactly the points of
    -- the sign-positive patch.
    have hx0 : x ∈ e0.source := by
      simpa [e, OpenPartialHomeomorph.centerAt_source] using hx
    change x ∈ ((unit_exterior_ray_sign_chart s).restr W).source at hx0
    rw [(unit_exterior_ray_sign_chart s).restr_source' W hW_open] at hx0
    rw [unit_exterior_ray_sign_chart_source] at hx0
    simpa [W, and_left_comm, and_assoc] using hx0
  have himage :
      e '' ((U \ Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) 1) ∩ e.source) =
        {z ∈ e.target | 0 ≤ z 0} := by
    ext z
    constructor
    · intro hz
      rcases hz with ⟨x, hx, rfl⟩
      refine ⟨e.map_source hx.2, ?_⟩
      have hxW : x ∈ W := hsource_mem_patch hx.2
      have hx_signed_pos : 0 < closed_unit_ball_boundary_sign s * x 0 := hxW.2
      have hx_abs : closed_unit_ball_boundary_sign s * x 0 = |x 0| :=
        unit_exterior_ray_signed_coord_eq_abs s hx_signed_pos
      have hx_abs_ge : 1 ≤ |x 0| :=
        one_le_abs_coord_of_not_mem_unit_ball hx.1.2
      have hx_signed_ge : 1 ≤ closed_unit_ball_boundary_sign s * x 0 := by
        rw [hx_abs]
        exact hx_abs_ge
      have hcoord :
          e x 0 = closed_unit_ball_boundary_sign s * x 0 - 1 := by
        calc
          e x 0 =
              closed_unit_ball_boundary_sign s * x 0 -
                closed_unit_ball_boundary_sign s * y 0 := by
                  simp [e, e0, p, centerAt_apply_eq_sub_basepoint,
                    unit_exterior_ray_sign_chart_apply_zero]
          _ = closed_unit_ball_boundary_sign s * x 0 - 1 := by
              rw [unit_exterior_ray_signed_sphere_coord_eq_one s hy_sphere hy_sign]
      rw [hcoord]
      linarith
    · intro hz
      refine ⟨e.symm z, ?_, ?_⟩
      · refine ⟨?_, e.map_target hz.1⟩
        have hx_source : e.symm z ∈ e.source := e.map_target hz.1
        have hxW : e.symm z ∈ W := hsource_mem_patch hx_source
        have hx_signed_pos : 0 < closed_unit_ball_boundary_sign s * (e.symm z) 0 := hxW.2
        have hx_abs : closed_unit_ball_boundary_sign s * (e.symm z) 0 = |(e.symm z) 0| :=
          unit_exterior_ray_signed_coord_eq_abs s hx_signed_pos
        have hz_coord :
            z 0 = closed_unit_ball_boundary_sign s * (e.symm z) 0 - 1 := by
          calc
            z 0 = e (e.symm z) 0 := by
              simpa using congrArg (fun v : EuclideanSpace ℝ (Fin 1) ↦ v 0) (e.right_inv hz.1).symm
            _ = closed_unit_ball_boundary_sign s * (e.symm z) 0 - 1 := by
              calc
                e (e.symm z) 0 =
                    closed_unit_ball_boundary_sign s * (e.symm z) 0 -
                      closed_unit_ball_boundary_sign s * y 0 := by
                        simp [e, e0, p, centerAt_apply_eq_sub_basepoint,
                          unit_exterior_ray_sign_chart_apply_zero]
                _ = closed_unit_ball_boundary_sign s * (e.symm z) 0 - 1 := by
                    rw [unit_exterior_ray_signed_sphere_coord_eq_one s hy_sphere hy_sign]
        have hx_signed_ge : 1 ≤ closed_unit_ball_boundary_sign s * (e.symm z) 0 := by
          linarith [hz.2, hz_coord]
        have hx_abs_ge : 1 ≤ |(e.symm z) 0| := by
          rw [← hx_abs]
          exact hx_signed_ge
        exact ⟨hxW.1, not_mem_unit_ball_of_one_le_abs_coord hx_abs_ge⟩
      · exact e.right_inv hz.1
  refine ⟨e, ?_, ?_⟩
  · -- The centered chart still contains the basepoint because centering preserves the source.
    simpa [e, OpenPartialHomeomorph.centerAt_source] using hy_e0source
  · refine ⟨?_, ?_⟩
    · have hrefl :
          (OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))) ∈
            IsManifold.maximalAtlas (𝓡 1) (⊤ : WithTop ℕ∞)
              (EuclideanSpace ℝ (Fin 1)) := by
        simpa using!
          (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 1)).id_mem_maximalAtlas
      have hsign_max :
          unit_exterior_ray_sign_chart s ∈
            IsManifold.maximalAtlas (𝓡 1) (⊤ : WithTop ℕ∞)
              (EuclideanSpace ℝ (Fin 1)) := by
        simpa using
          (trans_mem_maximalAtlas_of_mem_groupoid
            (m := 1)
            (X := EuclideanSpace ℝ (Fin 1))
            (e := OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))
            hrefl
            (chi := unit_exterior_ray_sign_chart s)
            (unit_exterior_ray_sign_chart_mem_contDiffGroupoid s))
      have hrestr_max :
          e0 ∈ IsManifold.maximalAtlas (𝓡 1) (⊤ : WithTop ℕ∞)
            (EuclideanSpace ℝ (Fin 1)) := by
        simpa [e0] using!
          (restr_mem_maximalAtlas
            (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 1))
            hsign_max
            hW_open)
      simpa [e] using centerAt_mem_maximalAtlas e0 hrestr_max p
    · rw [Set.IsHalfSliceInChart, Set.IsEuclideanHalfSlice]
      rcases full_dimensional_halfslice_eq_last_coordinate_nonneg (m := 0) e.target with
        ⟨c, hc⟩
      refine ⟨Nat.succ_pos _, le_rfl, c, ?_⟩
      calc
        e '' ((U \ Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) 1) ∩ e.source)
            = {z ∈ e.target | 0 ≤ z 0} := himage
        _ = Set.euclideanHalfSlice e.target 1 (Nat.succ_pos _) le_rfl c := by
            symm
            simpa using hc

/-- Helper for Problem 5-8: in orthonormal Euclidean coordinates, a sphere point should admit a
boundary slice chart for the exterior of the corresponding open ball. -/
lemma unit_exterior_signed_shell_boundary_slice_chart_at_sphere_point_succSucc
    {k : ℕ} {U : Set (EuclideanSpace ℝ (Fin (k + 2)))} (hU_open : IsOpen U)
    {y : EuclideanSpace ℝ (Fin (k + 2))}
    (hy_shell : y ∈ U \ Metric.ball (0 : EuclideanSpace ℝ (Fin (k + 2))) 1)
    (hy_sphere : y ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 2))) 1) :
    ∃ e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (k + 2)))
        (EuclideanSpace ℝ (Fin (k + 2))),
      y ∈ e.source ∧
        e.IsBoundarySliceChart
          (U \ Metric.ball (0 : EuclideanSpace ℝ (Fin (k + 2))) 1) (k + 2) := by
  obtain ⟨i, s, hy_sign⟩ := unit_sphere_point_exists_positive_signed_coordinate hy_sphere
  let e0 := unit_exterior_signed_shell_chart k i s
  have hy_norm : ‖y‖ = 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hy_sphere
  have hy_tail : ‖(split_at_coordinate i y).1‖ < 1 := by
    have hsplit :
        ‖y‖ ^ 2 = ‖(split_at_coordinate i y).1‖ ^ 2 + (split_at_coordinate i y).2 ^ 2 := by
      simpa using split_at_coordinate_symm_norm_sq i (split_at_coordinate i y)
    have hcoord_ne : (split_at_coordinate i y).2 ≠ 0 := by
      cases s <;>
        simpa [split_at_coordinate_snd_apply, closed_unit_ball_boundary_sign] using hy_sign.ne'
    have hcoord_sq_pos : 0 < (split_at_coordinate i y).2 ^ 2 := sq_pos_iff.mpr hcoord_ne
    nlinarith [norm_nonneg ((split_at_coordinate i y).1)]
  have hy_e0source : y ∈ e0.source := by
    simpa [e0, unit_exterior_signed_shell_chart_source,
      unit_exterior_signed_shell_source_set] using ⟨hy_tail, hy_sign⟩
  have hy_e0zero : e0 y 0 = 0 := by
    exact unit_exterior_signed_shell_chart_apply_zero_of_mem_sphere k i s
      (by simpa [e0, unit_exterior_signed_shell_chart_source] using hy_e0source) hy_sphere
  let e1 := e0.restr U
  have hy_e1source : y ∈ e1.source := by
    change y ∈ (e0.restr U).source
    rw [e0.restr_source' U hU_open]
    exact ⟨hy_e0source, hy_shell.1⟩
  let p : e1.source := ⟨y, hy_e1source⟩
  let ec := e1.centerAt p
  have hcenter_image :
      ec '' ((U \ Metric.ball (0 : EuclideanSpace ℝ (Fin (k + 2))) 1) ∩ ec.source) =
        {z ∈ ec.target | 0 ≤ z 0} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨ec.map_source hx.2, ?_⟩
      have hx_e1source : x ∈ e1.source := by
        simpa [ec, OpenPartialHomeomorph.centerAt_source] using hx.2
      have hx_e0source : x ∈ e0.source := by
        change x ∈ (e0.restr U).source at hx_e1source
        rw [e0.restr_source' U hU_open] at hx_e1source
        exact hx_e1source.1
      have hx_nonneg : 0 ≤ e0 x 0 :=
        (unit_exterior_signed_shell_chart_apply_zero_nonneg_iff k i s
          (by simpa [e0, unit_exterior_signed_shell_chart_source] using hx_e0source)).2 hx.1.2
      have hcoord : ec x 0 = e0 x 0 := by
        simp [ec, e1, p, centerAt_apply_eq_sub_basepoint, hy_e0zero]
      simpa [hcoord] using hx_nonneg
    · intro hz
      refine ⟨ec.symm z, ?_, ec.right_inv hz.1⟩
      have hx_ecsource : ec.symm z ∈ ec.source := ec.map_target hz.1
      have hx_e1source : ec.symm z ∈ e1.source := by
        simpa [ec, OpenPartialHomeomorph.centerAt_source] using hx_ecsource
      have hx_e0source : ec.symm z ∈ e0.source := by
        change ec.symm z ∈ (e0.restr U).source at hx_e1source
        rw [e0.restr_source' U hU_open] at hx_e1source
        exact hx_e1source.1
      have hxU : ec.symm z ∈ U := by
        change ec.symm z ∈ (e0.restr U).source at hx_e1source
        rw [e0.restr_source' U hU_open] at hx_e1source
        exact hx_e1source.2
      have hx_nonneg : 0 ≤ e0 (ec.symm z) 0 := by
        have hcoord : ec (ec.symm z) 0 = e0 (ec.symm z) 0 := by
          simp [ec, e1, p, centerAt_apply_eq_sub_basepoint, hy_e0zero]
        rw [← hcoord, ec.right_inv hz.1]
        exact hz.2
      have hx_not_ball :
          ec.symm z ∉ Metric.ball (0 : EuclideanSpace ℝ (Fin (k + 2))) 1 :=
        (unit_exterior_signed_shell_chart_apply_zero_nonneg_iff k i s
          (by simpa [e0, unit_exterior_signed_shell_chart_source] using hx_e0source)).1 hx_nonneg
      exact ⟨⟨hxU, hx_not_ball⟩, hx_ecsource⟩
  let qL : EuclideanSpace ℝ (Fin (k + 2)) ≃L[ℝ] EuclideanSpace ℝ (Fin (k + 2)) :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (Equiv.swap 0 (Fin.last (k + 1)))).toContinuousLinearEquiv
  let q : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (k + 2)))
      (EuclideanSpace ℝ (Fin (k + 2))) :=
    qL.toHomeomorph.toOpenPartialHomeomorph
  let e := ec.trans q
  have he_source : e.source = ec.source := by
    ext x
    simp [e, q]
  have himage :
      e '' ((U \ Metric.ball (0 : EuclideanSpace ℝ (Fin (k + 2))) 1) ∩ e.source) =
        {z ∈ e.target | 0 ≤ z (Fin.last (k + 1))} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx_ec : x ∈ ec.source := he_source ▸ hx.2
      have hw : ec x ∈ {w ∈ ec.target | 0 ≤ w 0} := by
        rw [← hcenter_image]
        exact ⟨x, ⟨hx.1, hx_ec⟩, rfl⟩
      refine ⟨e.map_source hx.2, ?_⟩
      have hlast : qL (ec x) (Fin.last (k + 1)) = ec x 0 := by
        simpa [qL] using swap_zero_last_linear_isometry_apply_last k (ec x)
      simpa [e, q, OpenPartialHomeomorph.trans_apply, hlast] using hw.2
    · intro hz
      let x := e.symm z
      have hx_source : x ∈ e.source := e.map_target hz.1
      have hx_ecsource : x ∈ ec.source := he_source ▸ hx_source
      have hex : e x = z := e.right_inv hz.1
      have hx_nonneg : 0 ≤ ec x 0 := by
        have hlast : qL (ec x) (Fin.last (k + 1)) = ec x 0 := by
          simpa [qL] using swap_zero_last_linear_isometry_apply_last k (ec x)
        have hzlast : 0 ≤ e x (Fin.last (k + 1)) := by
          simpa [hex] using hz.2
        simpa [e, q, OpenPartialHomeomorph.trans_apply, hlast] using hzlast
      have hw : ec x ∈ {w ∈ ec.target | 0 ≤ w 0} :=
        ⟨ec.map_source hx_ecsource, hx_nonneg⟩
      rw [← hcenter_image] at hw
      rcases hw with ⟨x', hx', hxx'⟩
      have hxeq : x' = x := ec.injOn hx'.2 hx_ecsource hxx'
      subst x'
      exact ⟨x, ⟨hx'.1, hx_source⟩, e.right_inv hz.1⟩
  refine ⟨e, ?_, ?_⟩
  · rw [he_source]
    simpa [ec, OpenPartialHomeomorph.centerAt_source] using hy_e1source
  · refine ⟨?_, ?_⟩
    · have hrefl :
          OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin (k + 2))) ∈
            IsManifold.maximalAtlas (𝓡 (k + 2)) (⊤ : WithTop ℕ∞)
              (EuclideanSpace ℝ (Fin (k + 2))) := by
          simpa using!
            (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 (k + 2))).id_mem_maximalAtlas
      have he0max : e0 ∈
          IsManifold.maximalAtlas (𝓡 (k + 2)) (⊤ : WithTop ℕ∞)
            (EuclideanSpace ℝ (Fin (k + 2))) := by
        simpa [e0] using
          (trans_mem_maximalAtlas_of_mem_groupoid
            (m := k + 2) (X := EuclideanSpace ℝ (Fin (k + 2)))
            (e := OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin (k + 2))))
            hrefl (chi := unit_exterior_signed_shell_chart k i s)
            (unit_exterior_signed_shell_chart_mem_contDiffGroupoid k i s))
      have he1max : e1 ∈
          IsManifold.maximalAtlas (𝓡 (k + 2)) (⊤ : WithTop ℕ∞)
            (EuclideanSpace ℝ (Fin (k + 2))) := by
        simpa [e1] using!
          (restr_mem_maximalAtlas
            (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 (k + 2))) he0max hU_open)
      have hecmax : ec ∈
          IsManifold.maximalAtlas (𝓡 (k + 2)) (⊤ : WithTop ℕ∞)
            (EuclideanSpace ℝ (Fin (k + 2))) := by
        simpa [ec] using centerAt_mem_maximalAtlas e1 he1max p
      have hq : q ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 (k + 2)) := by
        simpa [q] using (euclidean_linear_equiv_mem_contDiffGroupoid (L := qL))
      simpa [e] using trans_mem_maximalAtlas_of_mem_groupoid hecmax hq
    · rw [Set.IsHalfSliceInChart, Set.IsEuclideanHalfSlice]
      rcases full_dimensional_halfslice_eq_last_coordinate_nonneg
          (m := k + 1) e.target with ⟨c, hc⟩
      refine ⟨by omega, le_rfl, c, ?_⟩
      calc
        e '' ((U \ Metric.ball (0 : EuclideanSpace ℝ (Fin (k + 2))) 1) ∩ e.source) =
            {z ∈ e.target | 0 ≤ z (Fin.last (k + 1))} := himage
        _ = Set.euclideanHalfSlice e.target (k + 2) (by omega) le_rfl c := by
          simpa [Nat.add_assoc] using hc.symm

/-- Helper for Problem 5-8: prove the Euclidean exterior-ball boundary chart theorem by splitting
the ambient dimension into the impossible `0` case, the one-dimensional ray case, and the
higher-dimensional shell case. -/
lemma unit_exterior_ball_has_boundary_slice_chart_at_sphere_point_explicit_dim
    {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))} (hU_open : IsOpen U)
    {y : EuclideanSpace ℝ (Fin n)}
    (hy_shell : y ∈ U \ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
    (hy_sphere : y ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    ∃ e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)),
      y ∈ e.source ∧
        e.IsBoundarySliceChart (U \ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) n := by
  cases n with
  | zero =>
      -- A point on the unit sphere rules out the zero-dimensional Euclidean model.
      exfalso
      have hpos :
          0 < Module.finrank ℝ (EuclideanSpace ℝ (Fin 0)) := by
        exact sphere_point_forces_positive_dim
          (E := EuclideanSpace ℝ (Fin 0)) (r := 1) (by norm_num) hy_sphere
      simpa using hpos
  | succ n =>
      cases n with
      | zero =>
          -- In dimension `1`, Lee's shell proof is the sign-normalized exterior-ray chart.
          obtain ⟨s, hs⟩ := unit_exterior_ray_exists_positive_sign hy_sphere
          simpa using unit_exterior_ray_chart_local_image s hU_open hy_shell hy_sphere hs
      | succ k =>
          -- In dimension `k + 2`, hand the proof to the dedicated shell-chart theorem above.
          simpa using
            (unit_exterior_signed_shell_boundary_slice_chart_at_sphere_point_succSucc
              (k := k) hU_open hy_shell hy_sphere)

/-- Helper for Problem 5-8: in orthonormal Euclidean coordinates, a sphere point should admit a
boundary slice chart for the exterior of the corresponding open ball. -/
lemma unit_exterior_ball_has_boundary_slice_chart_at_sphere_point
    {U : Set (EuclideanSpace ℝ (Fin dimM))} (hU_open : IsOpen U)
    {y : EuclideanSpace ℝ (Fin dimM)}
    (hy_shell : y ∈ U \ Metric.ball (0 : EuclideanSpace ℝ (Fin dimM)) 1)
    (hy_sphere : y ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin dimM)) 1) :
    ∃ e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin dimM)) (EuclideanSpace ℝ (Fin dimM)),
      y ∈ e.source ∧ e.IsBoundarySliceChart (U \ Metric.ball (0 : EuclideanSpace ℝ (Fin dimM)) 1)
        dimM := by
  -- Route correction: the ambient-dimension split now happens in the explicit theorem over `n`,
  -- so the `dimM`-indexed statement is just a thin adapter.
  simpa using
    (unit_exterior_ball_has_boundary_slice_chart_at_sphere_point_explicit_dim
      (n := dimM) hU_open hy_shell hy_sphere)

/-- Dimension-explicit composition helper used by the radius-rescaling argument. -/
private lemma trans_chart_image_eq_inter_source_explicit
    {n : ℕ} {X : Type*} [TopologicalSpace X]
    {S : Set X} {T : Set (EuclideanSpace ℝ (Fin n))}
    {chart : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n))}
    {e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))}
    (himage : chart '' (S ∩ chart.source) = T) :
    chart '' (S ∩ (chart.trans e).source) = T ∩ e.source := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx_source : x ∈ chart.source := by
      simpa [OpenPartialHomeomorph.trans_source] using hx.2.1
    have hyT : chart x ∈ T := by
      rw [← himage]
      exact ⟨x, ⟨hx.1, hx_source⟩, rfl⟩
    have hy_source : chart x ∈ e.source := by
      simpa [OpenPartialHomeomorph.trans_source] using hx.2.2
    exact ⟨hyT, hy_source⟩
  · intro hy
    rw [← himage] at hy
    rcases hy.1 with ⟨x, hx, rfl⟩
    refine ⟨x, ⟨hx.1, ?_⟩, rfl⟩
    simpa [OpenPartialHomeomorph.trans_source, hx.2] using hy.2

/-- Dimension-explicit version of shrinking the ambient set of a Euclidean half-slice. -/
private lemma euclideanHalfSlice_inter_eq_of_subset_explicit
    {n k : ℕ} {hk : 0 < k} {hkn : k ≤ n}
    {U V : Set (EuclideanSpace ℝ (Fin n))}
    {c : Fin (n - k) → ℝ}
    (hsub : Set.euclideanHalfSlice U k hk hkn c ⊆ V) :
    Set.euclideanHalfSlice U k hk hkn c =
      Set.euclideanHalfSlice (U ∩ V) k hk hkn c := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨⟨hxU, hxTail⟩, hxNonneg⟩
    exact ⟨⟨⟨hxU, hsub ⟨⟨hxU, hxTail⟩, hxNonneg⟩⟩, hxTail⟩, hxNonneg⟩
  · rintro ⟨⟨⟨hxU, hxV⟩, hxTail⟩, hxNonneg⟩
    exact ⟨⟨hxU, hxTail⟩, hxNonneg⟩

/-- Dimension-explicit boundary-slice transport used by the radius-rescaling argument. -/
private lemma trans_isBoundarySliceChart_of_local_image_explicit
    {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    [IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) X]
    {S : Set X} {T : Set (EuclideanSpace ℝ (Fin n))}
    {chart : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n))}
    {e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))}
    (htrans : chart.trans e ∈
      IsManifold.maximalAtlas (𝓡 n) (⊤ : WithTop ℕ∞) X)
    (hlocal : chart '' (S ∩ (chart.trans e).source) = T ∩ e.source)
    (hsub : T ⊆ chart.target)
    (he : e.IsBoundarySliceChart T n) :
    (chart.trans e).IsBoundarySliceChart S n := by
  rcases he.2 with ⟨hk, hkn, c, hc⟩
  refine ⟨htrans, ?_⟩
  rw [Set.IsHalfSliceInChart, Set.IsEuclideanHalfSlice]
  refine ⟨hk, hkn, c, ?_⟩
  have hHalfSlice_subset :
      Set.euclideanHalfSlice e.target n hk hkn c ⊆ e.symm ⁻¹' chart.target := by
    intro z hz
    rw [← hc] at hz
    rcases hz with ⟨y, hy, rfl⟩
    simpa [hy.2] using hsub hy.1
  calc
    (chart.trans e) '' (S ∩ (chart.trans e).source) =
        e '' (chart '' (S ∩ (chart.trans e).source)) := by
          ext z
          constructor
          · rintro ⟨x, hx, rfl⟩
            exact ⟨chart x, ⟨x, hx, rfl⟩, by simp [OpenPartialHomeomorph.trans_apply]⟩
          · rintro ⟨y, ⟨x, hx, rfl⟩, hz⟩
            exact ⟨x, hx, by simpa [OpenPartialHomeomorph.trans_apply] using hz⟩
    _ = e '' (T ∩ e.source) := by rw [hlocal]
    _ = Set.euclideanHalfSlice e.target n hk hkn c := hc
    _ = Set.euclideanHalfSlice (e.target ∩ e.symm ⁻¹' chart.target) n hk hkn c :=
      euclideanHalfSlice_inter_eq_of_subset_explicit hHalfSlice_subset
    _ = Set.euclideanHalfSlice (chart.trans e).target n hk hkn c := by
      rw [OpenPartialHomeomorph.trans_target]

/-- Helper for Problem 5-8: the arbitrary-radius exterior shell chart is just the unit-radius
shell chart transported by the global scaling `x ↦ (1 / r) • x`. -/
private lemma euclidean_exterior_ball_has_boundary_slice_chart_explicit
    {n : ℕ} {r : ℝ} (hr : 0 < r) {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU_open : IsOpen U) {y : EuclideanSpace ℝ (Fin n)}
    (hy_shell : y ∈ U \ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r)
    (hy_sphere : y ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) r) :
    ∃ e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)),
      y ∈ e.source ∧
        e.IsBoundarySliceChart (U \ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) n := by
  let V := EuclideanSpace ℝ (Fin n)
  have hr_inv_ne : r⁻¹ ≠ 0 := inv_ne_zero hr.ne'
  let scale : V ≃L[ℝ] V :=
    ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := V) (Units.mk0 r⁻¹ hr_inv_ne)
  let d : OpenPartialHomeomorph V V := scale.toHomeomorph.toOpenPartialHomeomorph
  let U1 : Set V := scale '' U
  have hscale_apply (x : V) : scale x = r⁻¹ • x := by
    simp [scale, Units.smul_def]
  have hball (x : V) :
      scale x ∈ Metric.ball (0 : V) 1 ↔ x ∈ Metric.ball (0 : V) r := by
    rw [Metric.mem_ball, Metric.mem_ball]
    simp only [dist_zero_right]
    rw [hscale_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    exact inv_mul_lt_one₀ hr
  have hsphere_norm : ‖y‖ = r := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hy_sphere
  have hy1_sphere : scale y ∈ Metric.sphere (0 : V) 1 := by
    rw [Metric.mem_sphere, dist_zero_right, hscale_apply, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr), hsphere_norm]
    exact inv_mul_cancel₀ hr.ne'
  have hy1_shell : scale y ∈ U1 \ Metric.ball (0 : V) 1 := by
    refine ⟨⟨y, hy_shell.1, rfl⟩, ?_⟩
    rw [hball]
    exact hy_shell.2
  have hU1_open : IsOpen U1 := scale.toHomeomorph.isOpenMap U hU_open
  rcases unit_exterior_ball_has_boundary_slice_chart_at_sphere_point_explicit_dim
      (n := n) hU1_open hy1_shell hy1_sphere with ⟨e1, hy1_source, he1⟩
  have himage_base :
      d '' ((U \ Metric.ball (0 : V) r) ∩ d.source) =
        U1 \ Metric.ball (0 : V) 1 := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨x, hx.1.1, by simp [d]⟩, ?_⟩
      simpa [d] using (show scale x ∉ Metric.ball (0 : V) 1 from
        (not_congr (hball x)).2 hx.1.2)
    · rintro ⟨⟨x, hxU, rfl⟩, hxball⟩
      refine ⟨x, ⟨⟨hxU, ?_⟩, by simp [d]⟩, by simp [d]⟩
      exact (not_congr (hball x)).1 (by simpa using hxball)
  have hlocal :
      d '' ((U \ Metric.ball (0 : V) r) ∩ (d.trans e1).source) =
        (U1 \ Metric.ball (0 : V) 1) ∩ e1.source :=
    trans_chart_image_eq_inter_source_explicit himage_base
  have hrefl : OpenPartialHomeomorph.refl V ∈
      IsManifold.maximalAtlas (𝓡 n) (⊤ : WithTop ℕ∞) V := by
    simpa using!
      (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 n)).id_mem_maximalAtlas
  have hd_group : d ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 n) := by
    simpa [d] using (euclidean_linear_equiv_mem_contDiffGroupoid (L := scale))
  have he1_group : e1 ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 n) := by
    have hcompat :=
      IsManifold.compatible_of_mem_maximalAtlas hrefl he1.mem_maximalAtlas
    rw [OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_trans] at hcompat
    exact hcompat
  have htrans_group : d.trans e1 ∈
      contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 n) :=
    (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 n)).trans hd_group he1_group
  have htrans : d.trans e1 ∈ IsManifold.maximalAtlas (𝓡 n)
      (⊤ : WithTop ℕ∞) V := by
    simpa using
      (trans_mem_maximalAtlas_of_mem_groupoid (e := OpenPartialHomeomorph.refl V)
        hrefl htrans_group)
  refine ⟨d.trans e1, ?_, ?_⟩
  · simpa [OpenPartialHomeomorph.trans_source, d] using hy1_source
  · exact trans_isBoundarySliceChart_of_local_image_explicit htrans hlocal (by simp [d]) he1

/-- Helper for Problem 5-8: the arbitrary-radius exterior shell chart is just the unit-radius
shell chart transported by the global scaling `x ↦ (1 / r) • x`. -/
lemma euclidean_exterior_ball_has_boundary_slice_chart_at_sphere_point
    {r : ℝ} (hr : 0 < r) {U : Set (EuclideanSpace ℝ (Fin dimM))} (hU_open : IsOpen U)
    {y : EuclideanSpace ℝ (Fin dimM)}
    (hy_shell : y ∈ U \ Metric.ball (0 : EuclideanSpace ℝ (Fin dimM)) r)
    (hy_sphere : y ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin dimM)) r) :
    ∃ e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin dimM)) (EuclideanSpace ℝ (Fin dimM)),
      y ∈ e.source ∧ e.IsBoundarySliceChart (U \ Metric.ball (0 : EuclideanSpace ℝ (Fin dimM)) r)
        dimM := by
  simpa using euclidean_exterior_ball_has_boundary_slice_chart_explicit
    (n := dimM) hr hU_open hy_shell hy_sphere

set_option maxHeartbeats 400000 in
/-- The orthonormal-coordinate chart is a maximal-atlas chart for the basis-transported
Euclidean structure.  Keeping this atlas calculation separate prevents the geometric transport
argument below from exhausting a single declaration's heartbeat budget. -/
private lemma basis_model_orthonormal_chart_data
    (b : Module.Basis (Fin dimM) ℝ E) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin dimM)) E :=
      basis_model_chartedSpace b
    let _ : IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) E :=
      basis_model_isManifold b
    let ortho : E ≃L[ℝ] EuclideanSpace ℝ (Fin dimM) :=
      (stdOrthonormalBasis ℝ E).repr.toContinuousLinearEquiv
    ∃ eOrtho : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin dimM)),
      eOrtho ∈ IsManifold.maximalAtlas (𝓡 dimM) (⊤ : WithTop ℕ∞) E ∧
        eOrtho.source = Set.univ ∧ ∀ x : E, eOrtho x = ortho x := by
  let V := EuclideanSpace ℝ (Fin dimM)
  let _ : ChartedSpace V E := basis_model_chartedSpace b
  dsimp only
  let _ : IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) E := basis_model_isManifold b
  let _ : TopologicalManifold dimM E := topologicalManifoldOfChartedSpace dimM E
  let ortho : E ≃L[ℝ] V := (stdOrthonormalBasis ℝ E).repr.toContinuousLinearEquiv
  let eBasis : OpenPartialHomeomorph E V :=
    (basis_model_diffeomorph b).symm.toHomeomorph.toOpenPartialHomeomorph
  let changeModel : V ≃L[ℝ] V := (basis_model_continuousLinearEquiv b).trans ortho
  let changeChart : OpenPartialHomeomorph V V :=
    changeModel.toHomeomorph.toOpenPartialHomeomorph
  let eOrtho : OpenPartialHomeomorph E V := eBasis.trans changeChart
  have heOrtho_apply (x : E) : eOrtho x = ortho x := by
    simp [eOrtho, eBasis, changeChart, changeModel, ortho, basis_model_diffeomorph,
      ContinuousLinearEquiv.apply_symm_apply]
    exact (basis_model_continuousLinearEquiv b).apply_symm_apply x
  have heOrtho_source : eOrtho.source = Set.univ := by
    ext x
    simp [eOrtho, eBasis, changeChart]
  have hId : OpenPartialHomeomorph.refl E ∈
      IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) E := by
    simpa using!
      (contDiffGroupoid (⊤ : WithTop ℕ∞)
        (modelWithCornersSelf ℝ E)).id_mem_maximalAtlas
  have heBasisMax : eBasis ∈
      IsManifold.maximalAtlas (𝓡 dimM) (⊤ : WithTop ℕ∞) E := by
    simpa [eBasis] using
      (basis_model_chart_mem_maximalAtlas (M := E) b
        (chart := OpenPartialHomeomorph.refl E) hId)
  have hchange : changeChart ∈
      contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 dimM) := by
    simpa [changeChart] using
      (euclidean_linear_equiv_mem_contDiffGroupoid (L := changeModel))
  have heOrthoMax : eOrtho ∈
      IsManifold.maximalAtlas (𝓡 dimM) (⊤ : WithTop ℕ∞) E := by
    simpa [eOrtho] using
      (trans_mem_maximalAtlas_of_mem_groupoid (e := eBasis) heBasisMax (chi := changeChart)
        hchange)
  exact ⟨eOrtho, heOrthoMax, heOrtho_source, heOrtho_apply⟩

/-- Postcomposition by a smooth Euclidean chart change preserves the maximal atlas.  This variant
only assumes the charted-space structure actually used by the proof. -/
private lemma problem58_trans_mem_maximalAtlas_of_mem_groupoid
    {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    [IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) X]
    {e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n))}
    (he : e ∈ IsManifold.maximalAtlas (𝓡 n) (⊤ : WithTop ℕ∞) X)
    {chi : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))}
    (hchi : chi ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 n)) :
    e.trans chi ∈ IsManifold.maximalAtlas (𝓡 n) (⊤ : WithTop ℕ∞) X := by
  rw [IsManifold.mem_maximalAtlas_iff]
  intro e' he'
  have he'max : e' ∈ IsManifold.maximalAtlas (𝓡 n) (⊤ : WithTop ℕ∞) X :=
    IsManifold.subset_maximalAtlas he'
  have hleft : e.symm.trans e' ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 n) :=
    IsManifold.compatible_of_mem_maximalAtlas he he'max
  have hright : e'.symm.trans e ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 n) :=
    IsManifold.compatible_of_mem_maximalAtlas he'max he
  constructor
  · rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc]
    exact (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 n)).trans
      ((contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 n)).symm hchi) hleft
  · have hright' : (e'.symm.trans e).trans chi ∈
        contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 n) :=
      (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 n)).trans hright hchi
    simpa [OpenPartialHomeomorph.trans_assoc] using hright'

/-- Pull a Euclidean boundary-slice chart back through a global chart in the maximal atlas. -/
private lemma pullback_boundary_slice_through_global_chart
    {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    [IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) X]
    {S : Set X} {T : Set (EuclideanSpace ℝ (Fin n))} {x : X}
    {chart : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n))}
    {e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))}
    (hchart : chart ∈ IsManifold.maximalAtlas (𝓡 n) (⊤ : WithTop ℕ∞) X)
    (hsource : chart.source = Set.univ)
    (hx : chart x ∈ e.source)
    (himage : chart '' (S ∩ chart.source) = T)
    (he : e.IsBoundarySliceChart T n) :
    ∃ e' : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)),
      x ∈ e'.source ∧ e'.IsBoundarySliceChart S n := by
  have hlocal :
      chart '' (S ∩ (chart.trans e).source) = T ∩ e.source :=
    trans_chart_image_eq_inter_source_explicit himage
  have hrefl : OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin n)) ∈
      IsManifold.maximalAtlas (𝓡 n) (⊤ : WithTop ℕ∞)
        (EuclideanSpace ℝ (Fin n)) := by
    simpa using!
      (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 n)).id_mem_maximalAtlas
  have he_group : e ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 n) := by
    simpa using IsManifold.compatible_of_mem_maximalAtlas hrefl he.mem_maximalAtlas
  have htrans : chart.trans e ∈
      IsManifold.maximalAtlas (𝓡 n) (⊤ : WithTop ℕ∞) X :=
    problem58_trans_mem_maximalAtlas_of_mem_groupoid (e := chart) hchart he_group
  have hsub : T ⊆ chart.target := by
    intro z hz
    rw [← himage] at hz
    rcases hz with ⟨w, hw, rfl⟩
    exact chart.map_source hw.2
  refine ⟨chart.trans e, ?_, ?_⟩
  · simpa [OpenPartialHomeomorph.trans_source, hsource] using hx
  · exact trans_isBoundarySliceChart_of_local_image_explicit htrans hlocal hsub he

set_option maxHeartbeats 800000 in
/-- Helper for Problem 5-8: in the transported Euclidean ambient structure, each frontier point of
`closure B \ B` should admit a boundary slice chart for the complement. -/
lemma ball_exterior_boundary_slice_chart_in_basis_model
    (b : Module.Basis (Fin dimM) ℝ E)
    {r : ℝ} (hr : 0 < r) {U : Set E} (hU_open : IsOpen U)
    {y : E} (hy_shell : y ∈ U \ Metric.ball (0 : E) r)
    (hy_sphere : y ∈ Metric.sphere (0 : E) r) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin dimM)) E :=
      basis_model_chartedSpace b
    let _ : IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) E :=
      basis_model_isManifold b
    ∃ e : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin dimM)),
      y ∈ e.source ∧ e.IsBoundarySliceChart (U \ Metric.ball (0 : E) r) dimM := by
  let V := EuclideanSpace ℝ (Fin dimM)
  let _ : ChartedSpace V E := basis_model_chartedSpace b
  dsimp only
  let _ : IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) E := basis_model_isManifold b
  let _ : TopologicalManifold dimM E := topologicalManifoldOfChartedSpace dimM E
  let ortho : E ≃L[ℝ] V := (stdOrthonormalBasis ℝ E).repr.toContinuousLinearEquiv
  rcases basis_model_orthonormal_chart_data (E := E) b with
    ⟨eOrtho, heOrthoMax, heOrtho_source, heOrtho_apply⟩
  let U1 : Set V := ortho '' U
  have hortho_norm (x : E) : ‖ortho x‖ = ‖x‖ := by
    change ‖(stdOrthonormalBasis ℝ E).repr x‖ = ‖x‖
    exact (stdOrthonormalBasis ℝ E).repr.norm_map x
  have hball (x : E) :
      ortho x ∈ Metric.ball (0 : V) r ↔ x ∈ Metric.ball (0 : E) r := by
    simp only [Metric.mem_ball, dist_zero_right]
    rw [hortho_norm]
  have hsphere (x : E) :
      ortho x ∈ Metric.sphere (0 : V) r ↔ x ∈ Metric.sphere (0 : E) r := by
    simp only [Metric.mem_sphere, dist_zero_right]
    rw [hortho_norm]
  have hU1_open : IsOpen U1 := ortho.toHomeomorph.isOpenMap U hU_open
  have hy1_shell : ortho y ∈ U1 \ Metric.ball (0 : V) r := by
    exact ⟨⟨y, hy_shell.1, rfl⟩, (not_congr (hball y)).2 hy_shell.2⟩
  have hy1_sphere : ortho y ∈ Metric.sphere (0 : V) r := (hsphere y).2 hy_sphere
  rcases euclidean_exterior_ball_has_boundary_slice_chart_at_sphere_point
      hr hU1_open hy1_shell hy1_sphere with ⟨e1, hy1_source, he1⟩
  have himage_base :
      eOrtho '' ((U \ Metric.ball (0 : E) r) ∩ eOrtho.source) =
        U1 \ Metric.ball (0 : V) r := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [heOrtho_apply]
      exact ⟨⟨x, hx.1.1, rfl⟩, (not_congr (hball x)).2 hx.1.2⟩
    · rintro ⟨⟨x, hxU, rfl⟩, hxball⟩
      refine ⟨x, ⟨⟨hxU, (not_congr (hball x)).1 hxball⟩, ?_⟩, ?_⟩
      · simp [heOrtho_source]
      · exact heOrtho_apply x
  have hy_e : eOrtho y ∈ e1.source := by
    rw [heOrtho_apply]
    exact hy1_source
  exact pullback_boundary_slice_through_global_chart heOrthoMax heOrtho_source
    hy_e himage_base he1

/-- Helper for Problem 5-8: in the transported Euclidean ambient structure, each frontier point of
`closure B \ B` should admit a boundary slice chart for the complement. -/
lemma regular_coordinate_ball_frontier_has_boundary_sliceChart_for_compl_of_pos {B : Set M}
    (hB : IsRegularCoordinateBall E B)
    (b : Module.Basis (Fin dimM) ℝ E)
    (hdim : 0 < dimM) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M :=
      basis_model_chartedSpace b
    let _ : IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) M :=
      basis_model_isManifold b
    ∀ x ∈ closure B \ B,
      ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin dimM)),
        x ∈ e.source ∧ e.IsBoundarySliceChart (Set.compl B) dimM := by
  let V := EuclideanSpace ℝ (Fin dimM)
  let _ : ChartedSpace V M := basis_model_chartedSpace b
  let _ : IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) M := basis_model_isManifold b
  dsimp only
  intro x hx
  rcases hB with
    ⟨chart, hchart, hclosure, r, r', hr, hrr', himage, hclosure_image, htarget⟩
  have hsubset : B ⊆ chart.source := fun z hz ↦ hclosure (subset_closure hz)
  have himage_diff : chart '' (chart.source \ B) = chart '' chart.source \ chart '' B :=
    chart.injOn.image_diff_subset hsubset
  have hcomplImage :
      chart '' ((Set.compl B) ∩ chart.source) = chart.target \ Metric.ball (0 : E) r := by
    calc
      chart '' ((Set.compl B) ∩ chart.source) = chart '' (chart.source \ B) := by
        ext z
        constructor
        · rintro ⟨w, hw, rfl⟩
          exact ⟨w, ⟨hw.2, hw.1⟩, rfl⟩
        · rintro ⟨w, hw, rfl⟩
          exact ⟨w, ⟨hw.2, hw.1⟩, rfl⟩
      _ = chart '' chart.source \ chart '' B := himage_diff
      _ = chart.target \ Metric.ball (0 : E) r := by
        rw [chart.image_source_eq_target, himage]
  have hy_shell : chart x ∈ chart.target \ Metric.ball (0 : E) r :=
    regular_coordinate_ball_witness_frontier_point_mem_ball_exterior
      hclosure hcomplImage hx
  have hy_sphere : chart x ∈ Metric.sphere (0 : E) r :=
    regular_coordinate_ball_witness_frontier_point_mem_sphere
      hclosure himage hclosure_image hx
  rcases ball_exterior_boundary_slice_chart_in_basis_model b hr chart.open_target
      hy_shell hy_sphere with ⟨e1, hy_source, he1⟩
  have hlocal :
      chart '' (Set.compl B ∩ (chart.trans e1).source) =
        (chart.target \ Metric.ball (0 : E) r) ∩ e1.source :=
    trans_chart_image_eq_inter_source_of_image_eq hcomplImage
  let eModel : OpenPartialHomeomorph E V :=
    (basis_model_diffeomorph b).symm.toHomeomorph.toOpenPartialHomeomorph
  let _ : ChartedSpace V E := basis_model_chartedSpace b
  let _ : IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) E := basis_model_isManifold b
  let _ : TopologicalManifold dimM E := topologicalManifoldOfChartedSpace dimM E
  have hId : OpenPartialHomeomorph.refl E ∈
      IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) E := by
    simpa using!
      (contDiffGroupoid (⊤ : WithTop ℕ∞)
        (modelWithCornersSelf ℝ E)).id_mem_maximalAtlas
  have heModelMax : eModel ∈
      IsManifold.maximalAtlas (𝓡 dimM) (⊤ : WithTop ℕ∞) E := by
    simpa [eModel] using
      (basis_model_chart_mem_maximalAtlas (M := E) b
        (chart := OpenPartialHomeomorph.refl E) hId)
  have hchartModelMax : chart.trans eModel ∈
      IsManifold.maximalAtlas (𝓡 dimM) (⊤ : WithTop ℕ∞) M := by
    simpa [eModel] using basis_model_chart_mem_maximalAtlas b hchart
  have hchange : eModel.symm.trans e1 ∈
      contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 dimM) :=
    IsManifold.compatible_of_mem_maximalAtlas heModelMax he1.mem_maximalAtlas
  have htransRaw : (chart.trans eModel).trans (eModel.symm.trans e1) ∈
      IsManifold.maximalAtlas (𝓡 dimM) (⊤ : WithTop ℕ∞) M :=
    problem58_trans_mem_maximalAtlas_of_mem_groupoid
      (e := chart.trans eModel) hchartModelMax hchange
  have hcancel : eModel.trans eModel.symm = OpenPartialHomeomorph.refl E := by
    simpa [eModel] using
      (Homeomorph.trans_toOpenPartialHomeomorph
        (basis_model_diffeomorph b).symm.toHomeomorph
        (basis_model_diffeomorph b).toHomeomorph).symm
  have htransEq :
      (chart.trans eModel).trans (eModel.symm.trans e1) = chart.trans e1 := by
    calc
      (chart.trans eModel).trans (eModel.symm.trans e1) =
          chart.trans (eModel.trans (eModel.symm.trans e1)) :=
        OpenPartialHomeomorph.trans_assoc (e := chart) (e' := eModel)
          (eModel.symm.trans e1)
      _ = chart.trans ((eModel.trans eModel.symm).trans e1) := by
        rw [OpenPartialHomeomorph.trans_assoc (e := eModel) (e' := eModel.symm) e1]
      _ = chart.trans e1 := by rw [hcancel, OpenPartialHomeomorph.refl_trans]
  have htrans : chart.trans e1 ∈
      IsManifold.maximalAtlas (𝓡 dimM) (⊤ : WithTop ℕ∞) M := by
    rwa [htransEq] at htransRaw
  refine ⟨chart.trans e1, ?_, ?_⟩
  · simpa [OpenPartialHomeomorph.trans_source, hclosure hx.1] using hy_source
  · exact trans_isBoundarySliceChart_of_local_image htrans hlocal diff_subset he1

/-- Helper for Problem 5-8: in the transported Euclidean ambient structure, each frontier point of
`closure B \ B` should admit a boundary slice chart for the complement. -/
lemma regular_coordinate_ball_frontier_has_boundary_sliceChart_for_compl {B : Set M}
    (hB : IsRegularCoordinateBall E B)
    (b : Module.Basis (Fin dimM) ℝ E) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M :=
      basis_model_chartedSpace b
    let _ : IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) M :=
      basis_model_isManifold b
    ∀ x ∈ closure B \ B,
      ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin dimM)),
        x ∈ e.source ∧ e.IsBoundarySliceChart (Set.compl B) dimM := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M := basis_model_chartedSpace b
  let _ : IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) M := basis_model_isManifold b
  dsimp only
  by_cases hdim : 0 < dimM
  · exact regular_coordinate_ball_frontier_has_boundary_sliceChart_for_compl_of_pos
      hB b hdim
  · have hdim0 : dimM = 0 := Nat.eq_zero_of_not_pos hdim
    intro x hx
    have hempty : closure B \ B = ∅ :=
      regular_coordinate_ball_frontier_eq_empty_of_dim_zero hB hdim0
    rw [hempty] at hx
    exact False.elim hx

/-- Helper for Problem 5-8: in positive ambient dimension, the geometric frontier `closure B \ B`
is homeomorphic to the standard unit sphere after first identifying it with the witness-radius
sphere and then transporting that sphere to Euclidean coordinates and rescaling to radius `1`. -/
lemma regular_coordinate_ball_frontier_homeomorph_to_boundarySphere {B : Set M}
    (hB : IsRegularCoordinateBall E B) (hdim : 0 < dimM) :
    Nonempty (↥(closure B \ B) ≃ₜ boundarySphere) := by
  rcases hB with
    ⟨chart, hchart, hclosure, r, r', hr, hrr', himage, hclosure_image, htarget⟩
  have hInj : Set.InjOn chart (closure B) := chart.injOn.mono hclosure
  have hfrontier_image :
      chart '' (closure B \ B) = Metric.sphere (0 : E) r := by
    calc
      chart '' (closure B \ B) = chart '' closure B \ chart '' B :=
        hInj.image_diff_subset subset_closure
      _ = Metric.closedBall (0 : E) r \ Metric.ball (0 : E) r := by
        rw [hclosure_image, himage]
      _ = Metric.sphere (0 : E) r := Metric.closedBall_diff_ball
  let hChart : ↥(closure B \ B) ≃ₜ Metric.sphere (0 : E) r :=
    chart.homeomorphOfImageSubsetSource (diff_subset.trans hclosure) hfrontier_image
  let V := EuclideanSpace ℝ (Fin dimM)
  let ortho : E ≃ₗᵢ[ℝ] V := (stdOrthonormalBasis ℝ E).repr
  let hOrtho : Metric.sphere (0 : E) r ≃ₜ Metric.sphere (0 : V) r :=
    ortho.toHomeomorph.subtype (by
      intro x
      simp only [Metric.mem_sphere, dist_zero_right]
      change ‖x‖ = r ↔ ‖ortho x‖ = r
      rw [ortho.norm_map])
  let scale : V ≃ₜ V := Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne')
  let hScale : Metric.sphere (0 : V) r ≃ₜ Metric.sphere (0 : V) 1 :=
    scale.subtype (by
      intro x
      have hscale_norm : ‖scale x‖ = r⁻¹ * ‖x‖ := by
        simp [scale, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
      simp only [Metric.mem_sphere, dist_zero_right]
      rw [hscale_norm]
      constructor
      · intro hx
        rw [hx, inv_mul_cancel₀ hr.ne']
      · intro hx
        calc
          ‖x‖ = r * (r⁻¹ * ‖x‖) := by field_simp
          _ = r * 1 := congrArg (r * ·) hx
          _ = r := by ring)
  have hdim_succ : (dimM - 1) + 1 = dimM := by omega
  let reindex : V ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin ((dimM - 1) + 1)) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr hdim_succ.symm)
  let hReindex : Metric.sphere (0 : V) 1 ≃ₜ boundarySphere :=
    reindex.toHomeomorph.subtype (by
      intro x
      simp only [Metric.mem_sphere, dist_zero_right]
      change ‖x‖ = 1 ↔ ‖reindex x‖ = 1
      rw [reindex.norm_map])
  refine ⟨?_⟩
  exact hChart.trans (hOrtho.trans (hScale.trans hReindex))

/-- Helper for Problem 5-8: transport a Euclidean charted-space structure across a
homeomorphism. -/
private noncomputable abbrev problem58TransportedChartedSpace
    {n : ℕ} {R N : Type*} [TopologicalSpace R] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) R] (e : R ≃ₜ N) :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) N := by
  let eN : OpenPartialHomeomorph N R := e.symm.toOpenPartialHomeomorph
  let _ : ChartedSpace R N := eN.singletonChartedSpace (by
    ext x
    simp [eN])
  exact ChartedSpace.comp (EuclideanSpace ℝ (Fin n)) R N

/-- The preferred chart in the transported structure is the transporting homeomorphism followed
by the preferred chart at the corresponding source point. -/
private lemma problem58TransportedChartedSpace_chartAt
    {n : ℕ} {R N : Type*} [TopologicalSpace R] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) R]
    (e : R ≃ₜ N) (y : N) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) N :=
      problem58TransportedChartedSpace e
    chartAt (EuclideanSpace ℝ (Fin n)) y =
      e.symm.toOpenPartialHomeomorph.trans
        (chartAt (EuclideanSpace ℝ (Fin n)) (e.symm y)) := by
  rfl

/-- Helper for Problem 5-8: the smooth manifold structure transports across the preceding
homeomorphism construction. -/
private lemma problem58TransportedIsManifold
    {n : ℕ} {R N : Type*} [TopologicalSpace R] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) R]
    [IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) R]
    (e : R ≃ₜ N) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) N :=
      problem58TransportedChartedSpace e
    IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) N := by
  let eN : OpenPartialHomeomorph N R := e.symm.toOpenPartialHomeomorph
  have heN_source : eN.source = Set.univ := by
    ext x
    simp [eN]
  let _ : ChartedSpace R N := eN.singletonChartedSpace heN_source
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) N :=
    problem58TransportedChartedSpace e
  have hGroupoid : HasGroupoid N (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 n)) := by
    refine ⟨?_⟩
    rintro _ _ ⟨f, hf, c, hc, rfl⟩ ⟨f', hf', c', hc', rfl⟩
    have hfEq : f = eN := by
      simpa [eN] using eN.singletonChartedSpace_mem_atlas_eq heN_source f hf
    have hf'Eq : f' = eN := by
      simpa [eN] using eN.singletonChartedSpace_mem_atlas_eq heN_source f' hf'
    subst f
    subst f'
    have hmid : eN.symm.trans eN = OpenPartialHomeomorph.refl R := by
      simpa [eN] using (Homeomorph.trans_toOpenPartialHomeomorph e e.symm).symm
    have hcompat :
        ((c.symm.trans eN.symm).trans eN).trans c' ∈
          contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 n) := by
      have hinner : (c.symm.trans eN.symm).trans eN =
          c.symm.trans (eN.symm.trans eN) :=
        OpenPartialHomeomorph.trans_assoc (e := c.symm) (e' := eN.symm) eN
      rw [hinner, hmid, OpenPartialHomeomorph.trans_refl]
      exact HasGroupoid.compatible hc hc'
    simpa [eN, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc] using hcompat
  let _ : HasGroupoid N (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 n)) := hGroupoid
  exact IsManifold.mk' (𝓡 n) (⊤ : WithTop ℕ∞) N

/-- Helper for Problem 5-8: with the transported structure, the transporting homeomorphism is a
diffeomorphism. -/
private noncomputable def problem58TransportedDiffeomorph
    {n : ℕ} {R N : Type*} [TopologicalSpace R] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) R]
    [IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) R]
    (e : R ≃ₜ N) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) N :=
      problem58TransportedChartedSpace e
    let _ : IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) N :=
      problem58TransportedIsManifold e
    R ≃ₘ^(⊤ : WithTop ℕ∞)⟮𝓡 n, 𝓡 n⟯ N := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) N :=
    problem58TransportedChartedSpace e
  let _ : IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) N :=
    problem58TransportedIsManifold e
  refine
    { toEquiv := e.toEquiv
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · rw [contMDiff_iff_target]
    refine ⟨e.continuous, ?_⟩
    intro y
    convert (contMDiffOn_extChartAt (I := 𝓡 n) (n := (⊤ : WithTop ℕ∞))
      (x := e.symm y)) using 1
    · funext x
      simp [problem58TransportedChartedSpace_chartAt, Function.comp]
    · ext x
      simp [problem58TransportedChartedSpace_chartAt, Function.comp]
  · rw [contMDiff_iff_target]
    refine ⟨e.symm.continuous, ?_⟩
    intro y
    convert (contMDiffOn_extChartAt (I := 𝓡 n) (n := (⊤ : WithTop ℕ∞))
      (x := e y)) using 1
    · funext x
      simp [problem58TransportedChartedSpace_chartAt, Function.comp]
    · ext x
      simp [problem58TransportedChartedSpace_chartAt, Function.comp]

/-- Lowering the differentiability index preserves the local normal forms defining an
immersion. -/
private lemma problem58IsImmersionOfLE
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
    {H₁ : Type*} [TopologicalSpace H₁]
    {X : Type*} [TopologicalSpace X] [ChartedSpace H₁ X]
    {I₁ : ModelWithCorners 𝕜 E₁ H₁} [IsManifold I₁ (⊤ : WithTop ℕ∞) X]
    {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
    {H₂ : Type*} [TopologicalSpace H₂]
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace H₂ Y]
    {I₂ : ModelWithCorners 𝕜 E₂ H₂} [IsManifold I₂ (⊤ : WithTop ℕ∞) Y]
    {m n : WithTop ℕ∞} {f : X → Y} (hmn : m ≤ n)
    (hf : Manifold.IsImmersion I₁ I₂ n f) :
    Manifold.IsImmersion I₁ I₂ m f := by
  let F := hf.complement
  let hF := hf.isImmersionOfComplement_complement
  refine ⟨F, inferInstance, inferInstance, ?_⟩
  intro x
  let hx := hF x
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts
    hx.equiv hx.domChart hx.codChart hx.mem_domChart_source hx.mem_codChart_source ?_ ?_
      hx.source_subset_preimage_source hx.writtenInCharts
  · exact (IsManifold.maximalAtlas_subset_of_le hmn) hx.domChart_mem_maximalAtlas
  · exact (IsManifold.maximalAtlas_subset_of_le hmn) hx.codChart_mem_maximalAtlas

/-- The identity from the basis-transported Euclidean model to the original model is an
immersion. -/
private lemma basis_model_identity_isImmersion_to_original
    (b : Module.Basis (Fin dimM) ℝ E) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M :=
      basis_model_chartedSpace b
    let _ : IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) M :=
      basis_model_isManifold b
    Manifold.IsImmersion (𝓡 dimM) (modelWithCornersSelf ℝ E)
      (⊤ : WithTop ℕ∞) (id : M → M) := by
  let V := EuclideanSpace ℝ (Fin dimM)
  let _ : ChartedSpace V M := basis_model_chartedSpace b
  let _ : IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) M := basis_model_isManifold b
  let eModel : OpenPartialHomeomorph E V :=
    (basis_model_diffeomorph b).symm.toHomeomorph.toOpenPartialHomeomorph
  refine ⟨PUnit.{uE + 1}, inferInstance, inferInstance, ?_⟩
  intro x
  let codChart : OpenPartialHomeomorph M E := chartAt E x
  let domChart : OpenPartialHomeomorph M V := codChart.trans eModel
  let equiv : (V × PUnit.{uE + 1}) ≃L[ℝ] E :=
    (ContinuousLinearEquiv.prodUnique ℝ V PUnit.{uE + 1}).trans
      (basis_model_continuousLinearEquiv b)
  have hcodChart : codChart ∈
      IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M := by
    exact IsManifold.chart_mem_maximalAtlas x
  have hdomChart : domChart ∈
      IsManifold.maximalAtlas (𝓡 dimM) (⊤ : WithTop ℕ∞) M := by
    simpa [domChart, codChart, eModel] using
      basis_model_chart_mem_maximalAtlas b hcodChart
  refine Manifold.IsImmersionAtOfComplement.mk_of_continuousAt continuousAt_id equiv
    domChart codChart ?_ ?_ hdomChart hcodChart ?_
  · simpa [domChart, codChart, eModel, OpenPartialHomeomorph.trans_source] using
      (mem_chart_source E x)
  · exact mem_chart_source E x
  intro u hu
  have hu_target : (basis_model_continuousLinearEquiv b) u ∈ codChart.target := by
    simpa [domChart, codChart, eModel, OpenPartialHomeomorph.extend_target,
      OpenPartialHomeomorph.trans_target, basis_model_diffeomorph,
      basis_model_continuousLinearEquiv] using hu
  have hequiv_apply :
      equiv (u, (0 : PUnit.{uE + 1})) = (basis_model_continuousLinearEquiv b) u := by
    simp only [equiv, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.prodUnique_apply]
    rfl
  simp only [Function.comp_apply, id_eq]
  rw [hequiv_apply]
  simpa [Function.comp, domChart, codChart, eModel,
    OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    basis_model_diffeomorph, basis_model_continuousLinearEquiv] using
      codChart.right_inv hu_target

-- Proof sketch: choose a chart witnessing that `B` is a regular coordinate ball. In this chart,
-- the complement of the round open ball is diffeomorphic to a Euclidean half-space, so the
-- complement carries the chapter's canonical owner `SmoothManifoldWithBoundary dimM`; the ambient
-- compatibility is then expressed by the codimension-`0` owner `Set.IsRegularDomain`.
/-- Problem 5-8 (1), existence half: the complement of a regular coordinate ball carries a smooth
manifold-with-boundary structure making it a regular domain in the ambient manifold. -/
theorem regularCoordinateBall_compl_exists_smoothManifoldWithBoundary
    [T2Space M] [SecondCountableTopology M]
    {B : Set M} (hB : IsRegularCoordinateBall E B) :
    ∃ instSmooth : SmoothManifoldWithBoundary dimM (Set.compl B),
      letI : SmoothManifoldWithBoundary dimM (Set.compl B) := instSmooth
      Set.IsRegularDomain (modelWithCornersSelf ℝ E) (Set.compl B) := by
  let b : Module.Basis (Fin dimM) ℝ E := Module.finBasis ℝ E
  let instCharted : ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M :=
    basis_model_chartedSpace b
  letI : ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M := instCharted
  let instManifold : IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) M :=
    basis_model_isManifold b
  letI : IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) M := instManifold
  letI : TopologicalManifold dimM M :=
    topologicalManifoldOfChartedSpace dimM M
  have hfrontier :=
    regular_coordinate_ball_frontier_has_boundary_sliceChart_for_compl hB b
  have hlocal :
      Set.SatisfiesLocalSliceConditionWithBoundary dimM (Set.compl B) dimM :=
    regular_coordinate_ball_compl_satisfiesLocalSliceConditionWithBoundary hB hfrontier
  rcases (local_slice_criterion_for_embedded_submanifold_with_boundary
      dimM (Set.compl B)).mp hlocal with ⟨instSmooth, hEmbBasis⟩
  refine ⟨instSmooth, ?_⟩
  letI : SmoothManifoldWithBoundary dimM (Set.compl B) := instSmooth
  have hModelImmersionTop :
      Manifold.IsImmersion (𝓡 dimM) (modelWithCornersSelf ℝ E)
        (⊤ : WithTop ℕ∞) (id : M → M) :=
    basis_model_identity_isImmersion_to_original (M := M) b
  have hModelImmersion :
      Manifold.IsImmersion (𝓡 dimM) (modelWithCornersSelf ℝ E)
        (∞ : WithTop ℕ∞) (id : M → M) :=
    problem58IsImmersionOfLE (by simp) hModelImmersionTop
  have hEmbBasisImmersion :
      Manifold.IsImmersion (leeBoundaryModelWithCorners dimM) (𝓡 dimM)
        (∞ : WithTop ℕ∞) ((↑) : Set.compl B → M) :=
    problem58IsImmersionOfLE (by simp) hEmbBasis.isImmersion
  have hEmbOriginal :
      Manifold.IsSmoothEmbedding
        (leeBoundaryModelWithCorners dimM)
        (modelWithCornersSelf ℝ E)
        (∞ : WithTop ℕ∞)
        ((↑) : Set.compl B → M) := by
    refine ⟨?_, hEmbBasis.isEmbedding⟩
    simpa [Function.comp] using
      Manifold.IsImmersion.ex416_comp hModelImmersion hEmbBasisImmersion
  exact
    { isSmoothEmbedding_subtype_val := hEmbOriginal
      isProperlyEmbedded := (regular_coordinate_ball_compl_isClosed hB).isProperlyEmbedded }

-- Proof sketch: first use the existence half to choose a smooth manifold-with-boundary structure
-- on `Bᶜ` making it a regular domain. For that chosen complement structure, its boundary subtype
-- admits the induced smooth structure coming from the round-ball chart, and that boundary
-- manifold is diffeomorphic to the standard unit sphere. Positive ambient dimension is a genuine
-- hypothesis only for this sphere conclusion, so it is kept explicitly here rather than as a
-- global instance.
/-- Problem 5-8 (2), boundary half: the complement of a regular coordinate ball admits a smooth
manifold-with-boundary structure making it a regular domain, and for that induced complement
structure its boundary is diffeomorphic to the standard sphere `S^(n - 1)`. -/
theorem regularCoordinateBall_compl_boundary_diffeomorph_sphere
    [T2Space M] [SecondCountableTopology M]
    {B : Set M} (hB : IsRegularCoordinateBall E B)
    (hdim : 0 < dimM) :
    ∃ instSmooth : SmoothManifoldWithBoundary dimM (Set.compl B),
      letI : SmoothManifoldWithBoundary dimM (Set.compl B) := instSmooth
      ∃ hRegular : Set.IsRegularDomain (modelWithCornersSelf ℝ E) (Set.compl B),
        ∃ _ : ChartedSpace (EuclideanSpace ℝ (Fin (dimM - 1)))
          ↥((leeBoundaryModelWithCorners dimM).boundary (Set.compl B)),
          ∃ _ : IsManifold
            (𝓡 (dimM - 1))
            (⊤ : WithTop ℕ∞)
            ↥((leeBoundaryModelWithCorners dimM).boundary (Set.compl B)),
            Nonempty
              (↥((leeBoundaryModelWithCorners dimM).boundary (Set.compl B)) ≃ₘ⟮𝓡 (dimM - 1),
                𝓡 (dimM - 1)⟯ boundarySphere) := by
  rcases regularCoordinateBall_compl_exists_smoothManifoldWithBoundary hB with
    ⟨instSmooth, hRegular⟩
  refine ⟨instSmooth, ?_⟩
  letI : SmoothManifoldWithBoundary dimM (Set.compl B) := instSmooth
  refine ⟨hRegular, ?_⟩
  have hBoundaryImage :
      Subtype.val ''
          (leeBoundaryModelWithCorners dimM).boundary (Set.compl B) =
        frontier (Set.compl B) := by
    exact regular_domain_manifoldBoundary_image_eq_frontier
      (I := modelWithCornersSelf ℝ E)
  let hBoundaryFrontier :
      ↥((leeBoundaryModelWithCorners dimM).boundary (Set.compl B)) ≃ₜ
        ↥(frontier (Set.compl B)) :=
    (Topology.IsEmbedding.subtypeVal.homeomorphImage
      ((leeBoundaryModelWithCorners dimM).boundary (Set.compl B))).trans
      (Homeomorph.setCongr hBoundaryImage)
  let hBoundaryGeometric :
      ↥((leeBoundaryModelWithCorners dimM).boundary (Set.compl B)) ≃ₜ
        ↥(closure B \ B) :=
    hBoundaryFrontier.trans
      (Homeomorph.setCongr
        (regular_coordinate_ball_compl_frontier_eq_closure_diff hB))
  rcases regular_coordinate_ball_frontier_homeomorph_to_boundarySphere hB hdim with
    ⟨hGeometricSphere⟩
  let hBoundarySphere :
      ↥((leeBoundaryModelWithCorners dimM).boundary (Set.compl B)) ≃ₜ boundarySphere :=
    hBoundaryGeometric.trans hGeometricSphere
  let instCharted : ChartedSpace (EuclideanSpace ℝ (Fin (dimM - 1)))
      ↥((leeBoundaryModelWithCorners dimM).boundary (Set.compl B)) :=
    problem58TransportedChartedSpace hBoundarySphere.symm
  refine ⟨instCharted, ?_⟩
  letI : ChartedSpace (EuclideanSpace ℝ (Fin (dimM - 1)))
      ↥((leeBoundaryModelWithCorners dimM).boundary (Set.compl B)) := instCharted
  let instManifold : IsManifold (𝓡 (dimM - 1)) (⊤ : WithTop ℕ∞)
      ↥((leeBoundaryModelWithCorners dimM).boundary (Set.compl B)) :=
    problem58TransportedIsManifold hBoundarySphere.symm
  refine ⟨instManifold, ?_⟩
  letI : IsManifold (𝓡 (dimM - 1)) (⊤ : WithTop ℕ∞)
      ↥((leeBoundaryModelWithCorners dimM).boundary (Set.compl B)) := instManifold
  let topDiffeomorph :
      ↥((leeBoundaryModelWithCorners dimM).boundary (Set.compl B))
        ≃ₘ^(⊤ : WithTop ℕ∞)⟮𝓡 (dimM - 1), 𝓡 (dimM - 1)⟯ boundarySphere :=
    (problem58TransportedDiffeomorph (n := dimM - 1) hBoundarySphere.symm).symm
  refine ⟨{
    toEquiv := topDiffeomorph.toEquiv
    contMDiff_toFun := topDiffeomorph.contMDiff.of_le (by simp)
    contMDiff_invFun := topDiffeomorph.symm.contMDiff.of_le (by simp) }⟩
