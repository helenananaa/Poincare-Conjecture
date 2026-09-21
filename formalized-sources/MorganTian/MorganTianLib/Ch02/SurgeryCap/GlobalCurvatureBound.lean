import MorganTianLib.Ch02.SurgeryCap.FullPuncturedCurvature
import MorganTianLib.Ch02.SurgeryCap.CurvatureNaturality
import MorganTianLib.Ch02.SurgeryCap.PolarMetric
open Set Riemannian
open scoped ContDiff Manifold Topology
noncomputable section
namespace MorganTianLib.SurgeryCap
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- **Math.** The constructed global cap has nonnegative uniformly bounded
sectional curvature on every plane, including the tip. -/
theorem RoundCapProfile.global_curvature_nonneg_bounded (P : RoundCapProfile) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X Y : SmoothVectorField (𝓡 3) E3) (x : E3),
        0 ≤ P.globalMetric.metricInner x
          (P.globalMetric.leviCivitaConnection.curvature X Y X x) (Y x) ∧
        P.globalMetric.metricInner x
          (P.globalMetric.leviCivitaConnection.curvature X Y X x) (Y x) ≤
          C * (P.globalMetric.metricInner x (X x) (X x) *
            P.globalMetric.metricInner x (Y x) (Y x) -
            P.globalMetric.metricInner x (X x) (Y x) ^ 2) := by
/- SWARM_PROOF_BEGIN -/
  obtain ⟨C, hC, hpunct⟩ := P.punctured_curvature_nonneg_bounded
  refine ⟨C, hC, ?_⟩
  intro X Y
  obtain ⟨phi, hphi, hmetric⟩ := exists_cap_polar_metric_preserving P
  let e : E3 := EuclideanSpace.single 0 (1 : ℝ)
  have he : e ≠ 0 := by
    simp [e]
  let q0 : ↥capPuncturedSpace := ⟨e, he⟩
  have hne : Nonempty (↥capPuncturedSpace) := ⟨q0⟩
  let ph := capPuncturedSpace.openPartialHomeomorphSubtypeCoe hne
  have hph : (ph : (↥capPuncturedSpace) → E3) = Subtype.val := by
    exact TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_coe
      capPuncturedSpace hne
  have hinv : ContMDiffOn (𝓡 3) (𝓡 3) ∞ ph.symm ph.target := by
    intro x hx
    apply (ContMDiffWithinAt.subtypeVal_comp_iff capPuncturedSpace ph.symm
      ph.target x).mp
    have hid : ContMDiffWithinAt (𝓡 3) (𝓡 3) ∞
        (id : E3 → E3) ph.target x := contMDiffWithinAt_id
    apply hid.congr_of_eventuallyEq
    · have hmem : ∀ᶠ y in 𝓝[ph.target] x, y ∈ ph.target := self_mem_nhdsWithin
      exact hmem.mono (fun y hy => by
        have hri := ph.right_inv hy
        rw [hph] at hri
        simpa [Function.comp_def] using hri)
    · have hri := ph.right_inv hx
      rw [hph] at hri
      exact hri
  let inc : PartialDiffeomorph (𝓡 3) (𝓡 3)
      (↥capPuncturedSpace) E3 ∞ := {
    toPartialEquiv := ph.toPartialEquiv
    open_source := ph.open_source
    open_target := ph.open_target
    contMDiffOn_toFun := by
      exact (Riemannian.contMDiff_subtype_val_opens :
        ContMDiff (𝓡 3) (𝓡 3) ∞
          (Subtype.val : ↥capPuncturedSpace → E3)).contMDiffOn
    contMDiffOn_invFun := hinv }
  have hinc : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (Subtype.val : (↥capPuncturedSpace) → E3) := by
    intro x
    apply inc.isLocalDiffeomorphAt
    simp [inc, ph]
  let f : PuncturedCap → E3 := fun p => (phi p : E3)
  have hf : IsLocalDiffeomorph PuncturedCapModel (𝓡 3) ∞ f := by
    intro p
    have hcomp := (phi.isLocalDiffeomorph p).comp (𝓡 3) E3 (hinc (phi p))
    simpa [f, Function.comp_def] using hcomp
  have hf_inv : ∀ p : PuncturedCap,
      (mfderiv PuncturedCapModel (𝓡 3) f p).IsInvertible := by
    intro p
    rw [← (hf p).mfderivToContinuousLinearEquiv_coe (by simp)]
    exact ContinuousLinearMap.isInvertible_equiv
  let Xp : SmoothVectorField PuncturedCapModel PuncturedCap :=
    { toFun := fun p => VectorField.mpullback PuncturedCapModel (𝓡 3)
        f X.toFun p
      smooth := by
        simpa using
          (ContMDiff.mpullback_vectorField (V := X.toFun) (m := ∞) (n := ∞)
            X.smooth hf.contMDiff hf_inv (by simp)) }
  let Yp : SmoothVectorField PuncturedCapModel PuncturedCap :=
    { toFun := fun p => VectorField.mpullback PuncturedCapModel (𝓡 3)
        f Y.toFun p
      smooth := by
        simpa using
          (ContMDiff.mpullback_vectorField (V := Y.toFun) (m := ∞) (n := ∞)
            Y.smooth hf.contMDiff hf_inv (by simp)) }
  have hXp : ∀ p : PuncturedCap,
      mfderiv PuncturedCapModel (𝓡 3) f p (Xp p) = X (f p) := by
    intro p
    change mfderiv PuncturedCapModel (𝓡 3) f p
        ((mfderiv PuncturedCapModel (𝓡 3) f p).inverse (X.toFun (f p))) = _
    exact (hf_inv p).self_apply_inverse _
  have hYp : ∀ p : PuncturedCap,
      mfderiv PuncturedCapModel (𝓡 3) f p (Yp p) = Y (f p) := by
    intro p
    change mfderiv PuncturedCapModel (𝓡 3) f p
        ((mfderiv PuncturedCapModel (𝓡 3) f p).inverse (Y.toFun (f p))) = _
    exact (hf_inv p).self_apply_inverse _
  have hconnP : leviCivitaConnectionGeneral P.puncturedMetric =
      P.puncturedConnection := by
    apply AffineConnection.leviCivita_unique' P.puncturedMetric
    · exact leviCivitaConnectionGeneral_isLeviCivita P.puncturedMetric
    · simpa [RoundCapProfile.puncturedConnection, RoundCapProfile.puncturedMetric] using
        (warpedConnection_isLeviCivita unitRoundSphereMetric P.w P.smooth P.positive)
  have hconnG : leviCivitaConnectionGeneral P.globalMetric =
      P.globalMetric.leviCivitaConnection := by
    apply AffineConnection.leviCivita_unique' P.globalMetric
    · exact leviCivitaConnectionGeneral_isLeviCivita P.globalMetric
    · exact P.globalMetric.leviCivitaConnection.isLeviCivita_of_koszulDual
        P.globalMetric (fun A B D q => P.globalMetric.koszulDualSection_dual A B D q)
  have hmetric' : ∀ (p : PuncturedCap) (u v : TangentSpace PuncturedCapModel p),
      P.puncturedMetric.metricInner p u v =
        P.globalMetric.metricInner (f p)
          (mfderiv PuncturedCapModel (𝓡 3) f p u)
          (mfderiv PuncturedCapModel (𝓡 3) f p v) := by
    intro p u v
    simpa [f] using hmetric p u v
  have hcurv : ∀ p : PuncturedCap,
      mfderiv PuncturedCapModel (𝓡 3) f p
          (P.puncturedConnection.curvature Xp Yp Xp p) =
        P.globalMetric.leviCivitaConnection.curvature X Y X (f p) := by
    intro p
    have h := local_metric_map_curvature_related f hf P.puncturedMetric
      P.globalMetric hmetric' Xp Yp Xp X Y X hXp hYp hXp p
    rw [hconnP, hconnG] at h
    exact h
  have hscalar : ∀ p : PuncturedCap,
      P.globalMetric.metricInner (f p)
          (P.globalMetric.leviCivitaConnection.curvature X Y X (f p)) (Y (f p)) =
        P.puncturedMetric.metricInner p
          (P.puncturedConnection.curvature Xp Yp Xp p) (Yp p) := by
    intro p
    calc
      P.globalMetric.metricInner (f p)
          (P.globalMetric.leviCivitaConnection.curvature X Y X (f p)) (Y (f p)) =
          P.globalMetric.metricInner (f p)
            (mfderiv PuncturedCapModel (𝓡 3) f p
              (P.puncturedConnection.curvature Xp Yp Xp p)) (Y (f p)) := by
            rw [hcurv p]
      _ = P.globalMetric.metricInner (f p)
            (mfderiv PuncturedCapModel (𝓡 3) f p
              (P.puncturedConnection.curvature Xp Yp Xp p))
            (mfderiv PuncturedCapModel (𝓡 3) f p (Yp p)) := by
            rw [hYp p]
      _ = P.puncturedMetric.metricInner p
          (P.puncturedConnection.curvature Xp Yp Xp p) (Yp p) := by
            exact (hmetric' p _ _).symm
  have hXX : ∀ p : PuncturedCap,
      P.globalMetric.metricInner (f p) (X (f p)) (X (f p)) =
        P.puncturedMetric.metricInner p (Xp p) (Xp p) := by
    intro p
    calc
      P.globalMetric.metricInner (f p) (X (f p)) (X (f p)) =
          P.globalMetric.metricInner (f p)
            (mfderiv PuncturedCapModel (𝓡 3) f p (Xp p))
            (mfderiv PuncturedCapModel (𝓡 3) f p (Xp p)) := by rw [hXp p]
      _ = P.puncturedMetric.metricInner p (Xp p) (Xp p) :=
        (hmetric' p _ _).symm
  have hYY : ∀ p : PuncturedCap,
      P.globalMetric.metricInner (f p) (Y (f p)) (Y (f p)) =
        P.puncturedMetric.metricInner p (Yp p) (Yp p) := by
    intro p
    calc
      P.globalMetric.metricInner (f p) (Y (f p)) (Y (f p)) =
          P.globalMetric.metricInner (f p)
            (mfderiv PuncturedCapModel (𝓡 3) f p (Yp p))
            (mfderiv PuncturedCapModel (𝓡 3) f p (Yp p)) := by rw [hYp p]
      _ = P.puncturedMetric.metricInner p (Yp p) (Yp p) :=
        (hmetric' p _ _).symm
  have hXY : ∀ p : PuncturedCap,
      P.globalMetric.metricInner (f p) (X (f p)) (Y (f p)) =
        P.puncturedMetric.metricInner p (Xp p) (Yp p) := by
    intro p
    calc
      P.globalMetric.metricInner (f p) (X (f p)) (Y (f p)) =
          P.globalMetric.metricInner (f p)
            (mfderiv PuncturedCapModel (𝓡 3) f p (Xp p))
            (mfderiv PuncturedCapModel (𝓡 3) f p (Yp p)) := by rw [hXp p, hYp p]
      _ = P.puncturedMetric.metricInner p (Xp p) (Yp p) :=
        (hmetric' p _ _).symm
  let F : E3 → ℝ := fun x =>
    P.globalMetric.metricInner x
      (P.globalMetric.leviCivitaConnection.curvature X Y X x) (Y x)
  let Q : E3 → ℝ := fun x =>
    C * (P.globalMetric.metricInner x (X x) (X x) *
      P.globalMetric.metricInner x (Y x) (Y x) -
      P.globalMetric.metricInner x (X x) (Y x) ^ 2)
  have hnonzero : ∀ x : E3, x ≠ 0 → 0 ≤ F x ∧ F x ≤ Q x := by
    intro x hx
    let p : PuncturedCap := phi.symm ⟨x, hx⟩
    have hfp : f p = x := by
      dsimp [p, f]
      exact congrArg Subtype.val (phi.right_inv ⟨x, hx⟩)
    obtain ⟨hlo, hhi⟩ := hpunct Xp Yp p
    have hs := hscalar p
    have hxx := hXX p
    have hyy := hYY p
    have hxy := hXY p
    rw [hfp] at hs hxx hyy hxy
    have hpair : 0 ≤
        P.globalMetric.metricInner x
            (P.globalMetric.leviCivitaConnection.curvature X Y X x) (Y x) ∧
        P.globalMetric.metricInner x
            (P.globalMetric.leviCivitaConnection.curvature X Y X x) (Y x) ≤
          C * (P.globalMetric.metricInner x (X x) (X x) *
            P.globalMetric.metricInner x (Y x) (Y x) -
            P.globalMetric.metricInner x (X x) (Y x) ^ 2) := by
      constructor
      · rw [hs]
        exact hlo
      · rw [hs, hxx, hyy, hxy]
        exact hhi
    simpa [F, Q] using hpair
  have hF : Continuous F := by
    simpa [F] using
      (P.globalMetric.metricInner_field_contMDiff
        (P.globalMetric.leviCivitaConnection.curvature X Y X) Y).continuous
  have hXXc : Continuous (fun x : E3 =>
      P.globalMetric.metricInner x (X x) (X x)) :=
    (P.globalMetric.metricInner_field_contMDiff X X).continuous
  have hYYc : Continuous (fun x : E3 =>
      P.globalMetric.metricInner x (Y x) (Y x)) :=
    (P.globalMetric.metricInner_field_contMDiff Y Y).continuous
  have hXYc : Continuous (fun x : E3 =>
      P.globalMetric.metricInner x (X x) (Y x)) :=
    (P.globalMetric.metricInner_field_contMDiff X Y).continuous
  have hQ : Continuous Q := by
    dsimp [Q]
    exact continuous_const.mul ((hXXc.mul hYYc).sub (hXYc.pow 2))
  have hdense : Dense ({x : E3 | x ≠ 0}) := by
    apply dense_compl_singleton_iff_not_open.mpr
    exact not_isOpen_singleton (0 : E3)
  have hnonneg : ∀ x : E3, 0 ≤ F x := by
    intro x
    exact hdense.induction (fun y hy => (hnonzero y hy).1)
      (isClosed_le continuous_const hF) x
  have hupper : ∀ x : E3, F x ≤ Q x := by
    intro x
    exact hdense.induction (fun y hy => (hnonzero y hy).2)
      (isClosed_le hF hQ) x
  intro x
  simpa [F, Q] using And.intro (hnonneg x) (hupper x)
/- SWARM_PROOF_END -/
end MorganTianLib.SurgeryCap
