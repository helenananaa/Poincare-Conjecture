import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ConnectionDifferenceField
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => Fin 3 → Fin 3 → Fin 3 → ℝ
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

/-- **Math.** connection difference pointwise. -/
theorem connection_difference_pointwise {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    [SigmaCompactSpace M] [T2Space M]
    (nabla nabla0 : Riemannian.AffineConnection (𝓡 3) M)
    (X X1 Y Y1 : Riemannian.SmoothVectorField (𝓡 3) M) (p : M)
    (hX : X p=X1 p) (hY : Y p=Y1 p) :
    connectionDifferenceField nabla nabla0 X Y p = connectionDifferenceField nabla nabla0 X1 Y1 p :=
/- SWARM_PROOF_BEGIN -/
by
  have hleft : connectionDifferenceField nabla nabla0 X Y p =
      connectionDifferenceField nabla nabla0 X1 Y p := by
    simp only [connectionDifferenceField, Riemannian.SmoothVectorField.sub_apply]
    rw [nabla.cov_congr_apply_left Y hX, nabla0.cov_congr_apply_left Y hX]

  have hσ : (Y - Y1) p = 0 := by
    simp only [Riemannian.SmoothVectorField.sub_apply, hY, sub_self]
  obtain ⟨k, f, hf, W, τ, hfp, hτ0, hdecomp⟩ :=
    Riemannian.exists_decomposition_of_apply_eq_zero (Y - Y1) hσ

  letI : AddCommMonoid (Riemannian.SmoothVectorField (𝓡 3) M) := {
    add_assoc a b c := Riemannian.SmoothVectorField.ext fun q => add_assoc (a q) (b q) (c q)
    zero_add a := Riemannian.SmoothVectorField.ext fun q => zero_add (a q)
    add_zero a := Riemannian.SmoothVectorField.ext fun q => add_zero (a q)
    add_comm a b := Riemannian.SmoothVectorField.ext fun q => add_comm (a q) (b q)
    nsmul := nsmulRec }

  have hsum : ∀ s : Finset (Fin k),
      connectionDifferenceField nabla nabla0 X1
        (∑ i ∈ s, Riemannian.SmoothVectorField.smul (f i) (hf i) (W i)) p =
        ∑ i ∈ s, connectionDifferenceField nabla nabla0 X1
          (Riemannian.SmoothVectorField.smul (f i) (hf i) (W i)) p := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [connectionDifferenceField, nabla.cov_zero_right,
        nabla0.cov_zero_right]
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      rw [(connection_difference_field_linear nabla nabla0).2.1]
      exact congrArg (fun z =>
        connectionDifferenceField nabla nabla0 X1
          (Riemannian.SmoothVectorField.smul (f a) (hf a) (W a)) p + z) ih

  have hterm (i : Fin k) :
      connectionDifferenceField nabla nabla0 X1
        (Riemannian.SmoothVectorField.smul (f i) (hf i) (W i)) p = 0 := by
    rw [(connection_difference_field_linear nabla nabla0).2.2.2]
    simp only [Riemannian.SmoothVectorField.smul_apply, hfp i, zero_smul]

  have hsum0 :
      connectionDifferenceField nabla nabla0 X1
        (∑ i, Riemannian.SmoothVectorField.smul (f i) (hf i) (W i)) p = 0 := by
    rw [hsum Finset.univ]
    exact Finset.sum_eq_zero (fun i hi => hterm i)

  have hsumApply (s : Finset (Fin k)) (q : M) :
      (∑ i ∈ s, Riemannian.SmoothVectorField.smul (f i) (hf i) (W i)) q =
        ∑ i ∈ s, f i q • W i q := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        Riemannian.SmoothVectorField.add_apply,
        Riemannian.SmoothVectorField.smul_apply, ih]

  have hτnabla : (nabla.cov X1 τ) p = 0 := by
    obtain ⟨g, hg, hgp, hgτ⟩ :=
      Riemannian.exists_smul_eq_self_of_eventuallyEq_zero hτ0
    have h := nabla.leibniz g hg X1 τ p
    rw [hgτ, hτ0.self_of_nhds, smul_zero, add_zero, hgp, zero_smul] at h
    exact h
  have hτnabla0 : (nabla0.cov X1 τ) p = 0 := by
    obtain ⟨g, hg, hgp, hgτ⟩ :=
      Riemannian.exists_smul_eq_self_of_eventuallyEq_zero hτ0
    have h := nabla0.leibniz g hg X1 τ p
    rw [hgτ, hτ0.self_of_nhds, smul_zero, add_zero, hgp, zero_smul] at h
    exact h
  have hτ : connectionDifferenceField nabla nabla0 X1 τ p = 0 := by
    simp only [connectionDifferenceField, Riemannian.SmoothVectorField.sub_apply,
      hτnabla, hτnabla0, sub_self]

  have hdecompField : Y - Y1 =
      (∑ i, Riemannian.SmoothVectorField.smul (f i) (hf i) (W i)) + τ := by
    ext q
    rw [Riemannian.SmoothVectorField.sub_apply,
      Riemannian.SmoothVectorField.add_apply, hsumApply Finset.univ q]
    exact hdecomp q

  have hσzero : connectionDifferenceField nabla nabla0 X1 (Y - Y1) p = 0 := by
    rw [hdecompField, (connection_difference_field_linear nabla nabla0).2.1]
    simp only [Riemannian.SmoothVectorField.add_apply, hsum0, hτ,
      add_zero]

  have hsplit : Y = Y1 + (Y - Y1) := by
    ext q
    simp only [Riemannian.SmoothVectorField.add_apply,
      Riemannian.SmoothVectorField.sub_apply]
    abel
  have hright : connectionDifferenceField nabla nabla0 X1 Y p =
      connectionDifferenceField nabla nabla0 X1 Y1 p := by
    rw [hsplit, (connection_difference_field_linear nabla nabla0).2.1]
    simp only [Riemannian.SmoothVectorField.add_apply, hσzero, add_zero]
  rw [hleft, hright]
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
