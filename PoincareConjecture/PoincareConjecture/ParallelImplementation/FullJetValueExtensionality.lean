import PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.FullJetValueExtensionality
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph
open scoped Topology BoundedContinuousFunction
/-- On a positive slab, the actual value determines every field of a full parabolic jet. -/
theorem full_jet_eq_of_value_eq (T alpha : ℝ) (hT : 0 < T)
    (z w : FullJet T)
    (hz : z ∈ fullParabolicJetSet T alpha hT.le)
    (hw : w ∈ fullParabolicJetSet T alpha hT.le)
    (hvalue : z.1.1.1.1 = w.1.1.1.1) :
    z = w :=
/- SWARM_PROOF_BEGIN -/
by
  have hgrad : z.1.1.1.2.1 = w.1.1.1.2.1 := by
    apply BoundedContinuousFunction.ext
    intro p
    rcases p with ⟨t, x⟩
    have h₁ := (hz.1.1 t).1 x
    have h₂ := (hw.1.1 t).1 x
    have hfun : (fun y : EuclideanSpace ℝ (Fin 3) => z.1.1.1.1 (t, y)) =
        (fun y : EuclideanSpace ℝ (Fin 3) => w.1.1.1.1 (t, y)) := by
      funext y
      exact congrArg (fun F : Slab T →ᵇ EuclideanSpace ℝ (Fin 6) => F (t, y)) hvalue
    rw [hfun] at h₁
    exact h₁.unique h₂
  have hhess : z.1.1.1.2.2 = w.1.1.1.2.2 := by
    apply BoundedContinuousFunction.ext
    intro p
    rcases p with ⟨t, x⟩
    have h₁ := (hz.1.1 t).2 x
    have h₂ := (hw.1.1 t).2 x
    have hfun : (fun y : EuclideanSpace ℝ (Fin 3) => z.1.1.1.2.1 (t, y)) =
        (fun y : EuclideanSpace ℝ (Fin 3) => w.1.1.1.2.1 (t, y)) := by
      funext y
      exact congrArg
        (fun F : Slab T →ᵇ (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 6)) =>
          F (t, y)) hgrad
    rw [hfun] at h₁
    exact h₁.unique h₂
  have hincr : z.1.1.2 = w.1.1.2 := by
    apply BoundedContinuousFunction.ext
    intro p
    rw [hz.1.2 p, hw.1.2 p, hhess]
  have htimeInterior : ∀ ts : Set.Icc (0 : ℝ) T, 0 < (ts : ℝ) →
      (ts : ℝ) < T → ∀ x : EuclideanSpace ℝ (Fin 3),
        z.1.2 (ts, x) = w.1.2 (ts, x) := by
    intro ts hs0 hsT x
    have h₁ := hz.2.1 ts hs0 hsT x
    have h₂ := hw.2.1 ts hs0 hsT x
    have hfun : timeExtension z.1.1.1.1 x = timeExtension w.1.1.1.1 x := by
      funext u
      simp [timeExtension, hvalue]
    rw [hfun] at h₁
    have hderiv := h₁.unique h₂
    simpa using hderiv
  have htime : z.1.2 = w.1.2 := by
    apply BoundedContinuousFunction.ext
    intro p
    rcases p with ⟨t, x⟩
    let clamp : ℝ → Set.Icc (0 : ℝ) T := fun s =>
      ⟨max 0 (min s T), ⟨le_max_left _ _, max_le hT.le (min_le_right _ _)⟩⟩
    have hclamp : Continuous clamp := by
      apply Continuous.subtype_mk
      · exact continuous_const.max (continuous_id.min continuous_const)
    let f : ℝ → EuclideanSpace ℝ (Fin 6) := fun s => z.1.2 (clamp s, x)
    let g : ℝ → EuclideanSpace ℝ (Fin 6) := fun s => w.1.2 (clamp s, x)
    have hf : Continuous f := by
      exact z.1.2.continuous.comp (hclamp.prodMk continuous_const)
    have hg : Continuous g := by
      exact w.1.2.continuous.comp (hclamp.prodMk continuous_const)
    have hEqInterior : ∀ s ∈ Set.Ioo (0 : ℝ) T, f s = g s := by
      intro s hs
      have hclamp_s : clamp s = ⟨s, ⟨hs.1.le, hs.2.le⟩⟩ := by
        apply Subtype.ext
        simp [clamp, min_eq_left hs.2.le, max_eq_right hs.1.le]
      change z.1.2 (clamp s, x) = w.1.2 (clamp s, x)
      rw [hclamp_s]
      exact htimeInterior ⟨s, ⟨hs.1.le, hs.2.le⟩⟩ hs.1 hs.2 x
    let eqSet : Set ℝ := {s | f s = g s}
    have heqClosed : IsClosed eqSet := isClosed_eq hf hg
    have hsubset : Set.Ioo (0 : ℝ) T ⊆ eqSet := hEqInterior
    have hcl : (t : ℝ) ∈ closure eqSet := by
      apply closure_mono hsubset
      rw [closure_Ioo (a := (0 : ℝ)) (b := T) (ne_of_lt hT)]
      exact t.2
    have hEqAtT : f (t : ℝ) = g (t : ℝ) := heqClosed.closure_subset hcl
    have hclamp_t : clamp (t : ℝ) = t := by
      apply Subtype.ext
      simp [clamp, min_eq_left t.2.2, max_eq_right t.2.1]
    simpa [f, g, hclamp_t] using hEqAtT
  have htimeIncr : z.2 = w.2 := by
    apply BoundedContinuousFunction.ext
    intro p
    rw [hz.2.2.1 p, hw.2.2.1 p, htime]
  apply Prod.ext
  · apply Prod.ext
    · apply Prod.ext
      · apply Prod.ext
        · exact hvalue
        · apply Prod.ext
          · exact hgrad
          · exact hhess
      · exact hincr
    · exact htime
  · exact htimeIncr
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.FullJetValueExtensionality
