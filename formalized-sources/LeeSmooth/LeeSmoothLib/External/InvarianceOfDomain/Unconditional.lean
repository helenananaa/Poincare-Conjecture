/-
Copyright (c) 2026 Kai Lam and the mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kai Lam

The invariance-of-domain argument in `Core` is adapted from mathlib PR #36770,
commit 230d75acb32d80e7d7c4f4cd028b139f3dc28be7.  This module closes its sole
intermediate assumption using the genuine Brouwer proof ported from
math-xmum/Brouwer commit 7556f9adcc89f81aa758ddeff4f0dcfeb2d99cda; see
`BROUWER_LICENSE` for that dependency's MIT license.
-/

import LeeSmoothLib.External.Brouwer.ClosedBall
import LeeSmoothLib.External.InvarianceOfDomain.Core

open Metric Set

noncomputable section

namespace LeeSmooth.External.InvarianceOfDomain

/-- The genuine closed-ball Brouwer theorem discharges the intermediate fixed-point interface
used by the invariance-of-domain proof. -/
noncomputable instance brouwerFixedPointOfClosedBall
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    BrouwerFixedPoint E where
  brouwer_fixed_point f hf := by
    let toBall : E → closedBall (0 : E) 1 := fun x ↦
      ⟨LeeSmooth.External.Brouwer.radialClip x,
        LeeSmooth.External.Brouwer.radialClip_mem_closedBall x⟩
    have htoBall : Continuous toBall := by
      exact Continuous.subtype_mk LeeSmooth.External.Brouwer.continuous_radialClip
        (fun x ↦ LeeSmooth.External.Brouwer.radialClip_mem_closedBall x)
    let F : E → E := fun x ↦ (f (toBall x) : E)
    have hF : Continuous F := continuous_subtype_val.comp (hf.comp htoBall)
    have hFmap : MapsTo F (closedBall (0 : E) 1) (closedBall 0 1) := by
      intro x hx
      exact (f (toBall x)).property
    obtain ⟨x, hx, hfix⟩ :=
      LeeSmooth.External.Brouwer.closedBall_fixedPoint F hF.continuousOn hFmap
    refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
    change (f ⟨x, hx⟩ : E) = x
    simpa [F, toBall, LeeSmooth.External.Brouwer.radialClip_eq_self hx] using hfix

namespace Unconditional

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Unconditional invariance of domain at the center of a closed unit ball. -/
theorem invariance_of_domain_interior (f : E → E)
    (hf_cont : ContinuousOn f (closedBall 0 1))
    (hf_inj : Set.InjOn f (closedBall 0 1)) :
    f 0 ∈ interior (f '' closedBall 0 1) :=
  LeeSmooth.External.InvarianceOfDomain.invariance_of_domain_interior f hf_cont hf_inj

/-- Unconditional invariance of domain: a continuous injection on an open subset of a
finite-dimensional real inner-product space has open image. -/
theorem invariance_of_domain_open_map (f : E → E) (U : Set E) (hU : IsOpen U)
    (hf_cont : ContinuousOn f U) (hf_inj : Set.InjOn f U) : IsOpen (f '' U) :=
  LeeSmooth.External.InvarianceOfDomain.invariance_of_domain_open_map f U hU hf_cont hf_inj

/-- Unconditional invariance-of-domain neighborhood statement for partial equivalences. -/
theorem invariance_of_domain_partial_equiv {x : E} {s : Set E} {f : PartialEquiv E E}
    (hCont : ContinuousOn f f.source) : s ∈ nhds x → s ⊆ f.source →
    f '' s ∈ nhds (f x) :=
  LeeSmooth.External.InvarianceOfDomain.invariance_of_domain_partial_equiv hCont

/-- An unconditional continuous-injection dimension bound for finite-dimensional real
inner-product spaces. -/
theorem dim_le_of_injective_continuous
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (f : E → F) (hf_cont : Continuous f) (hf_inj : Function.Injective f) :
    Module.finrank ℝ E ≤ Module.finrank ℝ F :=
  LeeSmooth.External.InvarianceOfDomain.dim_le_of_injective_continuous f hf_cont hf_inj

/-- Unconditional invariance of dimension for finite-dimensional real inner-product spaces. -/
theorem invariance_of_dimension
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (φ : E ≃ₜ F) : Module.finrank ℝ E = Module.finrank ℝ F :=
  LeeSmooth.External.InvarianceOfDomain.invariance_of_dimension φ

end Unconditional

end LeeSmooth.External.InvarianceOfDomain
