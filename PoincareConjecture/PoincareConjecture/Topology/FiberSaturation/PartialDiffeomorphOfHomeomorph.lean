import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

set_option autoImplicit false
open scoped ContDiff Manifold
open Set

namespace PoincareConjecture.Topology.FiberSaturation

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H]
  {G : Type*} [TopologicalSpace G]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {n : WithTop ℕ∞}

/-- Package an open partial homeomorphism with two-sided `C^n` maps as a
`PartialDiffeomorph`. Does not construct collars or necks. -/
noncomputable def partialDiffeomorph_of_openPartialHomeomorph
    (e : OpenPartialHomeomorph M N)
    (hfwd : ContMDiffOn I J n e e.source)
    (hinv : ContMDiffOn J I n e.symm e.target) :
    PartialDiffeomorph I J M N n :=
/- SWARM_PROOF_BEGIN -/
{ toPartialEquiv := e.toPartialEquiv
  open_source := e.open_source
  open_target := e.open_target
  contMDiffOn_toFun := hfwd
  contMDiffOn_invFun := hinv }
/- SWARM_PROOF_END -/

theorem partialDiffeomorph_of_openPartialHomeomorph_toPartialEquiv
    (e : OpenPartialHomeomorph M N)
    (hfwd : ContMDiffOn I J n e e.source)
    (hinv : ContMDiffOn J I n e.symm e.target) :
    (partialDiffeomorph_of_openPartialHomeomorph e hfwd hinv).toPartialEquiv =
      e.toPartialEquiv :=
/- SWARM_PROOF_BEGIN -/
rfl
/- SWARM_PROOF_END -/

end PoincareConjecture.Topology.FiberSaturation
