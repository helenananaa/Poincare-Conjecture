import PoincareConjecture

open Set
open scoped Manifold ContDiff
open PoincareConjecture.Topology.FiberSaturation
noncomputable section

/-- The actual standard product collar around a unit two-sphere. -/
def testSphereCollar (z : Sphere2 × NeckParameter) : Sphere2 × ℝ := (z.1, z.2)

theorem testSphereCollar_open : Topology.IsOpenEmbedding testSphereCollar :=
  Topology.IsOpenEmbedding.id.prodMap
    (isOpen_Ioo : IsOpen (Ioo (-1 : ℝ) 1)).isOpenEmbedding_subtypeVal

def testContinuingRegion : Set (Sphere2 × ℝ) := univ ×ˢ Iic (0 : ℝ)

theorem testCollarSide (z : Sphere2 × NeckParameter) :
    testSphereCollar z ∈ testContinuingRegion ↔ (z.2 : ℝ) ≤ 0 := by
  simp [testSphereCollar, testContinuingRegion]

theorem testCentralSection : collarSection testSphereCollar = univ ×ˢ ({0} : Set ℝ) := by
  ext ⟨x,t⟩
  simp [collarSection, testSphereCollar, neckCenter, Prod.ext_iff, eq_comm]

-- Actual contact with the complement component forces every central sphere point.
example {p : Sphere2 × ℝ} {x : Sphere2}
    (hx : (x,0) ∈ frontier (connectedComponentIn testContinuingRegionᶜ p)) :
    ∀ y : Sphere2, (y,0) ∈ frontier (connectedComponentIn testContinuingRegionᶜ p) :=
  oneSidedCollar_frontier_saturated testSphereCollar_open testCollarSide hx

local instance : LocallyConnectedSpace (Sphere2 × ℝ) := by
  letI : LocallyConnectedSpace (ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) :=
    inferInstanceAs (LocallyConnectedSpace (EuclideanSpace ℝ (Fin 2) × ℝ))
  exact ChartedSpace.locallyConnectedSpace (ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) (Sphere2 × ℝ)

-- Instantiate the full finite-selection theorem, not only its collar hypothesis.
example (x : Sphere2) :
    ∃ A : Set Unit, A.Finite ∧ A.Nonempty ∧
      frontier (connectedComponentIn testContinuingRegionᶜ (x,1)) =
        ⋃ _ : A, collarSection testSphereCollar ∧
      (∀ _ : A, IsConnected (collarSection testSphereCollar) ∧
        ∀ z ∈ collarSection testSphereCollar,
          connectedComponentIn (frontier (connectedComponentIn testContinuingRegionᶜ (x,1))) z =
            collarSection testSphereCollar) ∧
      (∀ i ∉ A, Disjoint (collarSection testSphereCollar)
        (frontier (connectedComponentIn testContinuingRegionᶜ (x,1)))) := by
  have hC : IsClosed testContinuingRegion := isClosed_univ.prod isClosed_Iic
  have hp : (x, (1 : ℝ)) ∉ testContinuingRegion := by simp [testContinuingRegion]
  have hproper : connectedComponentIn testContinuingRegionᶜ (x,1) ≠ connectedComponent (x,1) := by
    intro h
    have hz : (x, (0 : ℝ)) ∈ connectedComponentIn testContinuingRegionᶜ (x,1) := by
      rw [h, PreconnectedSpace.connectedComponent_eq_univ]
      exact mem_univ _
    exact connectedComponentIn_subset testContinuingRegionᶜ (x,1) hz (by simp [testContinuingRegion])
  apply sphere_collared_complement_frontier_components hC (fun _ : Unit => testSphereCollar)
    (fun _ => testSphereCollar_open) (fun _ => testCollarSide) ?_ ?_ hp hproper
  · simp only [testContinuingRegion, frontier_univ_prod_eq, frontier_Iic, testCentralSection, iUnion_const]
  · intro i j hij
    exact (hij (Subsingleton.elim i j)).elim

-- The proper-component condition cannot be omitted: an entire component
-- has empty frontier even in a connected, locally connected ambient manifold.
example : frontier (connectedComponentIn (∅ : Set ℝ)ᶜ 0) = ∅ := by
  simp [connectedComponentIn_univ, PreconnectedSpace.connectedComponent_eq_univ]

-- Reversing the collar orientation changes which side represents C.
example (x : Sphere2) :
    testSphereCollar (x, ⟨(1 : ℝ) / 2, by norm_num⟩) ∉ testContinuingRegion := by
  norm_num [testSphereCollar, testContinuingRegion]
