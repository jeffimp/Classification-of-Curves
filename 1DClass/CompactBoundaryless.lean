import Mathlib.Tactic -- import all the tactics
import Mathlib.Analysis.Complex.Circle
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.Instances.Real
import «1DClass».RealClass
import «1DClass».Top

open Set Function Manifold

/- Let M be a compact connected topological 1-dimensional manifold. -/
variable (M : Type*) [TopologicalSpace M] [ConnectedSpace M] [CompactSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M] [IsManifold (𝓡 1) 0 M]
-- I think that this is enough to define M as a *topological* manifold without boundary
-- When it comes to topological manifolds with boundary, it's enough to change ChartedSpace model space from ℝ to (EuclideanHalfSpace 1)
-- Be careful when it comes to the later case of defining smooth manifolds; more invovled ModelWithCorners etc structures.

/- If M is a connected compact one-dimensional manifold, then it has a finite cover where each
open set in the cover is homeomorphic to ℝ. -/
lemma finite_chart_cover : ∃ (Cover : Finset (Set M)), (∀ U ∈ Cover, (IsOpen U ∧ Nonempty (U ≃ₜ ℝ) ∧ ⋃₀ (Cover : Set (Set M)) = univ)) := by
  -- For each point p ∈ M, get a chart from the charted space structure
  /-
  For every point p ∈ M, there exists an open neighborhood U_p ⊆ M and a homeomorphism
  φ_p : U_p → V_p ⊆ ℝ, where V_p is open in ℝ.
  Each V_p ⊆ ℝ is a disjoint union of open intervals (by real_class lemma).
  Let I_p be the interval in V_p which contains the point φ_p(p) and set W_p = (φ_p)⁻¹(I_p).
  Then φ_p | W_p : W_p → I_p is a homeomorphism onto the open interval I_p.
  Every open interval in ℝ is homeomorphic to ℝ so W_p ≃ₜ ℝ.
  By contruction, {W_p : p ∈ M} is an open cover of M and by compactness, there exists a
  finite subcover {W_{p_i} : i ∈ {1, ..., n}}, where each W_{p_i} ≃ₜ ℝ. ∎
  -/
  have h_local_chart : ∀ p : M, ∃ (W : Set M), IsOpen W ∧ p ∈ W ∧ Nonempty (W ≃ₜ ℝ) := by
    intro p
    -- Get a chart around p
    let U := (chartAt (EuclideanSpace ℝ (Fin 1)) p).source
    let φ := chartAt (EuclideanSpace ℝ (Fin 1)) p

    have hUOpen : IsOpen U := (chartAt (EuclideanSpace ℝ (Fin 1)) p).open_source
    have hp : p ∈ U := ChartedSpace.mem_chart_source p

    -- φ(U) is open in EuclideanSpace ℝ (Fin 1) ≃ ℝ
    let V := φ '' U
    have hVOpen : IsOpen V := PartialHomeomorph.isOpen_image_of_subset_source φ hUOpen fun ⦃a⦄ a ↦ a

    sorry
  sorry

/- We can arrange the elements of the cover obtained in the previous lemma in an order such
that each union V_k = U_1 ∪ ⋯ ∪ U_k is connected. -/
-- lemma ordered_cover_connected_unions (Cover : Finset (Set M))
--     (h_cover : ∀ U ∈ Cover, (IsOpen U ∧ Nonempty (U ≃ₜ ℝ) ∧ ⋃₀ (Cover : Set (Set M)) = univ)) : true := by
  -- Indexing sets by
  -- Find minimal cover (cover of size at least n): there must be 1-2
    -- If n = 1, contradiction - ℝ not compact.
    -- n ≥ 2 so there must be at least 2 sets that overlap because M connected
    -- Lemma says the union must be ℝ or circle - by minimality it's the circle.
    -- Circle clopen (closed by compactness open by union of open sets) - whole space M.

    -- If they intersect in one component, then the cover is not minimal since we can take the union
      -- Union is ℝ by lemma
    -- By lemma, union must be circle.
  -- 2+ intersections between elements of cover => circle
  -- Assume at most 1-intersection contradiction to minimal cover unless n = 1 which is another contradiction (homeo to ℝ not compact).

/- Every compact, connected, one-dimensional manifold without boundary is homeomorphic to the circle. -/
theorem compact_connected_curve : Nonempty (M ≃ₜ Circle) := by
  -- Indexing sets by
  -- Find minimal cover (cover of size at least n): there must be 1-2
    -- If n = 1, contradiction - ℝ not compact.
    -- n ≥ 2 so there must be at least 2 sets that overlap because M connected
    -- Lemma says the union must be ℝ or circle - by minimality it's the circle.
    -- Circle clopen (closed by compactness open by union of open sets) - whole space M.
  sorry
