import Mathlib.Tactic -- import all the tactics
import Mathlib.Analysis.Complex.Circle
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import «1DClass».RealClass
import «1DClass».Top

open Set Function Manifold

/- Let M be a compact connected topological 1-dimensional manifold. -/
variable (M : Type*) [TopologicalSpace M] [ConnectedSpace M] [CompactSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M] [IsManifold (𝓡 1) 0 M]

lemma chart_homeo_real : ∀ (x : M), Nonempty ((chartAt (EuclideanSpace ℝ (Fin 1)) x).source ≃ₜ ℝ) := by
  intro x
  let U := (chartAt (EuclideanSpace ℝ (Fin 1)) x).source
  let V := (chartAt (EuclideanSpace ℝ (Fin 1)) x).target
  have φ : U ≃ₜ V := (chartAt (EuclideanSpace ℝ (Fin 1)) x).toHomeomorphSourceTarget
  have hUV : Nonempty (U ≃ₜ V) := Nonempty.intro φ
  have hVOpen : IsOpen V := (chartAt (EuclideanSpace ℝ (Fin 1)) x).open_target
  have h : (EuclideanSpace ℝ (Fin 1)) ≃ₜ ℝ := by
    -- have h'' : AddCommGroup ℝ := by exact Real.instAddCommGroup
    -- obtain h' := toEuclidean ℝ
    sorry
  have i : V ≃ₜ ℝ := by

    sorry
  have φi : U ≃ₜ ℝ := φ.trans i
  exact Nonempty.intro φi

/- If M is a connected compact one-dimensional manifold, then it has a finite cover where each
open set in the cover is homeomorphic to ℝ. -/
lemma finite_chart_cover' : ∃ (ι : Set M), (∃ (U : ι → Set M), (∀ (i : ι), IsOpen (U i) ∧ Nonempty (U i ≃ₜ ℝ)) ∧ univ ⊆ ⋃ i, U i) := by
  have hCompact : IsCompact (univ : Set M) := CompactSpace.isCompact_univ
  obtain hChartCover := iUnion_source_chartAt (EuclideanSpace ℝ (Fin 1)) M

  sorry

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
  have hCompact : IsCompact (univ : Set M) := CompactSpace.isCompact_univ

  -- Covering M with charts
  obtain hChartCover := iUnion_source_chartAt (EuclideanSpace ℝ (Fin 1)) M

  obtain hFinCov := IsCompact.elim_finite_subcover hCompact

  have hLocalChart : ∀ (p : M), (∃ (U : Set M), IsOpen U ∧ p ∈ U ∧ Nonempty (U ≃ₜ ℝ)) := by
    intro p
    let U := (chartAt (EuclideanSpace ℝ (Fin 1)) p).source
    let φ := chartAt (EuclideanSpace ℝ (Fin 1)) p
    have hUOpen : IsOpen U := (chartAt (EuclideanSpace ℝ (Fin 1)) p).open_source
    have hp : p ∈ U := ChartedSpace.mem_chart_source p

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
  -- Find minimal cover (cover of size at least n): there must be 1-2
    -- If n = 1, contradiction - ℝ not compact.
    -- n ≥ 2 so there must be at least 2 sets that overlap because M connected
    -- Lemma says the union must be ℝ or circle - by minimality it's the circle.
    -- Circle clopen (closed by compactness open by union of open sets) - whole space M.
  sorry
