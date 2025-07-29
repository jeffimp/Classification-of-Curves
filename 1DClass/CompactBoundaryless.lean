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

def euc1ToReal : EuclideanSpace ℝ (Fin 1) → ℝ := fun x => x 0

def realToEuc1 : ℝ → EuclideanSpace ℝ (Fin 1) := fun r =>
  WithLp.equiv 2 (Fin 1 → ℝ) |>.symm (fun _ => r)

lemma euc1ToReal_realToEuc1 : Function.LeftInverse euc1ToReal realToEuc1 := by
  intro r
  simp [euc1ToReal, realToEuc1]

lemma realToEuc1_euc1ToReal : Function.RightInverse euc1ToReal realToEuc1 := by
  intro x
  simp [euc1ToReal, realToEuc1]
  ext i
  fin_cases i
  simp

lemma euc1ToReal_continuous : Continuous euc1ToReal := by
  -- The coordinate projection is continuous
  exact continuous_apply 0

lemma realToEuc1_continuous : Continuous realToEuc1 := by
  -- This follows from continuity of the isometric equivalence and constant functions
  apply Continuous.comp
  · exact PiLp.continuous_toLp 2 fun i ↦ ℝ
  · apply continuous_pi
    intro i
    exact continuous_id'

def homeomorph_euclidean_real : (EuclideanSpace ℝ (Fin 1)) ≃ₜ ℝ := by
  refine ⟨⟨euc1ToReal, realToEuc1, ?_, ?_⟩, euc1ToReal_continuous, realToEuc1_continuous⟩
  · intro x
    simp only [realToEuc1, euc1ToReal, Fin.isValue, WithLp.equiv_symm_apply]
    ext i
    fin_cases i
    simp
  · intro x
    simp [euc1ToReal, realToEuc1]

lemma chart_homeo_real : ∀ (x : M), Nonempty ((chartAt (EuclideanSpace ℝ (Fin 1)) x).source ≃ₜ ℝ) := by
  intro x
  -- connected components of x
  let U := (chartAt (EuclideanSpace ℝ (Fin 1)) x).source
  let V := (chartAt (EuclideanSpace ℝ (Fin 1)) x).target
  have φ : U ≃ₜ V := (chartAt (EuclideanSpace ℝ (Fin 1)) x).toHomeomorphSourceTarget
  have hUV : Nonempty (U ≃ₜ V) := Nonempty.intro φ
  have hVOpen : IsOpen V := (chartAt (EuclideanSpace ℝ (Fin 1)) x).open_target
  -- have : TopologicalSpace (EuclideanSpace ℝ (Fin 1)) := PiLp.topologicalSpace 2 fun x ↦ ℝ
  have h : (EuclideanSpace ℝ (Fin 1)) ≃ₜ ℝ := by
    exact homeomorph_euclidean_real
  have i : V ≃ₜ ℝ := by
    -- tan / log

    sorry
  have φi : U ≃ₜ ℝ := φ.trans i
  exact Nonempty.intro φi

/- If M is a connected compact one-dimensional manifold, then it has a finite cover where each
open set in the cover is homeomorphic to ℝ. -/
lemma finite_chart_cover' : ∃ (ι : Finset M), (∃ (U : ι → Set M), (∀ (i : ι), IsOpen (U i) ∧ Nonempty (U i ≃ₜ ℝ)) ∧ univ ⊆ ⋃ i, U i) := by
  have hCompact : IsCompact (univ : Set M) := CompactSpace.isCompact_univ
  obtain hChartCover := iUnion_source_chartAt (EuclideanSpace ℝ (Fin 1)) M
  -- Cover by charts with connected domain
  -- Finite cover
  -- Image of charts in subcover
  -- Homeomorphism of charts in subcover to ℝ last step

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
  -- Find minimal cover (cover of size at least n): there must be 1-2 (minimality on cardinality map)
    -- If n = 1, contradiction - ℝ not compact.
    -- n ≥ 2 so there must be at least 2 sets that overlap because M connected
    -- Lemma says the union must be ℝ or circle - by minimality it's the circle.
    -- Circle clopen (closed by compactness open by union of open sets) - whole space M.
  sorry


def DoubleSetoid (X : Type*) (Boundary : Set X) : Setoid (X × ({0, 1} : Set ℕ)) :=
  let r (a b : X × ({0, 1} : Set ℕ)) := sorry
  { r := r
    iseqv := sorry}

-- def ... Quotient
-- Create instance and prove desired properties about manifold structure.
-- classify 0-manifold as point

-- Or instance Setoid (X × Bool)
