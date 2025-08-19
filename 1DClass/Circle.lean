import Mathlib.Tactic -- import all the tactics
import Mathlib.Analysis.Complex.Circle
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import «1DClass».RealClass
import «1DClass».Top

open Set Function Manifold Real Topology

/- Let M be a compact connected topological 1-dimensional manifold. -/
variable (M : Type*) [TopologicalSpace M] [ConnectedSpace M] [CompactSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M] [IsManifold (𝓡 1) 0 M] [Nonempty M]

lemma chart_homeo_real : ∀ (x : M), Nonempty ((chartAt (EuclideanSpace ℝ (Fin 1)) x).source ≃ₜ ℝ) := by
  intro x
  -- connected components of x
  let U := (chartAt (EuclideanSpace ℝ (Fin 1)) x).source
  let V := (chartAt (EuclideanSpace ℝ (Fin 1)) x).target
  -- let V' := connectedComponentIn ((chartAt (EuclideanSpace ℝ (Fin 1)) x) x) ↑(chartAt (EuclideanSpace ℝ (Fin 1)) x).target
  have φ : U ≃ₜ V := (chartAt (EuclideanSpace ℝ (Fin 1)) x).toHomeomorphSourceTarget
  have hUV : Nonempty (U ≃ₜ V) := Nonempty.intro φ
  have hVOpen : IsOpen V := (chartAt (EuclideanSpace ℝ (Fin 1)) x).open_target
  have h : (EuclideanSpace ℝ (Fin 1)) ≃ₜ ℝ := Homeomorph.funUnique (Fin 1) ℝ
  have i : V ≃ₜ ℝ := by
    -- tan / log

    sorry
  have φi : U ≃ₜ ℝ := φ.trans i
  exact Nonempty.intro φi

/- If M is a connected compact one-dimensional manifold, then it has a finite cover where each
open set in the cover is homeomorphic to ℝ. -/
-- omit [ConnectedSpace M] [T2Space M] [IsManifold (𝓡 1) 0 M]
lemma chart_cover : ∃ (ι : Set M), (∃ (U : ι → Set M), (∀ (i : ι), IsOpen (U i) ∧ Nonempty (U i ≃ₜ ℝ)) ∧ univ ⊆ ⋃ i, U i) := by
  have hCompact : IsCompact (univ : Set M) := CompactSpace.isCompact_univ
  obtain hChartCover := iUnion_source_chartAt (EuclideanSpace ℝ (Fin 1)) M
  use (univ : Set M)
  use fun x => (chartAt (EuclideanSpace ℝ (Fin 1)) x.val).source

  constructor
  · intro i
    constructor
    · exact (chartAt (EuclideanSpace ℝ (Fin 1)) i.val).open_source
    · apply chart_homeo_real

  · rw [← hChartCover]
    simp

-- lemma fin_cover : ∃ (t : Finset (Set M)), (∃ (U : t → Set M), (∀ (i : t), IsOpen (U i) ∧ Nonempty (U i ≃ₜ ℝ)) ∧ univ ⊆ ⋃ i, U i) := by
--   sorry

/- If two sets in M are homeomorphic to ℝ but their union is not homeomorphic to ℝ, then M is homeomorphic to the circle. -/
lemma circle_union (U V : Set M) (hOverlap : (U ∩ V).Nonempty) (φ : U ≃ₜ ℝ) (ψ : V ≃ₜ ℝ) (h : ¬ Nonempty ({x // x ∈ (U ∪ V)} ≃ₜ ℝ)) : Nonempty (M ≃ₜ Circle) := by sorry

/--
A compact, connected, 1-dimensional manifold is homeomorphic to the circle.
-/
theorem compact_connected_one_manifold_is_circle [DecidableEq (Set M)] : Nonempty (M ≃ₜ Circle) := by
  -- M cannot be homeomorphic to ℝ.
  -- A homeomorphism preserves compactness. M is compact, but ℝ is not.
  have hNReal : ¬ Nonempty (M ≃ₜ ℝ) := by
    intro h
    obtain φ := h.some
    -- If M ≃ₜ ℝ, then ℝ would have to be compact.
    have hNRCompact : ¬CompactSpace ℝ := by
      refine not_compactSpace_iff.mpr ?_
      exact instNoncompactSpaceReal
    exact hNRCompact (Homeomorph.compactSpace φ)

  have hCompact : IsCompact (univ : Set M) := CompactSpace.isCompact_univ
  obtain ⟨ι, U, h₂⟩ := chart_cover M
  have hUOpen: ∀ (i : ↑ι), IsOpen (U i) := by
    intro i
    apply h₂.left at i
    exact i.left
  obtain ⟨t, h⟩ := IsCompact.elim_finite_subcover hCompact U hUOpen h₂.right

  have ht : 2 ≤ t.card := by
    -- Assume for contradiction that t.card < 2.
    by_contra htCard2
    -- Since M is non-empty, t cannot be empty, so t.card = 1.
    have htNemp : Nonempty t := by
      obtain ⟨x, hx⟩ := exists_mem_of_nonempty M
      have hx_cover : x ∈ ⋃ (i : ι) (hi : i ∈ (t : Finset ι)), U i := h hx
      rw [mem_iUnion] at hx_cover
      aesop
    have htCard1 : t.card = 1 := by
      have : 0 < t.card := Finset.card_pos.mpr (Finset.nonempty_coe_sort.mp htNemp)
      linarith
    -- Since t had cardinality 1, there exists some x such that M ⊆ U x.
    have hxCover : ∃ x, univ ⊆ U x := by
      obtain ⟨x, hx⟩ := Finset.card_eq_one.1 htCard1
      use x
      intro y hy
      have hyCover := h (mem_univ y)
      -- rw [mem_iUnion] at hyCover
      rw [hx] at hyCover
      simp only [Finset.mem_singleton, iUnion_iUnion_eq_left] at hyCover
      exact hyCover
    -- This implies that M is homeomorphic to ℝ → contradiction!
    have hmRHom : Nonempty (M ≃ₜ ℝ) := by
      obtain ⟨x, hx⟩ := hxCover
    -- Use the fact that each member of the cover is homeomorphic to ℝ.
      obtain hx' := (h₂.1 x).2
      -- Complete the proof by composing homeomorphisms
      have hUniv : (univ : Set M) = U x := Eq.symm (eq_univ_of_univ_subset hx)
      -- The homeomorphism from M to ℝ is the composition:
      -- M ≃ univ ≃ U x ≃ ℝ
      let φ₁ : M ≃ₜ (univ : Set M) := (Homeomorph.Set.univ M).symm
      let φ₂ : (univ : Set M) ≃ₜ U x := by
        rw [hUniv]
        exact Homeomorph.refl _
      let φ₃ : U x ≃ₜ ℝ := hx'.some
      exact ⟨φ₁.trans (φ₂.trans φ₃)⟩
    exact hNReal hmRHom

  -- Existence of minimal cover
  have hMin : ∃ (s : Finset ι), ((∀ (i : s), IsOpen (U i)) ∧ univ ⊆ ⋃ i, U i) ∧
      (∀ (s' : Finset ι), ((∀ (i : s'), IsOpen (U i)) ∧ univ ⊆ ⋃ i ∈ s', U i) → s.card ≤ s'.card) := by
    let P := fun (s : Finset ι) => (∀ i ∈ s, IsOpen (U i)) ∧ univ ⊆ ⋃ i ∈ s, U i
    have hex : ∃ n, ∃ s, s.card = n ∧ P s :=
      ⟨t.card, ⟨t, rfl, ⟨fun i hi => hUOpen i, h⟩⟩⟩
    -- Nat.find requires a DecidablePred on ℕ; provide it classically
    haveI : DecidablePred fun n => ∃ s, s.card = n ∧ P s := fun n => Classical.dec _
    -- Pick the least n for which there exists s with card = n and P s
    let n := Nat.find hex
    obtain ⟨s, hs_card, hsP⟩ := Nat.find_spec hex
    -- Prove minimality against any other candidate s'
    have hnMin : ∀ (s' : Finset ι), ((∀ (i : s'), IsOpen (U i)) ∧ univ ⊆ ⋃ i ∈ s', U i) → n ≤ s'.card := by
      intro s' hs'
      have : P s' := ⟨fun i hi => hs'.1 ⟨i, hi⟩, hs'.2⟩
      by_contra hlt
      have : ∃ m, (∃ (s : Finset ι), s.card = m ∧ P s) := ⟨s'.card, ⟨s', rfl, this⟩⟩
      aesop
    use s
    constructor
    · exact And.imp_left (fun a i ↦ hUOpen ↑i) h₂
    · intro s' hs'
      have hn_le : n ≤ s'.card := by
        exact hnMin s' hs'
      exact le_of_eq_of_le hs_card hn_le

  obtain ⟨s, hs, hsMin⟩ := hMin
  -- Lemma Nonempty cover
  have hsNonemp: Nonempty s := by sorry

  have hOverlap : ∃ (i j : s), i ≠ j ∧ (U i ∩ U j).Nonempty := by
    -- n ≥ 2 so there must be at least 2 sets that overlap because M connected
    contrapose! h
    -- let k := hsNonemp.some
    -- let V := U k
    -- haveI : DecidablePred fun x => x ≠ k := fun n => Classical.dec _
    -- -- let W := ⋃ i ∈ {x ∈ s | x ≠ k}
    have hMCon: IsConnected (univ : Set M) := by (expose_names; exact connectedSpace_iff_univ.mp inst_1)
    haveI : DecidablePred fun x ↦ ∃ i, U ↑i = x := fun x => Classical.dec _
    -- let U' : (Finset (Set M)) := {U i | i ∈ s}
    obtain h1 := isConnected_iff_sUnion_disjoint_open.mp hMCon (Finset.image U s)
    simp only [univ_subset_iff] at hs h1 ⊢
    exfalso
    have h2 : (∀ (u v : Set M), u ∈ Finset.image U s → v ∈ Finset.image U s → (univ ∩ (u ∩ v)).Nonempty → u = v) := by
      intro u v hu hv
      simp [univ_inter]
      obtain ⟨a, ha₁, ha₂⟩ := Finset.mem_image.mp hu
      obtain ⟨b, hb₁, hb₂⟩ := Finset.mem_image.mp hv
      rw [← ha₂, ← hb₂]
      intro hIE
      have hab : a = b := by
        obtain hab1 := h ⟨a, ha₁⟩ ⟨b, hb₁⟩
        by_contra hanb
        have : (⟨a, ha₁⟩ : s) ≠ ⟨b, hb₁⟩ := by grind
        apply hab1 at this
        rw [nonempty_iff_ne_empty] at hIE
        exact hIE this
      exact congrArg U hab
    apply h1 at h2
    have h3 : (∀ u ∈ Finset.image U s, IsOpen u) := by
      intro u hu
      obtain ⟨a, ha₁, ha₂⟩ := Finset.mem_image.mp hu
      have : IsOpen (U a) := hUOpen a
      rwa [ha₂] at this
    apply h2 at h3
    have h4 : ⋃₀ (Finset.image U s).toSet = univ := by sorry
    apply h3 at h4
    obtain ⟨u, ⟨hu, hv⟩⟩ := h4
    obtain ⟨a, ha₁, ha₂⟩ := Finset.mem_image.mp hu
    have h5 : Nonempty (U a ≃ₜ ℝ) := by exact (h₂.1 a).2
    rw [ha₂, hv] at h5
    have hReal : Nonempty (M ≃ₜ ℝ) := Nonempty.intro (((Homeomorph.Set.univ M).symm).trans h5.some)
    exact hNReal hReal

  obtain ⟨i, j, hij₁, hij₂⟩ := hOverlap

  -- Stating (U i ∪ U j) ≃ₜ Circle leads to error failed to synthesize Union (Type u_1)
  let C := (U i ∪ U j)

  have hCircle : C ≃ₜ Circle := by
    sorry


  -- Lemma says the union must be ℝ or circle - by minimality it's the circle.
  -- Circle clopen (closed by compactness open by union of open sets) - whole space M.
  sorry

noncomputable section

/--
The tangent function as a homeomorphism between the open interval `(-π/2, π/2)` and the real line `ℝ`.
-/
def tanHomeo : (Ioo (-(π / 2)) (π / 2)) ≃ₜ ℝ where
  toFun x := tan x.val
  invFun y := ⟨arctan y, ⟨neg_pi_div_two_lt_arctan y, arctan_lt_pi_div_two y⟩⟩
  left_inv x := by
    -- To prove arctan(tan x.val) = x.val for x ∈ Ioo (-π/2, π/2)
    apply Subtype.eq
    apply arctan_tan
    · exact x.2.1
    · exact x.2.2
  right_inv y := by
    -- To prove tan(arctan y) = y
    exact tan_arctan y
  continuous_toFun := by
    exact continuousOn_tan_Ioo.comp_continuous continuous_subtype_val (fun x ↦ x.property)
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ fun x ↦ ⟨neg_pi_div_two_lt_arctan x, arctan_lt_pi_div_two x⟩
    exact continuous_arctan

def intervalHomeo (a b : ℝ) (h : a < b): (Ioo a b) ≃ₜ (Ioo (-(π / 2)) (π / 2)) := by
  -- Define the forward and inverse functions as affine transformations on ℝ.
  -- f(x) scales the interval (a, b) to have length π and centers it at 0.
  let f (x : ℝ) : ℝ := (π / (b - a)) * (x - (a + b) / 2)
  -- g(y) is the algebraic inverse of f(x).
  let g (y : ℝ) : ℝ := (y * (b - a) / π) + (a + b) / 2

  have hne : a ≠ b := ne_of_lt h
  exact {
    toFun := fun x : Ioo a b =>
      ⟨f x.val, by
        -- We show that if `a < x.val < b`, then `-π/2 < f(x.val) < π/2`.
        -- First, show that f maps the endpoints correctly.
        have fa : f a = -(π / 2) := by
          calc
            f a = (π / (b - a)) * (a - (a + b) / 2) := rfl
            _ = (π / (b - a)) * ((a - b) / 2) := by ring_nf
            _ = -(π / (a - b)) * ((a - b) / 2) := by rw [← neg_sub a b, div_neg]
            _ = -(π / (a - b) * (a - b) / 2) := by ring_nf
            _ = -(π * (a - b) / (a - b) / 2) := by rw [div_mul_eq_mul_div]
            _ = -(π * 1 / 2) := by field_simp [sub_ne_zero.mpr hne]
            _ = -(π / 2) := by ring_nf
        have fb : f b = π / 2 := by
          calc
          f b = (π / (b - a)) * (b - (a + b) / 2) := rfl
          _ = (π / (b - a) * (b - a) / 2) := by ring_nf
          _ = π / 2 := by grind
        rw [mem_Ioo]
        constructor
        · calc
            -(π / 2) = f a := fa.symm
            _ < f x.val := by
              -- the multiplier is positive because π > 0 and b - a > 0
              have hpos : 0 < π / (b - a) := div_pos pi_pos (sub_pos.mpr h)
              -- subtracting the same constant preserves the inequality
              have inner : a - (a + b) / 2 < x.val - (a + b) / 2 := by aesop
              -- multiply both sides by the positive scalar
              exact (mul_lt_mul_of_pos_left inner hpos)
        · calc
            f x.val < f b := by
              have hpos : 0 < π / (b - a) := div_pos pi_pos (sub_pos.mpr h)
              have inner : x.val - (a + b) / 2 < b - (a + b) / 2 := by aesop
              exact (mul_lt_mul_of_pos_left inner hpos)
            _ = π / 2 := fb
      ⟩,

    invFun := fun y : Ioo (-(π / 2)) (π / 2) =>
      -- Similarly, provide the value `g y.val` and a proof it's in the original interval.
      ⟨g y.val, by
        -- We show that if `-π/2 < y.val < π/2`, then `a < g(y.val) < b`.
        have ga : g (-(π / 2)) = a := by field_simp [g, ne_of_gt pi_pos]; ring
        have gb : g (π / 2) = b := by field_simp [g, ne_of_gt pi_pos]; ring
        rw [mem_Ioo]
        constructor
        · calc
            a = g (-(π / 2)) := ga.symm
            _ = (-(π / 2) * (b - a) / π) + (a + b) / 2 := rfl
            _ < (y.val * (b - a) / π) + (a + b) / 2 := by
              have hpos' : 0 < (b - a) / π := div_pos (sub_pos.mpr h) pi_pos
              obtain hmul := mul_lt_mul_of_pos_left y.2.1 hpos'
              rw [mul_comm] at hmul
              nth_rw 2 [mul_comm] at hmul
              obtain h' := add_lt_add_right hmul ((a + b) / 2)
              simpa [div_eq_mul_inv, mul_assoc] using h'
            _ = g y.val := rfl
        · calc
            g y.val = (y.val * (b - a) / π) + (a + b) / 2 := rfl
            _ < ((π / 2) * (b - a) / π) + (a + b) / 2 := by
              have pos_div : 0 < (b - a) / π := by
                exact div_pos (sub_pos.mpr h) Real.pi_pos
              -- multiply y < π/2 by that positive factor
              have hmul := mul_lt_mul_of_pos_right y.2.2 pos_div
              -- add (a+b)/2 to both sides
              obtain h' := add_lt_add_left hmul ((a + b) / 2)
              simpa [div_eq_mul_inv, mul_assoc] using h'
            _ = g (π / 2) := rfl
            _ = b := gb
      ⟩,

    left_inv := by
      intro x
      apply Subtype.ext
      simp only [f, g]
      calc
        π / (b - a) * (↑x - (a + b) / 2) * (b - a) / π + (a + b) / 2 = (↑x - (a + b) / 2) + (a + b) / 2 := by field_simp [pi_ne_zero, sub_ne_zero.mpr hne.symm]; linarith
        _ = ↑x := by norm_num,

    right_inv := by
      intro y
      apply Subtype.ext
      simp only [f, g]
      calc
        π / (b - a) * (↑y * (b - a) / π + (a + b) / 2 - (a + b) / 2) = π / (b - a) * (↑y * (b - a) / π) := by norm_num
        _ = ↑y := by field_simp [pi_ne_zero, sub_ne_zero.mpr hne.symm]; linarith

    continuous_toFun := by
      continuity,

    continuous_invFun := by
      continuity
  }

-- def circleHomeo : M ≃ₜ Circle := by
--   sorry
