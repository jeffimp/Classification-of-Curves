/-
Formalization of the Classification of Curves
Author: Jeff Lee
-/
import Mathlib.Tactic -- import all the tactics
import Mathlib.Analysis.Complex.Circle

open Set

/- X is a connected Hausdorff space -/
variable (X : Type*) [TopologicalSpace X] [ConnectedSpace X] [T2Space X]

/- If a connected Hausdorff space X can be represented as the
union of two open subsets homeomorphic to ℝ, then X is
homeomorphic to either ℝ or the sphere. -/
lemma union_two_real (U V : Set X) (hUOpen : IsOpen U) (hVOpen : IsOpen V)
    (hCover : U ∪ V = (Set.univ : Set X)) (φ : Homeomorph U ℝ) (ψ : Homeomorph V ℝ) :
    Nonempty (Homeomorph X ℝ) ∨ Nonempty (Homeomorph X Circle) := by
  -- Simple cases where U ⊆ V or V ⊆ U
  -- TODO: Shorten repeated proofs through lemma
  by_cases hUV : U ⊆ V
  · have h1 : U ∪ V = V := Set.union_eq_self_of_subset_left hUV
    rw [h1] at hCover
    have h2 : Homeomorph V X := by
      rw [hCover]
      exact Homeomorph.Set.univ X
    have h3 : X ≃ₜ ℝ := by
      exact (id h2.symm).trans ψ
    have h4 : Nonempty (X ≃ₜ ℝ) := by
      exact Nonempty.intro h3
    exact Or.symm (Or.inr h4)
  · by_cases hVU : V ⊆ U
    · have h1 : U ∪ V = U := Set.union_eq_self_of_subset_right hVU
      rw [h1] at hCover
      have h2 : Homeomorph U X := by
        rw [hCover]
        exact Homeomorph.Set.univ X
      have h3 : X ≃ₜ ℝ := by
        exact (id h2.symm).trans φ
      have h4 : Nonempty (X ≃ₜ ℝ) := by
        exact Nonempty.intro h3
      exact Or.symm (Or.inr h4)
    · let A := φ.toFun '' (Subtype.val ⁻¹' (U ∩ V))
      let B := ψ.toFun '' (Subtype.val ⁻¹' (U ∩ V))
      -- φ(U ∩ V) and ψ(U ∩ V) are open in ℝ
      have h1 : IsOpen (U ∩ V) :=  IsOpen.inter hUOpen hVOpen
      have h2 : IsOpen A := by
        have h2_1 : IsOpen ((@Subtype.val X U) ⁻¹' (U ∩ V)) := by
          exact isOpen_induced h1
        have h2_2 : IsOpenMap φ.toFun := Homeomorph.isOpenMap φ
        exact h2_2 (Subtype.val ⁻¹' (U ∩ V)) h2_1
      have h3 : IsOpen B := by
        have h3_1 : IsOpen ((@Subtype.val X V) ⁻¹' (U ∩ V)) := by
          exact isOpen_induced h1
        have h3_2 : IsOpenMap ψ.toFun := Homeomorph.isOpenMap ψ
        exact h3_2 (Subtype.val ⁻¹' (U ∩ V)) h3_1
      -- Components of φ(U ∩ V) and ψ(U ∩ V) are intervals
      have h4 : ∀ x ∈ A, ∃ a, (connectedComponent x) = Iio (a) ∨
          ∃ b, (connectedComponent x) = Ioi (b) := by
        intro x hx
        let Y := (connectedComponent x)
        have h4_1 : ∀ x ∈ A, (connectedComponent x) ∈ ({Icc (sInf (connectedComponent x))
            (sSup (connectedComponent x)), Ico (sInf (connectedComponent x))
            (sSup (connectedComponent x)), Ioc (sInf (connectedComponent x))
            (sSup (connectedComponent x)), Ioo (sInf (connectedComponent x))
            (sSup (connectedComponent x)), Ici (sInf (connectedComponent x)),
            Ioi (sInf (connectedComponent x)), Iic (sSup (connectedComponent x)),
            Iio (sSup (connectedComponent x)), univ, ∅} : Set (Set ℝ)) := by
          intro x hx
          have h4_1_1 : IsPreconnected (connectedComponent x) := isPreconnected_connectedComponent
          exact IsPreconnected.mem_intervals h4_1_1
        apply h4_1 at hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        have h4_2 : IsOpen Y := isOpen_connectedComponent
        have h4_3 : ¬ Y = Icc (sInf Y) (sSup Y) := by sorry
        sorry
      -- have h5 : ∀ x ∈ B, (connectedComponent x) ∈ ({Icc (sInf (connectedComponent x))
      --     (sSup (connectedComponent x)), Ico (sInf (connectedComponent x))
      --     (sSup (connectedComponent x)), Ioc (sInf (connectedComponent x))
      --     (sSup (connectedComponent x)), Ioo (sInf (connectedComponent x))
      --     (sSup (connectedComponent x)), Ici (sInf (connectedComponent x)),
      --     Ioi (sInf (connectedComponent x)), Iic (sSup (connectedComponent x)),
      --     Iio (sSup (connectedComponent x)), univ, ∅} : Set (Set ℝ)) := by
      --   intro x hx
      --   have h5_1 : IsPreconnected (connectedComponent x) := isPreconnected_connectedComponent
      --   exact IsPreconnected.mem_intervals h5_1
      -- Eliminating closed intervals, bounded intervals, ℝ and ∅

      sorry

example(p q : Prop) (h1 : p ∨ q) (h2 : ¬ p) : q := by
  cases h1 with
  | inl hp => contradiction
  | inr hq => exact hq
