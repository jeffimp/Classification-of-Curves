/-
Formalization of the Classification of Curves
Author: Jeff Lee
-/
import Mathlib.Tactic -- import all the tactics
import Mathlib.Analysis.Complex.Circle
import «1DClass».Test

open Set

-- /- A non-empty proper set in ℝ cannot be both open and closed. -/
-- lemma open_not_closed (A B : Set ℝ) (hAOpen : IsOpen A) (hBClosed : IsClosed B)
--     (hANonempty : A.Nonempty) (hAProper : A ≠ univ) : A ≠ B := by
--   intro h
--   rw [←h] at hBClosed
--   have hAClopen : IsClopen A := ⟨hBClosed, hAOpen⟩
--   have hClopen : A = ∅ ∨ A = univ := by exact isClopen_iff.mp hAClopen
--   cases' hClopen with hEmp hUniv
--   · exact hANonempty.ne_empty hEmp
--   · exact hAProper hUniv

/- X is a connected Hausdorff space -/
variable (X : Type*) [TopologicalSpace X] [ConnectedSpace X] [T2Space X]

/- If a connected Hausdorff space X can be represented as the
union of two open subsets homeomorphic to ℝ, then X is
homeomorphic to either ℝ or the sphere. -/
lemma union_two_real (U V : Set X) (hUOpen : IsOpen U) (hVOpen : IsOpen V)
    (hCover : U ∪ V = (Set.univ : Set X)) (φ : Homeomorph U ℝ) (ψ : Homeomorph V ℝ) :
    Nonempty (Homeomorph X ℝ) ∨ Nonempty (Homeomorph X Circle) := by
  -- Simple cases where U ⊆ V or V ⊆ U
  -- Helper lemma to condense code
  let simple_homeo (W : Set X) (h_eq : U ∪ V = W) (homeo : Homeomorph W ℝ) : Nonempty (Homeomorph X ℝ) := by
    have h_univ : W = Set.univ := by rw [←hCover, h_eq]
    have h_homeo : Homeomorph W X := by rw [h_univ]; exact Homeomorph.Set.univ X
    exact ⟨h_homeo.symm.trans homeo⟩
  by_cases hUV : U ⊆ V
  · exact Or.inl (simple_homeo V (Set.union_eq_self_of_subset_left hUV) ψ)
  · by_cases hVU : V ⊆ U
    · exact Or.inl (simple_homeo U (Set.union_eq_self_of_subset_right hVU) φ)
    -- Now working with the assumption that ¬ U ⊆ V and ¬ V ⊆ U
    · let A := φ.toFun '' (Subtype.val ⁻¹' (U ∩ V))
      let B := ψ.toFun '' (Subtype.val ⁻¹' (U ∩ V))
      -- φ(U ∩ V) and ψ(U ∩ V) are open in ℝ
      have hUVOpen : IsOpen (U ∩ V) :=  IsOpen.inter hUOpen hVOpen
      have hAOpen : IsOpen A := by
        have h2_1 : IsOpen ((@Subtype.val X U) ⁻¹' (U ∩ V)) := by
          exact isOpen_induced hUVOpen
        have h2_2 : IsOpenMap φ.toFun := Homeomorph.isOpenMap φ
        exact h2_2 (Subtype.val ⁻¹' (U ∩ V)) h2_1
      have hBOpen : IsOpen B := by
        have h3_1 : IsOpen ((@Subtype.val X V) ⁻¹' (U ∩ V)) := by
          exact isOpen_induced hUVOpen
        have h3_2 : IsOpenMap ψ.toFun := Homeomorph.isOpenMap ψ
        exact h3_2 (Subtype.val ⁻¹' (U ∩ V)) h3_1
      -- Components of φ(U ∩ V) and ψ(U ∩ V) are intervals
      have hRClass : ∀ x ∈ A, ∃ a, (connectedComponent x) = Iio (a) ∨
          ∃ b, (connectedComponent x) = Ioi (b) := by
        intro x hx
        let Y := (connectedComponent x)
        have hRClassInt : ∀ y ∈ A, (connectedComponent y) ∈ ({Icc (sInf (connectedComponent y))
            (sSup (connectedComponent y)), Ico (sInf (connectedComponent y))
            (sSup (connectedComponent y)), Ioc (sInf (connectedComponent y))
            (sSup (connectedComponent y)), Ioo (sInf (connectedComponent y))
            (sSup (connectedComponent y)), Ici (sInf (connectedComponent y)),
            Ioi (sInf (connectedComponent y)), Iic (sSup (connectedComponent y)),
            Iio (sSup (connectedComponent y)), univ, ∅} : Set (Set ℝ)) := by
          intro y hy
          have hPrecon : IsPreconnected (connectedComponent y) := isPreconnected_connectedComponent
          exact IsPreconnected.mem_intervals hPrecon
        apply hRClassInt at hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        have hYOpen : IsOpen Y := isOpen_connectedComponent
        -- First prove unbounded?
        have hYNonempty : Y.Nonempty := connectedComponent_nonempty
        have hYProper : Y ≠ univ := by sorry
        have hYnotIcc : Y ≠ Icc (sInf Y) (sSup Y) := by
          have hIccClosed : IsClosed (Icc (sInf Y) (sSup Y)) := isClosed_Icc
          exact open_not_closed Y (Icc (sInf Y) (sSup Y)) hYOpen hIccClosed hYNonempty hYProper
        have hYnotIci : Y ≠ Ici (sInf Y) := by
          have hIciClosed : IsClosed (Ici (sInf Y)) := isClosed_Ici
          exact open_not_closed Y (Ici (sInf Y)) hYOpen hIciClosed hYNonempty hYProper
        have hYnotIic : Y ≠ Iic (sSup Y) := by
          have hIicClosed : IsClosed (Iic (sSup Y)) := isClosed_Iic
          exact open_not_closed Y (Iic (sSup Y)) hYOpen hIicClosed hYNonempty hYProper
        sorry
      sorry

example (p q : Prop) (h1 : p ∨ q) (h2 : ¬ p) : q := by
  cases h1 with
  | inl hp => contradiction
  | inr hq => exact hq

variable {α : Type u} {β : Type v} {γ : Type w} [ConditionallyCompleteLinearOrder α]
  [TopologicalSpace α] [OrderTopology α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β]
  [OrderTopology β] [Nonempty γ]

theorem interval_test {s : Set α} (hs : IsPreconnected s) :
    s ∈
      ({Icc (sInf s) (sSup s), Ico (sInf s) (sSup s), Ioc (sInf s) (sSup s), Ioo (sInf s) (sSup s),
          Ici (sInf s), Ioi (sInf s), Iic (sSup s), Iio (sSup s), univ, ∅} : Set (Set α)) := by
  rcases s.eq_empty_or_nonempty with (rfl | hne)
  · apply_rules [Or.inr, mem_singleton]
  have hs' : IsConnected s := ⟨hne, hs⟩
  by_cases hb : BddBelow s <;> by_cases ha : BddAbove s
  · refine mem_of_subset_of_mem ?_ <| mem_Icc_Ico_Ioc_Ioo_of_subset_of_subset
      (hs'.Ioo_csInf_csSup_subset hb ha) (subset_Icc_csInf_csSup hb ha)
    simp only [insert_subset_iff, mem_insert_iff, mem_singleton_iff, true_or, or_true,
      singleton_subset_iff, and_self]
  · refine Or.inr <| Or.inr <| Or.inr <| Or.inr ?_
    cases'
      mem_Ici_Ioi_of_subset_of_subset (hs.Ioi_csInf_subset hb ha) fun x hx => csInf_le hb hx with
      hs hs
    · exact Or.inl hs
    · exact Or.inr (Or.inl hs)
  · iterate 6 apply Or.inr
    cases' mem_Iic_Iio_of_subset_of_subset (hs.Iio_csSup_subset hb ha) fun x hx => le_csSup ha hx
      with hs hs
    · exact Or.inl hs
    · exact Or.inr (Or.inl hs)
  · iterate 8 apply Or.inr
    exact Or.inl (hs.eq_univ_of_unbounded hb ha)

lemma test_lemma (p q : Prop) (h : p) : p ∨ q := by
  (constructor ; exact h)
  -- constructor <;> exact h
