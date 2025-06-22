/-
Formalization of the Classification of Curves
Author: Jeff Lee
-/
import Mathlib.Tactic -- import all the tactics
import Mathlib.Analysis.Complex.Circle
import «1DClass».RealClass

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

      have hUNonempty : U.Nonempty := by sorry

      -- φ(U ∩ V) is not a proper set i.e. φ(U ∩ V) ≠ ℝ
      have hAProper : A ≠ univ := by
        have hVnX : V ≠ (univ : Set X) := by
          simp_all only [Equiv.toFun_as_coe, Homeomorph.coe_toEquiv, preimage_inter, Subtype.coe_preimage_self,
            univ_inter, Homeomorph.isOpen_image, IsOpen.inter_preimage_val_iff, inter_univ, ne_eq, A, B]
          apply Aesop.BuiltinRules.not_intro
          intro a
          subst a
          simp_all only [isOpen_univ, subset_univ, not_true_eq_false]
        have hxnV : ∃ x ∈ (univ : Set X), x ∉ V := by
          simp only [mem_univ, true_and]
          exact not_forall.mp fun a ↦ hUV fun ⦃a_1⦄ a_2 ↦ a a_1
        have hxUnUV : ∃ x ∈ U, x ∉ (U ∩ V) := by
          obtain ⟨x, hx⟩ := hxnV
          simp only [mem_inter_iff, not_and, B, A]
          use x
          constructor
          · have hxUV : x ∈ U ∪ V := by
              simp_all only [Equiv.toFun_as_coe, Homeomorph.coe_toEquiv, preimage_inter, Subtype.coe_preimage_self,
                univ_inter, Homeomorph.isOpen_image, IsOpen.inter_preimage_val_iff, inter_univ, ne_eq, mem_univ,
                true_and, B, A]
            exact hxUV.resolve_right hx.2
          · intro hxU
            exact hx.2
        have hUVnV : U ∩ V ≠ U := by
          simp_all only [Equiv.toFun_as_coe, Homeomorph.coe_toEquiv, preimage_inter, Subtype.coe_preimage_self,
            univ_inter, Homeomorph.isOpen_image, IsOpen.inter_preimage_val_iff, inter_univ, ne_eq, mem_univ, true_and,
            mem_inter_iff, not_and, inter_eq_left, not_false_eq_true, B, A]
        have hφUV : A = φ.toFun '' (Subtype.val ⁻¹' (U ∩ V)) := rfl
        have hφU : (univ : Set ℝ) = φ.toFun '' (Subtype.val ⁻¹' (U)) := by
          simp only [Equiv.toFun_as_coe,
            Homeomorph.coe_toEquiv, Subtype.coe_preimage_self, image_univ, EquivLike.range_eq_univ, B, A]
        rw [hφUV, hφU]
        -- simp only [Equiv.toFun_as_coe, Homeomorph.coe_toEquiv, preimage_inter, Subtype.coe_preimage_self, univ_inter, image_univ, EquivLike.range_eq_univ, ne_eq, B, A]
        by_contra h
        -- Proving injectivity of φ (considering Subtype complications as well)
        have hφSubInj : Function.Injective (fun p ↦ φ.toFun '' (Subtype.val ⁻¹' (p))) := by
          simp only [Equiv.toFun_as_coe, Homeomorph.coe_toEquiv, B, A]
          intros p q hpq
          have hφInj : Function.Injective φ.toFun := φ.injective
          have hSubEq : (Subtype.val ⁻¹' p : Set ↑U) = (Subtype.val ⁻¹' q : Set ↑U) := (image_eq_image hφInj).mp hpq
          -- TODO: Prove injectivity of Subtype.val pre-image
          sorry
        have hcontra : U ∩ V = U := by
          sorry
        exact hUVnV (hφSubInj h)

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
        have hYProper : Y ≠ univ := sorry
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
