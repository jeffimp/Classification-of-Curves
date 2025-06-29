/-
Formalization of the Classification of Curves
Author: Jeff Lee
-/
import Mathlib.Tactic -- import all the tactics
import Mathlib.Analysis.Complex.Circle
import «1DClass».RealClass

open Set Function

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

/- If a connected Hausdorff space X can be represented as the union of two open subsets homeomorphic to ℝ, then X is
homeomorphic to either ℝ or the sphere. -/
-- Using PartialHomeomorph structure instead of Homeomorph in order to avoid Subtype difficulties
-- Notation: U = φ.source, V = ψ.source
lemma real_cover (φ ψ : PartialHomeomorph X ℝ) (hCover : φ.source ∪ ψ.source = univ)
    (hφ : φ.target = univ) (hψ : ψ.target = univ) : Nonempty (Homeomorph X ℝ) ∨ Nonempty (Homeomorph X Circle) := by

  have hUOpen : IsOpen φ.source := φ.open_source
  have hVOpen : IsOpen ψ.source := ψ.open_source

  by_cases hUV : φ.source ⊆ ψ.source
  · have hV : φ.source ∪ ψ.source = ψ.source := union_eq_self_of_subset_left hUV
    rw [hV] at hCover
    -- have hHomVX : Homeomorph ψ.source X := by
    --   rw [hCover]
    --   exact Homeomorph.Set.univ X
    have hHomXReal : Homeomorph X ℝ := by
      -- calc
      --   X ≃ₜ (ψ.source) := by exact id hHomVX.symm
      --   _ ≃ₜ (ψ.target) := by sorry
      -- have hψst : ψ.source ≃ₜ ψ.target := by exact ψ.toHomeomorphSourceTarget
      exact ψ.toHomeomorphOfSourceEqUnivTargetEqUniv hCover hψ
    apply Or.inl
    exact Nonempty.intro hHomXReal
  · by_cases hVU : ψ.source ⊆ φ.source
    · have hU : φ.source ∪ ψ.source = φ.source := union_eq_self_of_subset_right hVU
      rw [hU] at hCover
      -- have hHomUX : Homeomorph φ.source X := by
      --   rw [hCover]
      --   exact Homeomorph.Set.univ X
      have hHomXReal : Homeomorph X ℝ := φ.toHomeomorphOfSourceEqUnivTargetEqUniv hCover hφ
      apply Or.inl
      exact Nonempty.intro hHomXReal

    · let A := φ '' (φ.source ∩ ψ.source)
      let B := ψ '' (φ.source ∩ ψ.source)

      -- have hUVOpen : IsOpen (φ.source ∩ ψ.source) := by exact IsOpen.inter hUOpen hVOpen
      have hAOpen : IsOpen A := PartialHomeomorph.isOpen_image_source_inter φ hVOpen
      have hBOpen : IsOpen B := by
        have hUVsym : ψ.source ∩ φ.source = φ.source ∩ ψ.source := inter_comm ψ.source φ.source
        have hB : B = ψ '' (ψ.source ∩ φ.source) := by simp_all only [B]
          -- simp_all only [A, B]
          -- ext x : 1
          -- simp_all only [mem_image, mem_inter_iff]
          -- apply Iff.intro
          -- · intro a
          --   obtain ⟨w, h⟩ := a
          --   obtain ⟨left, right⟩ := h
          --   obtain ⟨left, right_1⟩ := left
          --   subst right
          --   apply Exists.intro
          --   · apply And.intro
          --     on_goal 2 => {rfl
          --     }
          --     · simp_all only [and_self]
          -- · intro a
          --   obtain ⟨w, h⟩ := a
          --   obtain ⟨left, right⟩ := h
          --   obtain ⟨left, right_1⟩ := left
          --   subst right
          --   apply Exists.intro
          --   · apply And.intro
          --     on_goal 2 => {rfl
          --     }
          --     · simp_all only [and_self]
        have hBOpen' : IsOpen (ψ '' (ψ.source ∩ φ.source)) := PartialHomeomorph.isOpen_image_source_inter ψ hUOpen
        simp_all only [A, B]

      have hUVnV : φ.source ∩ ψ.source ≠ ψ.source := by
          simp only [ne_eq, inter_eq_right, A, B]
          exact hVU

      have hAProper : A ≠ univ := by
        have hφU : φ '' (φ.source) = univ := by
          have hφU' : φ '' (φ.source) = φ.target := PartialHomeomorph.image_source_eq_target φ
          rw [hφ] at hφU'
          exact hφU'
        -- Specify domain and range!
        have hφInj : InjOn φ (φ.source) := PartialHomeomorph.injOn φ
        have hUVsubU : φ.source ∩ ψ.source ⊆ φ.source := inter_subset_left
        have hφAInj : InjOn φ (φ.source ∩ ψ.source) := by exact InjOn.mono hUVsubU hφInj
        have hProper : φ '' (φ.source ∩ ψ.source) ≠ φ '' (φ.source) := by
          -- Use hUVnV and hφInj!
          intro hC
          have hC' : φ.source ∩ ψ.source = φ.source := by
            apply (InjOn.image_eq_image_iff hφInj hUVsubU (subset_refl _)).mp
            exact hC
          have hC'' : φ.source ⊆ ψ.source := by
            rw [← hC']
            exact inter_subset_right
          have hC''' : φ.source ∩ ψ.source = ψ.source := by
            exact False.elim (hUV hC'')
          exact hUVnV hC'''
        exact Ne.symm (Lean.Grind.ne_of_ne_of_eq_left (id (Eq.symm hφU)) (id (Ne.symm hProper)))

      have hBProper : B ≠ univ := by
        have hψV : ψ '' (ψ.source) = univ := by
          have hψV' : ψ '' (ψ.source) = ψ.target := PartialHomeomorph.image_source_eq_target ψ
          rw [hψ] at hψV'
          exact hψV'
        have hψInj : InjOn ψ (ψ.source) := PartialHomeomorph.injOn ψ
        have hUVsubV : φ.source ∩ ψ.source ⊆ ψ.source := inter_subset_right
        have hψBInj : InjOn ψ (φ.source ∩ ψ.source) := InjOn.mono hUVsubV hψInj
        have hProper : ψ '' (φ.source ∩ ψ.source) ≠ ψ '' (ψ.source) := by
          intro hC
          have hC' : φ.source ∩ ψ.source = ψ.source := by
            apply (InjOn.image_eq_image_iff hψInj hUVsubV (subset_refl _)).mp
            exact hC
          have hC'' : ψ.source ⊆ φ.source := by
            rw [← hC']
            exact inter_subset_left
          have hC''' : φ.source ∩ ψ.source = φ.source := by
            exact False.elim (hVU hC'')
          exact hVU hC''
        exact Ne.symm (Lean.Grind.ne_of_ne_of_eq_left (id (Eq.symm hψV)) (id (Ne.symm hProper)))

      -- A and B induced subspace topology
      -- have hATop : TopologicalSpace A := by exact instTopologicalSpaceSubtype
      -- have hBTop : TopologicalSpace B := by exact instTopologicalSpaceSubtype

      -- have hRClass : ∀ (x : A), ∃ a, (connectedComponent x) = Iio a ∨ ∃ b, (connectedComponent x) = Ioi b := by
      --   -- Careful with types
      --   intro x
      --   let Y := (connectedComponent x)
      --   let Y' := Subtype.val '' Y
      --   have hY'Proper : Y' ≠ univ := by
      --     intro h
      --     have hY'SubA : Y' ⊆ A :=  Subtype.coe_image_subset A Y
      --     rw [h] at hY'SubA
      --     have hAUniv : A = univ := eq_univ_of_univ_subset hY'SubA
      --     exact hAProper hAUniv

      --   -- Why does isOpen_connectedComponent fail? - Why LocallyConnectedSpace issue instead of connectedComponent issue?
      --   have hY'Open : IsOpen Y' := by
      --     sorry -- exact isOpen_connectedComponent

      have hRClassA : ∀ x ∈ A, (∃ a b, (connectedComponentIn A x) = Ioo a b) ∨ (∃ a, (connectedComponentIn A x) = Iio a) ∨ (∃ b, (connectedComponentIn A x) = Ioi b) := by
        intro x hx
        let Y := (connectedComponentIn A x)

        have hYCon : IsConnected Y := by exact isConnected_connectedComponentIn_iff.mpr hx

        have hYProper : Y ≠ univ := by
          intro hC
          have hYsubA : Y ⊆ A := connectedComponentIn_subset A x
          rw [hC] at hYsubA
          have hAUniv : A = univ := SurjOn.image_eq_of_mapsTo hYsubA fun ⦃x⦄ a ↦ trivial
          exact hAProper hAUniv

        have hYOpen : IsOpen Y := IsOpen.connectedComponentIn hAOpen

        have hYNonempty : Y.Nonempty := by
          refine connectedComponentIn_nonempty_iff.mpr ?_
          exact hx

        obtain hRC := real_class Y hYOpen hYCon
        simp only [hYProper, or_false] at hRC

        rcases hRC with (h1 | h2 | h3 )
        · left ; exact h1
        · right ; left ; exact h2
        · right ; right ; exact h3

      have hRClassA' : ∀ x ∈ A, (∃ a, (connectedComponentIn A x) = Iio a) ∨ (∃ b, (connectedComponentIn A x) = Ioi b) := by
        intro x hx
        let Y := (connectedComponentIn A x)

        have hYCon : IsConnected Y := by exact isConnected_connectedComponentIn_iff.mpr hx

        have hYProper : Y ≠ univ := by
          intro hC
          have hYsubA : Y ⊆ A := connectedComponentIn_subset A x
          rw [hC] at hYsubA
          have hAUniv : A = univ := SurjOn.image_eq_of_mapsTo hYsubA fun ⦃x⦄ a ↦ trivial
          exact hAProper hAUniv

        have hYOpen : IsOpen Y := IsOpen.connectedComponentIn hAOpen

        have hYNonempty : Y.Nonempty := by
          refine connectedComponentIn_nonempty_iff.mpr ?_
          exact hx

        obtain hRC := real_class Y hYOpen hYCon
        simp only [hYProper, or_false] at hRC

        rcases hRC with (h1 | h2 | h3 )
        · -- Difficult case: proving that connected components of A are unbounded:
          exfalso
          sorry
        · left
          exact h2
        · right
          exact h3

      sorry




/- Attempt #1 (Uses Homeomorph and connectedComponent structures instead of PartialHomeomorph and connectedComponentIn) -/
lemma union_two_real (U V : Set X) (hUOpen : IsOpen U) (hVOpen : IsOpen V)
    (hCover : U ∪ V = (Set.univ : Set X)) (φ : Homeomorph U ℝ) (ψ : Homeomorph V ℝ) :
    Nonempty (Homeomorph X ℝ) ∨ Nonempty (Homeomorph X Circle) := by
  -- Simple cases where U ⊆ V or V ⊆ U
  -- Helper lemma to condense code
  -- let simple_homeo (W : Set X) (h_eq : U ∪ V = W) (homeo : Homeomorph W ℝ) : Nonempty (Homeomorph X ℝ) := by
  --   have h_univ : W = Set.univ := by rw [←hCover, h_eq]
  --   have h_homeo : Homeomorph W X := by rw [h_univ]; exact Homeomorph.Set.univ X
  --   exact ⟨h_homeo.symm.trans homeo⟩
  -- by_cases hUV : U ⊆ V
  -- · exact Or.inl (simple_homeo V (Set.union_eq_self_of_subset_left hUV) ψ)
  -- · by_cases hVU : V ⊆ U
  --   · exact Or.inl (simple_homeo U (Set.union_eq_self_of_subset_right hVU) φ)
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
