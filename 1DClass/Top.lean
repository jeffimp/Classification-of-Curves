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

      -- U and V are connected (to be used in clopen argument below)
      have hRCon : IsConnected (univ : Set ℝ) := by exact isConnected_univ
      have hVCon : IsConnected ψ.source := by
        have hψHomeo : Homeomorph ψ.source ψ.target := ψ.toHomeomorphSourceTarget
        have hψTCon : IsConnected ψ.target := by
          rw [hψ]
          exact hRCon
        -- exact hψHomeo.isConnected_image.mpr hTargetCon
        -- have hT : ψ.target = hψHomeo.toFun '' (ψ.source) := by
        have hψTCon' : ConnectedSpace ψ.target := isConnected_iff_connectedSpace.mp hψTCon
        have hψTCon'' : IsConnected (univ : Set ψ.target) := isConnected_univ
        have hψSCon : IsConnected (univ : Set ψ.source) := (Homeomorph.isConnected_preimage (id hψHomeo.symm)).mp hψTCon''
        have hψSCon' : ConnectedSpace ψ.source := connectedSpace_iff_univ.mpr hψSCon
        exact isConnected_iff_connectedSpace.mpr hψSCon'
      have hUCon : IsConnected φ.source := by
        have hφHomeo : Homeomorph φ.source φ.target := φ.toHomeomorphSourceTarget
        have hφTCon : IsConnected φ.target := by
          rw [hφ]
          exact hRCon
        have hφTCon' : ConnectedSpace φ.target := isConnected_iff_connectedSpace.mp hφTCon
        have hφTCon'' : IsConnected (univ : Set φ.target) := isConnected_univ
        have hφSCon : IsConnected (univ : Set φ.source) := (Homeomorph.isConnected_preimage (id hφHomeo.symm)).mp hφTCon''
        have hφSCon' : ConnectedSpace φ.source := connectedSpace_iff_univ.mpr hφSCon
        exact isConnected_iff_connectedSpace.mpr hφSCon'

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

        rcases hRC with (hBounded | hIio | hIoi )
        · -- Difficult case: proving that connected components of A are unbounded
          exfalso

          let Z := φ.symm '' (Y)
          have hZsubV : Z ⊆ ψ.source := by sorry
          obtain ⟨a, b, hInt⟩ := hBounded
          have hZ : Z = φ.symm '' (Ioo a b) := by simp_all only [ne_eq, inter_eq_right, not_false_eq_true, mem_image,
            mem_inter_iff, forall_exists_index, and_imp, A, B, Y, Z]
          -- Specify that Z is closed in V instead of X!
          have hZClosed : IsClosed Z := by
            -- have hZClosed' : Z = φ.symm '' (Icc a b)
            sorry
          have hZOpen : IsOpen Z := by sorry
          have hZV : ψ.source = Z := by sorry
          have hVsubU : ψ.source ⊆ φ.source := by sorry
          exact hVU hVsubU

        · left
          exact hIio
        · right
          exact hIoi

      have hRClassA'' : (∃ a_1, A = Iio a_1) ∨ (∃ a_2, A = Ioi a_2) ∨ (∃ a_3 a_4, (a_3 < a_4) ∧ B = (Iio a_3) ∪ (Ioi a_4)):= by sorry
      have hRClassB'' : (∃ b_1, B = Iio b_1) ∨ (∃ b_2, B = Ioi b_2) ∨ (∃ b_3 b_4, (b_3 < b_4) ∧ B = (Iio b_3) ∪ (Ioi b_4)) := by sorry

      -- have hMono : StrictMono (ψ ∘ φ.symm) ∨ StrictAnti (ψ ∘ φ.symm) := by
      --   apply Continuous.strictMono_of_inj
      --   · apply Continuous.comp
      --     · exact ψ.continuousOn.continuousAt
      --       sorry
      --     · exact φ.continuousOn.continuousAt
      --       sorry
      --   · sorry

      have hMono' : StrictMonoOn (ψ ∘ φ.symm) (φ.target) ∨ StrictAntiOn (ψ ∘ φ.symm) (φ.target) := by
        have hψCont : ContinuousOn ψ (ψ.source) := by exact PartialHomeomorph.continuousOn ψ
        have hUVsubV : ψ.source ∩ φ.source ⊆ φ.source := by exact inter_subset_right
        have hψCont' : ContinuousOn ψ (ψ.source ∩ φ.source) := by
          apply ContinuousOn.mono hψCont
          exact inter_subset_left
        sorry

      rcases hRClassA'' with (hAIio | hAIoi | hAUnion)
      · rcases hRClassB'' with (hBIio | hBIoi | hBUnion)
        ·
          sorry
        · sorry
        · sorry
      · rcases hRClassB'' with (hBIio | hBIoi | hBUnion)
        · sorry
        · sorry
        · sorry
      · rcases hRClassB'' with (hBIio | hBIoi | hBUnion)
        · sorry
        · sorry
        · sorry
