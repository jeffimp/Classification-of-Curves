/-
Formalization of the Classification of Curves
Author: Jeff Lee
-/
import Mathlib.Tactic -- import all the tactics
import Mathlib.Analysis.Complex.Circle
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.Instances.Real
import «1DClass».RealClass

open Set Function

/- X is a connected Hausdorff space -/
variable (X : Type*) [TopologicalSpace X] [ConnectedSpace X] [T2Space X]

/- If a connected Hausdorff space X can be represented as the union of two open subsets homeomorphic to ℝ, then X is homeomorphic to either ℝ or the sphere. -/
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
          simp only [ne_eq, inter_eq_right]
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
          have hZsubV' : φ.source ∩ ψ.source ⊆ ψ.source := inter_subset_right
          have hZsubUV : Z ⊆ φ.source ∩ ψ.source := by
            simp only [Z, Y, A]
            intro z hz
            simp only [Set.mem_image] at hz
            rcases hz with ⟨y, hy, hzy⟩
            have hyA : y ∈ φ '' (φ.source ∩ ψ.source) := by
              apply connectedComponentIn_subset A x
              exact hy
            simp only [Set.mem_image] at hyA
            rcases hyA with ⟨w, hw, hyw⟩
            have hwφ : w ∈ φ.source := mem_of_mem_inter_left hw
            have hφinv : φ.symm (φ w) = w := by
              apply PartialHomeomorph.left_inv
              exact hwφ
            have hz_eq_w : z = w := by
              subst hyw hzy
              simp_all only [ne_eq, inter_eq_right, not_false_eq_true, mem_image, mem_inter_iff, forall_exists_index,
                and_imp, inter_subset_right, true_and, PartialHomeomorph.left_inv, A, B, Y]
            exact hz_eq_w ▸ hw
          have hZsubV : Z ⊆ ψ.source := by
            exact fun ⦃a⦄ a_1 ↦ hZsubV' (hZsubUV a_1)
          obtain ⟨a, b, hInt⟩ := hBounded
          have hZ : Z = φ.symm '' (Ioo a b) := by simp_all only [ne_eq, inter_eq_right, not_false_eq_true, mem_image,
            mem_inter_iff, forall_exists_index, and_imp, A, B, Y, Z]
          -- Specify that Z is closed in V instead of X!
          have hZClosed : IsClosed Z := by
            -- have hZClosed' : Z = φ.symm '' (Icc a b)

            sorry
          have hZOpen : IsOpen Z := by sorry
          have hZClopen: IsClopen Z := by sorry
          have hZV : ψ.source = Z := by sorry
          have hVsubU : ψ.source ⊆ φ.source := by sorry
          exact hVU hVsubU

        · left
          exact hIio
        · right
          exact hIoi

      have hRClassA'' : (∃ a_1, A = Iio a_1) ∨ (∃ a_2, A = Ioi a_2) ∨ (∃ a_3 a_4, (a_3 < a_4) ∧ A = (Iio a_3) ∪ (Ioi a_4)):= by sorry
      have hRClassB'' : (∃ b_1, B = Iio b_1) ∨ (∃ b_2, B = Ioi b_2) ∨ (∃ b_3 b_4, (b_3 < b_4) ∧ B = (Iio b_3) ∪ (Ioi b_4)) := by sorry

      -- have φ' : Homeomorph φ.source φ.target := by exact φ.toHomeomorphSourceTarget
      -- have ψ' : Homeomorph ψ.source ψ.target := ψ.toHomeomorphSourceTarget
      -- let T := ((φ' '' ((univ : Set φ.source) ∩ (univ : Set ψ.source))).restrict (ψ ∘ φ.symm))

      let invφ' : A → X := fun x => φ.symm x.val
      -- (φ '' (φ.source ∩ ψ.source)).restrict φ.symm

      have hinvφ'ran : range invφ' = φ.source ∩ ψ.source := by
        ext y
        simp only [mem_range, mem_inter_iff]
        constructor
        · rintro ⟨x, rfl⟩
          obtain ⟨z, hzUV⟩ := x.prop
          simp_all [A, B, invφ']
          obtain ⟨val, property⟩ := x
          obtain ⟨left, right⟩ := hzUV
          obtain ⟨left, right_1⟩ := left
          subst right
          simp_all only [PartialHomeomorph.left_inv]
        · intro hy
          use ⟨φ y, ⟨y, hy, rfl⟩⟩
          simp_all only [ne_eq, inter_eq_right, not_false_eq_true, mem_image, mem_inter_iff, forall_exists_index,
            and_imp, PartialHomeomorph.left_inv, A, B, invφ']

      -- let invφ'' : A → (φ.source ∩ ψ.source : Set X) := fun x => φ.symm x.val

      have hinvφ'Cont : Continuous invφ' := by
        refine continuous_iff_continuousAt.mpr ?_
        intro x
        -- have : TopologicalSpace A := instTopologicalSpaceSubtype
        obtain h := PartialHomeomorph.continuousAt_symm φ
        have hAsubTarget : A ⊆ φ.target := by
          simp only [A] at ⊢
          intro y hy
          obtain ⟨x, hx, rfl⟩ := hy
          refine PartialHomeomorph.map_source φ ?_
          exact mem_of_mem_inter_left hx
        have : x.val ∈ A := by exact Subtype.coe_prop x
        have h': x.val ∈ φ.target := by exact hAsubTarget this
        -- have h'' : x.val ∈ φ.target := h'
        -- apply h at h'
        -- We currently have ContinuousAt ↑φ.symm ↑x but we want ContinuousAt invφ' x
        rw [show invφ' = fun x => φ.symm x.val from rfl]
        apply ContinuousAt.comp (h h')
        exact continuousAt_subtype_val

      let ψ' : (φ.source ∩ ψ.source : Set X) → ℝ := fun x => ψ x.val

      have hψ'Cont : Continuous ψ' := by
        refine continuous_iff_continuousAt.mpr ?_
        intro x
        obtain h := PartialHomeomorph.continuousAt ψ
        have : x.val ∈ φ.source ∩ ψ.source := by exact Subtype.coe_prop x
        have h' : x.val ∈ ψ.source := by exact mem_of_mem_inter_right this
        apply ContinuousAt.comp (h h')
        exact continuousAt_subtype_val

      -- let transition : A → ℝ := fun x => ψ' (invφ' x)

      let T : φ '' (φ.source ∩ ψ.source) → ℝ := (φ '' (φ.source ∩ ψ.source)).restrict (ψ ∘ φ.symm)

      have hMono : StrictMono T ∨ StrictAnti T := by
        sorry -- apply Continuous.strictMono_of_inj

      -- Proving that U ∩ V is nonempty to choose elements
      have hUNonempty : (φ.source).Nonempty := by exact IsConnected.nonempty hUCon
      have hVNonempty : (ψ.source).Nonempty := by exact IsConnected.nonempty hVCon

      have hUVNonempty : (φ.source ∩ ψ.source).Nonempty := by
        by_contra hUVEmpty
        have hUVEmpty' : φ.source ∩ ψ.source = ∅ := not_nonempty_iff_eq_empty.mp hUVEmpty
        have hUVDisjoint : Disjoint φ.source ψ.source := disjoint_iff_inter_eq_empty.mpr hUVEmpty'
        have hXCon : IsConnected (univ : Set X) := by (expose_names; exact connectedSpace_iff_univ.mp inst_1)
        have hPrecon : IsPreconnected (univ : Set X) := hXCon.isPreconnected
        rw [← hCover] at hPrecon
        have hUnion : (φ.source ∪ ψ.source).Nonempty := by exact Nonempty.inr hVNonempty
        -- We want to get a contradiction from the fact that φ.source and ψ.source are disjoint, yet it is preconnected AND not empty!
        sorry

      -- Splitting into cases approach
      rcases hRClassA'' with (hAIio | hAIoi | hAUnion)
      · rcases hRClassB'' with (hBIio | hBIoi | hBUnion)
        ·
          sorry
        · -- Case explored in Beginner's Course in Topology
          obtain ⟨a, hAIio'⟩ := hAIio
          obtain ⟨b, hBIoi'⟩ := hBIoi
          have hMonoTr : StrictMonoOn (ψ ∘ φ.symm) (A) := by
            simp_all only [A, B]
            refine strictMono_restrict.mp ?_
            have hCOTA : OrderClosedTopology (Iio a) := by exact Subtype.instOrderClosedTopology
            have hContTr : Continuous ((Iio a).restrict (ψ ∘ φ.symm)) := by
              have hψCont : Continuous ((φ.symm '' (Iio a)).restrict ψ) := by
                sorry
              sorry
            -- exact Continuous.strictMono_of_inj hCOTA
            sorry

          have hx_0 : ∃ x_0, x_0 ∈ (φ.source ∩ ψ.source) := by exact hUVNonempty
          obtain ⟨x_0, hx_0⟩ := hx_0 -- hx_0
          let X' := ψ.symm '' (Iic (ψ x_0)) ∪ φ.symm '' (Ici (φ x_0))

          have hy : ∃ y, y ∈ (φ.source ∩ ψ.source) := by exact hUVNonempty
          obtain ⟨y, hy⟩ := hy


          -- U and V contained in X', so X' = X = U ∪ V
          have hUsubX' : φ.source ⊆ X' := by
            have hφa : φ x_0 < a := by
              sorry
            sorry

          sorry
        · sorry
      · rcases hRClassB'' with (hBIio | hBIoi | hBUnion)
        · sorry
        · sorry
        · sorry
      · rcases hRClassB'' with (hBIio | hBIoi | hBUnion)
        · sorry
        · sorry
        · sorry
