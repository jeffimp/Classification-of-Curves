/-
Classification of connected open sets in ℝ.
-/
import Mathlib.Tactic -- import all the tactics

open Set

/- A non-empty proper set in ℝ cannot be both open and closed. -/
lemma open_not_closed (A B : Set ℝ) (hAOpen : IsOpen A) (hBClosed : IsClosed B)
    (hANonempty : A.Nonempty) (hAProper : A ≠ univ) : A ≠ B := by
  intro h
  rw [←h] at hBClosed
  have hAClopen : IsClopen A := ⟨hBClosed, hAOpen⟩
  have hClopen : A = ∅ ∨ A = univ := by exact isClopen_iff.mp hAClopen
  cases' hClopen with hEmp hUniv
  · exact hANonempty.ne_empty hEmp
  · exact hAProper hUniv

/- An open set in ℝ cannot be of the form [a, ∞). -/
lemma Ici_not_open (A : Set ℝ) (a : ℝ) (hAOpen : IsOpen A) : (A ≠ Ici a) := by
  by_contra hEq
  rw [hEq] at hAOpen
  have hIciClosed : IsClosed (Ici a) := isClosed_Ici
  have hComplOpen : IsOpen (Ici a)ᶜ := IsClosed.isOpen_compl
  have hCon : IsPreconnected (univ : Set ℝ) := isPreconnected_univ
  obtain hCon_1 := hCon (Ici a) ((Ici a)ᶜ) hAOpen hComplOpen
  have hCover : Ici a ∪ (Ici a)ᶜ = univ := union_compl_self (Ici a)
  rw [hCover] at hCon_1
  simp only [subset_refl, univ_inter, nonempty_Ici, compl_Ici, nonempty_Iio, forall_const] at hCon_1
  have hEmp (b : ℝ) : (Ici b ∩ Iio b) = ∅ := by
    have hCap : Ici b ∩ Iio b = Ico b b := rfl
    rw [hCap]
    exact Ico_self b
  rw [hEmp] at hCon_1
  apply Set.not_nonempty_empty
  exact hCon_1

/- An open set in ℝ cannot be of the form (-∞, a]. -/
lemma Iic_not_open (A : Set ℝ) (a : ℝ) (hAOpen : IsOpen A) : (A ≠ Iic a) := by
  by_contra hEq
  rw [hEq] at hAOpen
  -- have hIicProper : Iic a ≠ univ := by
  --   intro hEquniv
  --   -- Since `Iic a = ℝ`, every `x ∈ ℝ` lies in `Iic a`, in particular `a + 1`.
  --   have hmem : a + 1 ∈ Iic a := by
  --     aesop
  --   -- But `a + 1 ∈ Iic a` means `a + 1 ≤ a`, impossible in ℝ.
  --   have hcontra : a + 1 ≤ a := hmem
  --   linarith
  have hIicClosed : IsClosed (Iic a) := isClosed_Iic
  have hComplOpen : IsOpen (Iic a)ᶜ := IsClosed.isOpen_compl
  have hCon : IsPreconnected (univ : Set ℝ) := isPreconnected_univ
  obtain hCon_1 := hCon (Iic a) ((Iic a)ᶜ) hAOpen hComplOpen
  have hCover : Iic a ∪ (Iic a)ᶜ = univ := union_compl_self (Iic a)
  rw [hCover] at hCon_1
  simp only [subset_refl, univ_inter, nonempty_Iic, compl_Iic, nonempty_Ioi, forall_const] at hCon_1
  have hEmp (b : ℝ) : (Iic b ∩ Ioi b) = ∅ := by
    have hCap : Iic b ∩ Ioi b = Ioc b b := by exact Iic_inter_Ioi
    rw [hCap]
    exact Ioc_self b
  rw [hEmp] at hCon_1
  apply Set.not_nonempty_empty
  exact hCon_1

/- A nonempty open set in ℝ cannot be of the form (a b]. -/
lemma Ioc_not_open (A : Set ℝ) (a b : ℝ) (hAOpen : IsOpen A) (hANonempty : A ≠ ∅) : A ≠ Ioc a b := by
  by_cases hab : a < b
  · have hnIoc : ¬ IsOpen (Ioc a b) := by
      have hIic : (Ioc a b) ∪ (Iio b) = Iic b := by
        ext x
        simp only [mem_union, mem_Ioc, mem_Iio, mem_Iic]
        constructor
        · intro a_1
          simp_all only [ne_eq]
          cases a_1 with
          | inl h => simp_all only
          | inr h_1 => exact le_of_lt h_1
        · intro a_1
          simp_all only [ne_eq, and_true]
          exact LT.lt.gt_or_lt hab x
      by_contra h
      have hIioOpen : IsOpen (Iio b) := isOpen_Iio
      have hIicOpen : IsOpen (Iic b) := by
        rw [← hIic]
        exact IsOpen.union h hIioOpen
      have hcomplOpen : IsOpen (Iic b)ᶜ := by
        simp only [compl_Iic]
        exact isOpen_Ioi
      obtain hPrecon := isPreconnected_univ (Iic b) (Iic b)ᶜ hIicOpen hcomplOpen
      simp_all only [ne_eq, compl_Iic, Iic_union_Ioi, subset_refl, univ_inter, nonempty_Iic, nonempty_Ioi,
        forall_const]
      rcases hPrecon with ⟨x, hx⟩
      simp only [mem_inter_iff, mem_Iic, mem_Ioi] at hx
      linarith
    simp_all only [ne_eq]
    apply Aesop.BuiltinRules.not_intro
    intro a_1
    subst a_1
    exact hnIoc hAOpen
  · have hEmp : (Ioc a b) = ∅ := by
      exact Ioc_eq_empty hab
    exact Ne.symm (Lean.Grind.ne_of_ne_of_eq_left hEmp (id (Ne.symm hANonempty)))

/- A nonempty set in ℝ cannot be of the form [a, b). -/
lemma Ico_not_open (A : Set ℝ) (a b : ℝ) (hAOpen : IsOpen A) (hANonempty : A ≠ ∅) : A ≠ Ico a b := by
  by_cases hab : a < b
  · have hnIco : ¬ IsOpen (Ico a b) := by
      have hIci : (Ico a b) ∪ (Ioi a) = Ici a := by
        ext x
        simp only [mem_union, mem_Ico, mem_Ioi, mem_Ici]
        constructor
        · intro a_1
          simp_all only [ne_eq]
          cases a_1 with
          | inl h => simp_all only
          | inr h_1 => exact le_of_lt h_1
        · intro a_1
          simp_all only [ne_eq, true_and]
          exact Or.symm (LT.lt.gt_or_lt hab x)
      by_contra h
      have hIoiOpen : IsOpen (Ioi a) := isOpen_Ioi
      have hIciOpen : IsOpen (Ici a) := by
        rw [← hIci]
        exact IsOpen.union h hIoiOpen
      have hcomplOpen : IsOpen (Ici a)ᶜ := by
        simp only [compl_Ici]
        exact isOpen_Iio
      obtain hPrecon := isPreconnected_univ (Ici a) (Ici a)ᶜ hIciOpen hcomplOpen
      simp_all only [ne_eq, compl_Ici, univ_subset_iff, univ_inter, nonempty_Ici, nonempty_Iio,
        forall_const]
      have hUniv : Ici a ∪ Iio a = univ := by
        have hUniv' : Ici a ∪ Iio a = Iio a ∪ Ici a := by exact union_comm (Ici a) (Iio a)
        rw [hUniv']
        exact Iio_union_Ici
      apply hPrecon at hUniv
      rcases hUniv with ⟨x, hx⟩
      simp only [mem_inter_iff, mem_Ici, mem_Iio] at hx
      linarith
    simp_all only [ne_eq]
    apply Aesop.BuiltinRules.not_intro
    intro a_1
    subst a_1
    exact hnIco hAOpen
  · have hEmp : (Ico a b) = ∅ := by
      exact Ico_eq_empty hab
    exact Ne.symm (Lean.Grind.ne_of_ne_of_eq_left hEmp (id (Ne.symm hANonempty)))

/- A nonempty set in ℝ cannot be of the form [a, b]. -/
lemma Icc_not_open (A : Set ℝ) (a b : ℝ) (hAOpen : IsOpen A) (hANonempty : A ≠ ∅) : A ≠ Icc a b := by
  by_cases hab : a ≤ b
  · have hnIcc : ¬ IsOpen (Icc a b) := by
      by_contra hC
      have hIccClosed : IsClosed (Icc a b) := isClosed_Icc
      have hcomplOpen : IsOpen (Icc a b)ᶜ := IsClosed.isOpen_compl
      obtain hPrecon := isPreconnected_univ (Icc a b) (Icc a b)ᶜ hC hcomplOpen
        (by simp only [union_compl_self, subset_refl])
        (by simp only [univ_inter, nonempty_Icc]
            linarith)
        (by simp only [univ_inter]
            have hy : ((b + 1) ∈ (Icc a b)ᶜ)
            simp only [mem_compl_iff, mem_Icc, add_le_iff_nonpos_right, not_and, not_le,
              zero_lt_one, implies_true]
            exact nonempty_of_mem hy)
      -- have h1 : univ ⊆ Icc a b ∪ (Icc a b)ᶜ := by simp only [union_compl_self, subset_refl]
      -- have h2 : (univ ∩ Icc a b).Nonempty := by simp only [univ_inter, nonempty_Icc] ; exact le_of_lt hab
      -- have h3 : (univ ∩ (Icc a b)ᶜ).Nonempty := by
      --   simp only [univ_inter]
      --   have hb : b + 1 ∈ (Icc a b)ᶜ := by
      --     simp only [mem_compl_iff, mem_Icc, add_le_iff_nonpos_right, not_and, not_le, zero_lt_one,
      --       implies_true]
      --   exact nonempty_of_mem hb
      -- apply hPrecon at h1
      -- apply h1 at h2
      -- apply h2 at h3
      -- simp only [inter_compl_self, inter_empty, Set.not_nonempty_empty] at h3
      simp only [inter_compl_self, inter_empty, Set.not_nonempty_empty] at hPrecon
    simp_all only [ne_eq]
    apply Aesop.BuiltinRules.not_intro
    intro a_1
    subst a_1
    simp_all only [not_true_eq_false]
  · have hEmp : (Icc a b) = ∅ := by
      exact Icc_eq_empty hab
    exact Ne.symm (Lean.Grind.ne_of_ne_of_eq_left hEmp (id (Ne.symm hANonempty)))

/- An open, connected set in ℝ must be one of the following forms: ℝ, ∅, (a, b), (-∞, a), (b, ∞). -/
lemma real_class (A : Set ℝ) (hAOpen : IsOpen A) (hACon : IsConnected A) :
    (∃ a b, A = Ioo a b) ∨ (∃ a, A = Iio a) ∨ (∃ b, A = Ioi b) ∨ (A = univ) := by
  have hPrecon : IsPreconnected A := by exact IsConnected.isPreconnected hACon
  obtain hRC := IsPreconnected.mem_intervals hPrecon
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hRC

  have hANonempty : A ≠ ∅ := by
    have hANonempty' : A.Nonempty := by exact hACon.1
    exact nonempty_iff_ne_empty.mp hANonempty'

  have hAnotIcc : A ≠ Icc (sInf A) (sSup A) := Icc_not_open A (sInf A) (sSup A) hAOpen hANonempty
  have hAnotIco : A ≠ Ico (sInf A) (sSup A) := Ico_not_open A (sInf A) (sSup A) hAOpen hANonempty
  have hAnotIoc : A ≠ Ioc (sInf A) (sSup A) := Ioc_not_open A (sInf A) (sSup A) hAOpen hANonempty
  have hAnotIci : A ≠ Ici (sInf A) := Ici_not_open A (sInf A) hAOpen
  have hAnotIic : A ≠ Iic (sSup A) := Iic_not_open A (sSup A) hAOpen
  simp only [hAnotIcc, hAnotIco, hAnotIoc, hAnotIci, hAnotIic, hANonempty, false_or, or_false] at hRC
  rcases hRC with (h1 | h2 | h3 | h4 )
  · left
    use sInf A, sSup A
  · right ; right ; left
    use sInf A
  · right ; left
    use sSup A
  · right ; right ; right
    exact h4
