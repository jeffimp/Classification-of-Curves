/-
Formalization of the Classification of Curves
Author: Jeff Lee
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
-- lemma Ici_not_open (A : Set ℝ) (a : ℝ) (hAOpen : IsOpen A) : (A ≠ Ici a) := by
--   by_contra hEq
--   rw [hEq] at hAOpen
--   have hIClosed : IsClosed (Ici a) := isClosed_Ici
--   have hComplOpen : IsOpen (Ici a)ᶜ := IsClosed.isOpen_compl
--   have hCon : IsPreconnected (univ : Set ℝ) := isPreconnected_univ
--   obtain hCon_1 := hCon (Ici a) ((Ici a)ᶜ) hAOpen hComplOpen
--   have hCover : Ici a ∪ (Ici a)ᶜ = univ := union_compl_self (Ici a)
--   rw [hCover] at hCon_1
--   simp only [subset_refl, univ_inter, nonempty_Ici, compl_Ici, nonempty_Iio, forall_const] at hCon_1
--   have hEmp (b : ℝ) : (Ici b ∩ Iio b) = ∅ := by
--     have hCap : Ici b ∩ Iio b = Ico b b := rfl
--     rw [hCap]
--     exact Ico_self b
--   rw [hEmp] at hCon_1
--   apply Set.not_nonempty_empty
--   exact hCon_1
