import Mathlib

set_option linter.unusedSectionVars false

open Matrix Polynomial BigOperators Finset

variable {R : Type*} [CommRing R] [Nontrivial R] [NoZeroDivisors R]
variable {n : Type*} [Fintype n] [DecidableEq n] [Nontrivial n]

lemma charMatrix_diag_degree (A : Matrix n n R) (i : n) : (charmatrix A i i).natDegree = 1 := by
  rw [charmatrix_apply_eq]
  rw [sub_eq_add_neg]
  rw [natDegree_add_eq_left_of_natDegree_lt]
  · exact natDegree_X
  · calc ((-C (A i i))).natDegree
        = (C (A i i)).natDegree := natDegree_neg _
        _ = 0 := natDegree_C _
        _ < X.natDegree := by rw [natDegree_X]; omega

lemma charMatrix_offdiag_degree (A : Matrix n n R) (i j : n) (hij : i ≠ j) : (charmatrix A i j).natDegree = 0 := by
  rw [charmatrix_apply_ne _ _ _ hij]
  calc (-C (A i j)).natDegree
      = (C (A i j)).natDegree := natDegree_neg _
      _ = 0 := natDegree_C _
