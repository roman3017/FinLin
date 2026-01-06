import Mathlib

set_option maxHeartbeats 0

/-
# Linear Representation of Functions

This file contains the Lean4 formalization of the theorem that every function
f: ℤ/nℤ → ℤ/nℤ has a linear representation.

The main result is that for any function f: ℤ/nℤ → ℤ/nℤ, there exists:
- A modulus m > 0
- A constant a ∈ ℤ/mℤ
- An injective map j: ℤ/nℤ → ℤ/mℤ

Such that j(f(i)) = a · j(i) for all i ∈ ℤ/nℤ.

The proof uses:
1. The adjacency matrix representation of the function f
2. Properties of the adjugate matrix adj(xI - A)
3. The fact that entries of the adjugate are polynomials in x
4. For sufficiently large x, these polynomial entries become strictly increasing

## Main Definitions

- `func_matrix`: The adjacency matrix of a function
- `has_linear_representation`: Definition of linear representation
- `linear_representation`: Main theorem

## Key Lemmas

- `func_matrix_eq`: Matrix-vector product gives function value
- `adj_eq`: Adjugate identity relating y_{f(i)} to y_i
- `adj_poly`: Polynomial structure of adjugate entries
- `adj_poly_strict_increasing`: Strict ordering for large x

## References

This formalization is based on the paper arXiv:2510.20167
-/

open Matrix Polynomial BigOperators Finset

/-
Adjacency Matrix of a Function
Let f: ℤ/nℤ → ℤ/nℤ be any function. The function f is represented by an
n × n adjacency matrix A=A_f, where the entry A_{ij} = δ_{f(i),j}.
-/
def func_matrix {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if f (i.val : ZMod n) = (j.val : ZMod n) then 1 else 0

/-
Matrix-vector product gives the function value
Let f: ℤ/nℤ → ℤ/nℤ be any function and A=A_f be the adjacency matrix of the function f.
Then (A⋅y)_i = y_{f(i)} for all i∈ℤ/nℤ and y∈ℤ^n.
-/
lemma func_matrix_eq {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (y : Fin n → ℤ) (i : Fin n) :
    (func_matrix f *ᵥ y) i = y ⟨ZMod.val (f (i.val : ZMod n)), ZMod.val_lt _⟩ := by
  -- mulVec is defined as (M *ᵥ v) i = ∑ j, M i j * v j
  simp only [Matrix.mulVec, func_matrix]
  -- Expand the dot product: (fun j => if ...) ⬝ᵥ y
  rw [show (fun j => if f (i.val : ZMod n) = (j.val : ZMod n) then (1 : ℤ) else 0) ⬝ᵥ y =
          ∑ j : Fin n, (if f (i.val : ZMod n) = (j.val : ZMod n) then (1 : ℤ) else 0) * y j
      from rfl]
  -- The sum has only one non-zero term: when j.val = f(i).val
  let fi : Fin n := ⟨ZMod.val (f (i.val : ZMod n)), ZMod.val_lt _⟩
  rw [Finset.sum_eq_single fi]
  · simp [fi]
  · intro j _ hj
    simp only [ite_mul, one_mul, zero_mul]
    split_ifs with h
    · -- If f(i) = j (as ZMod n), then j = fi, contradicting hj
      exfalso
      apply hj
      -- h : f(i.val) = j.val as ZMod n
      -- We need to show j = fi
      have : j = fi := by
        simp only [fi]
        ext
        -- h says f(i) = j as ZMod n, so their .val fields are equal
        simp
        exact (ZMod.val_cast_of_lt (Fin.is_lt j)).symm ▸ (congr_arg ZMod.val h).symm
      exact this
    · rfl
  · intro hfi
    exfalso
    exact hfi (Finset.mem_univ fi)

/-
Adjugate identity for the characteristic matrix
Let f: ℤ/nℤ → ℤ/nℤ be any function and A=A_f be the adjacency matrix of the function f.
Let v∈ℤ^n and y = adj(xI - A)⋅v.
Then y_{f(i)} = x⋅y_i - m⋅v_i where m = det(xI - A).

Note: We work with the characteristic matrix as a polynomial matrix evaluated at x,
since Mathlib's charmatrix uses polynomial ring R[X].
-/
lemma adj_eq {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (x : ℤ) (v : Fin n → ℤ) :
    ∀ i : Fin n,
    let A := func_matrix f
    -- The characteristic matrix is xI - A in our formulation
    -- Mathlib's charmatrix is X*I - M, so we adapt accordingly
    let M := x • (1 : Matrix (Fin n) (Fin n) ℤ) - A
    let y := M.adjugate *ᵥ v
    let m := M.det
    y ⟨ZMod.val (f (i.val : ZMod n)), ZMod.val_lt _⟩ = x * y i - m * v i := by
  intro i
  -- Let-bind the matrix and its properties
  let A := func_matrix f
  let M := x • (1 : Matrix (Fin n) (Fin n) ℤ) - A
  let y := Matrix.adjugate M *ᵥ v
  let m := Matrix.det M
  -- Use the fundamental adjugate identity: M * adjugate(M) = det(M) • I
  have adj_identity : M * Matrix.adjugate M = m • (1 : Matrix (Fin n) (Fin n) ℤ) :=
    Matrix.mul_adjugate M
  -- Apply this to the vector v: M * (adjugate(M) * v) = det(M) • v
  have h_vec : M *ᵥ y = m • v := by
    calc M *ᵥ y
        = M *ᵥ (Matrix.adjugate M *ᵥ v) := rfl
      _ = (M * Matrix.adjugate M) *ᵥ v := by rw [Matrix.mulVec_mulVec]
      _ = (m • (1 : Matrix (Fin n) (Fin n) ℤ)) *ᵥ v := by rw [adj_identity]
      _ = m • v := by rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  -- Extract the i-th component
  have h_i : (M *ᵥ y) i = m * v i := by
    rw [h_vec]
    simp [Pi.smul_apply]
  -- Expand M *ᵥ y using M = xI - A
  have h_expand : (M *ᵥ y) i = x * y i - (func_matrix f *ᵥ y) i := by
    show ((x • (1 : Matrix (Fin n) (Fin n) ℤ) - func_matrix f) *ᵥ Matrix.adjugate M *ᵥ v) i =
         x * (Matrix.adjugate M *ᵥ v) i - (func_matrix f *ᵥ Matrix.adjugate M *ᵥ v) i
    simp only [Matrix.sub_mulVec, Pi.sub_apply, Matrix.smul_mulVec, Matrix.one_mulVec,
               Pi.smul_apply, smul_eq_mul]
  -- Now use func_matrix_eq: (A *ᵥ y) i = y[f(i)]
  have h_Ay : (func_matrix f *ᵥ y) i = y ⟨ZMod.val (f (i.val : ZMod n)), ZMod.val_lt _⟩ :=
    func_matrix_eq f y i
  -- Combine everything
  rw [h_expand, h_Ay] at h_i
  linarith

lemma det_degree_le_sum_degrees {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ[X]) :
    (M.det).natDegree ≤ ∑ i : Fin n, ∑ j : Fin n, (M j i).natDegree := by
  -- Local helper: a single element is ≤ the sum of all elements
  have single_element_sum_le : ∀ (a : Fin n → ℕ) (ha: ∀ j, 0 ≤ a j) (i : Fin n), a i ≤ ∑ j, a j := by
    intros a ha i
    exact Finset.single_le_sum (fun j _ => ha j) (Finset.mem_univ i)

  calc (M.det).natDegree
      = (∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i : Fin n, M (σ i) i).natDegree := by
        rw [Matrix.det_apply]
      _ ≤ (univ : Finset (Equiv.Perm (Fin n))).sup
            (fun σ => (Equiv.Perm.sign σ • ∏ i : Fin n, M (σ i) i).natDegree) := by
        apply natDegree_sum_le
      _ ≤ (univ : Finset (Equiv.Perm (Fin n))).sup
            (fun σ => (∏ i : Fin n, M (σ i) i).natDegree) := by
        gcongr with σ
        exact natDegree_smul_le _ _
      _ ≤ (univ : Finset (Equiv.Perm (Fin n))).sup
            (fun σ => ∑ i : Fin n, (M (σ i) i).natDegree) := by
        gcongr with σ
        exact natDegree_prod_le univ (fun i => M (σ i) i)
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, (M j i).natDegree := by
        apply Finset.sup_le
        intro σ _
        apply Finset.sum_le_sum
        intro i _
        -- (M (σ i) i).natDegree ≤ ∑ j, (M j i).natDegree
        exact single_element_sum_le (fun j => (M j i).natDegree) (fun j => Nat.zero_le _) (σ i)

lemma charmatrix_det_eq_charpoly {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) :
    (charmatrix M).det = M.charpoly := by
  rfl

lemma charmatrix_det_monic {n : ℕ} [Nontrivial (Fin n)] (M : Matrix (Fin n) (Fin n) ℤ) :
    (charmatrix M).det.Monic := by
  rw [charmatrix_det_eq_charpoly]
  exact Matrix.charpoly_monic M

lemma charmatrix_det_natDegree {n : ℕ} [Nontrivial (Fin n)] (M : Matrix (Fin n) (Fin n) ℤ) :
    (charmatrix M).det.natDegree = Fintype.card (Fin n) := by
  rw [charmatrix_det_eq_charpoly]
  exact Matrix.charpoly_natDegree_eq_dim M

lemma adj_offdiag_sum_degrees_bound {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℤ) :
    ∀ i j : Fin n,
    (i ≠ j → ((charmatrix A).adjugate i j).natDegree ≤ n - 2) := by
  intro i j hne
  have h_n_ge_2 : n ≥ 2 := by
    by_contra h
    push_neg at h
    interval_cases n
    · exact (NeZero.ne 0) rfl
    · have : Subsingleton (Fin 1) := inferInstance
      exact hne (Subsingleton.elim i j)
  rw [adjugate_apply]
  -- Strategy: expand det by row j, which has only one non-zero entry at column i
  -- This gives: det = (Pi.single i 1)[j] * cofactor, where cofactor excludes row j and column i
  -- The cofactor matrix has diagonal degrees: 0 at j (row deleted), 0 at i (column deleted),
  -- and 1 at all other n-2 positions, giving total degree ≤ n-2

  have h_expand_by_row : ((charmatrix A).updateRow j (Pi.single i 1)).det.natDegree ≤ n - 2 := by
    -- Mathematical argument (cofactor expansion):
    -- 1. Row j of the updated matrix is Pi.single i 1 = [0,...,0,1,0,...,0] with 1 at position i
    -- 2. Expanding det by row j: det = ∑_k (-1)^(j+k) * M[j,k] * minor(j,k)
    -- 3. Since M[j,k] = 0 for all k ≠ i, only the k=i term survives
    -- 4. det = (-1)^(j+i) * 1 * minor(j,i) where minor(j,i) is the (n-1)×(n-1) determinant
    --    with row j and column i deleted
    -- 5. The minor matrix has:
    --    - Diagonal entries from charmatrix, except positions j and i are removed
    --    - So (n-2) diagonal entries of degree 1, rest are degree 0
    -- 6. By det_degree_le_sum_degrees on the minor: deg(minor) ≤ n-2
    -- 7. Therefore: deg(det) = deg(minor) ≤ n-2
    --
    -- To formalize this, we need either:
    -- - A version of det_succ_row that works with our index types
    -- - Or a direct minor/cofactor lemma
    -- - Or massage the types to use Fin (n-1).succ ≃ Fin n

    obtain ⟨n', hn'⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
    subst hn'
    rw [Matrix.det_succ_row _ j, Matrix.updateRow_self]
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same]
      simp only [mul_one]
      trans ((-1 : ℤ[X]) ^ (j + i : ℕ)).natDegree +
            (((charmatrix A).updateRow j (Pi.single i 1)).submatrix j.succAbove i.succAbove).det.natDegree
      · apply natDegree_mul_le
      trans 0 + (((charmatrix A).updateRow j (Pi.single i 1)).submatrix j.succAbove i.succAbove).det.natDegree
      · gcongr
        have : ((-1 : ℤ[X]) ^ (j + i : ℕ)) = (-1) ^ (j + i : ℕ) := by rfl
        rw [this, natDegree_pow]
        norm_num
      simp only [zero_add]
      have h_submatrix_bound : (((charmatrix A).updateRow j (Pi.single i 1)).submatrix j.succAbove i.succAbove).det.natDegree ≤ n' - 1 := by
        trans (∑ k, ∑ l, (((charmatrix A).updateRow j (Pi.single i 1)).submatrix j.succAbove i.succAbove l k).natDegree)
        · apply det_degree_le_sum_degrees
        have h_bound_sum : ∑ k, ∑ l, (((charmatrix A).updateRow j (Pi.single i 1)).submatrix j.succAbove i.succAbove l k).natDegree ≤ n' - 1 := by
          -- Key insight: count pairs (k,l) where j.succAbove k = i.succAbove l (diagonal in charmatrix)
          -- Note: submatrix l k accesses original matrix at row j.succAbove l, column i.succAbove k
          trans (∑ k : Fin n', ∑ l : Fin n', if j.succAbove l = i.succAbove k then 1 else 0)
          · apply Finset.sum_le_sum
            intro k _
            apply Finset.sum_le_sum
            intro l _
            simp only [Matrix.submatrix_apply]
            -- submatrix at (l,k) corresponds to original matrix at (j.succAbove l, i.succAbove k)
            have hrow_not_j : j.succAbove l ≠ j := Fin.succAbove_ne j l
            rw [Matrix.updateRow_apply, if_neg hrow_not_j]
            by_cases h_diag : j.succAbove l = i.succAbove k
            · -- Diagonal in charmatrix: degree = 1
              unfold charmatrix
              rw [h_diag]
              simp only [Matrix.diagonal_apply_eq, Matrix.sub_apply, Matrix.scalar_apply]
              calc (Polynomial.X - Polynomial.C (A (i.succAbove k) (i.succAbove k))).natDegree
                _ = 1 := Polynomial.natDegree_X_sub_C _
                _ ≤ 1 := le_refl _
            · -- Off-diagonal in charmatrix: degree = 0
              unfold charmatrix
              simp [Matrix.diagonal_apply_ne _ h_diag, Matrix.sub_apply, Matrix.scalar_apply]
          -- Now count: how many pairs (k,l) satisfy j.succAbove l = i.succAbove k?
          -- Answer: n' - 1 (one for each value in the range intersection)
          have h_count_pairs : (∑ k : Fin n', ∑ l : Fin n', if j.succAbove l = i.succAbove k then 1 else 0 : ℕ) = n' - 1 := by
            -- The pairs where they're equal correspond to values in both ranges
            -- Range of j.succAbove: Fin(n'+1) \ {j}
            -- Range of i.succAbove: Fin(n'+1) \ {i}
            -- Intersection: Fin(n'+1) \ {i,j}, which has size n'+1-2 = n'-1
            -- For each value v in the intersection, there's exactly one l with j.succAbove l = v
            -- and exactly one k with i.succAbove k = v, giving one pair (k,l).
            -- Strategy: collapse the inner sum - for each k, at most one l matches
            calc (∑ k : Fin n', ∑ l : Fin n', if j.succAbove l = i.succAbove k then 1 else 0)
              _ = ∑ k : Fin n', (Finset.filter (fun l => j.succAbove l = i.succAbove k) Finset.univ).card := by
                congr 1
                ext k
                trans (∑ l ∈ Finset.filter (fun l => j.succAbove l = i.succAbove k) Finset.univ, (1 : ℕ))
                · rw [← Finset.sum_filter]
                · rw [Finset.sum_const, Nat.smul_one_eq_cast, Nat.cast_id]
              _ = ∑ k : Fin n', if i.succAbove k ≠ j then 1 else 0 := by
                congr 1
                ext k
                by_cases h : i.succAbove k = j
                · rw [if_neg (not_not.mpr h)]
                  have : Finset.filter (fun l => j.succAbove l = i.succAbove k) Finset.univ = ∅ := by
                    ext l
                    simp [h, Fin.succAbove_ne]
                  rw [this, Finset.card_empty]
                · rw [if_pos h]
                  have hex : ∃ l, j.succAbove l = i.succAbove k := by
                    by_cases hlt : i.succAbove k < j
                    · have h_ne_last : i.succAbove k ≠ Fin.last n' := by
                        intro heq
                        rw [heq] at hlt
                        simp [Fin.lt_def, Fin.val_last] at hlt
                        omega
                      use (i.succAbove k).castPred h_ne_last
                      rw [Fin.succAbove_of_castSucc_lt]
                      · simp [Fin.castSucc_castPred]
                      · simp [Fin.castSucc_castPred]
                        exact hlt
                    · push_neg at hlt
                      have h_ne_zero : i.succAbove k ≠ 0 := by
                        intro heq
                        rw [heq] at h hlt
                        simp at hlt
                        omega
                      use (i.succAbove k).pred h_ne_zero
                      rw [Fin.succAbove_of_le_castSucc]
                      · simp [Fin.succ_pred]
                      · have : i.succAbove k = ((i.succAbove k).pred h_ne_zero).succ := by simp [Fin.succ_pred]
                        rw [this] at hlt
                        simp [Fin.le_castSucc_iff]
                        omega
                  obtain ⟨l, hl⟩ := hex
                  rw [Finset.card_eq_one]
                  use l
                  ext l'
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
                  constructor
                  · intro heq
                    have : j.succAbove l' = j.succAbove l := by rw [heq, hl]
                    exact Fin.succAbove_right_inj.mp this
                  · intro; subst l'; exact hl
              _ = Finset.card (Finset.filter (fun k => i.succAbove k ≠ j) Finset.univ) := by
                trans (∑ k ∈ Finset.filter (fun k => i.succAbove k ≠ j) Finset.univ, (1 : ℕ))
                · rw [← Finset.sum_filter]
                · rw [Finset.sum_const, Nat.smul_one_eq_cast, Nat.cast_id]
              _ = n' - 1 := by
                -- Range of i.succAbove is Fin(n'+1) \ {i}
                -- Since i ≠ j, j is in this range, so there's exactly one k with i.succAbove k = j
                -- Therefore, {k | i.succAbove k ≠ j} has cardinality n' - 1
                have : Finset.filter (fun k => i.succAbove k ≠ j) Finset.univ =
                       Finset.univ \ Finset.filter (fun k => i.succAbove k = j) Finset.univ := by
                  ext k
                  simp
                rw [this, Finset.card_sdiff]
                · simp [Finset.card_univ, Fintype.card_fin]
                  -- The key is that succAbove i is a bijection from Fin n' to Fin(n'+1) \ {i}
                  -- Since j ≠ i, there exists exactly one k such that i.succAbove k = j
                  have hcard : (Finset.filter (fun k => i.succAbove k = j) Finset.univ).card = 1 := by
                    rw [Finset.card_eq_one]
                    -- First, show existence: j ≠ i, so j is in range of i.succAbove
                    have hex : ∃ k, i.succAbove k = j := by
                      by_cases hlt : j < i
                      · -- j < i, so we can use castPred
                        have h_ne_last : j ≠ Fin.last n' := by
                          intro heq
                          rw [heq] at hlt
                          have : i.val ≤ n' := Fin.is_le i
                          have : (Fin.last n').val = n' := Fin.val_last n'
                          omega
                        use j.castPred h_ne_last
                        rw [Fin.succAbove_of_castSucc_lt]
                        · simp [Fin.castSucc_castPred]
                        · simp [Fin.castSucc_castPred]
                          exact hlt
                      · -- j ≥ i and j ≠ i, so j > i
                        push_neg at hlt
                        have h_ne_i : j ≠ i := hne.symm
                        have h_gt : i < j := by
                          cases Fin.lt_or_eq_of_le hlt with
                          | inl h => exact h
                          | inr h => exact absurd h.symm h_ne_i
                        have h_ne_zero : j ≠ 0 := by
                          intro heq
                          rw [heq] at h_gt
                          exact Nat.not_lt_zero i.val h_gt
                        use j.pred h_ne_zero
                        rw [Fin.succAbove_of_le_castSucc]
                        · simp [Fin.succ_pred]
                        · have : j = (j.pred h_ne_zero).succ := by simp [Fin.succ_pred]
                          rw [this] at hlt
                          simp [Fin.le_castSucc_iff]
                          omega
                    obtain ⟨k, hk⟩ := hex
                    use k
                    ext k'
                    simp
                    constructor
                    · intro hk'
                      -- succAbove is injective
                      exact Fin.succAbove_right_inj.mp (hk'.trans hk.symm)
                    · intro; subst k'; exact hk
                  rw [hcard]
          rw [h_count_pairs]
        exact h_bound_sum
      calc (((charmatrix A).updateRow j (Pi.single i 1)).submatrix j.succAbove i.succAbove).det.natDegree
        _ ≤ n' - 1 := h_submatrix_bound
        _ = n'.succ - 2 := by omega
    · intro k _ hk
      simp only [mul_assoc, mul_eq_zero]
      right
      left
      simp [hk]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  exact h_expand_by_row


/-
Polynomial entries of the adjugate matrix
Let M = M(x) = adj(xI - A) be the adjugate of the characteristic matrix xI - A.
Then M_{ij} = p_{ij}(x) is a polynomial in x for all i,j∈ℤ/nℤ such that
p_{ii}(x) is monic of degree n-1 for all i∈ℤ/nℤ and
p_{ij}(x) has degree at most n-2 for all i≠j∈ℤ/nℤ.

We use Mathlib's charmatrix (which is X*I - M as a polynomial matrix) to formalize this.
The adjugate entries are naturally polynomials via the charmatrix construction.

Proof structure:
1. Four helper lemmas encapsulate the main technical steps
2. Main proof splits into diagonal (i = j) and off-diagonal (i ≠ j) cases
3. Diagonal case: shows adjugate entry is monic of degree n-1 via characteristic polynomial
4. Off-diagonal case: uses degree bound from cofactor expansion
-/
lemma adj_poly {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℤ) :
    ∀ i j : Fin n,
    let p := (charmatrix A).adjugate i j
    (i = j → p.Monic ∧ p.natDegree = n - 1) ∧
    (i ≠ j → p.natDegree ≤ n - 2) := by
  intro i j
  have h_update_row : ∀ (M : Matrix (Fin n) (Fin n) (Polynomial ℤ)) (k : Fin n),
      (M.updateRow k (Pi.single k 1)).det =
      (M.submatrix (fun (i : {x // x ≠ k}) => i.val) (fun (j : {x // x ≠ k}) => j.val)).det := by
    intro M k
    rw [← Matrix.adjugate_apply M k k]
    -- Need to show: adjugate M k k = det of submatrix with row k and column k removed
    -- We'll use the fact that both index schemes give the same submatrix
    obtain ⟨n', hn'⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
    subst hn'
    -- Now we're working with Fin (n' + 1)
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    -- For diagonal entry k k, we have (-1)^(k+k) = (-1)^(2k) = 1
    have : ((-1 : ℤ[X]) ^ (k + k : ℕ)) = 1 := by
      rw [← two_mul]
      simp [pow_mul]
    rw [this, one_mul]
    let inv_fun : {x // x ≠ k} → Fin n' := fun ⟨x, hx⟩ =>
      if h : x < k then x.castPred (Fin.ne_last_of_lt h)
      else x.pred (by
        have : k ≤ x := Fin.not_lt.mp h
        cases Fin.lt_or_eq_of_le this with
        | inl h' => exact Fin.ne_zero_of_lt h'
        | inr h' => exact absurd h'.symm hx)
    have h_left_inv : ∀ i, inv_fun ⟨k.succAbove i, Fin.succAbove_ne k i⟩ = i := by
      intro i
      unfold inv_fun
      by_cases h : k.succAbove i < k
      · dsimp
        rw [dif_pos h]
        unfold Fin.succAbove at h
        split_ifs at h with hi
        · simp only [Fin.succAbove, hi, ite_true]
          exact Fin.castPred_castSucc
        · exfalso
          have h1 : k ≤ i.castSucc := Fin.not_lt.mp hi
          have h2 : k ≤ i.succ := le_trans h1 Fin.castSucc_lt_succ.le
          exact Fin.not_le.mpr h h2
      · dsimp
        rw [dif_neg h]
        unfold Fin.succAbove
        split_ifs with hi
        · exfalso
          have : i.castSucc < k := hi
          have : k.succAbove i < k := by simp [Fin.succAbove, hi]
          exact h this
        · exact Fin.pred_succ i
    have h_right_inv : ∀ x : {y // y ≠ k}, ⟨k.succAbove (inv_fun x), Fin.succAbove_ne k (inv_fun x)⟩ = x := by
      intro ⟨x, hx⟩
      simp only [Subtype.mk.injEq]
      unfold inv_fun
      by_cases h : x < k
      · dsimp
        rw [dif_pos h]
        exact Fin.succAbove_castPred_of_lt _ _ h
      · dsimp
        rw [dif_neg h]
        have hk : k < x := by
          cases Fin.lt_or_eq_of_le (Fin.not_lt.mp h) with
          | inl h => exact h
          | inr h => exact absurd h.symm hx
        exact Fin.succAbove_pred_of_lt _ _ hk
    let e : Fin n' ≃ {x // x ≠ k} := {
      toFun := fun i => ⟨k.succAbove i, Fin.succAbove_ne k i⟩
      invFun := inv_fun
      left_inv := h_left_inv
      right_inv := h_right_inv
    }
    have h_submatrix_eq : M.submatrix k.succAbove k.succAbove =
        (M.submatrix (fun (i : {x // x ≠ k}) => i.val) (fun (j : {x // x ≠ k}) => j.val)).reindex e.symm e.symm := by
      ext i j
      simp [Matrix.submatrix_apply, Matrix.reindex_apply, e]
    rw [h_submatrix_eq, Matrix.det_reindex_self]

  have h_card_complement : ∀ (k : Fin n), Fintype.card {x : Fin n // x ≠ k} = n - 1 := by
    intro k
    calc Fintype.card {x : Fin n // x ≠ k}
      _ = Fintype.card {x : Fin n // ¬(x = k)} := by simp [ne_eq]
      _ = Fintype.card (Fin n) - Fintype.card {x : Fin n // x = k} :=
          Fintype.card_subtype_compl (fun x => x = k)
      _ = n - Fintype.card {x : Fin n // x = k} := by
          congr 1
          convert Fintype.card_fin n
      _ = n - 1 := by rw [Fintype.card_subtype_eq k]

  have h_charmatrix_submatrix : ∀ (M : Matrix (Fin n) (Fin n) ℤ) (k : Fin n),
      (charmatrix M).submatrix (fun (i : {x // x ≠ k}) => i.val) (fun (j : {x // x ≠ k}) => j.val) =
      charmatrix (M.submatrix (fun (i : {x // x ≠ k}) => i.val) (fun (j : {x // x ≠ k}) => j.val)) := by
    intro M k
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.charmatrix_apply, Matrix.diagonal_apply]
    by_cases h : i = j
    · simp [h]
    · have hval : i.val ≠ j.val := by
        intro heq
        apply h
        exact Subtype.ext heq
      simp [h, hval]

  -- Off-diagonal case is handled by adj_offdiag_sum_degrees_bound
  -- Which proves the bound via counting diagonal entries in the submatrix

  by_cases hij : i = j
  · -- Case: i = j (Diagonal case: monic of degree n-1)
    rw [hij]
    have h1 (m : ℕ) : Fintype.card (Fin m) = m := by rw [Fintype.card_fin]

    by_cases hn1 : n = 1
    · -- Special case: n = 1
      constructor
      · intro _
        constructor
        · -- Monic
          unfold Polynomial.Monic
          rw [adjugate_apply]
          subst hn1
          have : j = 0 := Fin.fin_one_eq_zero j
          subst this
          simp [Pi.single_eq_same, Matrix.updateRow_self]
        · -- Degree n-1 = 0
          rw [adjugate_apply]
          subst hn1
          have : j = 0 := Fin.fin_one_eq_zero j
          subst this
          simp [Pi.single_eq_same, Matrix.updateRow_self, Polynomial.natDegree_one]
      · intro h_ne
        exact absurd rfl h_ne

    -- General case: n > 1
    have hn : n > 1 := by
      omega
    haveI : Nontrivial (Fin n) := by
      rw [← h1 n] at hn
      rw [_root_.nontrivial_iff]
      use 0, 1
      simp
      exact Nat.ne_of_gt (Nat.lt_of_lt_of_eq hn (h1 n))

    constructor
    · intro _
      constructor
      · -- Monic: The diagonal entry of adjugate(charmatrix A) is the charpoly of a submatrix
        rw [adjugate_apply]
        have h_eq : ((charmatrix A).updateRow j (Pi.single j 1)).det =
                    ((charmatrix A).submatrix (fun (i : {x // x ≠ j}) => i.val)
                                              (fun (k : {x // x ≠ j}) => k.val)).det := by
          have := h_update_row (charmatrix A) j
          rw [<-hij] at this ⊢
          exact this
        rw [h_eq]
        have char_submat := h_charmatrix_submatrix A j
        rw [char_submat, ← Matrix.charpoly]
        exact charpoly_monic _

      · -- Degree n-1
        rw [adjugate_apply]
        have h_eq : ((charmatrix A).updateRow j (Pi.single j 1)).det =
                    ((charmatrix A).submatrix (fun (i : {x // x ≠ j}) => i.val)
                                              (fun (k : {x // x ≠ j}) => k.val)).det := by
          exact h_update_row (charmatrix A) j
        rw [h_eq]
        have char_submat := h_charmatrix_submatrix A j
        rw [char_submat, ← Matrix.charpoly]
        have card_eq := h_card_complement j
        rw [← card_eq]
        exact charpoly_natDegree_eq_dim (A.submatrix (fun (i : {x // x ≠ j}) => i.val)
                                                      (fun (k : {x // x ≠ j}) => k.val))
    · intro h_ne
      exact absurd rfl h_ne

  · -- Case: i ≠ j (Off-diagonal case: degree ≤ n-2)
    constructor
    · intro h_eq
      exact absurd h_eq hij
    · intro _
      -- Use adj_offdiag_sum_degrees_bound which proves the bound via
      -- counting diagonal entries in the submatrix after row/column deletion
      exact adj_offdiag_sum_degrees_bound A i j hij

def coeff_bound (poly : Polynomial ℤ) : ℤ :=
  poly.support.sum (fun i => |poly.coeff i|)

/-
Polynomial with positive leading coefficient is eventually positive
If p ∈ ℤ[x] has positive leading coefficient, then p(n) > 0 for all n greater than polynomial_bound p.
-/
lemma polynomial_positive (poly : Polynomial ℤ) (h : poly.leadingCoeff > 0) (n : ℤ) :
    n ≥ coeff_bound poly → n > 0 ∧ (poly.eval n) > 0 := by
  have poly_nonzero : poly ≠ 0 := by
    intro H; simp [H] at h

  let d := poly.natDegree
  let a := poly.leadingCoeff

  intros hn

  -- First, establish n ≥ coeff_bound poly ≥ a ≥ 1 > 0
  have a_ge_one : a ≥ 1 := by omega
  have coeff_bound_ge_a : coeff_bound poly ≥ a := by
    simp [coeff_bound, a]
    have leading_nonzero : poly.coeff poly.natDegree ≠ 0 := by
      intro h_eq
      have : poly.leadingCoeff = 0 := by simp [Polynomial.leadingCoeff, h_eq]
      omega
    have leading_in_support : poly.natDegree ∈ poly.support := by
      rw [Polynomial.mem_support_iff]; exact leading_nonzero
    calc ∑ i ∈ poly.support, |poly.coeff i|
        ≥ |poly.coeff poly.natDegree| := by
          apply Finset.single_le_sum (f := fun i => |poly.coeff i|)
          · intro i _; apply abs_nonneg
          · exact leading_in_support
      _ = poly.leadingCoeff := abs_of_pos h
  have hn_pos : n > 0 := by
    calc n ≥ coeff_bound poly := hn
      _ ≥ a := coeff_bound_ge_a
      _ ≥ 1 := a_ge_one
      _ > 0 := by norm_num

  constructor
  · exact hn_pos

  -- Case d = 0
  by_cases hd : d = 0
  ·
    have : poly.eval n = a := by
      have hp : poly = C (poly.coeff 0) := eq_C_of_natDegree_eq_zero hd
      rw [hp, eval_C]
      have h_leading : poly.leadingCoeff = poly.coeff poly.natDegree := rfl
      rw [show poly.natDegree = 0 from hd] at h_leading
      rw [← h_leading]
    rw [this]
    exact h

  -- Case d ≥ 1
  have d_pos : 0 < d := Nat.pos_of_ne_zero hd
  have n_ge_one : n ≥ 1 := by omega

  -- Define B = coeff_bound poly - a (the sum of absolute values of non-leading coefficients)
  let B : ℤ := coeff_bound poly - a
  -- Define r = poly(n) - a·n^d (the remainder after subtracting the leading term)
  let r : ℤ := poly.eval n - a * n^d

  have B_nonneg : B ≥ 0 := by
    simp only [B]
    omega

  -- Split poly.eval n = a·n^d + r(n)
  have poly_split : poly.eval n = a * n^d + r := by
    simp only [r]
    ring

  -- Key lemma: the remainder bound |r(n)| ≤ B·n^{d-1}
  have r_bound : |r| ≤ B * n^(d-1) := by
    -- For n ≥ 1, |∑_{i<d} coeff_i·n^i| ≤ (∑_{i<d} |coeff_i|)·n^{d-1} = B·n^{d-1}
    calc |r|
    _ = |poly.eval n - a * n^d| := by simp only [r]
    _ = |a * n^d + ∑ i ∈ range d, poly.coeff i * n^i - a * n^d| := by
      rw [eval_eq_sum_range]
      congr 1
      rw [sum_range_succ]
      simp only [d, a]
      have : poly.leadingCoeff = poly.coeff poly.natDegree := rfl
      rw [this]
      ring
    _ = |∑ i ∈ range d, poly.coeff i * n^i| := by
      congr 1
      ring
    _ ≤ ∑ i ∈ range d, |poly.coeff i * n^i| := by exact abs_sum_le_sum_abs (fun i => poly.coeff i * n ^ i) (range d)
    _ ≤ ∑ i ∈ range d, |poly.coeff i| * n^(d-1) := by
      refine sum_le_sum ?_
      intro i hi
      rw [mem_range] at hi
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have hi_le : (i : ℤ) ≤ d - 1 := by omega
      have n_abs : |n| = n := abs_of_pos hn_pos
      rw [abs_pow, n_abs]
      by_cases h_i : i ≤ d - 1
      · have : n ^ i ≤ n ^ (d - 1) := by
          exact pow_le_pow_right₀ hn_pos h_i
        simp at this
        exact this
      · omega
    _ = (∑ i ∈ range d, |poly.coeff i|) * n^(d-1) := by
      rw [← sum_mul]
    _ = B * n^(d-1) := by
      congr 1
      simp only [B, coeff_bound]
      -- Show that ∑ i ∈ range d, |poly.coeff i| = ∑ i ∈ poly.support, |poly.coeff i| - |poly.coeff d|
      have sum_range_eq : ∑ i ∈ range d, |poly.coeff i| = ∑ i ∈ range d ∩ poly.support, |poly.coeff i| := by
        rw [← sum_inter_add_sum_diff (range d) poly.support (fun i => |poly.coeff i|)]
        simp
        apply sum_eq_zero
        intro i hi
        simp at hi
        simp [hi.2]
      rw [sum_range_eq]
      -- Show poly.support splits into d and elements < d
      have d_in_support : d ∈ poly.support := by
        rw [Polynomial.mem_support_iff]
        intro contra
        simp [Polynomial.leadingCoeff, d, contra] at h
      have filter_eq : poly.support.filter (· < d) = range d ∩ poly.support := by
        ext i
        simp [Polynomial.mem_support_iff]
        exact And.comm
      have support_split : ∑ i ∈ poly.support, |poly.coeff i| =
          |poly.coeff d| + ∑ i ∈ poly.support.filter (· < d), |poly.coeff i| := by
        conv_lhs => rw [← insert_erase d_in_support]
        rw [sum_insert (notMem_erase d poly.support)]
        congr 1
        have erase_eq_filter : poly.support.erase d = poly.support.filter (· < d) := by
          ext i
          simp [Polynomial.mem_support_iff]
          constructor
          · intro ⟨hi_supp, hi_ne_d⟩
            constructor
            · exact hi_ne_d
            · have : i ≤ d := Polynomial.le_natDegree_of_mem_supp _ (by rwa [Polynomial.mem_support_iff])
              omega
          · intro ⟨hi_supp, hi_lt⟩
            constructor
            · exact Nat.ne_of_lt hi_lt
            · exact hi_supp
        rw [erase_eq_filter]
      rw [support_split, filter_eq]
      simp [a]
      ring_nf
      have : poly.leadingCoeff = |poly.coeff d| := by
        simp [d]
        exact (abs_of_pos h).symm
      omega

  -- Main calculation following tex: p(n) = a·n^d + r(n) ≥ a·n^d - B·n^{d-1} = n^{d-1}(a·n - B) ≥ a·n - B
  have key_ineq : poly.eval n ≥ a * n - B := by
    calc poly.eval n
        = a * n^d + r := poly_split
      _ ≥ a * n^d - |r| := by
          have : r ≥ -|r| := neg_abs_le _
          omega
      _ ≥ a * n^d - B * n^(d-1) := by linarith [r_bound]
      _ = n^(d-1) * (a * n - B) := by
          have h_pow : n^d = n^(d-1) * n := by
            rw [← pow_succ]
            congr 1
            omega
          rw [h_pow]
          ring
      _ ≥ a * n - B := by
          -- For n ≥ 1, we have n^{d-1} ≥ 1
          have pow_ge_one : n^(d-1) ≥ 1 := by
            by_cases h_d1 : d = 1
            · simp [h_d1]
            · have d_minus_one_pos : d - 1 ≥ 1 := by omega
              calc n^(d-1) ≥ n^1 := by
                    have : (1 : ℤ) ≤ n := n_ge_one
                    have : (1 : ℕ) ≤ d - 1 := by omega
                    exact pow_le_pow_right₀ hn_pos this
                _ = n := by ring
                _ ≥ 1 := n_ge_one
          -- For n ≥ coeff_bound and coeff_bound ≥ a, we have n ≥ a ≥ 1
          -- So a*n ≥ a*coeff_bound = a*a + a*B ≥ a² + B (since a*B ≥ B when a ≥ 1)
          -- Thus a*n - B ≥ a² ≥ 1 > 0
          have h_nonneg : a * n - B ≥ 0 := by
            have : a * n ≥ a * coeff_bound poly := by
              apply mul_le_mul_of_nonneg_left hn
              omega
            calc a * n - B
                ≥ a * coeff_bound poly - B := by omega
              _ = a * (a + B) - B := by simp only [B]; ring
              _ = a * a + B * (a - 1) := by ring
              _ ≥ 0 := by
                  have h1 : a * a ≥ 0 := by apply mul_nonneg <;> omega
                  have h2 : B * (a - 1) ≥ 0 := by
                    have : a - 1 ≥ 0 := by omega
                    apply mul_nonneg B_nonneg this
                  omega
          calc n^(d-1) * (a * n - B)
              ≥ 1 * (a * n - B) := by
                apply mul_le_mul_of_nonneg_right pow_ge_one h_nonneg
            _ = a * n - B := by ring

  calc poly.eval n
      ≥ a * n - B := key_ineq
    _ ≥ a * coeff_bound poly - B := by
        have a_nonneg : 0 ≤ a := by omega
        have : a * n ≥ a * coeff_bound poly := by
          apply mul_le_mul_of_nonneg_left hn a_nonneg
        omega
    _ = a * (a + B) - B := by simp only [B]; ring
    _ = a * a + B * (a - 1) := by ring
    _ ≥ a := by
        have h1 : B * (a - 1) ≥ 0 := by
          have : a - 1 ≥ 0 := by omega
          have : B ≥ 0 := B_nonneg
          apply mul_nonneg <;> omega
        have h2 : a * a ≥ a := by
          calc a * a = a * 1 + a * (a - 1) := by ring
            _ ≥ a * 1 + 0 := by
                have : a * (a - 1) ≥ 0 := by
                  have : a - 1 ≥ 0 := by omega
                  apply mul_nonneg <;> omega
                omega
            _ = a := by ring
        omega
    _ ≥ 1 := a_ge_one
    _ > 0 := by norm_num

/-
Entries of M(x)v are strictly increasing for large x
Let M = M(x) = adj(xI - A) be the adjugate of the characteristic matrix xI - A.
Let v = (0,1,2,...,n-1)^T. Then there is x_0 such that for all x > x_0
the entries of M(x)v are non-negative, strictly increasing, and bounded by m = det(xI - A).
Note:
- y x i is a polynomial with non-negative leading coefficient (since v_k = k ≥ 0
  and diagonal adjugate entries are monic), so y x i ≥ 0 for large x.
- y x j - y x i (for j > i) is a polynomial with positive leading coefficient,
  so y x i < y x j for large x.
- m x is polynomial of degree n with leading coefficient 1, while y x i has degree ≤ n-1,
  so y x i < m x for large x.
-/
lemma adj_poly_strict_increasing {n : ℕ} [NeZero n] [h : Fact (n > 0)] (f : ZMod n → ZMod n) :
    let A := func_matrix f
    let v : Fin n → ℤ := fun i => i.val + 1  -- Use v = (1, 2, ..., n) instead of (0, 1, ..., n-1)
    let M := fun (x : ℤ) => (x • (1 : Matrix (Fin n) (Fin n) ℤ) - A).adjugate
    let y := fun (x : ℤ) => M x *ᵥ v
    let m := fun (x : ℤ) => (x • (1 : Matrix (Fin n) (Fin n) ℤ) - A).det
    ∃ x₀ : ℤ, ∀ x : ℤ, x > x₀ →
    (m x > 0) ∧
    (∀ i : Fin n, y x i ≥ 0) ∧
    (∀ i j : Fin n, i < j → y x i < y x j) ∧
    (∀ i : Fin n, y x i < m x) := by
  intro A v M y m

  -- First, observe that y x i and m x come from polynomial evaluations
  -- M x = (x•I - A).adjugate, whose entries are polynomials from charmatrix
  -- y x i = ∑_k (M x)_{ik} * v_k = ∑_k (M x)_{ik} * (k + 1)

  -- Define the polynomial for each entry y_i
  let p_i : Fin n → Polynomial ℤ := fun i =>
    ∑ k : Fin n, (charmatrix A).adjugate i k * Polynomial.C ((k.val + 1) : ℤ)

  -- Define the determinant polynomial
  let p_m : Polynomial ℤ := (charmatrix A).det

  -- Key lemma: The coefficient of p_i i at degree n-1 equals i.val + 1
  -- This is the core technical fact used throughout the proof
  have h_p_i_coeff : ∀ i : Fin n, (p_i i).coeff (n - 1) = i.val + 1 := by
    intro i
    -- The proof follows from:
    -- 1. p_i i = ∑_k adjugate[i,k] * C(k.val + 1)
    -- 2. Only the diagonal term adjugate[i,i] * C(i.val + 1) contributes to coeff at degree n-1
    -- 3. adjugate[i,i] is monic of degree n-1, so its coeff at n-1 is 1
    -- 4. C(i.val + 1) only has nonzero coeff at degree 0, where it equals (i.val + 1)
    -- 5. Therefore: coeff(n-1) = 1 * (i.val + 1) = i.val + 1

    -- Get properties of adjugate entries from adj_poly
    have h_adj := adj_poly A i i
    have h_diag : ((charmatrix A).adjugate i i).Monic ∧ ((charmatrix A).adjugate i i).natDegree = n - 1 :=
      h_adj.1 rfl
    have h_off : ∀ k : Fin n, k ≠ i → ((charmatrix A).adjugate i k).natDegree ≤ n - 2 :=
      fun k hk => (adj_poly A i k).2 (Ne.symm hk)

    -- Expand p_i i as a sum and compute its coefficient
    unfold p_i

    -- Use Finset.sum_eq_single to isolate the diagonal term directly
    calc (∑ k : Fin n, (charmatrix A).adjugate i k * Polynomial.C ((k.val + 1) : ℤ)).coeff (n - 1)
        = ∑ k : Fin n, ((charmatrix A).adjugate i k * Polynomial.C ((k.val + 1) : ℤ)).coeff (n - 1) := by
          -- Coefficient distributes over sums
          -- This follows from the fact that coeff is additive
          clear h_diag h_off h_adj
          induction' (Finset.univ : Finset (Fin n)) using Finset.induction_on with a s has ih
          · simp
          · rw [Finset.sum_insert has, Polynomial.coeff_add, Finset.sum_insert has, ih]
      _ = ((charmatrix A).adjugate i i * Polynomial.C ((i.val + 1) : ℤ)).coeff (n - 1) := by
          apply Finset.sum_eq_single i
          · -- Off-diagonal terms contribute 0 (degree too small)
            intro k _ hk
            rw [Polynomial.coeff_mul_C]
            have h_deg := h_off k hk
            have : ((charmatrix A).adjugate i k).coeff (n - 1) = 0 := by
              apply Polynomial.coeff_eq_zero_of_natDegree_lt
              omega
            rw [this]
            ring
          · -- Membership is automatic: i ∈ univ
            intro hi
            exfalso
            exact hi (Finset.mem_univ i)
      _ = i.val + 1 := by
          -- The diagonal term contributes i.val + 1
          rw [Polynomial.coeff_mul_C]
          have h_monic_coeff : ((charmatrix A).adjugate i i).coeff (n - 1) = 1 := by
            have ⟨h_monic, h_deg⟩ := h_diag
            rw [Polynomial.Monic.def] at h_monic
            rw [← h_deg]
            exact h_monic
          rw [h_monic_coeff]
          ring

  -- Key observation: y x i = (p_i i).eval x and m x = p_m.eval x
  have y_is_poly : ∀ i : Fin n, ∀ x : ℤ, y x i = (p_i i).eval x := by
    intro i x
    -- y x i = (M x *ᵥ v) i = ∑_k (M x)_{ik} * v_k = ∑_k (M x)_{ik} * k
    -- where M x = (x•I - A).adjugate
    -- We need to show this equals (p_i i).eval x where p_i i = ∑_k (charmatrix A).adjugate_{ik} * C k

    -- Expand definitions
    show (M x *ᵥ v) i = (p_i i).eval x

    -- LHS: (M x *ᵥ v) i = ∑_k (M x)_{ik} * v_k = ∑_k (M x)_{ik} * (k.val + 1)
    calc (M x *ᵥ v) i
        = ∑ k : Fin n, M x i k * v k := by
          unfold Matrix.mulVec
          rfl
      _ = ∑ k : Fin n, (x • (1 : Matrix (Fin n) (Fin n) ℤ) - A).adjugate i k * ((k.val + 1) : ℤ) := rfl
      _ = ∑ k : Fin n, ((charmatrix A).adjugate i k).eval x * ((k.val + 1) : ℤ) := by
          congr 1
          ext k
          -- Need: (x•I - A).adjugate_{ik} = (charmatrix A).adjugate_{ik}.eval x
          -- charmatrix A = scalar X - C.mapMatrix A
          -- When we evaluate at x: eval (scalar X) = scalar x, eval (C a) = a
          -- So eval(charmatrix A) x = scalar x - A = x•I - A
          -- Then adjugate commutes with ring homomorphisms
          have h_eval_charmatrix : (charmatrix A).map (Polynomial.evalRingHom x) = x • (1 : Matrix (Fin n) (Fin n) ℤ) - A := by
            unfold charmatrix
            ext i' j'
            simp only [Matrix.map_apply, Matrix.sub_apply, RingHom.mapMatrix_apply, Matrix.scalar_apply]
            by_cases hij : i' = j'
            · simp [hij, Polynomial.eval_X, Matrix.smul_apply]
            · simp [hij, Matrix.smul_apply]
          have h_adjugate_map : ((charmatrix A).adjugate).map (Polynomial.evalRingHom x) =
              ((charmatrix A).map (Polynomial.evalRingHom x)).adjugate := by
            have := RingHom.map_adjugate (Polynomial.evalRingHom x) (charmatrix A)
            simp only [RingHom.mapMatrix_apply] at this
            exact this
          show (x • 1 - A).adjugate i k * (↑↑k + 1) = ((charmatrix A).adjugate i k).eval x * (↑↑k + 1)
          rw [← h_eval_charmatrix, ← h_adjugate_map]
          rfl
      _ = ∑ k : Fin n, ((charmatrix A).adjugate i k).eval x * (Polynomial.C ((k.val + 1) : ℤ)).eval x := by
          congr 1; ext k; rw [Polynomial.eval_C]
      _ = (∑ k : Fin n, (charmatrix A).adjugate i k * Polynomial.C ((k.val + 1) : ℤ)).eval x := by
          rw [Polynomial.eval_finset_sum]
          congr 1
          ext k
          rw [Polynomial.eval_mul]
      _ = (p_i i).eval x := rfl

  have m_is_poly : ∀ x : ℤ, m x = p_m.eval x := by
    intro x
    -- m x = det(x•I - A)
    -- p_m = det(charmatrix A) = A.charpoly
    -- Matrix.eval_charpoly says: A.charpoly.eval μ = (scalar μ - A).det
    unfold m p_m
    rw [charmatrix_det_eq_charpoly]
    rw [Matrix.eval_charpoly]
    -- Now we have: (scalar x - A).det = ?
    -- We need to show scalar x - A = x • 1 - A
    congr 1
    ext i j
    simp [Matrix.scalar]

  -- Now we need to show strict ordering for large x
  -- Strategy: show that p_i(j) - p_i(i) has positive leading coeff for j > i
  -- and p_m - p_i(i) has positive leading coeff

  -- From adj_poly, we know:
  -- - Diagonal entries of adjugate are monic of degree n-1
  -- - Off-diagonal entries have degree ≤ n-2
  -- - det has degree n and is monic

  -- For j > i, we have p_i(j) - p_i(i):
  -- Since v_k = k, this is ∑_k adjugate[i,k] * k
  -- The coefficient of k=j is adjugate[i,j] which has degree ≤ n-2 (since i≠j)
  -- The coefficient of k=i is adjugate[i,i] which is monic of degree n-1
  -- So p_i(j) - p_i(i) = (j-i) * (monic poly of deg n-1) + lower order terms
  -- This has positive leading coefficient

  -- For each i, find x₀ such that y x i ≥ 0 for x > x₀
  have nonneg_bounds : ∀ i : Fin n,
      ∃ x₀ : ℤ, x₀ > 0 ∧ ∀ x : ℤ, x > x₀ → y x i ≥ 0 := by
    intro i
    -- p_i i has non-negative leading coefficient (monic of degree n-1)
    -- Since v_k = k + 1 ≥ 1, all components are positive
    have h_coeff_n_minus_1_nonneg : (p_i i).coeff (n - 1) ≥ 0 := by
      -- The coefficient at degree n-1 is i.val + 1 (from h_p_i_coeff)
      -- and i.val + 1 ≥ 1 > 0
      have : (p_i i).coeff (n - 1) = i.val + 1 := h_p_i_coeff i
      rw [this]
      omega

    by_cases h : (p_i i).leadingCoeff > 0
    · let x₀ := coeff_bound (p_i i)
      -- Prove that x₀ > 0
      have h_x₀_pos : x₀ > 0 := by
        have p_i_nonzero : p_i i ≠ 0 := by
          intro h_zero; rw [h_zero] at h; simp at h
        simp [x₀, coeff_bound]
        have supp_nonempty : (p_i i).support.Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro h_empty; apply p_i_nonzero; ext k
          by_cases hk : (p_i i).coeff k = 0
          · exact hk
          · exfalso
            have : k ∈ (p_i i).support := by rwa [Polynomial.mem_support_iff]
            rw [h_empty] at this; exact Finset.notMem_empty k this
        obtain ⟨k, hk⟩ := supp_nonempty
        have coeff_nonzero : (p_i i).coeff k ≠ 0 := by rwa [Polynomial.mem_support_iff] at hk
        have sum_ge : |(p_i i).coeff k| ≤ ∑ j ∈ (p_i i).support, |(p_i i).coeff j| :=
          Finset.single_le_sum (f := fun j => |(p_i i).coeff j|) (fun j _ => abs_nonneg _) hk
        calc ∑ j ∈ (p_i i).support, |(p_i i).coeff j|
            ≥ |(p_i i).coeff k| := sum_ge
          _ > 0 := abs_pos.mpr coeff_nonzero

      use x₀
      constructor
      · exact h_x₀_pos
      · intro x hx
        have ⟨hx_pos, h_eval⟩ : x > 0 ∧ (p_i i).eval x > 0 := polynomial_positive (p_i i) h x (le_of_lt hx)
        rw [← y_is_poly i x] at h_eval
        linarith
    · -- If leadingCoeff ≤ 0
      -- We know coeff(n-1) = i.val ≥ 0
      -- If natDegree = n-1, then leadingCoeff = coeff(n-1) = i.val ≥ 0
      -- Combined with leadingCoeff ≤ 0, we get leadingCoeff = 0, so i.val = 0
      -- If natDegree < n-1, then i = 0 (since coeff(n-1) = i.val must be 0)
      -- In either case, coeff(n-1) ≥ 0 means leadingCoeff could be negative for natDegree < n-1
      -- But if leadingCoeff ≤ 0 and the polynomial is not eventually positive,
      -- we need to handle this case differently

      -- For ALL i (including i=0), we now have coeff(n-1) = i.val + 1 ≥ 1 > 0
      -- So the polynomial must have degree n-1 and leadingCoeff = coeff(n-1) > 0
      -- This contradicts the assumption that leadingCoeff ≤ 0

      have h_coeff_pos : (p_i i).coeff (n - 1) > 0 := by
        have : (p_i i).coeff (n - 1) = i.val + 1 := h_p_i_coeff i
        rw [this]
        omega

      -- Since coeff(n-1) > 0, the polynomial must have degree n-1
      exfalso
      have h_deg : (p_i i).natDegree = n - 1 := by
        by_contra h_ne
        have h_lt : (p_i i).natDegree < n - 1 := by
          have h_le : (p_i i).natDegree ≤ n - 1 := by
            -- p_i i = ∑_k adjugate[i,k] * C (k+1), each term has degree ≤ n-1
            apply Polynomial.natDegree_sum_le_of_forall_le
            intro k _
            have h_adj := adj_poly A i k
            by_cases hik : i = k
            · -- Diagonal: degree = n-1
              by_cases hzero : ((k.val + 1) : ℤ) = 0
              · omega -- k.val + 1 ≥ 1, so never 0
              · subst hik
                have h_monic := (h_adj.1 rfl)
                have h_ne_zero : (charmatrix A).adjugate i i ≠ 0 := h_monic.1.ne_zero
                have h_C_ne_zero : Polynomial.C ((i.val + 1) : ℤ) ≠ 0 := Polynomial.C_ne_zero.mpr hzero
                rw [Polynomial.natDegree_mul h_ne_zero h_C_ne_zero, Polynomial.natDegree_C, add_zero, h_monic.2]
            · -- Off-diagonal: degree ≤ n-2 ≤ n-1
              by_cases hzero : ((k.val + 1) : ℤ) = 0
              · omega -- k.val + 1 ≥ 1, so never 0
              · have h_off := h_adj.2 hik
                by_cases h_poly_zero : (charmatrix A).adjugate i k = 0
                · simp [h_poly_zero]
                · rw [Polynomial.natDegree_mul h_poly_zero (Polynomial.C_ne_zero.mpr hzero), Polynomial.natDegree_C, add_zero]
                  calc ((charmatrix A).adjugate i k).natDegree
                      ≤ n - 2 := h_off
                    _ ≤ n - 1 := by omega
          omega
        have : (p_i i).coeff (n - 1) = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt h_lt
        rw [this] at h_coeff_pos
        omega
      have : (p_i i).leadingCoeff = (p_i i).coeff (n - 1) := by
        rw [Polynomial.leadingCoeff, h_deg]
      rw [this] at h
      omega

 -- For each pair i < j, find x₀ such that y x i < y x j for x > x₀
  have ordering_bounds : ∀ i j : Fin n, i < j →
      ∃ x₀ : ℤ, x₀ > 0 ∧ ∀ x : ℤ, x > x₀ → y x i < y x j := by
    intro i j hij
    -- The difference p_i(j) - p_i(i) is a polynomial with positive leading coefficient
    let diff_poly := p_i j - p_i i
    have h_lead_pos : diff_poly.leadingCoeff > 0 := by
      -- p_i j = ∑_k adjugate[j,k] * C k  (j-th row of adjugate dotted with v)
      -- p_i i = ∑_k adjugate[i,k] * C k  (i-th row of adjugate dotted with v)
      -- diff_poly = p_i j - p_i i = ∑_k (adjugate[j,k] - adjugate[i,k]) * C k
      --
      -- From adj_poly:
      -- - adjugate[j,j] is monic of degree n-1, adjugate[i,i] is monic of degree n-1
      -- - Off-diagonal entries have degree ≤ n-2
      --
      -- Leading coefficient analysis:
      -- - Term for k=j: adjugate[j,j] * j has leading coeff j (from monic degree n-1)
      -- - Term for k=i: -adjugate[i,i] * i has leading coeff -i (from monic degree n-1)
      -- - Since j > i and both have same degree n-1, the leading coeff is j - i > 0

      -- We know j > i, so j.val ≥ i.val + 1 ≥ 1, meaning j is always positive
      have h_j_pos : j.val > 0 := by
        have : i.val < j.val := Fin.val_fin_lt.mp hij
        omega

      -- Establish degrees of p_i j and p_i i
      -- p_i j always has degree n-1 (all k now have v_k = k+1 ≥ 1)
      have h_deg_j : (p_i j).natDegree = n - 1 := by
        have h_deg_le : (p_i j).natDegree ≤ n - 1 := by
          have h_bound : ∀ k ∈ Finset.univ, ((charmatrix A).adjugate j k * Polynomial.C ((k.val + 1) : ℤ)).natDegree ≤ n - 1 := by
            intro k _
            have h_adj := adj_poly A j k
            by_cases hjk : j = k
            · -- Diagonal case
              subst hjk
              have h_monic := (h_adj.1 rfl)
              have h_C_ne_zero : Polynomial.C ((j.val + 1) : ℤ) ≠ 0 := by
                apply Polynomial.C_ne_zero.mpr
                omega
              rw [Polynomial.natDegree_mul h_monic.1.ne_zero h_C_ne_zero, Polynomial.natDegree_C]
              simp [h_monic.2]
            · -- Off-diagonal case
              have h_off := h_adj.2 hjk
              by_cases h_poly_zero : (charmatrix A).adjugate j k = 0
              · simp [h_poly_zero]
              · have h_C_ne_zero : Polynomial.C ((k.val + 1) : ℤ) ≠ 0 := by
                  apply Polynomial.C_ne_zero.mpr
                  omega
                rw [Polynomial.natDegree_mul h_poly_zero h_C_ne_zero, Polynomial.natDegree_C]
                simp only [add_zero]
                calc ((charmatrix A).adjugate j k).natDegree
                    ≤ n - 2 := h_off
                  _ ≤ n - 1 := by omega
          exact Polynomial.natDegree_sum_le_of_forall_le Finset.univ _ h_bound
        have h_coeff_ne_zero : (p_i j).coeff (n - 1) ≠ 0 := by
          rw [h_p_i_coeff j]
          omega
        have h_deg_ge : (p_i j).natDegree ≥ n - 1 := by
          apply Polynomial.le_natDegree_of_ne_zero h_coeff_ne_zero
        omega

      -- With v = (1,2,...,n), ALL indices including i=0 have degree n-1
      -- because v_k = k.val + 1 ≥ 1 for all k ∈ Fin n
      have h_deg_i : (p_i i).natDegree = n - 1 := by
        have h_deg_le : (p_i i).natDegree ≤ n - 1 := by
          have h_bound : ∀ k ∈ Finset.univ, ((charmatrix A).adjugate i k * Polynomial.C ((k.val + 1) : ℤ)).natDegree ≤ n - 1 := by
            intro k _
            have h_adj := adj_poly A i k
            by_cases hik : i = k
            · -- Diagonal case
              subst hik
              have h_monic := (h_adj.1 rfl)
              have h_C_ne_zero : Polynomial.C ((i.val + 1) : ℤ) ≠ 0 := by
                apply Polynomial.C_ne_zero.mpr
                omega
              rw [Polynomial.natDegree_mul h_monic.1.ne_zero h_C_ne_zero, Polynomial.natDegree_C]
              simp [h_monic.2]
            · -- Off-diagonal case
              have h_off := h_adj.2 hik
              by_cases h_poly_zero : (charmatrix A).adjugate i k = 0
              · simp [h_poly_zero]
              · have h_C_ne_zero : Polynomial.C ((k.val + 1) : ℤ) ≠ 0 := by
                  apply Polynomial.C_ne_zero.mpr
                  omega
                rw [Polynomial.natDegree_mul h_poly_zero h_C_ne_zero, Polynomial.natDegree_C]
                simp only [add_zero]
                calc ((charmatrix A).adjugate i k).natDegree
                    ≤ n - 2 := h_off
                  _ ≤ n - 1 := by omega
          exact Polynomial.natDegree_sum_le_of_forall_le Finset.univ _ h_bound
        have h_coeff_ne_zero : (p_i i).coeff (n - 1) ≠ 0 := by
          rw [h_p_i_coeff i]
          omega
        have h_deg_ge : (p_i i).natDegree ≥ n - 1 := by
          apply Polynomial.le_natDegree_of_ne_zero h_coeff_ne_zero
        omega

      have h_coeff_diff : diff_poly.coeff (n - 1) = j.val - i.val := by
        calc diff_poly.coeff (n - 1)
            = (p_i j - p_i i).coeff (n - 1) := rfl
          _ = (p_i j).coeff (n - 1) - (p_i i).coeff (n - 1) := Polynomial.coeff_sub _ _ _
          _ = (j.val + 1) - (i.val + 1) := by
            rw [h_p_i_coeff j, h_p_i_coeff i]
          _ = j.val - i.val := by ring

      have h_deg_diff : diff_poly.natDegree = n - 1 := by
        have h_coeff_ne_zero : diff_poly.coeff (n - 1) ≠ 0 := by
          rw [h_coeff_diff]
          have : i.val < j.val := Fin.val_fin_lt.mp hij
          omega
        have h_deg_le : diff_poly.natDegree ≤ n - 1 := by
          calc diff_poly.natDegree
              ≤ max (p_i j).natDegree (p_i i).natDegree := Polynomial.natDegree_sub_le _ _
            _ = max (n - 1) (n - 1) := by rw [h_deg_j, h_deg_i]
            _ = n - 1 := max_self _
        have h_deg_ge : diff_poly.natDegree ≥ n - 1 := by
          apply Polynomial.le_natDegree_of_ne_zero h_coeff_ne_zero
        omega

      rw [Polynomial.leadingCoeff, h_deg_diff, h_coeff_diff]
      have : i.val < j.val := Fin.val_fin_lt.mp hij
      omega

    let x₀ := coeff_bound diff_poly
    -- Prove that x₀ > 0
    have h_x₀_pos : x₀ > 0 := by
      have diff_poly_nonzero : diff_poly ≠ 0 := by
        intro h; rw [h] at h_lead_pos; simp at h_lead_pos
      simp [x₀, coeff_bound]
      have supp_nonempty : diff_poly.support.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h; apply diff_poly_nonzero; ext k
        by_cases hk : diff_poly.coeff k = 0
        · exact hk
        · exfalso
          have : k ∈ diff_poly.support := by rwa [Polynomial.mem_support_iff]
          rw [h] at this; exact Finset.notMem_empty k this
      obtain ⟨k, hk⟩ := supp_nonempty
      have coeff_nonzero : diff_poly.coeff k ≠ 0 := by rwa [Polynomial.mem_support_iff] at hk
      have sum_ge : |diff_poly.coeff k| ≤ ∑ j ∈ diff_poly.support, |diff_poly.coeff j| :=
        Finset.single_le_sum (f := fun j => |diff_poly.coeff j|) (fun j _ => abs_nonneg _) hk
      calc ∑ j ∈ diff_poly.support, |diff_poly.coeff j|
          ≥ |diff_poly.coeff k| := sum_ge
        _ > 0 := abs_pos.mpr coeff_nonzero

    use x₀
    constructor
    · exact h_x₀_pos
    · intro x hx
      have ⟨hx_pos, h_eval⟩ : x > 0 ∧ diff_poly.eval x > 0 := polynomial_positive diff_poly h_lead_pos x (le_of_lt hx)
      rw [Polynomial.eval_sub] at h_eval
      have : (p_i j).eval x > (p_i i).eval x := by linarith
      rw [← y_is_poly j x, ← y_is_poly i x] at this
      exact this

  -- For each i, find x₀ such that y x i < m x for x > x₀
  have bound_by_det : ∀ i : Fin n,
      ∃ x₀ : ℤ, x₀ > 0 ∧ ∀ x : ℤ, x > x₀ → y x i < m x := by
    intro i
    let diff_poly := p_m - p_i i
    have h_lead_pos : diff_poly.leadingCoeff > 0 := by
      -- p_m = det(charmatrix A) is monic of degree n (from charpoly properties)
      -- p_i i = ∑_k adjugate[i,k] * C k has degree ≤ n-1
      --   (diagonal adjugate[i,i] is degree n-1, times constant C i, still degree n-1)
      -- Therefore diff_poly has leading coefficient 1 (from p_m) minus 0 (since p_i i has lower degree)

      -- p_m is the characteristic polynomial determinant, which is monic of degree n
      have h_deg_pm : p_m.natDegree = n := by
        by_cases hn : n = 1
        · -- For n = 1, the characteristic polynomial is X - a₀₀, which has degree 1
          subst hn
          -- charmatrix A is a 1×1 matrix [[X - A 0 0]]
          -- Its determinant is X - A 0 0, which has degree 1
          have : p_m = Polynomial.X - Polynomial.C (A 0 0) := by
            simp
            exact det_fin_one A.charmatrix
          rw [this]
          rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
          · simp [Polynomial.natDegree_X]
          · simp [Polynomial.natDegree_X]
        · -- For n ≥ 2, use charmatrix_det_natDegree
          have h_n_ge_2 : n ≥ 2 := by
            have h_n_pos : n > 0 := h.out
            omega
          have : Nontrivial (Fin n) := by
            rw [Fin.nontrivial_iff_two_le]
            exact h_n_ge_2
          rw [charmatrix_det_natDegree A]
          simp [Fintype.card_fin]
      have h_monic_pm : p_m.Monic := by
        by_cases hn : n = 1
        · -- For n = 1, X - c is monic
          subst hn
          have : p_m = Polynomial.X - Polynomial.C (A 0 0) := by
            simp
            exact det_fin_one A.charmatrix
          rw [this]
          exact Polynomial.monic_X_sub_C (A 0 0)
        · -- For n ≥ 2, use charmatrix_det_monic
          have h_n_ge_2 : n ≥ 2 := by
            have h_n_pos : n > 0 := h.out
            omega
          have : Nontrivial (Fin n) := by
            rw [Fin.nontrivial_iff_two_le]
            exact h_n_ge_2
          exact charmatrix_det_monic A

      -- p_i i has degree ≤ n-1
      have h_deg_pi : (p_i i).natDegree ≤ n - 1 := by
        -- p_i i = ∑_k adjugate[i,k] * C(k+1)
        -- Each term has degree at most n-1
        have h_bound : ∀ k ∈ Finset.univ, ((charmatrix A).adjugate i k * Polynomial.C ((k.val + 1) : ℤ)).natDegree ≤ n - 1 := by
          intro k _
          have h_adj := adj_poly A i k
          by_cases hik : i = k
          · -- Diagonal: degree = n-1
            subst hik
            have h_monic := (h_adj.1 rfl)
            have h_C_ne_zero : Polynomial.C ((i.val + 1) : ℤ) ≠ 0 := by
              apply Polynomial.C_ne_zero.mpr
              omega
            rw [Polynomial.natDegree_mul h_monic.1.ne_zero h_C_ne_zero, Polynomial.natDegree_C]
            simp [h_monic.2]
          · -- Off-diagonal: degree ≤ n-2 ≤ n-1
            have h_off := h_adj.2 hik
            by_cases h_poly_zero : (charmatrix A).adjugate i k = 0
            · simp [h_poly_zero]
            · have h_C_ne_zero : Polynomial.C ((k.val + 1) : ℤ) ≠ 0 := by
                apply Polynomial.C_ne_zero.mpr
                omega
              rw [Polynomial.natDegree_mul h_poly_zero h_C_ne_zero, Polynomial.natDegree_C]
              simp only [add_zero]
              calc ((charmatrix A).adjugate i k).natDegree
                  ≤ n - 2 := h_off
                _ ≤ n - 1 := by omega
        exact Polynomial.natDegree_sum_le_of_forall_le Finset.univ _ h_bound

      -- Since deg(p_m) = n > n-1 ≥ deg(p_i i), the leading coefficient is just that of p_m
      have h_deg_diff : diff_poly.natDegree = n := by
        have h_deg_lt : (p_i i).natDegree < p_m.natDegree := by
          rw [h_deg_pm]
          have h_n_pos : n > 0 := h.out
          omega
        rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt h_deg_lt, h_deg_pm]

      rw [Polynomial.leadingCoeff, h_deg_diff]
      rw [Polynomial.coeff_sub]
      have h_coeff_pm : p_m.coeff n = 1 := by
        have : p_m.leadingCoeff = 1 := h_monic_pm.leadingCoeff
        rw [Polynomial.leadingCoeff, h_deg_pm] at this
        exact this
      have h_coeff_pi : (p_i i).coeff n = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        have h_n_pos : n > 0 := h.out
        omega
      rw [h_coeff_pm, h_coeff_pi]
      norm_num

    let x₀ := coeff_bound diff_poly
    -- Prove that x₀ > 0
    have h_x₀_pos : x₀ > 0 := by
      have diff_poly_nonzero : diff_poly ≠ 0 := by
        intro h; rw [h] at h_lead_pos; simp at h_lead_pos
      simp [x₀, coeff_bound]
      have supp_nonempty : diff_poly.support.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h; apply diff_poly_nonzero; ext k
        by_cases hk : diff_poly.coeff k = 0
        · exact hk
        · exfalso
          have : k ∈ diff_poly.support := by rwa [Polynomial.mem_support_iff]
          rw [h] at this; exact Finset.notMem_empty k this
      obtain ⟨k, hk⟩ := supp_nonempty
      have coeff_nonzero : diff_poly.coeff k ≠ 0 := by rwa [Polynomial.mem_support_iff] at hk
      have sum_ge : |diff_poly.coeff k| ≤ ∑ j ∈ diff_poly.support, |diff_poly.coeff j| :=
        Finset.single_le_sum (f := fun j => |diff_poly.coeff j|) (fun j _ => abs_nonneg _) hk
      calc ∑ j ∈ diff_poly.support, |diff_poly.coeff j|
          ≥ |diff_poly.coeff k| := sum_ge
        _ > 0 := abs_pos.mpr coeff_nonzero

    use x₀
    constructor
    · exact h_x₀_pos
    · intro x hx
      have ⟨hx_pos, h_eval⟩ : x > 0 ∧ diff_poly.eval x > 0 := polynomial_positive diff_poly h_lead_pos x (le_of_lt hx)
      rw [Polynomial.eval_sub] at h_eval
      have : p_m.eval x > (p_i i).eval x := by linarith
      rw [← m_is_poly x, ← y_is_poly i x] at this
      exact this

  -- Combine all bounds: take the maximum of all x₀ values
  -- For non-negativity: need max over all i
  -- For ordering: need max over all pairs i < j
  -- For det bound: need max over all i

  -- Extract witnesses using Classical.choose
  -- All bounds are positive (from polynomial_positive)
  let nonneg_bound := fun i => Classical.choose (nonneg_bounds i)
  let ordering_bound := fun i j (hij : i < j) => Classical.choose (ordering_bounds i j hij)
  let det_bound := fun i => Classical.choose (bound_by_det i)

  -- All bounds are positive: each existential provides a witness > 0
  have nonneg_bound_pos : ∀ i : Fin n, nonneg_bound i > 0 := by
    intro i
    -- nonneg_bounds i : ∃ x₀ : ℤ, x₀ > 0 ∧ ∀ x : ℤ, x > x₀ → y x i ≥ 0
    -- Classical.choose_spec gives us: nonneg_bound i > 0 ∧ (∀ x > nonneg_bound i, y x i ≥ 0)
    exact (Classical.choose_spec (nonneg_bounds i)).1

  have ordering_bound_pos : ∀ i j (hij : i < j), ordering_bound i j hij > 0 := by
    intro i j hij
    -- ordering_bounds i j hij : ∃ x₀ : ℤ, x₀ > 0 ∧ ∀ x : ℤ, x > x₀ → y x i < y x j
    -- Classical.choose_spec gives us: ordering_bound i j hij > 0 ∧ (∀ x > ordering_bound i j hij, y x i < y x j)
    exact (Classical.choose_spec (ordering_bounds i j hij)).1

  have det_bound_pos : ∀ i : Fin n, det_bound i > 0 := by
    intro i
    -- det_bound i = Classical.choose (bound_by_det i)
    -- bound_by_det i : ∃ x₀ : ℤ, x₀ > 0 ∧ ∀ x : ℤ, x > x₀ → y x i < m x
    -- Classical.choose_spec gives us: det_bound i > 0 ∧ (∀ x > det_bound i, y x i < m x)
    exact (Classical.choose_spec (bound_by_det i)).1

  -- For m x > 0, we also need a bound from polynomial_positive on p_m
  -- We need to handle n=1 separately since Fin 1 is not Nontrivial
  have h_deg : Polynomial.degree p_m = n := by
    have pos : 0 < n := Fact.out (p := n > 0)
    by_cases h1 : n = 1
    · -- n = 1: special case, charmatrix is 1x1, p_m = X - A₀₀ has degree 1
      rw [h1]
      unfold p_m
      -- A.charmatrix.det = charmatrix A 0 0
      have : A.charmatrix.det = A.charmatrix 0 0 := by
        refine det_eq_elem_of_card_eq_one ?_ 0
        rw [Fintype.card_fin]
        exact h1
      rw [this]
      -- charmatrix A 0 0 = X - A 0 0
      simp only [charmatrix_apply]
      -- Since A is func_matrix f, and n=1, f maps 0 to 0, so A 0 0 = 1
      have h_A : A 0 0 = 1 := by
        have : f 0 = 0 := by
          have : ∀ x : ZMod n, x = 0 := by
            intro x
            have : x.val < n := ZMod.val_lt x
            have : n = 1 := h1
            rw [this] at this
            have : x.val < 1 := by (expose_names; exact Nat.lt_of_lt_of_eq this_2 h1)
            have : x.val = 0 := by omega
            exact (ZMod.val_eq_zero x).mp this
          exact this (f 0)
        have : A 0 0 = if f 0 = 0 then 1 else 0 := by
          simp [A, func_matrix]
        rw [this]
        simp
        (expose_names; exact this_2)
      rw [h_A]
      -- So det = X - 1, degree 1
      exact Polynomial.degree_X_sub_C 1
    · -- n ≥ 2: use charmatrix_det_natDegree
      have : Nontrivial (Fin n) := by
        have h_lt : 1 < n := by omega
        refine ⟨⟨⟨0, by omega⟩, ⟨1, by omega⟩, ?_⟩⟩
        intro h
        simp only [Fin.mk.injEq] at h
        norm_num at h
      have h_nat : p_m.natDegree = n := by
        have := charmatrix_det_natDegree A
        rw [Fintype.card_fin] at this
        exact this
      have h_nonzero : p_m ≠ 0 := by
        intro h
        have : (charmatrix A).det.Monic := charmatrix_det_monic A
        rw [show p_m = (charmatrix A).det from rfl] at h
        rw [h] at this
        exact Polynomial.Monic.ne_zero this rfl
      rw [Polynomial.degree_eq_natDegree h_nonzero, h_nat]

  have h_lead : p_m.leadingCoeff > 0 := by
    have pos : 0 < n := Fact.out (p := n > 0)
    by_cases h1 : n = 1
    · -- n = 1: special case, charmatrix is 1x1, p_m = X - A₀₀ has leading coeff 1
      -- p_m = A.charpoly, and charpoly is always monic
      have : p_m = A.charpoly := by
        unfold p_m
        exact charmatrix_det_eq_charpoly A
      rw [this]
      rw [Matrix.charpoly_monic A]
      norm_num
    · -- n ≥ 2: use charmatrix_det_monic
      have : Nontrivial (Fin n) := by
        have h_lt : 1 < n := by omega
        refine ⟨⟨⟨0, by omega⟩, ⟨1, by omega⟩, ?_⟩⟩
        intro h
        simp only [Fin.mk.injEq] at h
        norm_num at h
      have : (charmatrix A).det.Monic := charmatrix_det_monic A
      rw [show p_m.leadingCoeff = (charmatrix A).det.leadingCoeff from rfl]
      rw [Polynomial.Monic] at this
      rw [this]
      norm_num
  let det_pos_bound := coeff_bound p_m
  have h_det_pos_bound_pos : det_pos_bound > 0 := by
    -- Since p_m has positive leading coefficient, it's nonzero, so it has at least one nonzero coefficient
    -- Therefore coeff_bound p_m = sum of |coeff i| > 0
    have p_m_nonzero : p_m ≠ 0 := by
      intro h
      rw [h] at h_lead
      simp at h_lead
    simp [det_pos_bound, coeff_bound]
    -- p_m is nonzero, so its support is nonempty
    have supp_nonempty : p_m.support.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h
      apply p_m_nonzero
      ext i
      by_cases hi : p_m.coeff i = 0
      · exact hi
      · exfalso
        have : i ∈ p_m.support := by
          rwa [Polynomial.mem_support_iff]
        rw [h] at this
        exact Finset.notMem_empty i this
    -- The sum of absolute values of nonzero coefficients is positive
    obtain ⟨i, hi⟩ := supp_nonempty
    have coeff_nonzero : p_m.coeff i ≠ 0 := by
      rwa [Polynomial.mem_support_iff] at hi
    have sum_ge : |p_m.coeff i| ≤ ∑ j ∈ p_m.support, |p_m.coeff j| :=
      Finset.single_le_sum (f := fun j => |p_m.coeff j|) (fun j _ => abs_nonneg _) hi
    calc ∑ j ∈ p_m.support, |p_m.coeff j|
        ≥ |p_m.coeff i| := sum_ge
      _ > 0 := abs_pos.mpr coeff_nonzero

  -- Since all bounds are positive, we can simply sum them
  let final_bound : ℤ :=
    det_pos_bound +
    (Finset.univ.sum fun i => nonneg_bound i) +
    (Finset.univ.sum fun i => det_bound i) +
    (Finset.univ.sum fun i => Finset.univ.sum fun j => if hij : i < j then ordering_bound i j hij else 0)

  use final_bound
  intro x hx

  constructor
  · -- m x > 0: The determinant is monic of degree n with leading coefficient 1 > 0
    have : x > det_pos_bound := by
      have h1 : det_pos_bound ≤ final_bound := by
        unfold final_bound
        have h2 : 0 ≤ Finset.univ.sum fun i => nonneg_bound i := by
          apply Finset.sum_nonneg; intro j _; exact le_of_lt (nonneg_bound_pos j)
        have h3 : 0 ≤ Finset.univ.sum fun i => det_bound i := by
          apply Finset.sum_nonneg; intro j _; exact le_of_lt (det_bound_pos j)
        have h4 : 0 ≤ Finset.univ.sum fun i => Finset.univ.sum fun j => if hij : i < j then ordering_bound i j hij else 0 := by
          apply Finset.sum_nonneg; intro i' _; apply Finset.sum_nonneg; intro j' _
          split_ifs with hij
          · exact le_of_lt (ordering_bound_pos i' j' hij)
          · omega
        linarith
      omega
    have ⟨_, h_eval⟩ := polynomial_positive p_m h_lead x (le_of_lt this)
    rwa [← m_is_poly] at h_eval

  constructor
  · -- Non-negativity
    intro i
    have h_spec := Classical.choose_spec (nonneg_bounds i)
    have h_le : nonneg_bound i ≤ final_bound := by
      unfold final_bound
      have : nonneg_bound i ≤ Finset.univ.sum fun j => nonneg_bound j := by
        apply Finset.single_le_sum
        · intro j _
          exact le_of_lt (nonneg_bound_pos j)
        · exact Finset.mem_univ i
      have h1 : 0 ≤ Finset.univ.sum fun j => det_bound j := by
        apply Finset.sum_nonneg
        intro j _
        exact le_of_lt (det_bound_pos j)
      have h2 : 0 ≤ Finset.univ.sum fun i => Finset.univ.sum fun j => if hij : i < j then ordering_bound i j hij else 0 := by
        apply Finset.sum_nonneg
        intro i' _
        apply Finset.sum_nonneg
        intro j' _
        split_ifs with hij
        · exact le_of_lt (ordering_bound_pos i' j' hij)
        · omega
      linarith
    have : x > nonneg_bound i := by omega
    exact h_spec.2 x this
  constructor
  · -- Strict ordering
    intro i j hij
    have h_spec := Classical.choose_spec (ordering_bounds i j hij)
    have h_le : ordering_bound i j hij ≤ final_bound := by
      unfold final_bound
      -- ordering_bound i j hij appears in the 4th summand when i' = i, j' = j
      -- All other terms are non-negative, so we have the inequality
      have h1 : 0 ≤ det_pos_bound := le_of_lt h_det_pos_bound_pos
      have h2 : 0 ≤ Finset.univ.sum fun i => nonneg_bound i := by
        apply Finset.sum_nonneg; intro i' _; exact le_of_lt (nonneg_bound_pos i')
      have h3 : 0 ≤ Finset.univ.sum fun i => det_bound i := by
        apply Finset.sum_nonneg; intro i' _; exact le_of_lt (det_bound_pos i')
      have h4 : ordering_bound i j hij ≤
          Finset.univ.sum fun i' => Finset.univ.sum fun j' =>
            if hij' : i' < j' then ordering_bound i' j' hij' else 0 := by
        -- The sum includes the term for i' = i, j' = j, and all other terms are non-negative
        trans (∑ j' ∈ Finset.univ, if hij' : i < j' then ordering_bound i j' hij' else 0)
        · -- ordering_bound i j hij ≤ ∑_{j'} if i < j' then ordering_bound i j' ...
          have : ordering_bound i j hij = if hij : i < j then ordering_bound i j hij else 0 := by simp [hij]
          rw [this]
          apply Finset.single_le_sum (f := fun j' => if hij' : i < j' then ordering_bound i j' hij' else 0)
          · intro j' _
            by_cases h : i < j'
            · simp [h]; exact le_of_lt (ordering_bound_pos i j' h)
            · simp [h]
          · exact Finset.mem_univ j
        · -- ∑_{j'} ... ≤ ∑_{i'} ∑_{j'} ...
          apply Finset.single_le_sum (f := fun i' => ∑ j' ∈ Finset.univ, if hij' : i' < j' then ordering_bound i' j' hij' else 0)
          · intro i' _
            apply Finset.sum_nonneg
            intro j' _
            by_cases h : i' < j'
            · simp [h]; exact le_of_lt (ordering_bound_pos i' j' h)
            · simp [h]
          · exact Finset.mem_univ i
      linarith
    have : x > ordering_bound i j hij := by omega
    exact h_spec.2 x this
  · -- Bounded by det
    intro i
    have h_spec := Classical.choose_spec (bound_by_det i)
    have h_le : det_bound i ≤ final_bound := by
      unfold final_bound
      have : det_bound i ≤ Finset.univ.sum fun j => det_bound j := by
        apply Finset.single_le_sum
        · intro j _
          exact le_of_lt (det_bound_pos j)
        · exact Finset.mem_univ i
      have h1 : 0 ≤ Finset.univ.sum fun j => nonneg_bound j := by
        apply Finset.sum_nonneg
        intro j _
        exact le_of_lt (nonneg_bound_pos j)
      have h2 : 0 ≤ Finset.univ.sum fun i => Finset.univ.sum fun j => if hij : i < j then ordering_bound i j hij else 0 := by
        apply Finset.sum_nonneg
        intro i' _
        apply Finset.sum_nonneg
        intro j' _
        split_ifs with hij
        · exact le_of_lt (ordering_bound_pos i' j' hij)
        · omega
      linarith
    have : x > det_bound i := by omega
    exact h_spec.2 x this


/-
Lemma: Linear Representation with Parameter
For any function f: ℤ/nℤ → ℤ/nℤ, there exists a threshold a₀ such that for any a ≥ a₀,
we can construct a linear representation with multiplier a.

Proof strategy:
1. Use adj_poly_strict_increasing to get x₀ such that for x > x₀, entries are strictly ordered
2. For any a ≥ x₀, we can use x = a to construct the representation
3. Define j(i) = (y a i) mod (m a), where m a = det(aI - A)
4. Use adj_eq to show j(f(i)) = a · j(i) mod m a
5. Injectivity follows from strict ordering of y a i
-/
lemma linear_representation_lemma {n : ℕ} (hn : n > 1) (f : ZMod n → ZMod n) :
  ∃ (a_f : ℕ),
  ∀ (a : ℕ) (_ha : a > a_f),
  ∃ (m : ℕ) (_hm : m > a) (j : ZMod n → ZMod m) (_hj : Function.Injective j),
  let p : ZMod m → ZMod m := fun i => (a * i : ZMod m)
  j ∘ f = p ∘ j := by
    haveI : NeZero n := ⟨by omega⟩
    haveI : Fact (n > 0) := ⟨by omega⟩
    let zmodToFin : ZMod n → Fin n := fun x => ⟨ZMod.val x, ZMod.val_lt x⟩
    have h_increasing := adj_poly_strict_increasing f
    let A := func_matrix f
    let v : Fin n → ℤ := fun i => i.val + 1
    let M := fun (x : ℤ) => (x • (1 : Matrix (Fin n) (Fin n) ℤ) - A).adjugate
    let y := fun (x : ℤ) => M x *ᵥ v
    let m := fun (x : ℤ) => (x • (1 : Matrix (Fin n) (Fin n) ℤ) - A).det
    obtain ⟨x₀, hx₀⟩ := h_increasing
    let p_m : Polynomial ℤ := (charmatrix A).det
    let diff_poly_x := p_m - Polynomial.X
    have h_n_ge_2 : n ≥ 2 := hn
    have h_nontrivial : Nontrivial (Fin n) := by
      rw [Fin.nontrivial_iff_two_le]
      exact h_n_ge_2
    have h_monic : p_m.Monic := charmatrix_det_monic A
    have h_deg : p_m.natDegree = n := by
      rw [charmatrix_det_natDegree A]
      simp [Fintype.card_fin]
    have h_deg_X : (Polynomial.X : Polynomial ℤ).natDegree = 1 := Polynomial.natDegree_X
    have h_deg_diff : diff_poly_x.natDegree = n := by
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
      · exact h_deg
      · rw [h_deg, h_deg_X]
        exact h_n_ge_2
    have h_diff_lead_pos : diff_poly_x.leadingCoeff > 0 := by
      rw [Polynomial.leadingCoeff, h_deg_diff, Polynomial.coeff_sub]
      have h_coeff_pm : p_m.coeff n = 1 := by
        have : p_m.leadingCoeff = 1 := h_monic.leadingCoeff
        rw [Polynomial.leadingCoeff, h_deg] at this
        exact this
      have h_coeff_X : (Polynomial.X : Polynomial ℤ).coeff n = 0 := by
        rw [Polynomial.coeff_X]
        split_ifs with h
        · exfalso
          rw [← h] at h_n_ge_2
          omega
        · rfl
      rw [h_coeff_pm, h_coeff_X]
      norm_num
    have h_bound_nonneg : coeff_bound diff_poly_x ≥ 0 := by
      unfold coeff_bound
      apply Finset.sum_nonneg
      intro i _
      exact abs_nonneg (diff_poly_x.coeff i)
    let a₀_int := max (x₀ + 1) (coeff_bound diff_poly_x + 1)
    have h_a₀_ge_x₀ : a₀_int > x₀ := by
      calc a₀_int ≥ x₀ + 1 := le_max_left _ _
        _ > x₀ := by omega
    have h_a₀_ge_bound : a₀_int > coeff_bound diff_poly_x := by
      calc a₀_int ≥ coeff_bound diff_poly_x + 1 := le_max_right _ _
        _ > coeff_bound diff_poly_x := by omega
    have h_a₀_pos : a₀_int > 0 := by linarith [h_a₀_ge_x₀]
    use (a₀_int - 1).toNat
    intro a ha
    let x : ℤ := a
    have hx : x > x₀ := by
      have h_a_bound : a > ((a₀_int - 1).toNat : ℤ) := by exact_mod_cast ha
      have h_toNat : ((a₀_int - 1).toNat : ℤ) = a₀_int - 1 := by
        apply Int.toNat_of_nonneg
        omega
      calc x = (a : ℤ) := rfl
        _ > ((a₀_int - 1).toNat : ℤ) := h_a_bound
        _ = a₀_int - 1 := h_toNat
        _ ≥ x₀ := by linarith [h_a₀_ge_x₀]
    have ⟨m_pos, h_nonneg, h_strict, h_bound⟩ := hx₀ x hx
    let m_val := m x
    let modulus : ℕ := m_val.natAbs
    have modulus_pos : modulus > 0 := Int.natAbs_pos.mpr (ne_of_gt m_pos)
    have modulus_gt_a : modulus > a := by
      have h_m_gt_x : m_val > x := by
        have h_x_ge_bound : x ≥ coeff_bound diff_poly_x := by
          have h1 : x > a₀_int - 1 := by
            calc x = (a : ℤ) := rfl
              _ > ((a₀_int - 1).toNat : ℤ) := by exact_mod_cast ha
              _ = a₀_int - 1 := by
                apply Int.toNat_of_nonneg
                omega
          linarith [h_a₀_ge_bound]
        have h_eval : diff_poly_x.eval x > 0 := (polynomial_positive diff_poly_x h_diff_lead_pos x h_x_ge_bound).2
        rw [Polynomial.eval_sub, Polynomial.eval_X] at h_eval
        have : p_m.eval x > x := by linarith
        calc m_val = m x := rfl
          _ = (x • (1 : Matrix (Fin n) (Fin n) ℤ) - A).det := rfl
          _ = ((Matrix.scalar (Fin n)) x - A).det := by
            congr 1
            ext i j
            simp [Matrix.scalar]
          _ = p_m.eval x := by
            unfold p_m
            rw [charmatrix_det_eq_charpoly]
            rw [Matrix.eval_charpoly]
          _ > x := this
      omega
    let j : ZMod n → ZMod modulus := fun i =>
      let i_fin := zmodToFin i
      (y x i_fin : ZMod modulus)
    use modulus, modulus_gt_a, j
    have _hj_inj : Function.Injective j := by
      intro i₁ i₂ h_eq
      let i₁_fin := zmodToFin i₁
      let i₂_fin := zmodToFin i₂
      have hy1_nonneg : y x i₁_fin ≥ 0 := h_nonneg i₁_fin
      have hy2_nonneg : y x i₂_fin ≥ 0 := h_nonneg i₂_fin
      have hy1_lt : y x i₁_fin < m_val := h_bound i₁_fin
      have hy2_lt : y x i₂_fin < m_val := h_bound i₂_fin
      have h_y_eq : y x i₁_fin = y x i₂_fin := by
        have h_mod : (modulus : ℤ) = m_val := by
          simp only [modulus]
          omega
        have h1 : 0 ≤ y x i₁_fin := hy1_nonneg
        have h2 : y x i₁_fin < (modulus : ℤ) := by omega
        have h3 : 0 ≤ y x i₂_fin := hy2_nonneg
        have h4 : y x i₂_fin < (modulus : ℤ) := by omega
        have h_emod_eq : y x i₁_fin % (modulus : ℤ) = y x i₂_fin % (modulus : ℤ) := by
          have h_iff := ZMod.intCast_eq_intCast_iff (y x i₁_fin) (y x i₂_fin) modulus
          rw [h_iff] at h_eq
          rw [Int.ModEq] at h_eq
          exact h_eq
        have h1_emod : y x i₁_fin % (modulus : ℤ) = y x i₁_fin := by
          apply Int.emod_eq_of_lt
          · exact h1
          · exact h2
        have h2_emod : y x i₂_fin % (modulus : ℤ) = y x i₂_fin := by
          apply Int.emod_eq_of_lt
          · exact h3
          · exact h4
        calc y x i₁_fin
            = y x i₁_fin % (modulus : ℤ) := h1_emod.symm
          _ = y x i₂_fin % (modulus : ℤ) := h_emod_eq
          _ = y x i₂_fin := h2_emod
      have h_fin_eq : i₁_fin = i₂_fin := by
        by_contra h_ne
        cases' Ne.lt_or_gt h_ne with h_lt h_gt
        · have : y x i₁_fin < y x i₂_fin := h_strict i₁_fin i₂_fin h_lt
          omega
        · have : y x i₂_fin < y x i₁_fin := h_strict i₂_fin i₁_fin h_gt
          omega
      have h_val_eq : ZMod.val i₁ = ZMod.val i₂ := by
        have : i₁_fin.val = i₂_fin.val := congrArg Fin.val h_fin_eq
        simp only [i₁_fin, i₂_fin, zmodToFin] at this
        exact this
      exact ZMod.val_injective n h_val_eq
    use _hj_inj
    funext i
    let i_fin := zmodToFin i
    let fi_fin := zmodToFin (f i)
    have h_adj := adj_eq f x v i_fin
    have h_ifin : (i_fin.val : ZMod n) = i := by
      simp only [i_fin, zmodToFin]
      exact ZMod.natCast_zmod_val i
    have h_fi : ⟨ZMod.val (f (i_fin.val : ZMod n)), ZMod.val_lt _⟩ = fi_fin := by
      simp only [fi_fin, zmodToFin]
      congr 1
      rw [h_ifin]
    have h_y_relation : y x fi_fin = x * y x i_fin - m_val * v i_fin := by
      calc y x fi_fin
          = y x ⟨ZMod.val (f (i_fin.val : ZMod n)), ZMod.val_lt _⟩ := by rw [← h_fi]
        _ = x * y x i_fin - m_val * v i_fin := h_adj
    have h_v_eq : v i_fin = ((i_fin.val : ℤ) + 1) := rfl
    show j (f i) = ((a : ZMod modulus) * j i : ZMod modulus)
    calc j (f i)
        = (y x fi_fin : ZMod modulus) := rfl
      _ = ((x * y x i_fin - m_val * v i_fin) : ZMod modulus) := by
          rw [h_y_relation]
          push_cast
          ring
      _ = ((x * y x i_fin - m_val * (↑↑i_fin + 1)) : ZMod modulus) := by
          rw [h_v_eq]
          norm_cast
      _ = ((x * y x i_fin - (m_val * ↑↑i_fin + m_val)) : ZMod modulus) := by
          congr 1
          ring
      _ = ((x * y x i_fin) : ZMod modulus) - ((m_val * (i_fin.val : ℤ)) : ZMod modulus) - ((m_val : ℤ) : ZMod modulus) := by
          push_cast
          ring
      _ = ((x * y x i_fin) : ZMod modulus) - 0 - 0 := by
          congr 2
          · norm_cast
            refine (ZMod.intCast_zmod_eq_zero_iff_dvd (m_val * ↑↑i_fin) modulus).mpr ?_
            have h_mod_eq : (modulus : ℤ) = m_val := by
              simp only [modulus]
              exact Int.natAbs_of_nonneg (le_of_lt m_pos)
            rw [h_mod_eq]
            exact dvd_mul_right m_val (i_fin.val : ℤ)
          · norm_cast
            refine (ZMod.intCast_zmod_eq_zero_iff_dvd m_val modulus).mpr ?_
            have h_mod_eq : (modulus : ℤ) = m_val := by
              simp only [modulus]
              exact Int.natAbs_of_nonneg (le_of_lt m_pos)
            rw [h_mod_eq]
      _ = ((x * y x i_fin) : ZMod modulus) := by ring
      _ = (a : ZMod modulus) * j i := by simp only [x, j]; norm_cast

/-
Linear Representation Definition
Let f: ℤ/nℤ → ℤ/nℤ be any function. A linear representation of f is an injective function
j: ℤ/nℤ → ℤ/mℤ such that for all i∈ℤ/nℤ,
j(f(i)) = a ⋅ j(i) in ℤ/mℤ,
where m is a positive integer and a is a constant from ℤ/mℤ depending on f.
-/
def has_linear_representation {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) : Prop :=
  ∃ (m : ℕ) (_hm : m > 0) (a : ZMod m) (j : ZMod n → ZMod m),
    Function.Injective j ∧ ∀ i : ZMod n, j (f i) = a * j i

/-
Main Theorem: Linear Representation of Functions
Any function f: ℤ/nℤ → ℤ/nℤ has a linear representation.

Proof strategy:
Use linear_representation_lemma to get a threshold a₀ and construct a representation
with any multiplier a ≥ a₀. We choose a = a₀ to get a specific linear representation.
-/
theorem linear_representation {n : ℕ} [NeZero n] [Fact (n > 0)] (f : ZMod n → ZMod n) :
    has_linear_representation f := by
  by_cases hn : n > 1
  · obtain ⟨a_f, h_lemma⟩ := linear_representation_lemma hn f
    obtain ⟨m, hm, j, hj, h_linear⟩ := h_lemma (a_f + 1) (by omega : a_f + 1 > a_f)
    have hm_pos : m > 0 := by linarith
    use m, hm_pos, ((a_f + 1) : ZMod m), j
    constructor
    · exact hj
    · intro i
      have := congr_fun h_linear i
      simp at this
      exact this
  · have : n = 1 := by
      have h1 : n > 0 := Fact.out
      have h2 : ¬(n > 1) := hn
      omega
    subst this
    use 1, (by norm_num : 1 > 0), (0 : ZMod 1), id
    constructor
    · exact Function.injective_id
    · intro i
      have : i = 0 := Subsingleton.elim i 0
      have : f 0 = 0 := Subsingleton.elim (f 0) 0
      simp [‹i = 0›, this]

/-
## Explicit Example: Quadratic Function in ℤ/3ℤ

We compute an explicit linear representation for f(x) = x² in ℤ/3ℤ.

Given: f(0)=0, f(1)=1, f(2)=1 (since 2²=4≡1 mod 3)

Step 1: Adjacency matrix A
  A[i,j] = 1 if f(i)=j, else 0
  A = [[1, 0, 0],   (f(0)=0)
       [0, 1, 0],   (f(1)=1)
       [0, 1, 0]]   (f(2)=1)

Step 2: Form M(x) = xI - A as a polynomial matrix
  M(x) = [[x-1, 0, 0],
          [0, x-1, 0],
          [0, -1, x]]

Step 3: Compute characteristic polynomial m(x) = det(M(x))
  m(x) = det([[x-1,0,0], [0,x-1,0], [0,-1,x]])
       = (x-1) · det([[x-1,0], [-1,x]])
       = (x-1) · [(x-1)·x - 0·(-1)]
       = (x-1) · x · (x-1)
       = (x-1)² · x
       = x³ - 2x² + x

Step 4: Compute adjugate matrix adj(M(x)) as polynomial matrix
  adj(M(x)) = [[x(x-1), 0, 0],
               [0, x(x-1), 0],
               [0, (x-1), (x-1)²]]

Step 5: Choose v = (1, 2, 3)ᵀ, compute y(x) = adj(M(x)) · v as polynomials
  y₀(x) = x(x-1)·1 = x² - x
  y₁(x) = x(x-1)·2 = 2x² - 2x
  y₂(x) = (x-1)·2 + (x-1)²·3 = 2(x-1) + 3(x-1)² = (x-1)(2 + 3(x-1)) = (x-1)(3x-1)

Step 6: Verify polynomial properties
  - y₀(x) = x² - x = x(x-1)
  - y₁(x) = 2x² - 2x = 2x(x-1)
  - y₂(x) = (x-1)(3x-1)
  - For x ≥ 4: 0 < y₀(x) < y₁(x) < y₂(x) < m(x)

Step 7: Evaluate at x = 4
  - m = m(4) = 4³ - 2·4² + 4 = 64 - 32 + 4 = 36
  - y₀ = y₀(4) = 4² - 4 = 12
  - y₁ = y₁(4) = 2·4² - 2·4 = 32 - 8 = 24
  - y₂ = y₂(4) = (4-1)(3·4-1) = 3·11 = 33

  Indeed: 0 < 12 < 24 < 33 < 36 ✓

Step 8: Define linear representation
  - m = 36 (the modulus)
  - a = 4 (the multiplier)
  - j: ℤ/3ℤ → ℤ/36ℤ given by j(0)=12, j(1)=24, j(2)=33

Step 9: Verify j(f(i)) = a · j(i) mod m
  - j(f(0)) = j(0) = 12 = 4·12 mod 36 (48 = 36 + 12) ✓
  - j(f(1)) = j(1) = 24 = 4·24 mod 36 (96 = 2·36 + 24) ✓
  - j(f(2)) = j(1) = 24 = 4·33 mod 36 (132 = 3·36 + 24) ✓

Note: With v = (1,2,3) instead of v = (0,1,2), all coordinates are now positive
and strictly increasing, eliminating edge cases in the proof.
-/
example : ∃ (A : Matrix (Fin 3) (Fin 3) ℤ) (x : ℤ) (M : Matrix (Fin 3) (Fin 3) ℤ)
    (m : ℤ) (adj_M : Matrix (Fin 3) (Fin 3) ℤ) (v : Fin 3 → ℤ) (y : Fin 3 → ℤ),
    let f : ZMod 3 → ZMod 3 := fun x => x^2
    -- A is the adjacency matrix of f
    A = func_matrix f ∧
    -- M = xI - A with x = 4
    x = 4 ∧
    M = x • (1 : Matrix (Fin 3) (Fin 3) ℤ) - A ∧
    -- m is the determinant
    m = M.det ∧
    m = 36 ∧
    -- adj_M is the adjugate
    adj_M = M.adjugate ∧
    -- v and y are as computed (using v = (1,2,3))
    v = ![1, 2, 3] ∧
    y = adj_M *ᵥ v ∧
    y = ![12, 24, 33] ∧
    -- This gives a linear representation
    (let zmodToFin : ZMod 3 → Fin 3 := fun x => ⟨ZMod.val x, ZMod.val_lt x⟩
     let j : ZMod 3 → ZMod 36 := fun i => (y (zmodToFin i) : ZMod 36)
     let a : ZMod 36 := 4
     Function.Injective j ∧ ∀ i : ZMod 3, j (f i) = a * j i) := by
  let f : ZMod 3 → ZMod 3 := fun x => x^2
  let zmodToFin : ZMod 3 → Fin 3 := fun x => ⟨ZMod.val x, ZMod.val_lt x⟩

  -- Define all the components
  let A := func_matrix f
  let x : ℤ := 4
  let M := x • (1 : Matrix (Fin 3) (Fin 3) ℤ) - A
  let m := M.det
  let adj_M := M.adjugate
  let v : Fin 3 → ℤ := ![1, 2, 3]
  let y := adj_M *ᵥ v

  use A, x, M, m, adj_M, v, y

  constructor; · rfl  -- A = func_matrix f
  constructor; · rfl  -- x = 4
  constructor; · rfl  -- M = xI - A
  constructor; · rfl  -- m = M.det
  constructor
  · -- m = 36
    decide
  constructor; · rfl  -- adj_M = M.adjugate
  constructor; · rfl  -- v = ![1,2,3]
  constructor; · rfl  -- y = adj_M *ᵥ v
  constructor
  · -- y = ![12, 24, 33]
    decide
  -- Prove the linear representation property
  let j : ZMod 3 → ZMod 36 := fun i => (y (zmodToFin i) : ZMod 36)
  let a : ZMod 36 := 4

  constructor
  · -- Injectivity: j(0)=12, j(1)=24, j(2)=33 are distinct mod 36
    decide
  · -- Linear relation: j(f(i)) = a · j(i) mod 36
    intro i
    -- We need to check all three cases: i = 0, 1, 2
    -- f(0) = 0, f(1) = 1, f(2) = 1
    -- j(0) = 12, j(1) = 24, j(2) = 33
    -- a = 4
    -- Check: j(f(0)) = j(0) = 12 = 4·12 mod 36 = 48 mod 36 = 12 ✓
    -- Check: j(f(1)) = j(1) = 24 = 4·24 mod 36 = 96 mod 36 = 24 ✓
    -- Check: j(f(2)) = j(1) = 24 = 4·33 mod 36 = 132 mod 36 = 24 ✓
    fin_cases i <;> decide
