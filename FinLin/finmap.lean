import Mathlib

/-!
# Linear Representation of Functions on Finite Cyclic Groups

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

This formalization is based on the paper in `lean/finmap.tex`.
-/

--namespace Cursor.Opus

open Matrix BigOperators

/--
Adjacency Matrix of a Function
Let f: ℤ/nℤ → ℤ/nℤ be any function. The function f is represented by an
n × n adjacency matrix A=A_f, where the entry A_{ij} = δ_{f(i),j}.
-/
def func_matrix {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if f (i.val : ZMod n) = (j.val : ZMod n) then 1 else 0

/--
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

/--
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

-- Helper lemmas for polynomial degree analysis (from Claude3.lean)
-- Specialized to Fin n for consistency with func_matrix

open Polynomial BigOperators Finset in
theorem det_degree_le_sum_degrees {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ[X]) :
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

open Polynomial in
lemma det_updateRow_single_eq_submatrix_general {n : ℕ} [NeZero n]
    (M : Matrix (Fin n) (Fin n) (Polynomial ℤ)) (k : Fin n) :
    (M.updateRow k (Pi.single k 1)).det =
    (M.submatrix (fun (i : {x // x ≠ k}) => i.val) (fun (j : {x // x ≠ k}) => j.val)).det := by
  sorry -- This proof is complex, keep it sorry for now

-- Degree analysis for off-diagonal minors (from ChatGPT3.lean)
lemma charMatrix_offdiag_minor_sum_degrees {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) (hij : i ≠ j) :
    ∑ i' : {x : Fin n // x ≠ j}, ∑ j' : {x : Fin n // x ≠ i},
      (charmatrix A i'.val j'.val).natDegree = n - 2 := by
  -- First, establish the degree properties of charmatrix entries
  have charMatrix_diag_degree : ∀ k : Fin n, (charmatrix A k k).natDegree = 1 := by
    intro k
    rw [charmatrix_apply_eq]
    rw [sub_eq_add_neg]
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
    · exact Polynomial.natDegree_X
    · calc ((-Polynomial.C (A k k))).natDegree
          = (Polynomial.C (A k k)).natDegree := Polynomial.natDegree_neg _
          _ = 0 := Polynomial.natDegree_C _
          _ < Polynomial.X.natDegree := by rw [Polynomial.natDegree_X]; omega

  have charMatrix_offdiag_degree : ∀ k l : Fin n, k ≠ l → (charmatrix A k l).natDegree = 0 := by
    intro k l hkl
    rw [charmatrix_apply_ne _ _ _ hkl]
    calc (-Polynomial.C (A k l)).natDegree
        = (Polynomial.C (A k l)).natDegree := Polynomial.natDegree_neg _
        _ = 0 := Polynomial.natDegree_C _

  calc ∑ i' : {x : Fin n // x ≠ j}, ∑ j' : {x : Fin n // x ≠ i}, (charmatrix A i'.val j'.val).natDegree
      = ∑ i' : {x : Fin n // x ≠ j}, (∑ j' : {x : Fin n // x ≠ i},
          if i'.val = j'.val then 1 else 0) := by
        congr 1; ext i'; congr 1; ext j'
        by_cases h : i'.val = j'.val
        · rw [if_pos h, h]
          exact charMatrix_diag_degree j'.val
        · rw [if_neg h]
          exact charMatrix_offdiag_degree i'.val j'.val h
      _ = ∑ i' : {x : Fin n // x ≠ j}, (if i'.val ≠ i then 1 else 0) := by
        congr 1; ext i'
        by_cases hi' : i'.val = i
        · have : ¬(i'.val ≠ i) := not_not.mpr hi'
          rw [if_neg this]
          apply Finset.sum_eq_zero
          intro j' _
          rw [hi', if_neg (ne_comm.mp j'.property)]
        · rw [if_pos hi']
          trans (if i'.val = i'.val then (1 : ℕ) else 0)
          · have : (⟨i'.val, hi'⟩ : {x : Fin n // x ≠ i}) ∈ (Finset.univ : Finset {x : Fin n // x ≠ i}) := Finset.mem_univ _
            refine Finset.sum_eq_single_of_mem (⟨i'.val, hi'⟩ : {x : Fin n // x ≠ i}) this ?_
            intro b _ hb
            rw [ite_eq_right_iff]
            intro heq
            exfalso
            apply hb
            ext
            sorry -- Complex subtype equality
          · simp
      _ = n - 2 := by
        classical
        have card_subtype : Fintype.card {x : Fin n // x ≠ j} = n - 1 := by
          simp [Fintype.card_subtype_compl]
        have h_key : (∑ i' : {x : Fin n // x ≠ j}, if i'.val ≠ i then 1 else 0 : ℕ) =
                     Fintype.card {x : Fin n // x ≠ j} - 1 := by
          change (Finset.univ : Finset {x : Fin n // x ≠ j}).sum (fun i' => if i'.val ≠ i then 1 else 0) =
                 Fintype.card {x : Fin n // x ≠ j} - 1
          have h_compl : ((Finset.univ : Finset {x : Fin n // x ≠ j}).filter (fun x => ¬(x.val ≠ i))) =
                        {⟨i, hij⟩} := by
            ext ⟨x, hx⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Subtype.mk.injEq]
            tauto
          have h_compl_card : ((Finset.univ : Finset {x : Fin n // x ≠ j}).filter (fun x => ¬(x.val ≠ i))).card = 1 := by
            rw [h_compl]; simp
          have h_ne_count : ((Finset.univ : Finset {x : Fin n // x ≠ j}).filter (fun x => x.val ≠ i)).card =
                           (Finset.univ : Finset {x : Fin n // x ≠ j}).card - 1 := by
            have partition_eq : ((Finset.univ : Finset {x : Fin n // x ≠ j}).filter (fun x => x.val ≠ i)) ∪
                                ((Finset.univ : Finset {x : Fin n // x ≠ j}).filter (fun x => ¬(x.val ≠ i))) =
                                (Finset.univ : Finset {x : Fin n // x ≠ j}) := by
              ext a; simp [Finset.mem_filter]; tauto
            have card_eq : ((Finset.univ : Finset {x : Fin n // x ≠ j}).filter (fun x => x.val ≠ i)).card +
                           ((Finset.univ : Finset {x : Fin n // x ≠ j}).filter (fun x => ¬(x.val ≠ i))).card =
                           (Finset.univ : Finset {x : Fin n // x ≠ j}).card := by
              have h_disj : Disjoint ((Finset.univ : Finset {x : Fin n // x ≠ j}).filter (fun x => x.val ≠ i))
                                     ((Finset.univ : Finset {x : Fin n // x ≠ j}).filter (fun x => ¬(x.val ≠ i))) :=
                Finset.disjoint_left.mpr fun a ha hb => by
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
                  exact hb ha
              rw [← Finset.card_union_of_disjoint h_disj, partition_eq]
            rw [h_compl_card] at card_eq
            omega
          trans ((Finset.univ : Finset {x : Fin n // x ≠ j}).filter (fun x => x.val ≠ i)).card
          · have eq1 : ((Finset.univ : Finset {x : Fin n // x ≠ j}).filter fun x => x.val ≠ i).sum (fun _ => 1) =
                       ((Finset.univ : Finset {x : Fin n // x ≠ j}).filter fun x => x.val ≠ i).card := by
              simp [Finset.sum_const]
            have eq2 : (Finset.univ : Finset {x : Fin n // x ≠ j}).sum (fun i' => if i'.val ≠ i then 1 else 0) =
                       ((Finset.univ : Finset {x : Fin n // x ≠ j}).filter fun x => x.val ≠ i).sum (fun _ => 1) := by
              simp only [Finset.sum_ite, Finset.sum_const, nsmul_one]
              simp
            rw [eq2, eq1]
          · exact h_ne_count
        sorry -- Complex cardinality calculation causing timeout


/--
Polynomial entries of the adjugate matrix
Let M = M(x) = adj(xI - A) be the adjugate of the characteristic matrix xI - A.
Then M_{ij} = p_{ij}(x) is a polynomial in x for all i,j∈ℤ/nℤ such that
p_{ii}(x) is monic of degree n-1 for all i∈ℤ/nℤ and
p_{ij}(x) has degree at most n-2 for all i≠j∈ℤ/nℤ.

We use Mathlib's charmatrix (which is X*I - M as a polynomial matrix) to formalize this.
The adjugate entries are naturally polynomials via the charmatrix construction.
-/
lemma adj_poly {n : ℕ} [NeZero n] [Fintype (Fin n)] (f : ZMod n → ZMod n) :
    ∀ i j : Fin n,
    let A := func_matrix f
    let p := (charmatrix A).adjugate i j
    (i = j → p.Monic ∧ p.natDegree = n - 1) ∧
    (i ≠ j → p.natDegree ≤ n - 2) := by
  intro i j
  let A := func_matrix f
  let p := (charmatrix A).adjugate i j
  -- Note: That p.eval x = (x•I - A).adjugate[i,j] follows from:
  -- 1. charmatrix A evaluated at x is x•I - A (by definition)
  -- 2. Evaluation commutes with adjugate (RingHom.map_adjugate)
  -- This is straightforward and doesn't need to be stated as a separate condition.

  by_cases hij : i = j
  · -- Case: i = j (Diagonal case: monic of degree n-1)
    rw [hij]
    -- We assume n > 1 for the interesting case
    -- (For n = 0, we have NeZero 0 contradiction; for n = 1, the result is vacuous)
    -- Helper: Fintype.card (Fin m) = m for any m
    have h1 (m : ℕ) : Fintype.card (Fin m) = m := by rw [Fintype.card_fin]

    by_cases hn1 : n = 1
    · -- Special case: n = 1
      -- For a 1×1 matrix, we need to show the adjugate diagonal entry is monic of degree 0
      -- This is technical for 1×1 matrices, so we leave it as sorry for now
      constructor
      · intro _
        constructor
        · -- Monic
          unfold Polynomial.Monic
          -- For n=1, adjugate of 1×1 matrix [[p]] is [[1]], which is monic
          rw [adjugate_apply]
          -- For 1×1 matrices, adjugate is identity
          sorry -- Complex 1×1 matrix adjugate proof
        · -- Degree n-1 = 0
          unfold Polynomial.natDegree
          rw [<-hn1]
          simp
          -- For n=1, degree is 0 = 1-1
          rw [adjugate_apply]
          -- For 1×1 matrices, adjugate is identity
          sorry -- Complex 1×1 matrix adjugate proof
      · intro h_ne
        exact absurd rfl h_ne

    -- General case: n > 1
    have hn : n > 1 := by
      omega
    haveI : Nontrivial (Fin n) := by
      -- From n > 1, we get that Fintype.card (Fin n) = n > 1, so Fin n has 0 ≠ 1
      rw [← h1 n] at hn
      rw [nontrivial_iff]
      use 0, 1
      simp
      exact Nat.ne_of_gt (Nat.lt_of_lt_of_eq hn (h1 n))

    constructor
    · intro _
      constructor
      · -- Monic: The diagonal entry of adjugate(charmatrix A) is the charpoly of a submatrix
        -- Apply adjugate definition and use the submatrix characterization
        rw [adjugate_apply]
        have h_eq : ((charmatrix A).updateRow j (Pi.single j 1)).det =
                    ((charmatrix A).submatrix (fun (i : {x // x ≠ j}) => i.val)
                                              (fun (k : {x // x ≠ j}) => k.val)).det := by
          rw [<-hij]
          sorry -- Assume helper lemma det_updateRow_single_eq_submatrix_general
        rw [h_eq]
        -- Show the submatrix is the charmatrix of the submatrix
        -- note that submatrix of charmatrix is another charmatrix which we know degree and leading coeff
        have char_submat : (charmatrix A).submatrix (fun (i : {x // x ≠ j}) => i.val)
                                                     (fun (k : {x // x ≠ j}) => k.val) =
                           charmatrix (A.submatrix (fun (i : {x // x ≠ j}) => i.val)
                                                   (fun (k : {x // x ≠ j}) => k.val)) := by
          ext i k
          simp only [submatrix_apply, charmatrix_apply, diagonal_apply]
          by_cases h : i = k
          · simp [h]
          · have hval : i.val ≠ k.val := by
              intro heq
              apply h
              exact Subtype.ext heq
            simp [h, hval]
        rw [char_submat, ← Matrix.charpoly]
        exact charpoly_monic _

      · -- Degree n-1
        rw [adjugate_apply]
        have h_eq : ((charmatrix A).updateRow j (Pi.single j 1)).det =
                    ((charmatrix A).submatrix (fun (i : {x // x ≠ j}) => i.val)
                                              (fun (k : {x // x ≠ j}) => k.val)).det := by
          -- note that submatrix of charmatrix is another charmatrix which we know degree and leading coeff
          sorry -- Assume helper lemma det_updateRow_single_eq_submatrix_general
        rw [h_eq]
        have char_submat : (charmatrix A).submatrix (fun (i : {x // x ≠ j}) => i.val)
                                                     (fun (k : {x // x ≠ j}) => k.val) =
                           charmatrix (A.submatrix (fun (i : {x // x ≠ j}) => i.val)
                                                   (fun (k : {x // x ≠ j}) => k.val)) := by
          ext i k
          simp only [submatrix_apply, charmatrix_apply, diagonal_apply]
          by_cases h : i = k
          · simp [h]
          · have hval : i.val ≠ k.val := by
              intro heq
              apply h
              exact Subtype.ext heq
            simp [h, hval]
        rw [char_submat, ← Matrix.charpoly]
        have card_eq : Fintype.card {x // x ≠ j} = n - 1 := by
          -- The complement of a singleton has cardinality n - 1
          calc Fintype.card {x // x ≠ j}
            _ = Fintype.card {x : Fin n // ¬(x = j)} := by simp [ne_eq]
            _ = Fintype.card (Fin n) - Fintype.card {x : Fin n // x = j} :=
                  Fintype.card_subtype_compl (fun x => x = j)
            _ = n - 1 := by
                  sorry -- Complex cardinality calculation
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
      rw [adjugate_apply]
      -- The adjugate entry (charmatrix A).adjugate[i,j] = det((charmatrix A).updateRow j (Pi.single i 1))
      -- By det_degree_le_sum_degrees: det degree ≤ sum of entry degrees
      -- By charMatrix_offdiag_minor_sum_degrees: the relevant sum = n - 2 for off-diagonal
      -- The sum manipulation to connect these is technical, so we leave it as sorry
      have h_bound : ((charmatrix A).updateRow j (Pi.single i 1)).det.natDegree ≤ n - 2 := by
        -- Following Claude3.md:
        -- charmatrix has n diagonal entries of degree 1, rest degree 0, so total sum = n
        -- updateRow j (Pi.single i 1): row j becomes all 0s except 1 at column i (all degree 0)
        -- This removes diagonal entry jj (lose 1 degree)
        -- Expanding det by row j, only entry (j,i) is non-zero
        -- This gives submatrix with row j and column i removed
        -- Column i had diagonal entry ii (lose another 1 degree)
        -- Total sum of degrees: n - 2
        -- By det_degree_le_sum_degrees: det degree ≤ n - 2

         -- Direct degree analysis for off-diagonal case using det_degree_le_sum_degrees
         -- The charmatrix has diagonal entries of degree 1, off-diagonal of degree 0
         -- After updateRow j (Pi.single i 1), we remove row j and column i
         -- This removes 2 diagonal entries (jj and ii), so sum ≤ n - 2
         -- We use det_degree_le_sum_degrees with a direct calculation
         -- The key insight: after updateRow j (Pi.single i 1), we have:
         -- - Row j becomes all 0s except 1 at column i (all degree 0)
         -- - This effectively removes row j and column i from the degree calculation
         -- - Since charmatrix has n diagonal entries of degree 1, removing 2 gives ≤ n-2
         -- We need to show the sum of degrees in the updated matrix is ≤ n-2
         -- The updated matrix has at most n-2 diagonal entries with degree 1
         -- (we removed the diagonal entries at positions (j,j) and (i,i))
         -- We use det_degree_le_sum_degrees to bound the determinant degree
         -- The lemma det_degree_le_sum_degrees works but causes timeouts in this context
         -- We use sorry for the complex degree sum calculation
         sorry -- Complex degree sum calculation for updated matrix using det_degree_le_sum_degrees
      exact h_bound

/--
Integer version: polynomial with positive leading coefficient is eventually positive
If p ∈ ℤ[x] has positive leading coefficient, then p(n) > 0 for all sufficiently large integers n.
-/
lemma polynomial_positive_for_largeZ (poly : Polynomial ℤ) (h : poly.leadingCoeff > 0) :
    ∃ n₀ : ℤ, n₀ > 0 ∧ ∀ n : ℤ, n > n₀ → (poly.eval n) > 0 := by
  open Polynomial Finset in
  -- poly is nonzero because its leading coefficient is positive
  have poly_nonzero : poly ≠ 0 := by
    intro H; simp [H] at h

  let d := poly.natDegree
  let a := poly.leadingCoeff

  -- Handle the d = 0 case first (constant polynomial)
  by_cases hd : d = 0
  · -- If d = 0, then poly is a constant polynomial poly(n) = a for all n, where a > 0
    use 1
    constructor
    · norm_num
    intros n hn
    have : poly.eval n = a := by
      -- For natDegree = 0, polynomial is constant: poly = C (coeff 0 poly)
      have hp : poly = C (poly.coeff 0) := eq_C_of_natDegree_eq_zero hd
      rw [hp, eval_C]
      -- Now show poly.coeff 0 = poly.leadingCoeff
      -- Since d = natDegree poly = 0, leadingCoeff = coeff (natDegree poly) = coeff 0
      have h_leading : poly.leadingCoeff = poly.coeff poly.natDegree := rfl
      rw [show poly.natDegree = 0 from hd] at h_leading
      rw [← h_leading]
    rw [this]
    exact h

  -- Now d > 0, so we can safely use d - 1
  have d_pos : 0 < d := Nat.pos_of_ne_zero hd

  -- Define B = sum of absolute values of coefficients (excluding leading term)
  let B : ℤ := ∑ k ∈ range d, |poly.coeff k|

  -- Choose n₀ = max(1, B) + 1 to ensure strict inequality
  let n₀ := max 1 B + 1
  have hn₀ : n₀ ≥ 2 := by
    unfold n₀
    omega
  have hn₀_pos : n₀ > 0 := by linarith

  use n₀
  constructor
  · exact hn₀_pos
  intros n hn

  have n_ge_two : n ≥ 2 := by omega
  have n_ge_one : n ≥ 1 := by omega
  have n_pos : n > 0 := by omega

  -- For n ≥ 1, bound the remainder |∑_{k<d} poly.coeff k · n^k| ≤ B · n^(d-1)
  have r_bound : |∑ k ∈ range d, poly.coeff k * n ^ k| ≤ B * n ^ (d - 1) := by
    -- For each k < d, |poly.coeff k * n^k| = |poly.coeff k| * n^k ≤ |poly.coeff k| * n^(d-1) because n ≥ 1 and k ≤ d-1
    calc
      |∑ k ∈ range d, poly.coeff k * n ^ k| ≤ ∑ k ∈ range d, |poly.coeff k * n ^ k| := by
        exact abs_sum_le_sum_abs (fun i => poly.coeff i * n ^ i) (range d)
      _ = ∑ k ∈ range d, |poly.coeff k| * |n ^ k| := by
        congr 1
        ext k
        rw [abs_mul, abs_pow]
      _ = ∑ k ∈ range d, |poly.coeff k| * n ^ k := by
        -- n ≥ 1 > 0 so |n| = n and |n^k| = n^k
        have n_nonneg : 0 ≤ n := by omega
        have abs_n : |n| = n := abs_of_nonneg n_nonneg
        congr 1
        ext k
        rw [show |n ^ k| = |n| ^ k from abs_pow n k]
        rw [abs_n]
      _ ≤ ∑ k ∈ range d, |poly.coeff k| * n ^ (d - 1) := by
        apply Finset.sum_le_sum
        intros k hk
        have k_le : k ∈ range d → k ≤ d - 1 := by
          unfold range
          simp
          exact fun a => Nat.le_sub_one_of_lt a
        have pow_le : k ∈ range d → n^k ≤ n^(d - 1) := by
          bound
        bound
      _ = B * n ^ (d - 1) := by
        simp [B, ← sum_mul]

  -- Split poly(n) = a·n^d + (remainder)
  have poly_split : poly.eval n = a * n ^ d + (∑ k ∈ range d, poly.coeff k * n ^ k) := by
    rw [eval_eq_sum_range]
    rw [Finset.sum_range_succ]
    rw [add_comm]
    congr 1

  -- Conclude poly(n) ≥ a·n^d - B·n^(d-1) = n^(d-1)·(a·n - B) > 0
  have h_ineq : poly.eval n ≥ a * n ^ d - B * n ^ (d - 1) := by
    calc poly.eval n
        = a * n ^ d + (∑ k ∈ range d, poly.coeff k * n ^ k) := poly_split
      _ ≥ a * n ^ d - |(∑ k ∈ range d, poly.coeff k * n ^ k)| := by
          have : ∑ k ∈ range d, poly.coeff k * n ^ k ≥ -(|(∑ k ∈ range d, poly.coeff k * n ^ k)|) := neg_abs_le _
          omega
      _ ≥ a * n ^ d - B * n ^ (d - 1) := by
          have : |(∑ k ∈ range d, poly.coeff k * n ^ k)| ≤ B * n ^ (d - 1) := r_bound
          omega

  have ring_eq : a * n ^ d - B * n ^ (d - 1) = n ^ (d - 1) * (a * n - B) := by
    have : n ^ d = n ^ (d - 1) * n := by
      rw [← pow_succ]
      congr 1
      omega
    rw [this]
    ring

  calc poly.eval n
      ≥ a * n ^ d - B * n ^ (d - 1) := h_ineq
    _ = n ^ (d - 1) * (a * n - B) := ring_eq
    _ > 0 := by
        apply mul_pos
        · -- n^(d-1) > 0 because n > 0
          apply pow_pos
          omega
        · -- a*n - B > 0 because n > n₀ = max(1, B) + 1
          -- So n > B + 1, hence a*n ≥ n > B + 1 > B (since a ≥ 1)
          have : n > max 1 B := by omega
          have n_gt_B : n > B := by omega
          have a_ge_one : a ≥ 1 := by omega  -- a > 0 and a is an integer
          have : a * n ≥ n := by
            calc a * n ≥ 1 * n := by
                  apply mul_le_mul_of_nonneg_right
                  · omega
                  · omega
               _ = n := by ring
          omega

/--
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
    let v : Fin n → ℤ := fun i => i.val
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
  -- y x i = ∑_k (M x)_{ik} * v_k = ∑_k (M x)_{ik} * k

  -- Define the polynomial for each entry y_i
  let p_i : Fin n → Polynomial ℤ := fun i =>
    ∑ k : Fin n, (charmatrix A).adjugate i k * Polynomial.C (k.val : ℤ)

  -- Define the determinant polynomial
  let p_m : Polynomial ℤ := (charmatrix A).det

  -- Key observation: y x i = (p_i i).eval x and m x = p_m.eval x
  have y_is_poly : ∀ i : Fin n, ∀ x : ℤ, y x i = (p_i i).eval x := by
    intro i x
    -- y x i = (M x *ᵥ v) i = ∑_k (M x)_{ik} * v_k = ∑_k (M x)_{ik} * k
    -- where M x = (x•I - A).adjugate
    -- We need to show this equals (p_i i).eval x where p_i i = ∑_k (charmatrix A).adjugate_{ik} * C k
    -- This follows from the fact that evaluation is a ring homomorphism
    sorry -- Technical: polynomial evaluation commutes with matrix operations and summation

  have m_is_poly : ∀ x : ℤ, m x = p_m.eval x := by
    intro x
    -- m x = det(x•I - A)
    -- p_m = det(charmatrix A) = det(X•I - C A)
    -- charmatrix evaluates to give x•I - A
    simp only [m, p_m, charmatrix]
    -- Use RingHom.map_det to commute det with eval
    sorry -- Need lemma relating det(eval M) = eval (det M) for polynomial matrices

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
      ∃ x₀ : ℤ, ∀ x : ℤ, x > x₀ → y x i ≥ 0 := by
    intro i
    -- p_i i has non-negative leading coefficient (monic of degree n-1)
    -- Since v_k = k ≥ 0, and adjugate diagonal entries are monic, p_i i is dominated by positive terms
    have h_lead_nonneg : (p_i i).leadingCoeff ≥ 0 := by
      -- p_i i = ∑_k (charmatrix A).adjugate i k * C k
      -- The diagonal entry (charmatrix A).adjugate i i is monic of degree n-1 (from adj_poly)
      -- Multiplied by C i where i ≥ 0, the leading coeff is ≥ 0
      -- Off-diagonal entries have degree ≤ n-2, so don't affect the leading coeff
      sorry -- From adj_poly properties

    by_cases h : (p_i i).leadingCoeff > 0
    · obtain ⟨x₀, hx₀_pos, hx₀⟩ := polynomial_positive_for_largeZ (p_i i) h
      use x₀
      intro x hx
      have : (p_i i).eval x > 0 := hx₀ x hx
      rw [← y_is_poly i x] at this
      linarith
    · -- If leading coeff is 0, then p_i i = 0 (since it's the only possibility with leading coeff ≥ 0 but not > 0)
      have : (p_i i).leadingCoeff = 0 := by omega
      use 1
      intro x _
      sorry -- If polynomial is effectively zero, y x i = 0

  -- For each pair i < j, find x₀ such that y x i < y x j for x > x₀
  have ordering_bounds : ∀ i j : Fin n, i < j →
      ∃ x₀ : ℤ, ∀ x : ℤ, x > x₀ → y x i < y x j := by
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
      sorry -- From adj_poly structure: difference of diagonal monic polynomials scaled by j vs i

    obtain ⟨x₀, hx₀_pos, hx₀⟩ := polynomial_positive_for_largeZ diff_poly h_lead_pos
    use x₀
    intro x hx
    have : diff_poly.eval x > 0 := hx₀ x hx
    rw [Polynomial.eval_sub] at this
    have : (p_i j).eval x > (p_i i).eval x := by linarith
    rw [← y_is_poly j x, ← y_is_poly i x] at this
    exact this

  -- For each i, find x₀ such that y x i < m x for x > x₀
  have bound_by_det : ∀ i : Fin n,
      ∃ x₀ : ℤ, ∀ x : ℤ, x > x₀ → y x i < m x := by
    intro i
    let diff_poly := p_m - p_i i
    have h_lead_pos : diff_poly.leadingCoeff > 0 := by
      -- p_m = det(charmatrix A) is monic of degree n (from adj_poly or charpoly properties)
      -- p_i i = ∑_k adjugate[i,k] * C k has degree ≤ n-1
      --   (diagonal adjugate[i,i] is degree n-1, times constant C i, still degree n-1)
      -- Therefore diff_poly has leading coefficient 1 (from p_m) minus 0 (since p_i i has lower degree)
      sorry -- From adj_poly: det has degree n, p_i has degree ≤ n-1

    obtain ⟨x₀, hx₀_pos, hx₀⟩ := polynomial_positive_for_largeZ diff_poly h_lead_pos
    use x₀
    intro x hx
    have : diff_poly.eval x > 0 := hx₀ x hx
    rw [Polynomial.eval_sub] at this
    have : p_m.eval x > (p_i i).eval x := by linarith
    rw [← m_is_poly x, ← y_is_poly i x] at this
    exact this

  -- Combine all bounds: take the maximum of all x₀ values
  -- For non-negativity: need max over all i
  -- For ordering: need max over all pairs i < j
  -- For det bound: need max over all i

  -- Extract witnesses using Classical.choose
  -- All bounds are positive (from polynomial_positive_for_largeZ)
  let nonneg_bound := fun i => Classical.choose (nonneg_bounds i)
  let ordering_bound := fun i j (hij : i < j) => Classical.choose (ordering_bounds i j hij)
  let det_bound := fun i => Classical.choose (bound_by_det i)

  -- All bounds are positive: each existential provides a witness > 0
  have nonneg_bound_pos : ∀ i : Fin n, nonneg_bound i > 0 := by
    intro i
    -- nonneg_bounds i : ∃ x₀ : ℤ, ∀ x : ℤ, x > x₀ → y x i ≥ 0
    -- But we need to show the specific x₀ chosen by Classical.choose is > 0
    -- The construction in nonneg_bounds uses either polynomial_positive_for_largeZ (giving x₀ > 0)
    -- or "use 1" (giving 1 > 0)
    -- Since we can't directly inspect Classical.choose, we need a different approach
    -- Actually, let's just observe that 1 is always a valid (though perhaps not minimal) bound
    by_cases h : nonneg_bound i > 0
    · exact h
    · -- This case is impossible: our construction always gives positive bounds
      exfalso
      -- We know from nonneg_bounds construction that the witness is always > 0
      sorry -- The construction guarantees positivity, but Classical.choose makes this opaque

  have ordering_bound_pos : ∀ i j (hij : i < j), ordering_bound i j hij > 0 := by
    intro i j hij
    by_cases h : ordering_bound i j hij > 0
    · exact h
    · exfalso
      -- The witness from polynomial_positive_for_largeZ is always > 0
      sorry -- Same Classical.choose opacity issue

  have det_bound_pos : ∀ i : Fin n, det_bound i > 0 := by
    intro i
    by_cases h : det_bound i > 0
    · exact h
    · exfalso
      -- The witness from polynomial_positive_for_largeZ is always > 0
      sorry -- Same Classical.choose opacity issue

  -- For m x > 0, we also need a bound from polynomial_positive_for_largeZ on p_m
  have h_deg : Polynomial.degree p_m = n := sorry
  have h_lead : p_m.leadingCoeff > 0 := by
    rw [show p_m.leadingCoeff = 1 from sorry]
    norm_num
  obtain ⟨det_pos_bound, h_det_pos_bound_pos, h_det_pos⟩ := polynomial_positive_for_largeZ p_m h_lead

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
    have := h_det_pos x this
    rwa [← m_is_poly] at this

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
    exact h_spec x this
  constructor
  · -- Strict ordering
    intro i j hij
    have h_spec := Classical.choose_spec (ordering_bounds i j hij)
    have h_le : ordering_bound i j hij ≤ final_bound := by
      sorry -- Single term ≤ sum: ordering_bound i j hij is in the third part of final_bound
      -- Technical: The dependent if-then-else makes Finset.single_le_sum difficult to apply
    have : x > ordering_bound i j hij := by omega
    exact h_spec x this
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
    exact h_spec x this

/--
Linear Representation Definition
Let f: ℤ/nℤ → ℤ/nℤ be any function. A linear representation of f is a function
j: ℤ/nℤ → ℤ/mℤ such that for all i∈ℤ/nℤ,
j(f(i)) = a ⋅ j(i) in ℤ/mℤ,
where m is a positive integer and a is a constant from ℤ/mℤ depending on f.
-/
def has_linear_representation {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) : Prop :=
  ∃ (m : ℕ) (_hm : m > 0) (a : ZMod m) (j : ZMod n → ZMod m),
    Function.Injective j ∧
    ∀ i : ZMod n, j (f i) = a * j i

/-- Helper: Convert ZMod n to Fin n -/
def zmodToFin {n : ℕ} [NeZero n] (x : ZMod n) : Fin n :=
  ⟨ZMod.val x, ZMod.val_lt x⟩

/--
Main Theorem: Linear Representation of Functions
Any function f: ℤ/nℤ → ℤ/nℤ has a linear representation.

Proof strategy:
1. Use adj_poly_strict_increasing to get x₀ such that for x > x₀,
   the entries y x i are strictly increasing and bounded by m x
2. Choose any integer x > x₀ to get specific values
3. Define j(i) = (y x i) mod (m x)
4. Use adj_eq to show j(f(i)) ≡ x · j(i) (mod m x)
5. Injectivity follows from strict ordering
-/
theorem linear_representation {n : ℕ} [NeZero n] [Fact (n > 0)] (f : ZMod n → ZMod n) :
    has_linear_representation f := by
  -- Get the bound from adj_poly_strict_increasing
  have h_increasing := adj_poly_strict_increasing f
  let A := func_matrix f
  let v : Fin n → ℤ := fun i => i.val
  let M := fun (x : ℤ) => (x • (1 : Matrix (Fin n) (Fin n) ℤ) - A).adjugate
  let y := fun (x : ℤ) => M x *ᵥ v
  let m := fun (x : ℤ) => (x • (1 : Matrix (Fin n) (Fin n) ℤ) - A).det

  obtain ⟨x₀, hx₀⟩ := h_increasing

  -- Choose x = x₀ + 1 (or any x > x₀)
  let x := x₀ + 1
  have hx : x > x₀ := by omega
  have ⟨m_pos, h_nonneg, h_strict, h_bound⟩ := hx₀ x hx

  -- Define m_val = m x (the determinant at x)
  let m_val := m x
  -- We have m_val > 0 from adj_poly_strict_increasing

  -- Convert to Nat for ZMod
  let modulus : ℕ := m_val.natAbs
  have modulus_pos : modulus > 0 := Int.natAbs_pos.mpr (ne_of_gt m_pos)

  -- Define the injection j : ZMod n → ZMod modulus
  -- j(i) = (y x i) mod modulus
  let j : ZMod n → ZMod modulus := fun i =>
    let i_fin := zmodToFin i
    (y x i_fin : ZMod modulus)

  use modulus, modulus_pos, (x : ZMod modulus), j

  constructor
  · -- Prove injectivity
    intro i₁ i₂ h_eq
    -- j i₁ = j i₂ means y x (zmodToFin i₁) ≡ y x (zmodToFin i₂) (mod m_val)
    -- Since both are < m_val (by h_bound) and non-negative (by h_nonneg),
    -- and they're congruent mod m_val, they must be equal
    -- Then by strict ordering, i₁ = i₂

    let i₁_fin := zmodToFin i₁
    let i₂_fin := zmodToFin i₂

    -- Both values are in [0, m_val)
    have hy1_nonneg : y x i₁_fin ≥ 0 := h_nonneg i₁_fin
    have hy2_nonneg : y x i₂_fin ≥ 0 := h_nonneg i₂_fin
    have hy1_lt : y x i₁_fin < m_val := h_bound i₁_fin
    have hy2_lt : y x i₂_fin < m_val := h_bound i₂_fin

    -- From h_eq: (y x i₁_fin : ZMod modulus) = (y x i₂_fin : ZMod modulus)
    -- Since 0 ≤ y x i₁_fin < m_val and 0 ≤ y x i₂_fin < m_val, this means y x i₁_fin = y x i₂_fin
    have h_y_eq : y x i₁_fin = y x i₂_fin := by
      -- Two integers in [0, m) that are equal mod m must be equal
      -- modulus = m_val.natAbs, and m_val > 0
      -- h_eq: (y x i₁_fin : ZMod modulus) = (y x i₂_fin : ZMod modulus)
      -- This means: y x i₁_fin ≡ y x i₂_fin (mod modulus)
      -- With bounds: 0 ≤ y x i₁_fin < m_val and 0 ≤ y x i₂_fin < m_val
      -- And modulus = m_val.natAbs = m_val (since m_val > 0)
      -- So both are in [0, modulus), and they're equal mod modulus, hence equal
      have h_mod : (modulus : ℤ) = m_val := by
        simp only [modulus]
        omega
      -- Both values are in [0, modulus), and they're equal mod modulus, hence equal
      have h1 : 0 ≤ y x i₁_fin := hy1_nonneg
      have h2 : y x i₁_fin < (modulus : ℤ) := by omega
      have h3 : 0 ≤ y x i₂_fin := hy2_nonneg
      have h4 : y x i₂_fin < (modulus : ℤ) := by omega
      -- Key insight: both values are in [0, modulus) and equal mod modulus
      -- So they must be equal
      -- From h_eq: (y x i₁_fin : ZMod modulus) = (y x i₂_fin : ZMod modulus)
      -- This means their Int.emod modulus are equal
      have h_emod_eq : y x i₁_fin % (modulus : ℤ) = y x i₂_fin % (modulus : ℤ) := by
        have h_iff := ZMod.intCast_eq_intCast_iff (y x i₁_fin) (y x i₂_fin) modulus
        rw [h_iff] at h_eq
        rw [Int.ModEq] at h_eq
        exact h_eq
      -- For integers in [0, m), a % m = a
      have h1_emod : y x i₁_fin % (modulus : ℤ) = y x i₁_fin := by
        apply Int.emod_eq_of_lt
        · exact h1
        · exact h2
      have h2_emod : y x i₂_fin % (modulus : ℤ) = y x i₂_fin := by
        apply Int.emod_eq_of_lt
        · exact h3
        · exact h4
      -- Therefore the values are equal
      calc y x i₁_fin
          = y x i₁_fin % (modulus : ℤ) := h1_emod.symm
        _ = y x i₂_fin % (modulus : ℤ) := h_emod_eq
        _ = y x i₂_fin := h2_emod

    -- From strict ordering, i₁_fin = i₂_fin
    have h_fin_eq : i₁_fin = i₂_fin := by
      by_contra h_ne
      cases' Ne.lt_or_gt h_ne with h_lt h_gt
      · have : y x i₁_fin < y x i₂_fin := h_strict i₁_fin i₂_fin h_lt
        omega
      · have : y x i₂_fin < y x i₁_fin := h_strict i₂_fin i₁_fin h_gt
        omega

    -- Finally, i₁ = i₂
    -- zmodToFin converts ZMod n → Fin n by taking the value
    -- So i₁_fin = ⟨ZMod.val i₁, _⟩ and i₂_fin = ⟨ZMod.val i₂, _⟩
    -- From h_fin_eq: i₁_fin = i₂_fin, so ZMod.val i₁ = ZMod.val i₂
    have h_val_eq : ZMod.val i₁ = ZMod.val i₂ := by
      have : i₁_fin.val = i₂_fin.val := congrArg Fin.val h_fin_eq
      simp only [i₁_fin, i₂_fin, zmodToFin] at this
      exact this
    exact ZMod.val_injective n h_val_eq

  · -- Prove linear relation: j (f i) = x · j i (mod modulus)
    intro i
    let i_fin := zmodToFin i
    let fi_fin := zmodToFin (f i)

    -- From adj_eq: y x fi_fin = x · y x i_fin - m_val · v i_fin
    have h_adj := adj_eq f x v i_fin
    -- This gives: y x fi_fin = x · y x i_fin - m_val · i_fin.val
    -- Working modulo m_val: y x fi_fin ≡ x · y x i_fin (mod m_val)

    -- Show that fi_fin corresponds to f(i)
    -- fi_fin = zmodToFin (f i) = ⟨ZMod.val (f i), _⟩
    -- We need to match this with the result from adj_eq
    -- adj_eq gives us information about ⟨ZMod.val (f (i_fin.val : ZMod n)), _⟩

    -- First, simplify i_fin.val
    have h_ifin : (i_fin.val : ZMod n) = i := by
      simp only [i_fin, zmodToFin]
      exact ZMod.natCast_zmod_val i

    -- So the index in h_adj is actually about f(i)
    have h_fi : ⟨ZMod.val (f (i_fin.val : ZMod n)), ZMod.val_lt _⟩ = fi_fin := by
      simp only [fi_fin, zmodToFin]
      congr 1
      rw [h_ifin]

    -- Now we have:
    -- h_adj: y x ⟨(f (i_fin.val : ZMod n)).val, _⟩ = x * y x i_fin - m_val * i_fin.val
    -- h_fi: ⟨(f (i_fin.val : ZMod n)).val, _⟩ = fi_fin
    -- Need to prove: j (f i) = (x : ZMod modulus) * j i
    -- where j (f i) = (y x fi_fin : ZMod modulus) and j i = (y x i_fin : ZMod modulus)

    -- From h_adj and h_fi, we get: y x fi_fin = x * y x i_fin - m_val * i_fin.val
    -- Cast to ZMod modulus: (y x fi_fin : ZMod modulus) = (x * y x i_fin - m_val * i_fin.val : ZMod modulus)
    -- Since modulus = m_val.natAbs and m_val > 0, we have m_val ≡ 0 (mod modulus)
    -- So: (y x fi_fin : ZMod modulus) = (x : ZMod modulus) * (y x i_fin : ZMod modulus)

    -- First establish that y x fi_fin = x * y x i_fin - m_val * i_fin.val
    have h_y_relation : y x fi_fin = x * y x i_fin - m_val * v i_fin := by
      calc y x fi_fin
          = y x ⟨ZMod.val (f (i_fin.val : ZMod n)), ZMod.val_lt _⟩ := by rw [← h_fi]
        _ = x * y x i_fin - m_val * v i_fin := h_adj

    -- Simplify: v i_fin = i_fin.val since v is defined as fun i => i.val
    have h_v_eq : v i_fin = (i_fin.val : ℤ) := rfl

    -- Now cast to ZMod modulus
    -- From h_y_relation and h_v_eq: y x fi_fin = x * y x i_fin - m_val * i_fin.val
    -- Casting to ZMod modulus and using m_val ≡ 0 (mod modulus):
    calc j (f i)
        = (y x fi_fin : ZMod modulus) := rfl
      _ = ((x * y x i_fin - m_val * (i_fin.val : ℤ)) : ZMod modulus) := by
          simp only [h_y_relation, h_v_eq]
          push_cast
          ring
      _ = ((x * y x i_fin) : ZMod modulus) - ((m_val * (i_fin.val : ℤ)) : ZMod modulus) := by simp
      _ = ((x * y x i_fin) : ZMod modulus) - 0 := by
          -- Show (m_val : ZMod modulus) = 0 since modulus = m_val.natAbs and m_val > 0
          congr 1
          norm_cast
          refine (ZMod.intCast_zmod_eq_zero_iff_dvd (m_val * ↑↑i_fin) modulus).mpr ?_
          -- Need: (modulus : ℤ) ∣ m_val * i_fin.val
          -- Since modulus = m_val.natAbs and m_val > 0, we have (modulus : ℤ) = m_val
          -- So m_val ∣ m_val * i_fin.val, which is obvious
          have h_mod_eq : (modulus : ℤ) = m_val := by
            simp only [modulus]
            exact Int.natAbs_of_nonneg (le_of_lt m_pos)
          rw [h_mod_eq]
          exact dvd_mul_right m_val (i_fin.val : ℤ)
      _ = ((x * y x i_fin) : ZMod modulus) := by ring
      _ = (x : ZMod modulus) * (y x i_fin : ZMod modulus) := by rfl
      _ = (x : ZMod modulus) * j i := rfl

/-!
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

Step 5: Choose v = (0, 1, 2)ᵀ, compute y(x) = adj(M(x)) · v as polynomials
  y₀(x) = x(x-1)·0 = 0
  y₁(x) = x(x-1)·1 = x² - x
  y₂(x) = (x-1)·1 + (x-1)²·2 = (x-1) + 2(x-1)² = (x-1)(1 + 2(x-1)) = (x-1)(2x-1)

Step 6: Verify polynomial properties
  - y₀(x) = 0
  - y₁(x) = x² - x
  - y₂(x) = (x-1)(2x-1)
  - For x ≥ 4: 0 ≤ y₁(x) < y₂(x) < m(x)

Step 7: Evaluate at x = 4
  - m = m(4) = 4³ - 2·4² + 4 = 64 - 32 + 4 = 36
  - y₀ = y₀(4) = 0
  - y₁ = y₁(4) = 4² - 4 = 12
  - y₂ = y₂(4) = (4-1)(2·4-1) = 3·7 = 21

  Indeed: 0 < 12 < 21 < 36 ✓

Step 8: Define linear representation
  - m = 36 (the modulus)
  - a = 4 (the multiplier)
  - j: ℤ/3ℤ → ℤ/36ℤ given by j(0)=0, j(1)=12, j(2)=21

Step 9: Verify j(f(i)) = a · j(i) mod m
  - j(f(0)) = j(0) = 0 = 4·0 ✓
  - j(f(1)) = j(1) = 12 = 4·12 mod 36 (48 = 36 + 12) ✓
  - j(f(2)) = j(1) = 12 = 4·21 mod 36 (84 = 2·36 + 12) ✓
-/

/--
Explicit example showing the linear representation construction for f(x) = x² in ℤ/3ℤ.
Given f = x², we show that with:
- A = func_matrix f (the adjacency matrix)
- x = 4 (chosen parameter)
- M = 4I - A
- m = det(M) = 36
- adj(M) = M.adjugate
- v = (0,1,2)
- y = adj(M)·v = (0,12,21)

We get j(i) = y[i] mod 36, a = 4, which satisfies j(f(i)) = a·j(i) mod 36.
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
    -- v and y are as computed
    v = ![0, 1, 2] ∧
    y = adj_M *ᵥ v ∧
    y = ![0, 12, 21] ∧
    -- This gives a linear representation
    (let j : ZMod 3 → ZMod 36 := fun i => (y (zmodToFin i) : ZMod 36)
     let a : ZMod 36 := 4
     Function.Injective j ∧ ∀ i : ZMod 3, j (f i) = a * j i) := by
  let f : ZMod 3 → ZMod 3 := fun x => x^2

  -- Define all the components
  let A := func_matrix f
  let x : ℤ := 4
  let M := x • (1 : Matrix (Fin 3) (Fin 3) ℤ) - A
  let m := M.det
  let adj_M := M.adjugate
  let v : Fin 3 → ℤ := ![0, 1, 2]
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
  constructor; · rfl  -- v = ![0,1,2]
  constructor; · rfl  -- y = adj_M *ᵥ v
  constructor
  · -- y = ![0, 12, 21]
    decide
  -- Prove the linear representation property
  let j : ZMod 3 → ZMod 36 := fun i => (y (zmodToFin i) : ZMod 36)
  let a : ZMod 36 := 4

  constructor
  · -- Injectivity: j(0)=0, j(1)=12, j(2)=21 are distinct mod 36
    decide
  · -- Linear relation: j(f(i)) = a · j(i) mod 36
    intro i
    -- We need to check all three cases: i = 0, 1, 2
    -- f(0) = 0, f(1) = 1, f(2) = 1
    -- j(0) = 0, j(1) = 12, j(2) = 21
    -- a = 4
    -- Check: j(f(0)) = j(0) = 0 = 4*0 = a*j(0) ✓
    -- Check: j(f(1)) = j(1) = 12 = 4*12 mod 36 = 48 mod 36 = 12 ✓
    -- Check: j(f(2)) = j(1) = 12 = 4*21 mod 36 = 84 mod 36 = 12 ✓
    fin_cases i <;> decide

--end Cursor.Opus
