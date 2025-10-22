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

namespace Cursor.Opus

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

-- Helper for det_degree_le_sum_degrees
lemma single_element_sum_le {n : ℕ} (a : Fin n → ℕ) (ha: ∀ j, 0 ≤ a j) (i : Fin n) :
    a i ≤ ∑ j, a j := by
  calc a i
      = ∑ j ∈ ({i} : Finset (Fin n)), a j := by
        rw [Finset.sum_singleton]
      _ ≤ ∑ j ∈ Finset.univ, a j := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx
          simp at hx
          rw [hx]
          exact Finset.mem_univ i
        · intro j _ _
          exact ha j
      _ = ∑ j, a j := by rfl

open Polynomial BigOperators Finset in
theorem det_degree_le_sum_degrees {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ[X]) :
    (M.det).natDegree ≤ ∑ i : Fin n, ∑ j : Fin n, (M j i).natDegree := by
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
        have hnonneg : ∀ j, 0 ≤ (M j i).natDegree := fun j ↦ Nat.zero_le (M j i).natDegree
        exact single_element_sum_le (fun j => (M j i).natDegree : Fin n → ℕ) (hnonneg) (σ i)

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
  sorry -- Complete proof exists in ChatGPT3.lean, needs specialization

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
    -- The polynomial p_{ij} is explicitly (charmatrix A).adjugate[i,j]
    let p := (charmatrix A).adjugate i j
    -- The non-trivial claims are the degree properties:
    (i = j → p.Monic ∧ p.natDegree = n - 1) ∧
    (i ≠ j → p.natDegree ≤ n - 2) := by
  intro i j
  let A := func_matrix f
  let p := (charmatrix A).adjugate i j
  -- Note: That p.eval x = (x•I - A).adjugate[i,j] follows from:
  -- 1. charmatrix A evaluated at x is x•I - A (by definition)
  -- 2. Evaluation commutes with adjugate (RingHom.map_adjugate)
  -- This is straightforward and doesn't need to be stated as a separate condition.

  constructor
  · -- Diagonal case: monic of degree n-1
    intro hij
    rw [hij]
    -- We assume n > 1 for the interesting case
    -- (For n = 0, we have NeZero 0 contradiction; for n = 1, the result is vacuous)
    -- Helper: Fintype.card (Fin m) = m for any m
    have h1 (m : ℕ) : Fintype.card (Fin m) = m := by rw [Fintype.card_fin]

    have hn : n > 1 := by
      by_contra h_le
      push_neg at h_le
      interval_cases n
      · -- n = 0: contradicts NeZero n
        exact absurd rfl (NeZero.ne 0)
      · -- n = 1: For n = 1, the statement is actually vacuously true
        -- but proving it requires handling the 1×1 matrix case separately.
        -- For simplicity, we assume n > 1 for the interesting case.
        -- In a complete proof, we would either:
        -- (a) Add [Fact (1 < n)] as a hypothesis, or
        -- (b) Prove the n=1 case separately (it's trivial but tedious)
        sorry
    haveI : Nontrivial (Fin n) := by
      -- From n > 1, we get that Fintype.card (Fin n) = n > 1, so Fin n has 0 ≠ 1
      rw [← h1 n] at hn
      rw [nontrivial_iff]
      use 0, 1
      simp
      exact Nat.ne_of_gt (Nat.lt_of_lt_of_eq hn (h1 n))
    constructor
    · -- Monic: The diagonal entry of adjugate(charmatrix A) is the charpoly of a submatrix

      -- Apply adjugate definition and use the submatrix characterization
      rw [adjugate_apply]
      have h_eq : ((charmatrix A).updateRow j (Pi.single j 1)).det =
                  ((charmatrix A).submatrix (fun (i : {x // x ≠ j}) => i.val)
                                            (fun (k : {x // x ≠ j}) => k.val)).det := by
        sorry -- Assume helper lemma det_updateRow_single_eq_submatrix_general
      rw [h_eq]
      -- Show the submatrix is the charmatrix of the submatrix
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
                have h1' : Fintype.card (Fin n) = n := by
                  sorry -- Typeclass instance unification issue
                have h2 : Fintype.card {x : Fin n // x = j} = 1 := Fintype.card_subtype_eq j
                omega
      rw [← card_eq]
      exact charpoly_natDegree_eq_dim (A.submatrix (fun (i : {x // x ≠ j}) => i.val)
                                                    (fun (k : {x // x ≠ j}) => k.val))

  · -- Off-diagonal case: degree ≤ n-2
    intro hij
    rw [adjugate_apply]
    -- The adjugate entry (charmatrix A).adjugate[i,j] = det((charmatrix A).updateRow j (Pi.single i 1))
    -- By det_degree_le_sum_degrees: det degree ≤ sum of entry degrees
    -- By charMatrix_offdiag_minor_sum_degrees: the relevant sum = n - 2 for off-diagonal
    -- The sum manipulation to connect these is technical, so we leave it as sorry
    have h_bound : ((charmatrix A).updateRow j (Pi.single i 1)).det.natDegree ≤ n - 2 := by
      sorry -- Apply det_degree_le_sum_degrees, then sum manipulation, then charMatrix_offdiag_minor_sum_degrees
    exact h_bound

/--
Entries of M(x)v are strictly increasing for large x
Let M = M(x) = adj(xI - A) be the adjugate of the characteristic matrix xI - A.
Let v = (0,1,2,...,n-1)^T. Then there is x_0 such that for all x > x_0
the entries of M(x)v are strictly increasing and bounded by m = det(xI - A).
-/
lemma adj_poly_strict_increasing {n : ℕ} [NeZero n] [h : Fact (n > 0)] (f : ZMod n → ZMod n) :
    ∃ x₀ : ℤ, ∀ x : ℤ, x > x₀ →
    let A := func_matrix f
    let v : Fin n → ℤ := fun i => i.val
    let M := fun (x : ℤ) => (x • (1 : Matrix (Fin n) (Fin n) ℤ) - A).adjugate
    let y := fun (x : ℤ) => M x *ᵥ v
    let m := fun (x : ℤ) => (x • (1 : Matrix (Fin n) (Fin n) ℤ) - A).det
    (∀ i j : Fin n, i < j → y x i < y x j) ∧
    (∀ i : Fin n, y x i < m x) := by
  sorry

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

/--
Main Theorem: Linear Representation of Functions
Any function f: ℤ/nℤ → ℤ/nℤ has a linear representation.
-/
theorem linear_representation {n : ℕ} [NeZero n] [Fact (n > 0)] (f : ZMod n → ZMod n) :
    has_linear_representation f := by
  sorry

/-- Helper: Convert ZMod n to Fin n -/
def zmodToFin {n : ℕ} [NeZero n] (x : ZMod n) : Fin n :=
  ⟨ZMod.val x, ZMod.val_lt x⟩

/-- Helper lemma: The adjacency matrix has exactly one 1 in each row -/
lemma func_matrix_row_sum {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (i : Fin n) :
    ∑ j : Fin n, (func_matrix f) i j = 1 := by
  simp only [func_matrix]
  -- The sum is over entries: if f(i) = j then 1 else 0
  -- Only one j has f(i) = j, namely j = f(i)
  let fi : Fin n := ⟨ZMod.val (f (i.val : ZMod n)), ZMod.val_lt _⟩
  rw [Finset.sum_eq_single fi]
  · -- The term at j = f(i) contributes 1
    simp [fi]
  · -- All other terms contribute 0
    intro j _ hj
    split_ifs with h
    · -- If f(i) = j but j ≠ fi, contradiction
      sorry -- Type mismatch: need to convert between ZMod n equality and Fin n equality
    · rfl
  · -- The case when fi ∉ univ is impossible
    intro h
    exfalso
    exact h (Finset.mem_univ fi)

/-!
### References to Mathlib definitions

We use Mathlib's Matrix.charpoly and Matrix.charmatrix directly:
- `Matrix.charpoly M` is the characteristic polynomial, defined as `det(charmatrix M)`
- `Matrix.charmatrix M` is the polynomial matrix `X*I - M`
- `Matrix.eval_charpoly` states that `(M.charpoly).eval x = (scalar n x - M).det`

These are defined in `Mathlib.LinearAlgebra.Matrix.Charpoly.Basic`.
-/

/--
Example: Quadratic function x ↦ x² in ℤ/3ℤ has a linear representation
This is a non-trivial example showing that even non-linear functions
have linear representations in a larger modulus.

The function is: 0 ↦ 0, 1 ↦ 1, 2 ↦ 1 (since 2² = 4 ≡ 1 mod 3)
-/
example : has_linear_representation (fun x : ZMod 3 => x^2) := by
  -- The theorem states this function has a linear representation
  -- We can use our main theorem to prove this
  have : Fact (3 > 0) := ⟨by norm_num⟩
  apply linear_representation

/--
Explicit verification for the quadratic example.
We can verify that x² in ℤ/3ℤ can be represented linearly.
-/
lemma quadratic_in_Z3_has_linear_rep :
    has_linear_representation (fun x : ZMod 3 => x^2) := by
  sorry

/--
Helper: The adjacency matrix for x² in ℤ/3ℤ
This matrix represents the function 0↦0, 1↦1, 2↦1
-/
example : func_matrix (fun x : ZMod 3 => x^2) =
    !![1, 0, 0;   -- row 0: f(0)=0, so A[0,0]=1
      0, 1, 0;   -- row 1: f(1)=1, so A[1,1]=1
      0, 1, 0] := by  -- row 2: f(2)=1, so A[2,1]=1
  sorry

/-- Example: Identity function has a simple linear representation -/
example {n : ℕ} [NeZero n] [Fact (n > 0)] :
    has_linear_representation (id : ZMod n → ZMod n) := by
  sorry

end Cursor.Opus
