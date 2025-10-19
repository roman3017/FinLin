import Mathlib

open Matrix Polynomial BigOperators Finset

noncomputable section

variable {n : ℕ}

/-- The adjacency matrix of a function f: Fin n → Fin n, where A_{ij} = 1 if j = f(i), else 0. -/
def adjacencyMatrix (f : Fin n → Fin n) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if j = f i then 1 else 0

/-- The characteristic matrix xI - A for a function's adjacency matrix. -/
def charMatrix (f : Fin n → Fin n) : Matrix (Fin n) (Fin n) (Polynomial ℤ) :=
  (adjacencyMatrix f).charmatrix

/-- The adjugate matrix M(x) = adj(xI - A). -/
def adjugateMatrix (f : Fin n → Fin n) : Matrix (Fin n) (Fin n) (Polynomial ℤ) :=
  (adjacencyMatrix f).charmatrix.adjugate

/-- The characteristic polynomial p(x) = det(xI - A). -/
def charpoly (f : Fin n → Fin n) : Polynomial ℤ :=
  (adjacencyMatrix f).charpoly

/-- The vector v = (0, 1, ..., n-1) with integer entries. -/
def vVec : Fin n → ℤ := fun i => i.val

/-- For any vertex i, the diagonal entry of the adjugate has degree n-1. -/
lemma adjugate_diag_degree (f : Fin n → Fin n) (i : Fin n) :
    ((adjugateMatrix f) i i).natDegree = n - 1 := by
  -- The adjugate entry M_ii is (-1)^{i+i} times det of the minor with row i and column i removed
  -- Since the charmatrix has diagonal entries of degree 1 and off-diagonal of degree 0,
  -- the determinant of the minor has degree n-1
  sorry

/-- Leading coefficient of diagonal adjugate entry is 1. -/
lemma adjugate_diag_leading_coeff (f : Fin n → Fin n) (i : Fin n) :
    ((adjugateMatrix f) i i).leadingCoeff = 1 := by
  -- The leading coefficient comes from the monic property of the characteristic polynomial
  sorry

/-- For distinct vertices i ≠ j in the same component, deg(M_ij(x)) ≤ n - 2. -/
lemma adjugate_offdiag_degree (f : Fin n → Fin n) (i j : Fin n) (hij : i ≠ j) :
    ((adjugateMatrix f) i j).natDegree ≤ n - 2 := by
  -- The off-diagonal entry M_ij is (-1)^{i+j} times det of the minor with row i and column j removed
  -- This involves removing two rows/columns, so the degree is at most n-2
  sorry

/-- Main technical theorem: The vector M(x)v has entries that are strictly increasing for large x. -/
theorem main_technical_theorem (f : Fin n → Fin n) :
    ∃ (C : ℝ), ∀ (x : ℝ), C ≤ x →
      ∀ (i j : Fin n), i.val < j.val →
        Polynomial.eval x (((adjugateMatrix f).mulVec (fun i => Polynomial.C (vVec i)) i).map (Int.castRingHom ℝ)) <
        Polynomial.eval x (((adjugateMatrix f).mulVec (fun i => Polynomial.C (vVec i)) j).map (Int.castRingHom ℝ)) := by
  -- Let w(x) = M(x) * v
  -- From degree analysis, w_i(x) = i * x^{n-1} + O(x^{n-2})
  -- For i < j, the difference w_j(x) - w_i(x) = (j - i) * x^{n-1} + O(x^{n-2}) > 0 for large x
  sorry

/-- For a monic polynomial of degree n > 0, there exists some large integer where it doesn't vanish. -/
lemma exists_large_eval_nonzero (p : Polynomial ℤ) (hp : p.Monic) (hdeg : 0 < p.natDegree) :
    ∃ a : ℕ, ∀ b : ℤ, a ≤ b → p.eval b ≠ 0 := by
  -- A non-constant polynomial has finitely many roots, so outside a certain range it's non-zero
  sorry

/-- The characteristic polynomial is monic of degree n. -/
lemma charpoly_monic_degree (f : Fin n → Fin n) :
    (charpoly f).Monic ∧ (charpoly f).natDegree = n := by
  constructor
  · exact Matrix.charpoly_monic (adjacencyMatrix f)
  · have := Matrix.charpoly_natDegree_eq_dim (adjacencyMatrix f)
    rw [Fintype.card_fin] at this
    exact this

/-- For large enough a, the characteristic polynomial doesn't vanish. -/
lemma charpoly_eval_nonzero_large (f : Fin n → Fin n) :
    ∃ a : ℕ, ∀ b : ℤ, a ≤ b → (charpoly f).eval b ≠ 0 := by
  obtain ⟨hmonic, hdeg⟩ := charpoly_monic_degree f
  have hdeg_pos : 0 < n := by
    -- n is the size of Fin n, and Fin n is nontrivial
    sorry
  exact exists_large_eval_nonzero (charpoly f) hmonic (by rw [hdeg]; exact hdeg_pos)

/-- The adjugate identity: (xI - A) * adj(xI - A) = det(xI - A) * I -/
lemma adjugate_identity (f : Fin n → Fin n) (x : ℤ) :
    (charMatrix f).map (Polynomial.eval x) * (adjugateMatrix f).map (Polynomial.eval x) =
    (charpoly f).eval x • (1 : Matrix (Fin n) (Fin n) ℤ) := by
  have := Matrix.mul_adjugate (charMatrix f)
  -- This needs to be evaluated at x, which requires some ring homomorphism work
  sorry

/-- The linear relation from the adjugate identity. -/
lemma linear_relation_from_adjugate (f : Fin n → Fin n) (a : ℤ) (m : ℤ) (hm : m = (charpoly f).eval a) :
    ∀ i k : Fin n, ((adjugateMatrix f).map (Polynomial.eval a) * adjacencyMatrix f) i k ≡
                   a * ((adjugateMatrix f).map (Polynomial.eval a)) i k [ZMOD m] := by
  -- From the adjugate identity: (a*I - A) * M_a = m * I
  -- Rearranging: A * M_a = a * M_a - m * I
  -- Thus A * M_a ≡ a * M_a mod m
  let M_a := (adjugateMatrix f).map (Polynomial.eval a)
  have adj_id := adjugate_identity f a
  -- adj_id: (charMatrix f).map (eval a) * M_a = m • 1
  -- charMatrix f = a • 1 - adjacencyMatrix f
  -- So (a • 1 - A) * M_a = m • 1
  -- Thus A * M_a = a • 1 * M_a - m • 1 = a * M_a - m • 1
  -- So A * M_a + m • 1 = a * M_a
  -- Thus A * M_a ≡ a * M_a mod m
  intro i k
  -- Use the matrix identity to show the congruence
  have h : (a • (1 : Matrix (Fin n) (Fin n) ℤ) - adjacencyMatrix f) * M_a = m • (1 : Matrix (Fin n) (Fin n) ℤ) := by
    -- This follows from adj_id and the definition of charMatrix
    sorry
  -- From this: A * M_a = a * M_a - m * I
  -- So A * M_a + m * I = a * M_a
  -- Thus A * M_a ≡ a * M_a mod m
  sorry

/-- Linear representation corollary: Any function has a linear representation modulo some m. -/
theorem linear_representation_corollary (f : Fin n → Fin n) :
    ∃ (m : ℕ) (a : ℤ) (j : Fin n → ZMod m),
      Function.Injective j ∧ ∀ (y : Fin n), j (f y) = a * j y := by
  -- Get the constant C from the main technical theorem
  have hC_exists := main_technical_theorem f
  obtain ⟨C, hC⟩ := hC_exists

  -- Choose a large enough a
  have a_exists : ∃ a_lower : ℕ, ∀ b : ℤ, a_lower ≤ b → (charpoly f).eval b ≠ 0 :=
    charpoly_eval_nonzero_large f
  let a_lower := Classical.choose a_exists
  let a : ℤ := max (⌈C⌉ + 1) a_lower

  -- Let M_a be M(a), the adjugate evaluated at a
  let M_a := (adjugateMatrix f).map (Polynomial.eval a)

  -- Let w = M_a * v
  let w := M_a.mulVec vVec

  -- Let p be the characteristic polynomial
  let p := charpoly f

  -- Let m = p(a)
  let m_val := p.eval a

  -- m ≠ 0 by choice of a
  have m_ne_zero : m_val ≠ 0 := Classical.choose_spec a_exists a (le_max_right _ _)

  -- Convert to positive modulus
  let m : ℕ := m_val.natAbs

  -- Define j(y) = w_y mod m
  let j : Fin n → ZMod m := fun y => (w y : ZMod m)

  -- Prove injectivity: since w is strictly increasing for large a, and m is large enough
  have j_injective : Function.Injective j := by
    -- The theorem guarantees w_i are strictly increasing for large a
    -- Since m = p(a) and p has degree n while w_i have degree n-1,
    -- for large a, |w_i| grows slower than |m|, so distinct w_i remain distinct mod m
    sorry

  -- Prove the linear relation: j(f(y)) = a * j(y) mod m
  have linear_relation : ∀ y, j (f y) = a * j y := by
    -- Use the linear_relation_from_adjugate lemma
    have adj_rel := linear_relation_from_adjugate f a m_val rfl
    intro y
    -- w_{f(y)} = sum_k M_a_{f(y),k} * v_k
    -- From adj_rel: M_a_{f(y),k} ≡ a * M_a_{y,k} mod m_val
    -- So w_{f(y)} ≡ a * w_y mod m_val
    -- Since j maps to ZMod m and m = |m_val|, this gives the result
    sorry

  exact ⟨m, a, j, j_injective, linear_relation⟩
