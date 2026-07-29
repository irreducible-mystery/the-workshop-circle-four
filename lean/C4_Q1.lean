/-
  Circle Four — Q1: the spanning sentence, stated and settled.

  THE CHARGE'S FIRST QUESTION, verbatim: "Can the spanning statement —
  every antisymmetric vector as a sum over the strictly-upper index set,
  the sentence the sealed boundary names as `w = Σ_{i<j} w_ij (e_ij −
  e_ji)` — be stated and settled as a formal sentence, and once settled,
  does it follow from the sealed characterization of the antisymmetrizer's
  image, or the characterization from it, or neither?"

  Zero imports, in the sealed artifact's manner: the kernel on `Int`
  alone, no lake, no mathlib, no Std. Toolchain pinned
  leanprover/lean4:v4.32.0 (commit 8c9756b2…, measured by `lean --version`
  on the machine that compiled this file).

  WHAT IS CARRIED AND WHAT IS NEW. The block marked CARRIED below is
  copied byte-for-byte from the sealed artifact at
  `inherited/circle-two-three/lean/Zi.lean` (sealed pin
  6a6b6cb21ff89b9b533151ce6f3ee0370d3206c9632192f0920ad5da0d4560c0,
  unchanged since the seal `f13d2928…`). It is copied rather than
  imported because the sealed file is a zero-import single file and the
  record runs it as one; `audit/c4_carried_defs.sh` re-measures every
  carried declaration against the sealed file and goes red on any drift,
  so the copy is honest by construction rather than by promise.
  Everything below the CARRIED block is Circle Four's own.

  THE SCOPE, as the charge sets it: the antisymmetrizer's image over
  `Int`, at the generality the sealed section holds — every statement
  here is generic in the size `m` and in the vector, with no `decide`
  and no size-specific step.
-/

/- ==========================================================================
   CARRIED — byte-for-byte from the sealed artifact, section S7.
   Re-measured by audit/c4_carried_defs.sh; do not edit here.
   ========================================================================== -/

def sumTo (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => sumTo f n + f n

/-- A vector of the tensor square, in coordinates: `v i j` is the
    coefficient of the basis vector `e_ij`. -/
def swapT (v : Nat → Nat → Int) : Nat → Nat → Int := fun i j => v j i

/-- The basis vector `e_ab`. -/
def eBasis (a b : Nat) : Nat → Nat → Int := fun i j => if i = a ∧ j = b then 1 else 0

/-- **The antisymmetrizer, `M = I − swap`**, written in coordinates. -/
def antiM (v : Nat → Nat → Int) : Nat → Nat → Int := fun i j => v i j - swapT v i j

/-- The generator `e_ab − e_ba`, as the image of a basis vector. -/
def eDiff (a b : Nat) : Nat → Nat → Int := antiM (eBasis a b)

/-- `[0, 1, …, n−1]`. -/
def upTo : Nat → List Nat
  | 0 => []
  | n + 1 => upTo n ++ [n]

/-- The index set of the image basis: every pair `(i, j)` with `i < j < m`. -/
def upperPairs : Nat → List (Nat × Nat)
  | 0 => []
  | m + 1 => upperPairs m ++ (upTo m).map (fun i => (i, m))

/- ==========================================================================
   NEW — Circle Four's own.
   ========================================================================== -/

/-! ### The sum over the strictly-upper index set

    The charge's sentence is a sum indexed by `upperPairs`, so the sum is
    defined over the list itself rather than over a range that happens to
    have the same length. Nothing here assumes the list is duplicate-free
    or complete; both facts are consequences of the theorem below, not
    hypotheses of it. -/

/-- The sum of `f` over a list of index pairs. -/
def sumPairs (f : Nat × Nat → Int) : List (Nat × Nat) → Int
  | [] => 0
  | p :: ps => f p + sumPairs f ps

theorem sumPairs_append (f : Nat × Nat → Int) : ∀ l₁ l₂ : List (Nat × Nat),
    sumPairs f (l₁ ++ l₂) = sumPairs f l₁ + sumPairs f l₂
  | [], l₂ => by
      show sumPairs f l₂ = 0 + sumPairs f l₂
      omega
  | p :: ps, l₂ => by
      show f p + sumPairs f (ps ++ l₂) = (f p + sumPairs f ps) + sumPairs f l₂
      rw [sumPairs_append f ps l₂]
      omega

/-- The bridge from a sum over the list `upTo n` to the sealed `sumTo`:
    the two agree termwise, so any range fact proved for one holds of the
    other. -/
theorem sumPairs_upTo (f : Nat × Nat → Int) (m : Nat) : ∀ n : Nat,
    sumPairs f ((upTo n).map (fun a => (a, m))) = sumTo (fun a => f (a, m)) n
  | 0 => rfl
  | n + 1 => by
      show sumPairs f (((upTo n) ++ [n]).map (fun a => (a, m)))
             = sumTo (fun a => f (a, m)) n + f (n, m)
      rw [List.map_append]
      rw [sumPairs_append]
      rw [sumPairs_upTo f m n]
      show sumTo (fun a => f (a, m)) n + (f (n, m) + 0)
             = sumTo (fun a => f (a, m)) n + f (n, m)
      omega

/-- Negation passes through a range sum. -/
theorem sumTo_neg (f : Nat → Int) : ∀ n : Nat,
    sumTo (fun a => -(f a)) n = -(sumTo f n)
  | 0 => rfl
  | n + 1 => by
      show sumTo (fun a => -(f a)) n + -(f n) = -(sumTo f n + f n)
      rw [sumTo_neg f n]
      omega

/-- The zero sum. -/
theorem sumTo_zero : ∀ n : Nat, sumTo (fun _ => (0 : Int)) n = 0
  | 0 => rfl
  | n + 1 => by
      show sumTo (fun _ => (0 : Int)) n + 0 = 0
      rw [sumTo_zero n]
      omega

/-- The generator, entrywise — the two indicators the sum sees. -/
theorem eDiff_apply (a b i j : Nat) :
    eDiff a b i j
      = (if i = a ∧ j = b then (1 : Int) else 0)
          - (if j = a ∧ i = b then (1 : Int) else 0) := rfl

/-- The indicator of a single index, weighted: the sealed
    `sumTo_eq_indicator` with a coefficient carried through. -/
theorem sumTo_mul_indicator (g : Nat → Int) (i : Nat) : ∀ n : Nat,
    sumTo (fun a => g a * (if i = a then (1 : Int) else 0)) n
      = if i < n then g i else 0
  | 0 => rfl
  | n + 1 => by
      show sumTo (fun a => g a * (if i = a then (1 : Int) else 0)) n
             + g n * (if i = n then (1:Int) else 0)
           = if i < n + 1 then g i else 0
      rw [sumTo_mul_indicator g i n]
      by_cases h : i = n
      · subst h
        have h2 : ¬ i < i := by omega
        have h3 : i < i + 1 := by omega
        simp [h2, h3]
      · by_cases h2 : i < n
        · have h3 : i < n + 1 := by omega
          simp [h, h2, h3]
        · have h3 : ¬ i < n + 1 := by
            have : ¬ i = n := h
            omega
          simp [h, h2, h3]

/-- **The spanning sum**, exactly the charge's sentence: `w` reassembled
    from its strictly-upper coefficients against the generators
    `e_ij − e_ji`, summed over `upperPairs m`. -/
def spanSum (w : Nat → Nat → Int) (m : Nat) : Nat → Nat → Int :=
  fun i j => sumPairs (fun p => w p.1 p.2 * eDiff p.1 p.2 i j) (upperPairs m)

/-- The strictly-upper coefficient function, bounded to the range the sum
    runs over — the witness the spanning sum exhibits. -/
def upperPart (w : Nat → Nat → Int) (m : Nat) : Nat → Nat → Int :=
  fun a b => if a < b ∧ b < m then w a b else 0

/-- The antisymmetrizer of the strictly-upper part, entrywise. -/
theorem antiM_upperPart_apply (w : Nat → Nat → Int) (m i j : Nat) :
    antiM (upperPart w m) i j
      = (if i < j ∧ j < m then w i j else 0)
          - (if j < i ∧ i < m then w j i else 0) := rfl

/-! ### The identity underneath the spanning statement

    The whole combinatorial content in one sentence, and it needs **no**
    hypothesis on `w` and no bound on the indices: the sum over the
    strictly-upper index set of the coefficients against the generators is
    the antisymmetrizer applied to the strictly-upper coefficient
    function. That the index list is duplicate-free and hits every
    strictly-upper pair exactly once is what makes this true, and proving
    it is how those facts get used. -/

theorem spanSum_eq_antiM_upperPart (w : Nat → Nat → Int) : ∀ (m i j : Nat),
    spanSum w m i j = antiM (upperPart w m) i j
  | 0, i, j => by
      rw [antiM_upperPart_apply]
      have h1 : ¬ (i < j ∧ j < 0) := by
        intro hc
        exact absurd hc.2 (by omega)
      have h2 : ¬ (j < i ∧ i < 0) := by
        intro hc
        exact absurd hc.2 (by omega)
      rw [if_neg h1, if_neg h2]
      show (0 : Int) = 0 - 0
      omega
  | m + 1, i, j => by
      show sumPairs (fun p => w p.1 p.2 * eDiff p.1 p.2 i j)
             (upperPairs m ++ (upTo m).map (fun a => (a, m)))
           = antiM (upperPart w (m + 1)) i j
      rw [sumPairs_append]
      rw [show sumPairs (fun p => w p.1 p.2 * eDiff p.1 p.2 i j) (upperPairs m)
             = spanSum w m i j from rfl]
      rw [spanSum_eq_antiM_upperPart w m i j]
      rw [sumPairs_upTo]
      rw [antiM_upperPart_apply, antiM_upperPart_apply]
      show (if i < j ∧ j < m then w i j else 0) - (if j < i ∧ i < m then w j i else 0)
             + sumTo (fun a => w a m * eDiff a m i j) m
           = (if i < j ∧ j < m + 1 then w i j else 0)
               - (if j < i ∧ i < m + 1 then w j i else 0)
      have hterm : ∀ a : Nat, w a m * eDiff a m i j
          = w a m * ((if i = a ∧ j = m then (1 : Int) else 0)
                       - (if j = a ∧ i = m then (1 : Int) else 0)) := by
        intro a
        rw [eDiff_apply]
      by_cases hjm : j = m
      · by_cases him : i = m
        · -- both indices are the new one: everything vanishes
          have hz : (fun a => w a m * eDiff a m i j) = (fun _ => (0 : Int)) := by
            funext a
            rw [hterm a]
            have e : (if i = a ∧ j = m then (1 : Int) else 0)
                       - (if j = a ∧ i = m then (1 : Int) else 0) = 0 := by
              have hij : i = j := by
                rw [him, hjm]
              rw [hij]
              omega
            rw [e]
            omega
          rw [hz, sumTo_zero]
          have hnij : ¬ (i < j) := by omega
          have hnji : ¬ (j < i) := by omega
          have a1 : ¬ (i < j ∧ j < m) := by intro hc; exact hnij hc.1
          have a2 : ¬ (j < i ∧ i < m) := by intro hc; exact hnji hc.1
          have a3 : ¬ (i < j ∧ j < m + 1) := by intro hc; exact hnij hc.1
          have a4 : ¬ (j < i ∧ i < m + 1) := by intro hc; exact hnji hc.1
          rw [if_neg a1, if_neg a2, if_neg a3, if_neg a4]
          omega
        · -- the new column: j = m, i ≠ m
          have hz : (fun a => w a m * eDiff a m i j)
              = (fun a => w a m * (if i = a then (1 : Int) else 0)) := by
            funext a
            rw [hterm a]
            have hne : ¬ (j = a ∧ i = m) := by intro hc; exact him hc.2
            rw [if_neg hne]
            by_cases hia : i = a
            · rw [if_pos (⟨hia, hjm⟩ : i = a ∧ j = m), if_pos hia]
              omega
            · have hn2 : ¬ (i = a ∧ j = m) := by intro hc; exact hia hc.1
              rw [if_neg hn2, if_neg hia]
              omega
          rw [hz, sumTo_mul_indicator]
          have hjjm : ¬ (j < m) := by omega
          have a1 : ¬ (i < j ∧ j < m) := by intro hc; exact hjjm hc.2
          have a2 : ¬ (j < i ∧ i < m) := by
            intro hc
            have : m < i := by rw [hjm] at hc; exact hc.1
            exact absurd hc.2 (by omega)
          have a4 : ¬ (j < i ∧ i < m + 1) := by
            intro hc
            have hmi : m < i := by rw [hjm] at hc; exact hc.1
            exact absurd hc.2 (by omega)
          rw [if_neg a1, if_neg a2, if_neg a4]
          by_cases hlt : i < m
          · have a3 : i < j ∧ j < m + 1 := ⟨by rw [hjm]; exact hlt, by omega⟩
            rw [if_pos a3, if_pos hlt]
            have : w i j = w i m := by rw [hjm]
            rw [this]
            omega
          · have a3 : ¬ (i < j ∧ j < m + 1) := by
              intro hc
              have : i < m := by rw [hjm] at hc; exact hc.1
              exact hlt this
            rw [if_neg a3, if_neg hlt]
            omega
      · by_cases him : i = m
        · -- the new row: i = m, j ≠ m
          have hz : (fun a => w a m * eDiff a m i j)
              = (fun a => -(w a m * (if j = a then (1 : Int) else 0))) := by
            funext a
            rw [hterm a]
            have hne : ¬ (i = a ∧ j = m) := by intro hc; exact hjm hc.2
            rw [if_neg hne]
            by_cases hja : j = a
            · rw [if_pos (⟨hja, him⟩ : j = a ∧ i = m), if_pos hja]
              omega
            · have hn2 : ¬ (j = a ∧ i = m) := by intro hc; exact hja hc.1
              rw [if_neg hn2, if_neg hja]
              omega
          rw [hz, sumTo_neg, sumTo_mul_indicator]
          have hiim : ¬ (i < m) := by omega
          have a1 : ¬ (i < j ∧ j < m) := by
            intro hc
            have hmj : m < j := by rw [him] at hc; exact hc.1
            exact absurd hc.2 (by omega)
          have a2 : ¬ (j < i ∧ i < m) := by intro hc; exact hiim hc.2
          have a3 : ¬ (i < j ∧ j < m + 1) := by
            intro hc
            have hmj : m < j := by rw [him] at hc; exact hc.1
            exact absurd hc.2 (by omega)
          rw [if_neg a1, if_neg a2, if_neg a3]
          by_cases hlt : j < m
          · have a4 : j < i ∧ i < m + 1 := ⟨by rw [him]; exact hlt, by omega⟩
            rw [if_pos a4, if_pos hlt]
            have : w j i = w j m := by rw [him]
            rw [this]
            omega
          · have a4 : ¬ (j < i ∧ i < m + 1) := by
              intro hc
              have : j < m := by rw [him] at hc; exact hc.1
              exact hlt this
            rw [if_neg a4, if_neg hlt]
            omega
        · -- neither index is the new one: the tail is empty, the bounds agree
          have hz : (fun a => w a m * eDiff a m i j) = (fun _ => (0 : Int)) := by
            funext a
            rw [hterm a]
            have hne1 : ¬ (i = a ∧ j = m) := by intro hc; exact hjm hc.2
            have hne2 : ¬ (j = a ∧ i = m) := by intro hc; exact him hc.2
            rw [if_neg hne1, if_neg hne2]
            omega
          rw [hz, sumTo_zero]
          by_cases hij : i < j ∧ j < m
          · have hij' : i < j ∧ j < m + 1 := ⟨hij.1, by omega⟩
            have hji : ¬ (j < i ∧ i < m) := by
              intro hc
              exact absurd hij.1 (by omega)
            have hji' : ¬ (j < i ∧ i < m + 1) := by
              intro hc
              exact absurd hij.1 (by omega)
            rw [if_pos hij, if_pos hij', if_neg hji, if_neg hji']
            omega
          · have hij' : ¬ (i < j ∧ j < m + 1) := by
              intro hc
              have hjm' : j ≠ m := hjm
              exact hij ⟨hc.1, by omega⟩
            rw [if_neg hij, if_neg hij']
            by_cases hji : j < i ∧ i < m
            · have hji' : j < i ∧ i < m + 1 := ⟨hji.1, by omega⟩
              rw [if_pos hji, if_pos hji']
              omega
            · have hji' : ¬ (j < i ∧ i < m + 1) := by
                intro hc
                have him' : i ≠ m := him
                exact hji ⟨hc.1, by omega⟩
              rw [if_neg hji, if_neg hji']
              omega

/-! ### Q1, settled

    The spanning statement itself. On the range the sum runs over, and
    for every antisymmetric `w`, the sum of the strictly-upper
    coefficients against the generators **is** `w` — the sentence the
    sealed boundary named and left unwritten. -/

/-- The diagonal of an antisymmetric vector vanishes. Over `Int` this is a
    real step and not a convention: it is where torsion-freeness is used,
    and it is the only place the argument needs anything of the ring. -/
theorem antisym_diag_zero (w : Nat → Nat → Int) (hw : ∀ i j, w i j = - w j i)
    (i : Nat) : w i i = 0 := by
  have h := hw i i
  omega

/-- **THE SPANNING STATEMENT, PROVED.**
    `w = Σ_{i<j} w_ij (e_ij − e_ji)`, as a sum over `upperPairs m`, for
    every antisymmetric `w` and every index pair inside the range. -/
theorem spanning (w : Nat → Nat → Int) (hw : ∀ i j, w i j = - w j i)
    (m i j : Nat) (hi : i < m) (hj : j < m) :
    spanSum w m i j = w i j := by
  rw [spanSum_eq_antiM_upperPart]
  show (if i < j ∧ j < m then w i j else 0) - (if j < i ∧ i < m then w j i else 0) = w i j
  by_cases hlt : i < j
  · have h1 : i < j ∧ j < m := ⟨hlt, hj⟩
    have h2 : ¬ (j < i ∧ i < m) := by intro hc; exact absurd hc.1 (by omega)
    simp [h1, h2]
  · by_cases hgt : j < i
    · have h1 : ¬ (i < j ∧ j < m) := by intro hc; exact hlt hc.1
      have h2 : j < i ∧ i < m := ⟨hgt, hi⟩
      rw [if_neg h1, if_pos h2]
      have := hw i j
      omega
    · have hij : i = j := by omega
      subst hij
      have hz := antisym_diag_zero w hw i
      omega

/-- The same sentence in the form the sealed boundary wrote it: as an
    equality of vectors on the range, rather than pointwise. -/
theorem spanning_funext (w : Nat → Nat → Int) (hw : ∀ i j, w i j = - w j i) (m : Nat) :
    ∀ i j, i < m → j < m → spanSum w m i j = w i j :=
  fun i j hi hj => spanning w hw m i j hi hj

/-! ### Q1's second clause — the direction of implication

    The charge asks whether the spanning statement follows from the sealed
    characterization of the image, or the characterization from it, or
    neither. The answer this file earns is: **the spanning statement gives
    the characterization, on the range they share, and it gives it by one
    rewrite** — because the combinatorial identity above already exhibits
    the spanning sum AS the antisymmetrizer applied to an explicit
    witness. The converse is not available on the same terms; see the
    letter accompanying this file for the obstruction, which is recorded
    rather than proved away. -/

/-- **Spanning ⟹ the image characterization**, bounded to the range.
    Every antisymmetric `w` is, on `[0,m) × [0,m)`, the antisymmetrizer of
    an explicit vector — and the witness is exactly the coefficient
    function the spanning sum uses. The proof is the spanning theorem
    composed with the identity underneath it: no further induction, no
    further hypothesis. -/
theorem image_characterization_from_spanning
    (w : Nat → Nat → Int) (hw : ∀ i j, w i j = - w j i) (m i j : Nat)
    (hi : i < m) (hj : j < m) :
    antiM (upperPart w m) i j = w i j := by
  rw [← spanSum_eq_antiM_upperPart]
  exact spanning w hw m i j hi hj

/-- And the witness the bounded statement uses agrees, inside the range,
    with the sealed statement's unbounded witness `fun i j => if i < j
    then w i j else 0` — so the two characterizations are the same
    sentence about the same vector wherever both are defined, and the
    bound is the sum's, not the witness's. -/
theorem upperPart_eq_sealed_witness (w : Nat → Nat → Int) (m a b : Nat) (hb : b < m) :
    upperPart w m a b = (if a < b then w a b else 0) := by
  show (if a < b ∧ b < m then w a b else 0) = (if a < b then w a b else 0)
  by_cases h : a < b
  · have h1 : a < b ∧ b < m := ⟨h, hb⟩
    rw [if_pos h1, if_pos h]
  · have h1 : ¬ (a < b ∧ b < m) := by intro hc; exact h hc.1
    rw [if_neg h1, if_neg h]
