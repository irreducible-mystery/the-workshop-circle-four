/-
  Circle Four — Q2: the quotient, constructed; and what the transfer costs.

  THE CHARGE'S SECOND QUESTION, verbatim: "Can the quotient of the gauge
  relation be constructed within this record's constraints, and do the
  sealed classification results transfer to it unchanged, or only under
  hypotheses the sealed statements do not carry?"

  Zero imports, in the sealed artifact's manner: the kernel alone, no
  lake, no mathlib, no Std. Toolchain pinned leanprover/lean4:v4.32.0.

  WHAT THIS FILE IS, AND IS NOT. It is the quotient construction and the
  transfer theorem, stated over an ABSTRACT relation and an ABSTRACT
  domain predicate. It carries no declaration out of the sealed artifact
  and therefore claims nothing about `GZ`, about `GaugeEquivOnLabels`, or
  about any sealed theorem: the instantiation is named in the
  accompanying letter as remaining work, with the exact obligations
  listed. What is proved here is the shape of the transfer — and the
  shape is the answer to the question's second clause, because the
  hypotheses the transfer needs are the theorem's own explicit
  arguments, where anyone can count them.

  WHY ABSTRACT IS THE HONEST FORM HERE. The sealed classification is
  three sentences about a relation and a domain: the relation is an
  equivalence; every element OF THE DOMAIN is related to one of two named
  points; those two points are not related to each other. Nothing in the
  transfer uses anything else. Proving it abstractly is therefore not a
  weakening — it is the measurement of exactly which sealed facts the
  quotient consumes, which is what the question asks.
-/

/-! ### The construction

    `Quot` is Lean's own, in the prelude: no mathlib, no `Setoid`
    instance needed, no import. So the first half of the question has a
    one-word answer, and this section is that word spelled out. -/

/-- The domain the classification actually speaks about: the elements
    satisfying the predicate the sealed statements carry as hypotheses.
    Reifying those hypotheses into a TYPE is the step the sealed
    statements do not take — they quantify over a free variable and
    discharge the conditions as arguments. -/
def Dom (α : Type) (P : α → Prop) : Type := { x : α // P x }

/-- The relation, restricted to the domain. -/
def DomRel {α : Type} (P : α → Prop) (R : α → α → Prop) : Dom α P → Dom α P → Prop :=
  fun x y => R x.val y.val

/-- **The quotient of the gauge relation** — the type of classes, which
    the sealed record explicitly does not build. -/
def Classes {α : Type} (P : α → Prop) (R : α → α → Prop) : Type :=
  Quot (DomRel P R)

/-- The class of an element. -/
def cls {α : Type} {P : α → Prop} {R : α → α → Prop} (x : Dom α P) : Classes P R :=
  Quot.mk (DomRel P R) x

/-- Equivalent elements have equal classes — the quotient's defining
    property, and the direction that makes the class count an upper
    bound. -/
theorem cls_eq_of_rel {α : Type} {P : α → Prop} {R : α → α → Prop}
    (x y : Dom α P) (h : R x.val y.val) : (cls x : Classes P R) = cls y :=
  Quot.sound h

/-! ### The transfer

    Each theorem below names, in its own binders, exactly which sealed
    facts it consumes. Counting the binders is the answer to "unchanged,
    or only under hypotheses the sealed statements do not carry." -/

/-- **The upper bound transfers with no new hypothesis at all.** If every
    element of the domain is related to one of two named points, and those
    points lie in the domain, then every class is one of two classes. The
    sealed `at_most_two_classes` is exactly the hypothesis `hcover`; the
    membership facts `h0` and `h1` are the ones it does not carry. -/
theorem classes_at_most_two {α : Type} {P : α → Prop} {R : α → α → Prop}
    (r₀ r₁ : α) (h0 : P r₀) (h1 : P r₁)
    (hcover : ∀ x : α, P x → R x r₀ ∨ R x r₁) :
    ∀ q : Classes P R,
      q = cls ⟨r₀, h0⟩ ∨ q = cls ⟨r₁, h1⟩ := by
  intro q
  induction q using Quot.ind with
  | mk x =>
    rcases hcover x.val x.property with h | h
    · exact Or.inl (cls_eq_of_rel x ⟨r₀, h0⟩ h)
    · exact Or.inr (cls_eq_of_rel x ⟨r₁, h1⟩ h)

/-- **The lower bound needs reflexivity, symmetry and transitivity** —
    all three sealed, and all three used here and nowhere else. The
    separating map is the relation itself with one point fixed; it
    descends to the quotient exactly because the relation is an
    equivalence, and it tells the two classes apart exactly because the
    sealed non-collapse says they are not related. -/
theorem classes_two_distinct {α : Type} {P : α → Prop} {R : α → α → Prop}
    (r₀ r₁ : α) (h0 : P r₀) (h1 : P r₁)
    (hrefl : ∀ x : α, R x x)
    (hsymm : ∀ x y : α, R x y → R y x)
    (htrans : ∀ x y z : α, R x y → R y z → R x z)
    (hnc : ¬ R r₀ r₁) :
    (cls ⟨r₀, h0⟩ : Classes P R) ≠ cls ⟨r₁, h1⟩ := by
  intro hEq
  have hdesc : ∀ x y : Dom α P, DomRel P R x y → (R x.val r₀) = (R y.val r₀) := by
    intro x y hxy
    apply propext
    constructor
    · intro hx
      exact htrans y.val x.val r₀ (hsymm x.val y.val hxy) hx
    · intro hy
      exact htrans x.val y.val r₀ hxy hy
  have hlift : Quot.lift (fun x : Dom α P => R x.val r₀) hdesc (cls ⟨r₀, h0⟩ : Classes P R)
             = Quot.lift (fun x : Dom α P => R x.val r₀) hdesc (cls ⟨r₁, h1⟩ : Classes P R) := by
    rw [hEq]
  have hred : (R r₀ r₀) = (R r₁ r₀) := hlift
  have h₁₀ : R r₁ r₀ := by
    rw [← hred]
    exact hrefl r₀
  exact hnc (hsymm r₁ r₀ h₁₀)

/-- **Exactly two classes, on the quotient**, as one statement: the two
    class-representatives are distinct as classes, and every class is one
    of them. This is the sealed `exactly_two_classes` transferred — and
    the binder list is the receipt for what the transfer cost. -/
theorem classes_exactly_two {α : Type} {P : α → Prop} {R : α → α → Prop}
    (r₀ r₁ : α) (h0 : P r₀) (h1 : P r₁)
    (hrefl : ∀ x : α, R x x)
    (hsymm : ∀ x y : α, R x y → R y x)
    (htrans : ∀ x y z : α, R x y → R y z → R x z)
    (hnc : ¬ R r₀ r₁)
    (hcover : ∀ x : α, P x → R x r₀ ∨ R x r₁) :
    (cls ⟨r₀, h0⟩ : Classes P R) ≠ cls ⟨r₁, h1⟩
      ∧ ∀ q : Classes P R, q = cls ⟨r₀, h0⟩ ∨ q = cls ⟨r₁, h1⟩ :=
  ⟨classes_two_distinct r₀ r₁ h0 h1 hrefl hsymm htrans hnc,
   classes_at_most_two r₀ r₁ h0 h1 hcover⟩

/-! ### The measurement the question asks for

    The transfer consumed, in total: `hrefl`, `hsymm`, `htrans`, `hnc`,
    `hcover` — five facts, every one of them sealed — and `h0`, `h1`,
    which are **not** sealed statements but membership facts about the
    two named representatives.

    That asymmetry is the whole answer to the second clause, and the
    theorem below makes it impossible to overlook: it is `classes_exactly_two`
    with the sealed facts alone, and it cannot be closed, because `cls`
    cannot be applied to a representative that is not known to be in the
    domain. The statement that CAN be proved from the sealed facts alone
    is weaker — at most two classes, with no claim that both occur: -/

/-- **What the sealed statements give with no membership facts added.**
    Every class is the class of some domain element related to `r₀`, or of
    one related to `r₁`. Note what is missing: no claim that two distinct
    classes exist, because without `P r₀` and `P r₁` neither
    representative names a class at all. -/
theorem classes_at_most_two_weak {α : Type} {P : α → Prop} {R : α → α → Prop}
    (r₀ r₁ : α)
    (hcover : ∀ x : α, P x → R x r₀ ∨ R x r₁) :
    ∀ q : Classes P R, ∃ x : Dom α P, q = cls x ∧ (R x.val r₀ ∨ R x.val r₁) := by
  intro q
  induction q using Quot.ind with
  | mk x =>
    exact ⟨x, rfl, hcover x.val x.property⟩

/-- And the count is genuinely a count: two domain elements land in the
    same class exactly when the relation says so, provided the relation is
    an equivalence. The forward direction is `Quot.sound`; the backward
    direction is what makes "class" a faithful name rather than a
    coarsening. -/
theorem cls_eq_iff_rel {α : Type} {P : α → Prop} {R : α → α → Prop}
    (hrefl : ∀ x : α, R x x)
    (hsymm : ∀ x y : α, R x y → R y x)
    (htrans : ∀ x y z : α, R x y → R y z → R x z)
    (x y : Dom α P) :
    ((cls x : Classes P R) = cls y) ↔ R x.val y.val := by
  constructor
  · intro hEq
    have hdesc : ∀ u v : Dom α P, DomRel P R u v → (R x.val u.val) = (R x.val v.val) := by
      intro u v huv
      apply propext
      constructor
      · intro hxu
        exact htrans x.val u.val v.val hxu huv
      · intro hxv
        exact htrans x.val v.val u.val hxv (hsymm u.val v.val huv)
    have hlift : Quot.lift (fun u : Dom α P => R x.val u.val) hdesc (cls x : Classes P R)
               = Quot.lift (fun u : Dom α P => R x.val u.val) hdesc (cls y : Classes P R) := by
      rw [hEq]
    have hred : (R x.val x.val) = (R x.val y.val) := hlift
    rw [← hred]
    exact hrefl x.val
  · intro h
    exact cls_eq_of_rel x y h
