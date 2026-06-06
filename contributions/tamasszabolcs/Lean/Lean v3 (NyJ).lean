import Mathlib

/-!
# O-Minimal Geometry — Formalization in Lean 4 / Mathlib

Theorems:
  1. Extrema of Finite Sets
  2. Intervals in Dense Orders
  3. Definable Completeness
  4. Supremum of a Finite Union
-/

/-! ## O-minimal structure scaffold -/

def IsBoundedOpenInterval {M : Type*} [LinearOrder M] (I : Set M) : Prop :=
  ∃ a b : M, a < b ∧ I = Set.Ioo a b

def IsLeftUnboundedInterval {M : Type*} [LinearOrder M] (I : Set M) : Prop :=
  ∃ b : M, I = Set.Iio b

def IsOpenInterval {M : Type*} [LinearOrder M] (I : Set M) : Prop :=
  IsBoundedOpenInterval I ∨ IsLeftUnboundedInterval I

/-!
## Axiomatized o-minimal structure

We axiomatize the o-minimal setting by taking as primitive:
- a dense linear order,
- a predicate `Definable : Set M → Prop`,
- closure properties of definable sets,
- the one-dimensional o-minimal decomposition property.

The decomposition property says that every definable subset of `M` is a finite
union of open interval components and point components.
-/
class OMinimalStructure (M : Type*) extends
    LinearOrder M, DenselyOrdered M, NoMinOrder M where
  /-- The collection of definable subsets of `M`. -/
  Definable       : Set M → Prop

  /-- Boolean closure: `∅` and `M` are definable. -/
  definable_empty : Definable ∅
  definable_univ  : Definable Set.univ

  /-- Boolean closure: definable sets are closed under union, intersection, complement. -/
  definable_union : ∀ S T, Definable S → Definable T → Definable (S ∪ T)
  definable_inter : ∀ S T, Definable S → Definable T → Definable (S ∩ T)
  definable_compl : ∀ S, Definable S → Definable Sᶜ

  /-- Atomic definable sets I: all singletons `{x}` are definable. -/
  definable_singleton : ∀ x : M, Definable {x}

  /-- Atomic definable sets II: all open intervals `(a, b)` are definable. -/
  definable_Ioo : ∀ a b : M, Definable (Set.Ioo a b)

  /-- Atomic definable sets III: all left-unbounded intervals `(-∞, b)` are definable. -/
  definable_Iio : ∀ b : M, Definable (Set.Iio b)

  /--
  O-minimality axiom.

  Every definable subset of `M` is a finite union of open interval components
  and finitely many point components.
  -/
  omin_decomp : ∀ S : Set M, Definable S →
    ∃ (intervals : Finset (Set M)) (points : Finset M),
      (∀ I ∈ intervals, IsOpenInterval I) ∧
      (∀ I ∈ intervals, Definable I) ∧
      S = (intervals.sup id) ∪ (↑points : Set M)

/-- Derived: finite unions of definable sets are definable. -/
lemma OMinimalStructure.definable_iUnion_fin {M : Type*} [OMinimalStructure M]
    (s : Finset (Set M)) (hs : ∀ C ∈ s, OMinimalStructure.Definable C) :
    OMinimalStructure.Definable (s.sup id) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sup_empty]
      exact OMinimalStructure.definable_empty
  | insert A B hAB ih =>
      simp only [Finset.sup_insert, id]
      apply OMinimalStructure.definable_union
      · exact hs A (Finset.mem_insert_self A B)
      · apply ih
        intro C hC
        exact hs C (Finset.mem_insert_of_mem hC)

/-- Derived: every finite set of points is definable. -/
lemma OMinimalStructure.definable_finset_coe {M : Type*} [OMinimalStructure M]
    (P : Finset M) :
    OMinimalStructure.Definable (↑P : Set M) := by
  classical
  induction P using Finset.induction with
  | empty =>
      simp only [Finset.coe_empty]
      exact OMinimalStructure.definable_empty
  | insert x P hxP ih =>
      rw [Finset.coe_insert, Set.insert_eq]
      exact OMinimalStructure.definable_union _ _
        (OMinimalStructure.definable_singleton x) ih

/-! ## Theorem 1: Extrema of Finite Sets -/

section Thm1

variable {M : Type*} [LinearOrder M]

theorem finite_set_has_max (A : Finset M) (hA : A.Nonempty) :
    ∃ x ∈ A, ∀ y ∈ A, y ≤ x :=
  ⟨A.max' hA, A.max'_mem hA, fun y hy => A.le_max' y hy⟩

theorem finite_set_has_min (A : Finset M) (hA : A.Nonempty) :
    ∃ x ∈ A, ∀ y ∈ A, x ≤ y :=
  ⟨A.min' hA, A.min'_mem hA, fun y hy => A.min'_le y hy⟩

/--
**Theorem 1**: Every finite non-empty subset has both a minimum and a maximum.
-/
theorem thm1_extrema_of_finite_sets (A : Finset M) (hA : A.Nonempty) :
    (∃ m ∈ A, ∀ y ∈ A, m ≤ y) ∧
    (∃ x ∈ A, ∀ y ∈ A, y ≤ x) :=
  ⟨finite_set_has_min A hA, finite_set_has_max A hA⟩

end Thm1

/-! ## Theorem 2: Intervals in Dense Orders -/

section Thm2

variable {M : Type*} [LinearOrder M] [DenselyOrdered M] [NoMinOrder M]

omit [NoMinOrder M] in
/--
There is a strictly decreasing sequence `ℕ → M` with all values in `(a, b)`.
-/
lemma nat_decreasing_seq_in_interval (a b : M) (hab : a < b) :
    ∃ f : ℕ → M, (∀ n, f n ∈ Set.Ioo a b) ∧
      (∀ n, f (n + 1) < f n) := by
  obtain ⟨x₀, hx₀a, hx₀b⟩ := exists_between hab

  have step : ∀ x : M, a < x → ∃ y : M, a < y ∧ y < x :=
    fun x hx => exists_between hx

  choose g hg using step

  let F : ℕ → {x : M // a < x ∧ x < b} :=
    fun n => n.rec
      ⟨x₀, hx₀a, hx₀b⟩
      (fun _ xn =>
        ⟨g xn.val xn.prop.1,
          (hg xn.val xn.prop.1).1,
          lt_trans (hg xn.val xn.prop.1).2 xn.prop.2⟩)

  refine ⟨fun n => (F n).val, fun n => (F n).prop, fun n => ?_⟩
  exact (hg (F n).val (F n).prop.1).2

omit [NoMinOrder M] in
/--
**Theorem 2**: The open interval `(a, b)` is infinite whenever `a < b`.
-/
theorem thm2_open_interval_infinite (a b : M) (hab : a < b) :
    Set.Infinite (Set.Ioo a b) := by
  obtain ⟨f, hf_mem, hf_dec⟩ := nat_decreasing_seq_in_interval a b hab

  have hf_strict : StrictAnti f := by
    intro m n hmn
    induction hmn with
    | refl =>
        exact hf_dec m
    | step h ih =>
        exact lt_trans (hf_dec _) ih

  exact Set.infinite_of_injective_forall_mem hf_strict.injective hf_mem

/-- Any open interval is infinite. -/
lemma openInterval_infinite (I : Set M) (hI : IsOpenInterval I) :
    Set.Infinite I := by
  rcases hI with ⟨a, b, hab, rfl⟩ | ⟨b, rfl⟩
  · exact thm2_open_interval_infinite a b hab
  · obtain ⟨a, ha⟩ := exists_lt b
    exact (thm2_open_interval_infinite a b ha).mono Set.Ioo_subset_Iio_self

omit [NoMinOrder M] in
/-- The supremum of the bounded open interval `(a, b)` is `b`. -/
lemma open_interval_isLUB (a b : M) (hab : a < b) :
    IsLUB (Set.Ioo a b) b := by
  refine ⟨fun x hx => le_of_lt hx.2, fun y hy => ?_⟩
  by_contra hlt
  simp only [not_le] at hlt

  by_cases hay : a ≤ y
  · obtain ⟨z, hyz, hzb⟩ := exists_between hlt
    exact absurd (hy ⟨lt_of_le_of_lt hay hyz, hzb⟩) (not_le.mpr hyz)
  · simp only [not_le] at hay
    obtain ⟨z, haz, hzb⟩ := exists_between hab
    exact absurd (hy ⟨haz, hzb⟩) (not_le.mpr (lt_trans hay haz))

omit [NoMinOrder M] in
/-- The supremum of the left-unbounded interval `(-∞, b)` is `b`. -/
lemma Iio_isLUB (b : M) :
    IsLUB (Set.Iio b) b := by
  refine ⟨fun x hx => le_of_lt hx, fun y hy => ?_⟩
  by_contra hlt
  simp only [not_le] at hlt
  obtain ⟨z, hyz, hzb⟩ := exists_between hlt
  exact absurd (hy hzb) (not_le.mpr hyz)

omit [NoMinOrder M] in
/-- Any open interval that is bounded above has a supremum. -/
lemma open_interval_has_sup (I : Set M) (hI : IsOpenInterval I)
    (_hbdd : BddAbove I) (_hne : I.Nonempty) :
    ∃ s : M, IsLUB I s := by
  rcases hI with ⟨a, b, hab, rfl⟩ | ⟨b, rfl⟩
  · exact ⟨b, open_interval_isLUB a b hab⟩
  · exact ⟨b, Iio_isLUB b⟩

/-- Any open interval is non-empty. -/
lemma openInterval_nonempty (I : Set M) (hI : IsOpenInterval I) :
    I.Nonempty := by
  rcases hI with ⟨a, b, hab, rfl⟩ | ⟨b, rfl⟩
  · obtain ⟨z, haz, hzb⟩ := exists_between hab
    exact ⟨z, haz, hzb⟩
  · obtain ⟨a, ha⟩ := exists_lt b
    exact ⟨a, ha⟩

end Thm2

/-! ## Helpers: collectSuprema and finset_points_isLUB -/

section LinearOrderHelpers

variable {M : Type*} [LinearOrder M]

lemma finset_points_isLUB (P : Finset M) (hP : P.Nonempty) :
    IsLUB (↑P : Set M) (P.max' hP) := by
  constructor
  · intro x hx
    exact P.le_max' x (Finset.mem_coe.mp hx)
  · intro y hy
    exact hy (Finset.mem_coe.mpr (P.max'_mem hP))

/--
Finite set of chosen suprema: for each component, pick its supremum.
-/
noncomputable def collectSuprema
    (components : Finset (Set M))
    (sup_of : ∀ C ∈ components, M) :
    Finset M :=
  components.attach.image (fun ⟨C, hC⟩ => sup_of C hC)

lemma collectSuprema_nonempty
    {components : Finset (Set M)}
    {sup_of : ∀ C ∈ components, M}
    (hcomp : components.Nonempty) :
    (collectSuprema components sup_of).Nonempty := by
  obtain ⟨C, hC⟩ := hcomp
  exact
    ⟨sup_of C hC,
      Finset.mem_image.mpr ⟨⟨C, hC⟩, Finset.mem_attach _ _, rfl⟩⟩

lemma mem_collectSuprema
    {components : Finset (Set M)}
    {sup_of : ∀ C ∈ components, M}
    {s : M} :
    s ∈ collectSuprema components sup_of ↔
      ∃ C, ∃ hC : C ∈ components, sup_of C hC = s := by
  simp only [collectSuprema, Finset.mem_image, Finset.mem_attach, true_and]
  constructor
  · rintro ⟨⟨C, hC⟩, rfl⟩
    exact ⟨C, hC, rfl⟩
  · rintro ⟨C, hC, rfl⟩
    exact ⟨⟨C, hC⟩, rfl⟩

/--
Membership in `components.sup id` means membership in one of the components.

Mathematically:

`x ∈ ⋃ C ∈ components, C ↔ ∃ C ∈ components, x ∈ C`.
-/
lemma mem_finset_sup_id {M : Type*} [LinearOrder M]
    {components : Finset (Set M)} {x : M} :
    x ∈ components.sup id ↔ ∃ C ∈ components, x ∈ C := by
  classical
  induction components using Finset.induction with
  | empty =>
      simp
  | insert A B hAB ih =>
      simp [Finset.sup_insert]

end LinearOrderHelpers

/-! ## Theorem 4: Supremum of a Finite Union -/

section Thm4

variable {M : Type*} [OMinimalStructure M]

/--
**Theorem 4**:
`sup(A₁ ∪ … ∪ Aₙ) = max{sup(A₁), …, sup(Aₙ)}`.

We exhibit the finite set `S = {sup(A₁), …, sup(Aₙ)}` and prove that
`S.max'` is a least upper bound of the finite union.
-/
theorem thm4_sup_of_finite_union
    (components : Finset (Set M))
    (_hdef : ∀ C ∈ components, OMinimalStructure.Definable C)
    (_hne  : ∀ C ∈ components, (C : Set M).Nonempty)
    (hsup  : ∀ C ∈ components, ∃ s : M, IsLUB C s)
    (hcomp : components.Nonempty) :
    let sup_of : ∀ C ∈ components, M := fun C hC => (hsup C hC).choose
    let S   := collectSuprema components sup_of
    let hS  := collectSuprema_nonempty hcomp
    IsLUB (components.sup id) (S.max' hS) := by
  set sup_of : ∀ C ∈ components, M := fun C hC => (hsup C hC).choose

  have sup_spec : ∀ C (hC : C ∈ components), IsLUB C (sup_of C hC) :=
    fun C hC => (hsup C hC).choose_spec

  set S := collectSuprema components sup_of
  have hS := collectSuprema_nonempty (sup_of := sup_of) hcomp

  constructor
  · intro x hx

    have ⟨C, hCm, hxC⟩ : ∃ C ∈ components, x ∈ C :=
      mem_finset_sup_id.mp hx

    exact le_trans ((sup_spec C hCm).1 hxC)
      (Finset.le_max' S _ (mem_collectSuprema.mpr ⟨C, hCm, rfl⟩))

  · intro y hy
    apply Finset.max'_le
    intro s hs

    obtain ⟨C, hCm, rfl⟩ := mem_collectSuprema.mp hs

    apply (sup_spec C hCm).2
    intro x hxC

    apply hy
    exact mem_finset_sup_id.mpr ⟨C, hCm, hxC⟩

/--
Corollary: extract plain existence of a supremum for use in definable
completeness.
-/
lemma sup_union_exists
    (components : Finset (Set M))
    (_hdef : ∀ C ∈ components, OMinimalStructure.Definable C)
    (_hne  : ∀ C ∈ components, (C : Set M).Nonempty)
    (hsup  : ∀ C ∈ components, ∃ s : M, IsLUB C s)
    (hcomp : components.Nonempty) :
    ∃ s : M, IsLUB (components.sup id) s :=
  ⟨_, thm4_sup_of_finite_union components _hdef _hne hsup hcomp⟩

end Thm4

/-! ## Theorem 3: Definable Completeness -/

section Thm3

variable {M : Type*} [OMinimalStructure M]

/--
**Theorem 3**:
Every non-empty definable set bounded above has a supremum in `M`.
-/
theorem thm3_definable_completeness
    (S    : Set M)
    (hS   : OMinimalStructure.Definable S)
    (hne  : S.Nonempty)
    (hbdd : BddAbove S) :
    ∃ s : M, IsLUB S s := by
  obtain ⟨intervals, points, hI, hIdef, hdecomp⟩ :=
    OMinimalStructure.omin_decomp S hS

  have hS_eq : S = (intervals.sup id) ∪ (↑points : Set M) := hdecomp

  have hbdd_comp : ∀ C : Set M, C ⊆ S → BddAbove C :=
    fun C hCS => hbdd.mono hCS

  have hI_ne : ∀ I ∈ intervals, (I : Set M).Nonempty :=
    fun I hIm => openInterval_nonempty I (hI I hIm)

  have hI_sup : ∀ I ∈ intervals, ∃ s : M, IsLUB I s := by
    intro I hIm
    have hI_sub : I ⊆ S :=
      fun x hxI =>
        hS_eq ▸ Set.mem_union_left _ (Finset.le_sup (f := id) hIm hxI)
    exact open_interval_has_sup I (hI I hIm) (hbdd_comp I hI_sub) (hI_ne I hIm)

  -- Definability of the point set.
  have hP_def : OMinimalStructure.Definable (↑points : Set M) :=
    OMinimalStructure.definable_finset_coe points

  by_cases hPne : (points : Finset M).Nonempty

  · have hP_sup : ∃ s : M, IsLUB (↑points : Set M) s :=
      ⟨points.max' hPne, finset_points_isLUB points hPne⟩

    have hpoints_not_in : (↑points : Set M) ∉ intervals := fun hmem =>
      openInterval_infinite _ (hI _ hmem) (Set.toFinite _)

    let allComponents : Finset (Set M) :=
      intervals.cons (↑points) hpoints_not_in

    have hall_def : ∀ C ∈ allComponents, OMinimalStructure.Definable C := by
      intro C hC
      simp only [allComponents, Finset.mem_cons] at hC
      rcases hC with rfl | hC
      · exact hP_def
      · exact hIdef C hC

    have hall_ne : ∀ C ∈ allComponents, (C : Set M).Nonempty := by
      intro C hC
      simp only [allComponents, Finset.mem_cons] at hC
      rcases hC with rfl | hC
      · exact Finset.coe_nonempty.mpr hPne
      · exact hI_ne C hC

    have hall_sup : ∀ C ∈ allComponents, ∃ s : M, IsLUB C s := by
      intro C hC
      simp only [allComponents, Finset.mem_cons] at hC
      rcases hC with rfl | hC
      · exact hP_sup
      · exact hI_sup C hC

    obtain ⟨s, hs⟩ :=
      sup_union_exists allComponents hall_def hall_ne hall_sup
        ⟨↑points, Finset.mem_cons_self _ _⟩

    have hsup_eq :
        allComponents.sup id = (↑points : Set M) ∪ intervals.sup id := by
      simp [allComponents, id]

    refine ⟨s, ?_, ?_⟩

    · intro x hxS
      apply hs.1
      rw [hsup_eq, hS_eq] at *
      rcases hxS with hxI | hxP
      · exact Set.mem_union_right _ hxI
      · exact Set.mem_union_left _ hxP

    · intro y hy
      apply hs.2
      intro x hx
      rw [hsup_eq] at hx
      rcases hx with hxP | hxI
      · exact hy (hS_eq ▸ Set.mem_union_right _ hxP)
      · exact hy (hS_eq ▸ Set.mem_union_left _ hxI)

  · rw [Finset.not_nonempty_iff_eq_empty.mp hPne] at hS_eq
    simp only [Finset.coe_empty, Set.union_empty] at hS_eq

    by_cases hIne : intervals.Nonempty

    · obtain ⟨s, hs⟩ :=
        sup_union_exists intervals hIdef hI_ne hI_sup hIne

      exact ⟨s, hS_eq ▸ hs⟩

    · rw [Finset.not_nonempty_iff_eq_empty.mp hIne] at hS_eq
      simp only [Finset.sup_empty] at hS_eq
      exact absurd (hS_eq ▸ hne) Set.not_nonempty_empty

end Thm3

/-! ## Exact theorem statements matching the requested LaTeX formulations -/

section ExactStatements

variable {M : Type*} [OMinimalStructure M]

/--
Exact version of Extrema of Finite Sets.

Let `(M,<)` be the underlying totally ordered set of an o-minimal structure.
Every finite, non-empty subset `A ⊆ M` has a minimum and a maximum.
-/
theorem exact_extrema_of_finite_sets
    (A : Finset M) (hA : A.Nonempty) :
    (∃ m ∈ A, ∀ y ∈ A, m ≤ y) ∧
    (∃ x ∈ A, ∀ y ∈ A, y ≤ x) :=
  thm1_extrema_of_finite_sets A hA

/--
Exact version of Intervals in Dense Orders.

In an o-minimal structure `M = (M,<,...)`, for any `a,b ∈ M` with `a < b`,
the open interval `(a,b)` is infinite.
-/
theorem exact_interval_infinite
    (a b : M) (hab : a < b) :
    Set.Infinite (Set.Ioo a b) :=
  thm2_open_interval_infinite a b hab

/--
Helper: the finite set of indexed suprema.

Given indexed sets `A i`, and a chosen supremum `sup_of i` for each one,
this is the finite set `{sup(A_i) : i}`.
-/
noncomputable def indexedSuprema
    {ι : Type*} [Fintype ι]
    (_A : ι → Set M)
    (sup_of : ι → M) :
    Finset M :=
  Finset.univ.image sup_of

lemma indexedSuprema_nonempty
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {_A : ι → Set M}
    {sup_of : ι → M} :
    (indexedSuprema _A sup_of).Nonempty := by
  classical
  obtain ⟨i⟩ := ‹Nonempty ι›
  refine ⟨sup_of i, ?_⟩
  unfold indexedSuprema
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

lemma mem_indexedSuprema
    {ι : Type*} [Fintype ι]
    {_A : ι → Set M}
    {sup_of : ι → M}
    {s : M} :
    s ∈ indexedSuprema _A sup_of ↔ ∃ i : ι, sup_of i = s := by
  classical
  constructor
  · intro hs
    unfold indexedSuprema at hs
    rcases Finset.mem_image.mp hs with ⟨i, _hi, his⟩
    exact ⟨i, his⟩
  · rintro ⟨i, rfl⟩
    unfold indexedSuprema
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

/--
Exact version of Supremum of a Finite Union.

Let `Aᵢ`, indexed by a finite nonempty type `ι`, be non-empty definable subsets
of `M`. If each `Aᵢ` has a supremum in `M`, then their finite union has a
supremum, and that supremum is the maximum of the individual suprema.

This formalises:

`sup (⋃ i, Aᵢ) = max {sup(Aᵢ) : i}`

by proving that the maximum of the finite set of individual suprema is an
`IsLUB` of the union.
-/
theorem exact_supremum_of_finite_union
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (A : ι → Set M)
    (_hdef : ∀ i : ι, OMinimalStructure.Definable (A i))
    (_hne : ∀ i : ι, (A i).Nonempty)
    (hsup : ∀ i : ι, ∃ s : M, IsLUB (A i) s) :
    let sup_of : ι → M := fun i => Classical.choose (hsup i)
    let S : Finset M := indexedSuprema A sup_of
    let hS : S.Nonempty := indexedSuprema_nonempty
    IsLUB (⋃ i : ι, A i) (S.max' hS) := by
  classical

  dsimp

  let sup_of : ι → M := fun i => Classical.choose (hsup i)

  have sup_spec : ∀ i : ι, IsLUB (A i) (sup_of i) := by
    intro i
    exact Classical.choose_spec (hsup i)

  let S : Finset M := indexedSuprema A sup_of

  have hS : S.Nonempty := indexedSuprema_nonempty

  constructor
  · -- The maximum of the individual suprema is an upper bound for the union.
    intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩

    have hmem : sup_of i ∈ S := by
      unfold S
      exact mem_indexedSuprema.mpr ⟨i, rfl⟩

    exact le_trans ((sup_spec i).1 hxi)
      (Finset.le_max' S (sup_of i) hmem)

  · -- It is the least upper bound.
    intro y hy
    apply Finset.max'_le
    intro s hs

    rcases mem_indexedSuprema.mp hs with ⟨i, his⟩
    rw [← his]

    apply (sup_spec i).2
    intro x hx
    apply hy
    exact Set.mem_iUnion.mpr ⟨i, hx⟩

/--
Exact version of Definable Completeness.

Let `M` be an o-minimal structure. Every non-empty definable set `S ⊆ M`
that is bounded above has a supremum in `M`.
-/
theorem exact_definable_completeness
    (S : Set M)
    (hS : OMinimalStructure.Definable S)
    (hne : S.Nonempty)
    (hbdd : BddAbove S) :
    ∃ s : M, IsLUB S s :=
  thm3_definable_completeness S hS hne hbdd

end ExactStatements

/-!
## Theorem 5: Infinite Unions of Points and Intervals
-/

section Thm5

variable {M : Type*} [LinearOrder M]

omit [LinearOrder M] in
/--
**Infinite Unions of Points and Intervals**
Let `S ⊆ M` be constructed from the union of a finite number of points and open intervals.
If `S` is infinite, then `S` must contain an open interval (i.e., the set of intervals is non-empty).
-/
theorem thm5_infinite_union_contains_interval
    (S : Set M)
    (intervals : Finset (Set M))
    (points : Finset M)
    (hS_eq : S = (intervals.sup id) ∪ (↑points : Set M))
    (hS_inf : Set.Infinite S) :
    intervals.Nonempty := by
  by_contra h_empty
  rw [Finset.not_nonempty_iff_eq_empty] at h_empty
  have hS_fin : S.Finite := by
    subst hS_eq
    rw [h_empty]
    simp only [Finset.sup_empty, Set.bot_eq_empty, Set.empty_union]
    exact Set.toFinite (↑points : Set M)
  exact hS_inf hS_fin

end Thm5


/-!
## Theorem 6: Supremum of Points and Intervals (Extended Domain Dichotomy)
-/

section Thm6

variable {M : Type*} [OMinimalStructure M]

/--
**Supremum of a Union of Points and Intervals**
Let `S ⊆ M` be a non-empty definable set.
Either `S` is bounded above and possesses a supremum in `M`,
or `S` is unbounded above, which corresponds to a supremum of `+∞` in the extended domain `M ∪ {+∞}`.
-/
theorem thm6_supremum_dichotomy
    (S : Set M)
    (hS : OMinimalStructure.Definable S)
    (hne : S.Nonempty) :
    (∃ s : M, IsLUB S s) ∨ (∀ x : M, ∃ y ∈ S, x < y) := by
  by_cases hbdd : BddAbove S
  · exact Or.inl (thm3_definable_completeness S hS hne hbdd)
  · apply Or.inr
    intro x
    by_contra h_not
    push Not at h_not
    have h_upper : x ∈ upperBounds S := h_not
    exact hbdd ⟨x, h_upper⟩

end Thm6