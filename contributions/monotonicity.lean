import Mathlib.Data.Set.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

set_option linter.unusedSimpArgs false

universe u

namespace OMinimal

def setEmpty {A : Type u} : Set A :=
  fun _ => False

def setUnion {A : Type u} (X Y : Set A) : Set A :=
  fun a => X a \/ Y a

def setInter {A : Type u} (X Y : Set A) : Set A :=
  fun a => X a /\ Y a

def setCompl {A : Type u} (X : Set A) : Set A :=
  fun a => Not (X a)

def setUniv {A : Type u} : Set A :=
  setCompl setEmpty

abbrev Power (R : Type u) (n : Nat) := Fin n -> R

namespace Power

variable {R : Type u}

def left {n m : Nat} (z : Power R (n + m)) : Power R n :=
  fun i => z (Fin.castAdd m i)

def right {n m : Nat} (z : Power R (n + m)) : Power R m :=
  fun j => z (Fin.natAdd n j)

def deleteCoord {n : Nat} (k : Fin (n + 1)) (z : Power R (n + 1)) : Power R n :=
  fun i => z (Fin.succAbove k i)

def coord1 (x : Power R 1) : R :=
  x 0

def coord2_0 (x : Power R 2) : R :=
  x 0

def coord2_1 (x : Power R 2) : R :=
  x 1

def append {n m : Nat} (x : Power R n) (y : Power R m) : Power R (n + m) :=
  Fin.append x y

@[simp] theorem left_append {n m : Nat} (x : Power R n) (y : Power R m) :
    left (append x y) = x := by
  funext i
  simp [left, append]

@[simp] theorem right_append {n m : Nat} (x : Power R n) (y : Power R m) :
    right (append x y) = y := by
  funext i
  simp [right, append]

end Power

class DenseLinearOrderNoEndpoints (R : Type u) where
  lt : R -> R -> Prop
  irrefl : forall x : R, Not (lt x x)
  trans : forall {x y z : R}, lt x y -> lt y z -> lt x z
  trichotomy : forall x y : R,
      (lt x y /\ Not (lt y x) /\ Not (x = y)) \/
      (x = y /\ Not (lt x y) /\ Not (lt y x)) \/
      (lt y x /\ Not (lt x y) /\ Not (x = y))
  dense : forall {x y : R}, lt x y -> exists z : R, lt x z /\ lt z y
  no_left_endpoint : forall x : R, exists y : R, lt y x
  no_right_endpoint : forall x : R, exists y : R, lt x y

inductive Endpoint (R : Type u) where
  | negInf : Endpoint R
  | finite : R -> Endpoint R
  | posInf : Endpoint R

namespace Endpoint

variable {R : Type u}

def lt (D : DenseLinearOrderNoEndpoints R) : Endpoint R -> Endpoint R -> Prop
  | Endpoint.negInf, Endpoint.negInf => False
  | Endpoint.negInf, Endpoint.finite _ => True
  | Endpoint.negInf, Endpoint.posInf => True
  | Endpoint.finite _, Endpoint.negInf => False
  | Endpoint.finite a, Endpoint.finite b => D.lt a b
  | Endpoint.finite _, Endpoint.posInf => True
  | Endpoint.posInf, _ => False

end Endpoint

def pointSet {R : Type u} (a : R) : Set (Power R 1) :=
  fun x => Power.coord1 x = a

def openInterval {R : Type u} (D : DenseLinearOrderNoEndpoints R)
    (a b : Endpoint R) : Set (Power R 1) :=
  fun x => Endpoint.lt D a (Endpoint.finite (Power.coord1 x)) /\
           Endpoint.lt D (Endpoint.finite (Power.coord1 x)) b

def closedOpenInterval {R : Type u} (D : DenseLinearOrderNoEndpoints R)
    (a b : R) : Set (Power R 1) :=
  setUnion (openInterval D (Endpoint.finite a) (Endpoint.finite b)) (pointSet a)

inductive FiniteUnionOfPointsAndIntervals {R : Type u}
    (D : DenseLinearOrderNoEndpoints R) : Set (Power R 1) -> Prop where
  | empty :
      FiniteUnionOfPointsAndIntervals D (setEmpty : Set (Power R 1))
  | point (a : R) :
      FiniteUnionOfPointsAndIntervals D (pointSet a)
  | interval (a b : Endpoint R) :
      FiniteUnionOfPointsAndIntervals D (openInterval D a b)
  | union {A B : Set (Power R 1)} :
      FiniteUnionOfPointsAndIntervals D A ->
      FiniteUnionOfPointsAndIntervals D B ->
      FiniteUnionOfPointsAndIntervals D (setUnion A B)

structure OMinimalStructure {R : Type u} (D : DenseLinearOrderNoEndpoints R) where
  S : (n : Nat) -> Set (Set (Power R n))

  empty_mem : forall n : Nat, S n (setEmpty : Set (Power R n))
  union_mem : forall {n : Nat} {A B : Set (Power R n)},
    S n A -> S n B -> S n (setUnion A B)
  inter_mem : forall {n : Nat} {A B : Set (Power R n)},
    S n A -> S n B -> S n (setInter A B)
  compl_mem : forall {n : Nat} {A : Set (Power R n)},
    S n A -> S n (setCompl A)

  diagonal_mem : forall {n : Nat} (i j : Fin n),
    i < j -> S n (fun x : Power R n => x i = x j)

  product_mem : forall {n m : Nat} {A : Set (Power R n)} {B : Set (Power R m)},
    S n A -> S m B ->
      S (n + m) (fun z : Power R (n + m) =>
        A (Power.left z) /\ B (Power.right z))

  project_mem : forall {n : Nat} (k : Fin (n + 1)) {A : Set (Power R (n + 1))},
    S (n + 1) A ->
      S n (fun y : Power R n =>
        exists x : Power R (n + 1), A x /\ Power.deleteCoord k x = y)

  reindex_mem : forall {n m : Nat} (sigma : Fin n -> Fin m) {A : Set (Power R n)},
    S n A -> S m (fun x : Power R m => A (fun i : Fin n => x (sigma i)))

  existsLast_mem : forall {n m : Nat} {A : Set (Power R (n + m))},
    S (n + m) A ->
      S n (fun x : Power R n => exists y : Power R m, A (Power.append x y))

  lt_mem :
    S 2 (fun p : Power R 2 => D.lt (Power.coord2_0 p) (Power.coord2_1 p))

  ominimal : forall A : Set (Power R 1),
    S 1 A <-> FiniteUnionOfPointsAndIntervals D A

namespace OMinimalStructure

variable {R : Type u} {D : DenseLinearOrderNoEndpoints R}

def Definable (M : OMinimalStructure D) {n : Nat} (A : Set (Power R n)) : Prop :=
  M.S n A

def FunctionGraph {m n : Nat} {A : Set (Power R m)} {B : Set (Power R n)}
    (f : {x : Power R m // A x} -> {y : Power R n // B y}) :
    Set (Power R (m + n)) :=
  fun z => exists hx : A (Power.left z),
    Power.right z = (f (Subtype.mk (Power.left z) hx)).1

def compGIndex {a b c : Nat} (i : Fin (a + b)) : Fin ((a + c) + b) :=
  if h : (i : Nat) < a then
    Fin.castAdd b (Fin.castAdd c (Fin.mk (i : Nat) h))
  else
    Fin.natAdd (a + c) (Fin.mk ((i : Nat) - a) (by omega))

def compHIndex {a b c : Nat} (i : Fin (b + c)) : Fin ((a + c) + b) :=
  if h : (i : Nat) < b then
    Fin.natAdd (a + c) (Fin.mk (i : Nat) h)
  else
    Fin.castAdd b (Fin.natAdd a (Fin.mk ((i : Nat) - b) (by omega)))

def compGArg {a b c : Nat} (xyz : Power R ((a + c) + b)) : Power R (a + b) :=
  fun i => xyz (compGIndex (a := a) (b := b) (c := c) i)

def compHArg {a b c : Nat} (xyz : Power R ((a + c) + b)) : Power R (b + c) :=
  fun i => xyz (compHIndex (a := a) (b := b) (c := c) i)

theorem compGArg_append {a b c : Nat}
    (xz : Power R (a + c)) (y : Power R b) :
    compGArg (R := R) (a := a) (b := b) (c := c) (Power.append xz y) =
      Power.append (Power.left xz) y := by
  funext i
  change (Power.append xz y) (compGIndex (a := a) (b := b) (c := c) i) =
    (Power.append (Power.left xz) y) i
  by_cases h : (i : Nat) < a
  · let ia : Fin a := Fin.mk (i : Nat) h
    have hi : i = Fin.castAdd b ia := by
      ext
      simp [ia]
    have hidx : compGIndex (a := a) (b := b) (c := c) i =
        Fin.castAdd b (Fin.castAdd c ia) := by
      simp [compGIndex, h, ia]
    calc
      (Power.append xz y) (compGIndex (a := a) (b := b) (c := c) i)
          = (Power.append xz y) (Fin.castAdd b (Fin.castAdd c ia)) := by
              rw [hidx]
      _ = xz (Fin.castAdd c ia) := by
              simp [Power.append]
      _ = Power.left xz ia := by
              simp [Power.left]
      _ = (Power.append (Power.left xz) y) (Fin.castAdd b ia) := by
              simp [Power.append]
      _ = (Power.append (Power.left xz) y) i := by
              rw [hi]
  · let jb : Fin b := Fin.mk ((i : Nat) - a) (by omega)
    have hi : i = Fin.natAdd a jb := by
      ext
      simp [jb]
      omega
    have hidx : compGIndex (a := a) (b := b) (c := c) i =
        Fin.natAdd (a + c) jb := by
      simp [compGIndex, h, jb]
    calc
      (Power.append xz y) (compGIndex (a := a) (b := b) (c := c) i)
          = (Power.append xz y) (Fin.natAdd (a + c) jb) := by
              rw [hidx]
      _ = y jb := by
              simp [Power.append]
      _ = (Power.append (Power.left xz) y) (Fin.natAdd a jb) := by
              simp [Power.append]
      _ = (Power.append (Power.left xz) y) i := by
              rw [hi]

theorem compHArg_append {a b c : Nat}
    (xz : Power R (a + c)) (y : Power R b) :
    compHArg (R := R) (a := a) (b := b) (c := c) (Power.append xz y) =
      Power.append y (Power.right xz) := by
  funext i
  change (Power.append xz y) (compHIndex (a := a) (b := b) (c := c) i) =
    (Power.append y (Power.right xz)) i
  by_cases h : (i : Nat) < b
  · let ib : Fin b := Fin.mk (i : Nat) h
    have hi : i = Fin.castAdd c ib := by
      ext
      simp [ib]
    have hidx : compHIndex (a := a) (b := b) (c := c) i =
        Fin.natAdd (a + c) ib := by
      simp [compHIndex, h, ib]
    calc
      (Power.append xz y) (compHIndex (a := a) (b := b) (c := c) i)
          = (Power.append xz y) (Fin.natAdd (a + c) ib) := by
              rw [hidx]
      _ = y ib := by
              simp [Power.append]
      _ = (Power.append y (Power.right xz)) (Fin.castAdd c ib) := by
              simp [Power.append]
      _ = (Power.append y (Power.right xz)) i := by
              rw [hi]
  · let jc : Fin c := Fin.mk ((i : Nat) - b) (by omega)
    have hi : i = Fin.natAdd b jc := by
      ext
      simp [jc]
      omega
    have hidx : compHIndex (a := a) (b := b) (c := c) i =
        Fin.castAdd b (Fin.natAdd a jc) := by
      simp [compHIndex, h, jc]
    calc
      (Power.append xz y) (compHIndex (a := a) (b := b) (c := c) i)
          = (Power.append xz y) (Fin.castAdd b (Fin.natAdd a jc)) := by
              rw [hidx]
      _ = xz (Fin.natAdd a jc) := by
              simp [Power.append]
      _ = Power.right xz jc := by
              simp [Power.right]
      _ = (Power.append y (Power.right xz)) (Fin.natAdd b jc) := by
              simp [Power.append]
      _ = (Power.append y (Power.right xz)) i := by
              rw [hi]

def RelationComp {m n p : Nat}
    (G : Set (Power R (m + n))) (H : Set (Power R (n + p))) :
    Set (Power R (m + p)) :=
  fun xz => exists y : Power R n,
    G (Power.append (Power.left xz) y) /\
    H (Power.append y (Power.right xz))

theorem relation_comp_mem
    (M : OMinimalStructure D)
    {a b c : Nat}
    {G : Set (Power R (a + b))} {H : Set (Power R (b + c))}
    (hG : M.S (a + b) G) (hH : M.S (b + c) H) :
    M.S (a + c) (RelationComp (R := R) (m := a) (n := b) (p := c) G H) := by
  have hG' :
      M.S ((a + c) + b)
        (fun xyz : Power R ((a + c) + b) =>
          G (compGArg (R := R) (a := a) (b := b) (c := c) xyz)) := by
    simpa [compGArg] using!
      (M.reindex_mem
        (fun i : Fin (a + b) => compGIndex (a := a) (b := b) (c := c) i)
        hG)
  have hH' :
      M.S ((a + c) + b)
        (fun xyz : Power R ((a + c) + b) =>
          H (compHArg (R := R) (a := a) (b := b) (c := c) xyz)) := by
    simpa [compHArg] using!
      (M.reindex_mem
        (fun i : Fin (b + c) => compHIndex (a := a) (b := b) (c := c) i)
        hH)
  have hBoth :
      M.S ((a + c) + b)
        (fun xyz : Power R ((a + c) + b) =>
          G (compGArg (R := R) (a := a) (b := b) (c := c) xyz) /\
          H (compHArg (R := R) (a := a) (b := b) (c := c) xyz)) :=
    M.inter_mem hG' hH'
  have hProj :
      M.S (a + c)
        (fun xz : Power R (a + c) =>
          exists y : Power R b,
            G (compGArg (R := R) (a := a) (b := b) (c := c) (Power.append xz y)) /\
            H (compHArg (R := R) (a := a) (b := b) (c := c) (Power.append xz y))) :=
    M.existsLast_mem hBoth
  simpa [RelationComp, compGArg_append, compHArg_append] using! hProj

theorem relationComp_functionGraph_eq {m n p : Nat}
    {A : Set (Power R m)} {B : Set (Power R n)} {C : Set (Power R p)}
    (f : {x : Power R m // A x} -> {y : Power R n // B y})
    (g : {y : Power R n // B y} -> {z : Power R p // C z}) :
    RelationComp (R := R)
      (FunctionGraph (R := R) (m := m) (n := n) (A := A) (B := B) f)
      (FunctionGraph (R := R) (m := n) (n := p) (A := B) (B := C) g)
    =
    FunctionGraph (R := R) (m := m) (n := p) (A := A) (B := C)
      (fun x => g (f x)) := by
  funext xz
  apply propext
  constructor
  · intro h
    rcases h with ⟨y, hf, hg⟩
    have hf' : exists hx : A (Power.left xz),
        y = (f (Subtype.mk (Power.left xz) hx)).1 := by
      simpa [FunctionGraph] using! hf
    have hg' : exists hy : B y,
        Power.right xz = (g (Subtype.mk y hy)).1 := by
      simpa [FunctionGraph] using! hg
    rcases hf' with ⟨hx, hfy⟩
    rcases hg' with ⟨hy, hgz⟩
    refine ⟨hx, ?_⟩
    have hsub : (Subtype.mk y hy : {y : Power R n // B y}) =
        f (Subtype.mk (Power.left xz) hx) := by
      apply Subtype.ext
      exact hfy
    simpa [FunctionGraph, hsub] using! hgz
  · intro h
    rcases h with ⟨hx, hxz⟩
    let y : Power R n := (f (Subtype.mk (Power.left xz) hx)).1
    have hfProof :
        FunctionGraph (R := R) (m := m) (n := n) (A := A) (B := B) f
          (Power.append (Power.left xz) y) := by
      have hfCore : exists hx0 : A (Power.left xz),
          y = (f (Subtype.mk (Power.left xz) hx0)).1 := by
        exact Exists.intro hx rfl
      simpa [FunctionGraph] using! hfCore
    have hgProof :
        FunctionGraph (R := R) (m := n) (n := p) (A := B) (B := C) g
          (Power.append y (Power.right xz)) := by
      have hy : B y := by
        simpa [y] using! (f (Subtype.mk (Power.left xz) hx)).2
      have hsub : (Subtype.mk y hy : {y : Power R n // B y}) =
          f (Subtype.mk (Power.left xz) hx) := by
        apply Subtype.ext
        rfl
      have hgCore : exists hy0 : B y,
          Power.right xz = (g (Subtype.mk y hy0)).1 := by
        refine Exists.intro hy ?_
        simpa [y, hsub] using! hxz
      simpa [FunctionGraph] using! hgCore
    exact Exists.intro y (And.intro hfProof hgProof)

structure DefinableFunction (M : OMinimalStructure D) {m n : Nat}
    (A : Set (Power R m)) (B : Set (Power R n)) where
  domain_mem : M.S m A
  codomain_mem : M.S n B
  toFun : {x : Power R m // A x} -> {y : Power R n // B y}
  graph_mem :
    M.S (m + n) (FunctionGraph (R := R) (m := m) (n := n) (A := A) (B := B) toFun)

def DefinableFunction.comp
    (M : OMinimalStructure D)
    {m n p : Nat}
    {A : Set (Power R m)} {B : Set (Power R n)} {C : Set (Power R p)}
    (g : DefinableFunction M B C)
    (f : DefinableFunction M A B) :
    DefinableFunction M A C where
  domain_mem := f.domain_mem
  codomain_mem := g.codomain_mem
  toFun := fun x => g.toFun (f.toFun x)
  graph_mem := by
    have hrel :=
      relation_comp_mem (R := R) (D := D) M
        (G := FunctionGraph (R := R) (m := m) (n := n)
          (A := A) (B := B) f.toFun)
        (H := FunctionGraph (R := R) (m := n) (n := p)
          (A := B) (B := C) g.toFun)
        f.graph_mem g.graph_mem
    have heq :=
      relationComp_functionGraph_eq (R := R)
        (A := A) (B := B) (C := C) f.toFun g.toFun
    rw [heq] at hrel
    exact hrel


/-
Image of a definable function.

The graph of a function f : A -> B is stored in coordinates (x,y), where
x has length m and y has length n.  The image is the projection onto the
second block, so before applying the block-projection axiom existsLast_mem
we reindex the graph into coordinates (y,x).
-/

def FunctionImage {m n : Nat} {A : Set (Power R m)} {B : Set (Power R n)}
    (f : {x : Power R m // A x} -> {y : Power R n // B y}) :
    Set (Power R n) :=
  fun y => exists x : Power R m, exists hx : A x,
    y = (f (Subtype.mk x hx)).1

/--
The image of a function whose codomain is `B` is contained in `B`.
-/
theorem functionImage_subset_codomain {m n : Nat}
    {A : Set (Power R m)} {B : Set (Power R n)}
    (f : {x : Power R m // A x} -> {y : Power R n // B y}) :
    FunctionImage (R := R) (A := A) (B := B) f <= B := by
  intro y hy
  rcases hy with ⟨x, hx, hxy⟩
  rw [hxy]
  exact (f (Subtype.mk x hx)).2

/--
Index map implementing the block swap `(y,x) |-> (x,y)`.

The domain of the index map is the coordinate set of `(x,y)`, namely
`Fin (m+n)`.  The codomain is the coordinate set of `(y,x)`, namely
`Fin (n+m)`.  If an index lies in the first `m` coordinates, then it is an
`x`-coordinate and must be read from the right block of `(y,x)`.  Otherwise
it is a `y`-coordinate and must be read from the left block.
-/
def imageGraphIndex {m n : Nat} (i : Fin (m + n)) : Fin (n + m) :=
  if h : (i : Nat) < m then
    Fin.natAdd n (Fin.mk (i : Nat) h)
  else
    Fin.castAdd m (Fin.mk ((i : Nat) - m) (by omega))

/--
Given a tuple in coordinates `(y,x)`, read it as a tuple in coordinates `(x,y)`.
-/
def imageGraphArg {m n : Nat} (yx : Power R (n + m)) : Power R (m + n) :=
  fun i => yx (imageGraphIndex (m := m) (n := n) i)

/--
On an explicitly appended tuple, the block swap has the expected value.
-/
theorem imageGraphArg_append {m n : Nat}
    (y : Power R n) (x : Power R m) :
    imageGraphArg (R := R) (m := m) (n := n) (Power.append y x) =
      Power.append x y := by
  funext i
  change (Power.append y x) (imageGraphIndex (m := m) (n := n) i) =
    (Power.append x y) i
  by_cases h : (i : Nat) < m
  · let im : Fin m := Fin.mk (i : Nat) h
    have hi : i = Fin.castAdd n im := by
      ext
      simp [im]
    have hidx : imageGraphIndex (m := m) (n := n) i = Fin.natAdd n im := by
      simp [imageGraphIndex, h, im]
    calc
      (Power.append y x) (imageGraphIndex (m := m) (n := n) i)
          = (Power.append y x) (Fin.natAdd n im) := by
              rw [hidx]
      _ = x im := by
              simp [Power.append]
      _ = (Power.append x y) (Fin.castAdd n im) := by
              simp [Power.append]
      _ = (Power.append x y) i := by
              rw [hi]
  · let jn : Fin n := Fin.mk ((i : Nat) - m) (by omega)
    have hi : i = Fin.natAdd m jn := by
      ext
      simp [jn]
      omega
    have hidx : imageGraphIndex (m := m) (n := n) i = Fin.castAdd m jn := by
      simp [imageGraphIndex, h, jn]
    calc
      (Power.append y x) (imageGraphIndex (m := m) (n := n) i)
          = (Power.append y x) (Fin.castAdd m jn) := by
              rw [hidx]
      _ = y jn := by
              simp [Power.append]
      _ = (Power.append x y) (Fin.natAdd m jn) := by
              simp [Power.append]
      _ = (Power.append x y) i := by
              rw [hi]

/--
If the graph of `f : A -> B` is definable, then the image of `f` is definable.
This is the graph-projection version of the main mathematical statement.
-/
theorem functionImage_mem_of_graph_mem
    (M : OMinimalStructure D)
    {m n : Nat}
    {A : Set (Power R m)} {B : Set (Power R n)}
    {f : {x : Power R m // A x} -> {y : Power R n // B y}}
    (hGraph : M.S (m + n)
      (FunctionGraph (R := R) (m := m) (n := n) (A := A) (B := B) f)) :
    M.S n (FunctionImage (R := R) (m := m) (n := n) (A := A) (B := B) f) := by
  have hSwap :
      M.S (n + m)
        (fun yx : Power R (n + m) =>
          FunctionGraph (R := R) (m := m) (n := n) (A := A) (B := B) f
            (imageGraphArg (R := R) (m := m) (n := n) yx)) := by
    simpa [imageGraphArg] using!
      (M.reindex_mem
        (fun i : Fin (m + n) => imageGraphIndex (m := m) (n := n) i)
        hGraph)
  have hProj :
      M.S n
        (fun y : Power R n => exists x : Power R m,
          FunctionGraph (R := R) (m := m) (n := n) (A := A) (B := B) f
            (imageGraphArg (R := R) (m := m) (n := n) (Power.append y x))) := by
    simpa using! (M.existsLast_mem (n := n) (m := m) hSwap)
  have hProj' :
      M.S n
        (fun y : Power R n => exists x : Power R m,
          FunctionGraph (R := R) (m := m) (n := n) (A := A) (B := B) f
            (Power.append x y)) := by
    simpa [imageGraphArg_append] using! hProj
  simpa [FunctionImage, FunctionGraph] using! hProj'

/--
Main image theorem for `DefinableFunction`:
if `f : A -> B` is definable, then its image is a definable subset of `R^n`.
-/
theorem functionImage_mem
    (M : OMinimalStructure D)
    {m n : Nat}
    {A : Set (Power R m)} {B : Set (Power R n)}
    (f : DefinableFunction M A B) :
    M.S n (FunctionImage (R := R) (m := m) (n := n) (A := A) (B := B) f.toFun) := by
  exact functionImage_mem_of_graph_mem (R := R) (D := D) M f.graph_mem

/--
The image of a `DefinableFunction`, as a named set.
-/
def DefinableFunction.image
    {M : OMinimalStructure D}
    {m n : Nat}
    {A : Set (Power R m)} {B : Set (Power R n)}
    (f : DefinableFunction M A B) : Set (Power R n) :=
  FunctionImage (R := R) (m := m) (n := n) (A := A) (B := B) f.toFun

/--
The named image of a definable function is definable.
-/
theorem DefinableFunction.image_mem
    {M : OMinimalStructure D}
    {m n : Nat}
    {A : Set (Power R m)} {B : Set (Power R n)}
    (f : DefinableFunction M A B) :
    M.S n (f.image) := by
  simpa [DefinableFunction.image] using!
    functionImage_mem (R := R) (D := D) M f

/--
The named image of a definable function is contained in its codomain.
-/
theorem DefinableFunction.image_subset_codomain
    {M : OMinimalStructure D}
    {m n : Nat}
    {A : Set (Power R m)} {B : Set (Power R n)}
    (f : DefinableFunction M A B) :
    f.image <= B := by
  simpa [DefinableFunction.image] using!
    functionImage_subset_codomain (R := R) (A := A) (B := B) f.toFun



/-
Continuity of a one-variable definable function.

Usual interval definition, for a function f : I -> R and x in I:
for every open interval (a,b) containing f(x), there are c < x < d such that
for every y in I, if c < y < d then f(y) lies in (a,b).

Using the graph G of f, this becomes:
x is continuous iff x is in I and there do not exist a,b,v such that
G(x,v), a < v < b, and no interval (c,d) around x works.

A pair c,d works iff c < x < d and there is no counterexample y,w with
y in I, c < y < d, G(y,w), and w outside (a,b).

The set-theoretic operations used below are only finite intersections,
complements, and existential projections. Universal quantifiers and implications
are rewritten using complement and existential quantification.
-/

@[reducible] def Lt1 (D : DenseLinearOrderNoEndpoints R) (x y : Power R 1) : Prop :=
  D.lt (Power.coord1 x) (Power.coord1 y)

def ContinuousAtOnGraph (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) (x : Power R 1) : Prop :=
  I x /\
  forall a b v : Power R 1,
    G (Power.append x v) ->
    Lt1 D a v -> Lt1 D v b ->
    exists c d : Power R 1,
      Lt1 D c x /\ Lt1 D x d /\
      forall y w : Power R 1,
        I y ->
        Lt1 D c y -> Lt1 D y d ->
        G (Power.append y w) ->
        Lt1 D a w /\ Lt1 D w b

theorem setUniv_mem (M : OMinimalStructure D) (n : Nat) :
    M.S n (setUniv : Set (Power R n)) := by
  exact M.compl_mem (M.empty_mem n)

def pairIndex {n : Nat} (i j : Fin n) : Fin 2 -> Fin n :=
  fun k => if (k : Nat) = 0 then i else j

def HoldsAt {n m : Nat} (A : Set (Power R n)) (sigma : Fin n -> Fin m) :
    Set (Power R m) :=
  fun z => A (fun i : Fin n => z (sigma i))

def DomainOn {n : Nat} (I : Set (Power R 1)) (i : Fin n) : Set (Power R n) :=
  HoldsAt I (fun _ : Fin 1 => i)

def GraphOn {n : Nat} (G : Set (Power R 2)) (i j : Fin n) : Set (Power R n) :=
  HoldsAt G (pairIndex i j)

def LtOn (D : DenseLinearOrderNoEndpoints R) {n : Nat} (i j : Fin n) :
    Set (Power R n) :=
  HoldsAt (fun p : Power R 2 => D.lt (Power.coord2_0 p) (Power.coord2_1 p))
    (pairIndex i j)

theorem holdsAt_mem (M : OMinimalStructure D)
    {n m : Nat} {A : Set (Power R n)} (sigma : Fin n -> Fin m)
    (hA : M.S n A) :
    M.S m (HoldsAt A sigma) := by
  simpa [HoldsAt] using! M.reindex_mem sigma hA

theorem domainOn_mem (M : OMinimalStructure D)
    {n : Nat} {I : Set (Power R 1)} (hI : M.S 1 I) (i : Fin n) :
    M.S n (DomainOn I i) := by
  simpa [DomainOn] using!
    (holdsAt_mem (R := R) (D := D) M (fun _ : Fin 1 => i) hI)

theorem graphOn_mem (M : OMinimalStructure D)
    {n : Nat} {G : Set (Power R 2)} (hG : M.S 2 G) (i j : Fin n) :
    M.S n (GraphOn G i j) := by
  simpa [GraphOn] using!
    (holdsAt_mem (R := R) (D := D) M (pairIndex i j) hG)

theorem ltOn_mem (M : OMinimalStructure D)
    {n : Nat} (i j : Fin n) :
    M.S n (LtOn D i j) := by
  simpa [LtOn] using!
    (holdsAt_mem (R := R) (D := D) M (pairIndex i j) M.lt_mem)

def ValueIntervalAt (D : DenseLinearOrderNoEndpoints R)
    {n : Nat} (a w b : Fin n) : Set (Power R n) :=
  setInter (LtOn D a w) (LtOn D w b)

def NeighbourhoodAt (D : DenseLinearOrderNoEndpoints R)
    {n : Nat} (c x d : Fin n) : Set (Power R n) :=
  setInter (LtOn D c x) (LtOn D x d)

def CoreAt (D : DenseLinearOrderNoEndpoints R)
    {n : Nat} (G : Set (Power R 2)) (x a b v : Fin n) : Set (Power R n) :=
  setInter (GraphOn G x v) (ValueIntervalAt D a v b)

theorem valueIntervalAt_mem (M : OMinimalStructure D)
    {n : Nat} (a w b : Fin n) :
    M.S n (ValueIntervalAt D a w b) := by
  exact M.inter_mem (ltOn_mem (R := R) (D := D) M a w)
    (ltOn_mem (R := R) (D := D) M w b)

theorem neighbourhoodAt_mem (M : OMinimalStructure D)
    {n : Nat} (c x d : Fin n) :
    M.S n (NeighbourhoodAt D c x d) := by
  exact M.inter_mem (ltOn_mem (R := R) (D := D) M c x)
    (ltOn_mem (R := R) (D := D) M x d)

theorem coreAt_mem (M : OMinimalStructure D)
    {n : Nat} {G : Set (Power R 2)} (hG : M.S 2 G) (x a b v : Fin n) :
    M.S n (CoreAt D G x a b v) := by
  exact M.inter_mem (graphOn_mem (R := R) (D := D) M hG x v)
    (valueIntervalAt_mem (R := R) (D := D) M a v b)

-- Variables in arity 8 are ordered as x,a,b,v,c,d,y,w.
def Counter8 (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 8) :=
  setInter
    (setInter
      (setInter
        (setInter
          (DomainOn I (6 : Fin 8))
          (LtOn D (4 : Fin 8) (6 : Fin 8)))
        (LtOn D (6 : Fin 8) (5 : Fin 8)))
      (GraphOn G (6 : Fin 8) (7 : Fin 8)))
    (setCompl (ValueIntervalAt D (1 : Fin 8) (7 : Fin 8) (2 : Fin 8)))

theorem counter8_mem (M : OMinimalStructure D)
    {I : Set (Power R 1)} {G : Set (Power R 2)}
    (hI : M.S 1 I) (hG : M.S 2 G) :
    M.S 8 (Counter8 D I G) := by
  have hDomain : M.S 8 (DomainOn I (6 : Fin 8)) :=
    domainOn_mem (R := R) (D := D) M hI (6 : Fin 8)
  have hcy : M.S 8 (LtOn D (4 : Fin 8) (6 : Fin 8)) :=
    ltOn_mem (R := R) (D := D) M (4 : Fin 8) (6 : Fin 8)
  have hyd : M.S 8 (LtOn D (6 : Fin 8) (5 : Fin 8)) :=
    ltOn_mem (R := R) (D := D) M (6 : Fin 8) (5 : Fin 8)
  have hGraph : M.S 8 (GraphOn G (6 : Fin 8) (7 : Fin 8)) :=
    graphOn_mem (R := R) (D := D) M hG (6 : Fin 8) (7 : Fin 8)
  have hInside : M.S 8 (ValueIntervalAt D (1 : Fin 8) (7 : Fin 8) (2 : Fin 8)) :=
    valueIntervalAt_mem (R := R) (D := D) M (1 : Fin 8) (7 : Fin 8) (2 : Fin 8)
  have hNotInside : M.S 8 (setCompl (ValueIntervalAt D (1 : Fin 8) (7 : Fin 8) (2 : Fin 8))) :=
    M.compl_mem hInside
  exact M.inter_mem
    (M.inter_mem
      (M.inter_mem
        (M.inter_mem hDomain hcy)
        hyd)
      hGraph)
    hNotInside

-- Variables in arity 6 are ordered as x,a,b,v,c,d.
def CounterExists6 (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 6) :=
  fun z => exists yw : Power R 2,
    Counter8 D I G (Power.append z yw)

theorem counterExists6_mem (M : OMinimalStructure D)
    {I : Set (Power R 1)} {G : Set (Power R 2)}
    (hI : M.S 1 I) (hG : M.S 2 G) :
    M.S 6 (CounterExists6 D I G) := by
  simpa [CounterExists6] using!
    (M.existsLast_mem (n := 6) (m := 2)
      (counter8_mem (R := R) (D := D) M hI hG))

def Good6 (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 6) :=
  setInter
    (setInter
      (CoreAt D G (0 : Fin 6) (1 : Fin 6) (2 : Fin 6) (3 : Fin 6))
      (NeighbourhoodAt D (4 : Fin 6) (0 : Fin 6) (5 : Fin 6)))
    (setCompl (CounterExists6 D I G))

theorem good6_mem (M : OMinimalStructure D)
    {I : Set (Power R 1)} {G : Set (Power R 2)}
    (hI : M.S 1 I) (hG : M.S 2 G) :
    M.S 6 (Good6 D I G) := by
  have hCore : M.S 6 (CoreAt D G (0 : Fin 6) (1 : Fin 6) (2 : Fin 6) (3 : Fin 6)) :=
    coreAt_mem (R := R) (D := D) M hG (0 : Fin 6) (1 : Fin 6) (2 : Fin 6) (3 : Fin 6)
  have hNhd : M.S 6 (NeighbourhoodAt D (4 : Fin 6) (0 : Fin 6) (5 : Fin 6)) :=
    neighbourhoodAt_mem (R := R) (D := D) M (4 : Fin 6) (0 : Fin 6) (5 : Fin 6)
  have hNoCounter : M.S 6 (setCompl (CounterExists6 D I G)) :=
    M.compl_mem (counterExists6_mem (R := R) (D := D) M hI hG)
  exact M.inter_mem (M.inter_mem hCore hNhd) hNoCounter

-- Variables in arity 4 are ordered as x,a,b,v.
def GoodExists4 (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 4) :=
  fun z => exists cd : Power R 2,
    Good6 D I G (Power.append z cd)

theorem goodExists4_mem (M : OMinimalStructure D)
    {I : Set (Power R 1)} {G : Set (Power R 2)}
    (hI : M.S 1 I) (hG : M.S 2 G) :
    M.S 4 (GoodExists4 D I G) := by
  simpa [GoodExists4] using!
    (M.existsLast_mem (n := 4) (m := 2)
      (good6_mem (R := R) (D := D) M hI hG))

def Bad4 (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 4) :=
  setInter
    (CoreAt D G (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) (3 : Fin 4))
    (setCompl (GoodExists4 D I G))

theorem bad4_mem (M : OMinimalStructure D)
    {I : Set (Power R 1)} {G : Set (Power R 2)}
    (hI : M.S 1 I) (hG : M.S 2 G) :
    M.S 4 (Bad4 D I G) := by
  have hCore : M.S 4 (CoreAt D G (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)) :=
    coreAt_mem (R := R) (D := D) M hG (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)
  have hNoGood : M.S 4 (setCompl (GoodExists4 D I G)) :=
    M.compl_mem (goodExists4_mem (R := R) (D := D) M hI hG)
  exact M.inter_mem hCore hNoGood

def BadPoint1 (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 1) :=
  fun x => exists abv : Power R 3,
    Bad4 D I G (Power.append x abv)

theorem badPoint1_mem (M : OMinimalStructure D)
    {I : Set (Power R 1)} {G : Set (Power R 2)}
    (hI : M.S 1 I) (hG : M.S 2 G) :
    M.S 1 (BadPoint1 D I G) := by
  simpa [BadPoint1] using!
    (M.existsLast_mem (n := 1) (m := 3)
      (bad4_mem (R := R) (D := D) M hI hG))

def ContinuousPoints (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 1) :=
  setInter I (setCompl (BadPoint1 D I G))

theorem continuousPoints_mem (M : OMinimalStructure D)
    {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) :
    M.S 1 (ContinuousPoints D I
      (FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun)) := by
  have hBad : M.S 1 (BadPoint1 D I
      (FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun)) :=
    badPoint1_mem (R := R) (D := D) M f.domain_mem f.graph_mem
  exact M.inter_mem f.domain_mem (M.compl_mem hBad)


/-
Local constancy of a one-variable definable function.

Usual interval definition, for a function f : I -> R and x in I:
f is locally constant at x if there is an open interval (c,d) containing x
such that for every y in I, if c < y < d then f(y) = f(x).

Using the graph G of f, this can be written without mentioning f directly:
x is locally constant iff x is in I and there exist c,d,v such that
G(x,v), c < x < d, and there is no counterexample y,w satisfying
I(y), c < y < d, G(y,w), and w is not equal to v.

Again, the set-theoretic operations below are finite intersections,
complements, and existential projections.
-/

def LocallyConstantAtOnGraph (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) (x : Power R 1) : Prop :=
  I x /\
  exists c d v : Power R 1,
    G (Power.append x v) /\
    Lt1 D c x /\ Lt1 D x d /\
    forall y w : Power R 1,
      I y ->
      Lt1 D c y -> Lt1 D y d ->
      G (Power.append y w) ->
      v = w

def EqOn {n : Nat} (i j : Fin n) : Set (Power R n) :=
  fun z => z i = z j

theorem eqOn_mem_of_lt (M : OMinimalStructure D)
    {n : Nat} (i j : Fin n) (hij : i < j) :
    M.S n (EqOn (R := R) i j) := by
  simpa [EqOn] using! M.diagonal_mem i j hij

-- Variables in arity 6 are ordered as x,c,d,v,y,w.
def LocalConstCounter6 (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 6) :=
  setInter
    (setInter
      (setInter
        (setInter
          (DomainOn I (4 : Fin 6))
          (LtOn D (1 : Fin 6) (4 : Fin 6)))
        (LtOn D (4 : Fin 6) (2 : Fin 6)))
      (GraphOn G (4 : Fin 6) (5 : Fin 6)))
    (setCompl (EqOn (R := R) (3 : Fin 6) (5 : Fin 6)))

theorem localConstCounter6_mem (M : OMinimalStructure D)
    {I : Set (Power R 1)} {G : Set (Power R 2)}
    (hI : M.S 1 I) (hG : M.S 2 G) :
    M.S 6 (LocalConstCounter6 D I G) := by
  have hDomain : M.S 6 (DomainOn I (4 : Fin 6)) :=
    domainOn_mem (R := R) (D := D) M hI (4 : Fin 6)
  have hcy : M.S 6 (LtOn D (1 : Fin 6) (4 : Fin 6)) :=
    ltOn_mem (R := R) (D := D) M (1 : Fin 6) (4 : Fin 6)
  have hyd : M.S 6 (LtOn D (4 : Fin 6) (2 : Fin 6)) :=
    ltOn_mem (R := R) (D := D) M (4 : Fin 6) (2 : Fin 6)
  have hGraph : M.S 6 (GraphOn G (4 : Fin 6) (5 : Fin 6)) :=
    graphOn_mem (R := R) (D := D) M hG (4 : Fin 6) (5 : Fin 6)
  have hEq : M.S 6 (EqOn (R := R) (3 : Fin 6) (5 : Fin 6)) :=
    eqOn_mem_of_lt (R := R) (D := D) M (3 : Fin 6) (5 : Fin 6) (by decide)
  have hNeq : M.S 6 (setCompl (EqOn (R := R) (3 : Fin 6) (5 : Fin 6))) :=
    M.compl_mem hEq
  exact M.inter_mem
    (M.inter_mem
      (M.inter_mem
        (M.inter_mem hDomain hcy)
        hyd)
      hGraph)
    hNeq

-- Variables in arity 4 are ordered as x,c,d,v.
def LocalConstCounterExists4 (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 4) :=
  fun z => exists yw : Power R 2,
    LocalConstCounter6 D I G (Power.append z yw)

theorem localConstCounterExists4_mem (M : OMinimalStructure D)
    {I : Set (Power R 1)} {G : Set (Power R 2)}
    (hI : M.S 1 I) (hG : M.S 2 G) :
    M.S 4 (LocalConstCounterExists4 D I G) := by
  simpa [LocalConstCounterExists4] using!
    (M.existsLast_mem (n := 4) (m := 2)
      (localConstCounter6_mem (R := R) (D := D) M hI hG))

def LocalConstGood4 (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 4) :=
  setInter
    (setInter
      (GraphOn G (0 : Fin 4) (3 : Fin 4))
      (NeighbourhoodAt D (1 : Fin 4) (0 : Fin 4) (2 : Fin 4)))
    (setCompl (LocalConstCounterExists4 D I G))

theorem localConstGood4_mem (M : OMinimalStructure D)
    {I : Set (Power R 1)} {G : Set (Power R 2)}
    (hI : M.S 1 I) (hG : M.S 2 G) :
    M.S 4 (LocalConstGood4 D I G) := by
  have hGraph : M.S 4 (GraphOn G (0 : Fin 4) (3 : Fin 4)) :=
    graphOn_mem (R := R) (D := D) M hG (0 : Fin 4) (3 : Fin 4)
  have hNhd : M.S 4 (NeighbourhoodAt D (1 : Fin 4) (0 : Fin 4) (2 : Fin 4)) :=
    neighbourhoodAt_mem (R := R) (D := D) M (1 : Fin 4) (0 : Fin 4) (2 : Fin 4)
  have hNoCounter : M.S 4 (setCompl (LocalConstCounterExists4 D I G)) :=
    M.compl_mem (localConstCounterExists4_mem (R := R) (D := D) M hI hG)
  exact M.inter_mem (M.inter_mem hGraph hNhd) hNoCounter

def LocalConstGoodPoint1 (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 1) :=
  fun x => exists cdv : Power R 3,
    LocalConstGood4 D I G (Power.append x cdv)

theorem localConstGoodPoint1_mem (M : OMinimalStructure D)
    {I : Set (Power R 1)} {G : Set (Power R 2)}
    (hI : M.S 1 I) (hG : M.S 2 G) :
    M.S 1 (LocalConstGoodPoint1 D I G) := by
  simpa [LocalConstGoodPoint1] using!
    (M.existsLast_mem (n := 1) (m := 3)
      (localConstGood4_mem (R := R) (D := D) M hI hG))

def LocallyConstantPoints (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 1) :=
  setInter I (LocalConstGoodPoint1 D I G)

theorem locallyConstantPoints_mem (M : OMinimalStructure D)
    {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) :
    M.S 1 (LocallyConstantPoints D I
      (FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun)) := by
  have hGood : M.S 1 (LocalConstGoodPoint1 D I
      (FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun)) :=
    localConstGoodPoint1_mem (R := R) (D := D) M f.domain_mem f.graph_mem
  exact M.inter_mem f.domain_mem hGood


/-
Local monotonicity of a one-variable definable function.

We use the non-strict convention:
locally monotone increasing means locally nondecreasing, and
locally monotone decreasing means locally nonincreasing.

For the graph G of f, x is locally increasing iff x is in I and there are
c,d with c < x < d such that there is no bad pair y0,y1 in I with
c < y0 < d, c < y1 < d, y0 < y1, G(y0,w0), G(y1,w1), and w1 < w0.

The decreasing version has the same definition except that the bad value
inequality is w0 < w1.

As above, the set-theoretic operations used below are finite intersections,
complements, and existential projections.
-/

def LocallyIncreasingAtOnGraph (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) (x : Power R 1) : Prop :=
  I x /\
  exists c d : Power R 1,
    Lt1 D c x /\ Lt1 D x d /\
    forall y0 y1 w0 w1 : Power R 1,
      I y0 -> I y1 ->
      Lt1 D c y0 -> Lt1 D y0 d ->
      Lt1 D c y1 -> Lt1 D y1 d ->
      G (Power.append y0 w0) ->
      G (Power.append y1 w1) ->
      Lt1 D y0 y1 ->
      Not (Lt1 D w1 w0)

def LocallyDecreasingAtOnGraph (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) (x : Power R 1) : Prop :=
  I x /\
  exists c d : Power R 1,
    Lt1 D c x /\ Lt1 D x d /\
    forall y0 y1 w0 w1 : Power R 1,
      I y0 -> I y1 ->
      Lt1 D c y0 -> Lt1 D y0 d ->
      Lt1 D c y1 -> Lt1 D y1 d ->
      G (Power.append y0 w0) ->
      G (Power.append y1 w1) ->
      Lt1 D y0 y1 ->
      Not (Lt1 D w0 w1)

-- Variables in arity 7 are ordered as x,c,d,y0,y1,w0,w1.
def MonotoneBaseCounter7 (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 7) :=
  setInter
    (setInter
      (setInter
        (setInter
          (setInter
            (setInter
              (setInter
                (setInter
                  (DomainOn I (3 : Fin 7))
                  (DomainOn I (4 : Fin 7)))
                (LtOn D (1 : Fin 7) (3 : Fin 7)))
              (LtOn D (3 : Fin 7) (2 : Fin 7)))
            (LtOn D (1 : Fin 7) (4 : Fin 7)))
          (LtOn D (4 : Fin 7) (2 : Fin 7)))
        (GraphOn G (3 : Fin 7) (5 : Fin 7)))
      (GraphOn G (4 : Fin 7) (6 : Fin 7)))
    (LtOn D (3 : Fin 7) (4 : Fin 7))

theorem monotoneBaseCounter7_mem (M : OMinimalStructure D)
    {I : Set (Power R 1)} {G : Set (Power R 2)}
    (hI : M.S 1 I) (hG : M.S 2 G) :
    M.S 7 (MonotoneBaseCounter7 D I G) := by
  have hI0 : M.S 7 (DomainOn I (3 : Fin 7)) :=
    domainOn_mem (R := R) (D := D) M hI (3 : Fin 7)
  have hI1 : M.S 7 (DomainOn I (4 : Fin 7)) :=
    domainOn_mem (R := R) (D := D) M hI (4 : Fin 7)
  have hcy0 : M.S 7 (LtOn D (1 : Fin 7) (3 : Fin 7)) :=
    ltOn_mem (R := R) (D := D) M (1 : Fin 7) (3 : Fin 7)
  have hy0d : M.S 7 (LtOn D (3 : Fin 7) (2 : Fin 7)) :=
    ltOn_mem (R := R) (D := D) M (3 : Fin 7) (2 : Fin 7)
  have hcy1 : M.S 7 (LtOn D (1 : Fin 7) (4 : Fin 7)) :=
    ltOn_mem (R := R) (D := D) M (1 : Fin 7) (4 : Fin 7)
  have hy1d : M.S 7 (LtOn D (4 : Fin 7) (2 : Fin 7)) :=
    ltOn_mem (R := R) (D := D) M (4 : Fin 7) (2 : Fin 7)
  have hGraph0 : M.S 7 (GraphOn G (3 : Fin 7) (5 : Fin 7)) :=
    graphOn_mem (R := R) (D := D) M hG (3 : Fin 7) (5 : Fin 7)
  have hGraph1 : M.S 7 (GraphOn G (4 : Fin 7) (6 : Fin 7)) :=
    graphOn_mem (R := R) (D := D) M hG (4 : Fin 7) (6 : Fin 7)
  have hy0y1 : M.S 7 (LtOn D (3 : Fin 7) (4 : Fin 7)) :=
    ltOn_mem (R := R) (D := D) M (3 : Fin 7) (4 : Fin 7)
  exact M.inter_mem
    (M.inter_mem
      (M.inter_mem
        (M.inter_mem
          (M.inter_mem
            (M.inter_mem
              (M.inter_mem
                (M.inter_mem hI0 hI1)
                hcy0)
              hy0d)
            hcy1)
          hy1d)
        hGraph0)
      hGraph1)
    hy0y1

def MonoIncCounter7 (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 7) :=
  setInter (MonotoneBaseCounter7 D I G) (LtOn D (6 : Fin 7) (5 : Fin 7))

def MonoDecCounter7 (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 7) :=
  setInter (MonotoneBaseCounter7 D I G) (LtOn D (5 : Fin 7) (6 : Fin 7))

theorem monoIncCounter7_mem (M : OMinimalStructure D)
    {I : Set (Power R 1)} {G : Set (Power R 2)}
    (hI : M.S 1 I) (hG : M.S 2 G) :
    M.S 7 (MonoIncCounter7 D I G) := by
  have hBase : M.S 7 (MonotoneBaseCounter7 D I G) :=
    monotoneBaseCounter7_mem (R := R) (D := D) M hI hG
  have hBad : M.S 7 (LtOn D (6 : Fin 7) (5 : Fin 7)) :=
    ltOn_mem (R := R) (D := D) M (6 : Fin 7) (5 : Fin 7)
  exact M.inter_mem hBase hBad

theorem monoDecCounter7_mem (M : OMinimalStructure D)
    {I : Set (Power R 1)} {G : Set (Power R 2)}
    (hI : M.S 1 I) (hG : M.S 2 G) :
    M.S 7 (MonoDecCounter7 D I G) := by
  have hBase : M.S 7 (MonotoneBaseCounter7 D I G) :=
    monotoneBaseCounter7_mem (R := R) (D := D) M hI hG
  have hBad : M.S 7 (LtOn D (5 : Fin 7) (6 : Fin 7)) :=
    ltOn_mem (R := R) (D := D) M (5 : Fin 7) (6 : Fin 7)
  exact M.inter_mem hBase hBad

-- Variables in arity 3 are ordered as x,c,d.
def MonoIncCounterExists3 (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 3) :=
  fun z => exists yyww : Power R 4,
    MonoIncCounter7 D I G (Power.append z yyww)

def MonoDecCounterExists3 (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 3) :=
  fun z => exists yyww : Power R 4,
    MonoDecCounter7 D I G (Power.append z yyww)

theorem monoIncCounterExists3_mem (M : OMinimalStructure D)
    {I : Set (Power R 1)} {G : Set (Power R 2)}
    (hI : M.S 1 I) (hG : M.S 2 G) :
    M.S 3 (MonoIncCounterExists3 D I G) := by
  simpa [MonoIncCounterExists3] using!
    (M.existsLast_mem (n := 3) (m := 4)
      (monoIncCounter7_mem (R := R) (D := D) M hI hG))

theorem monoDecCounterExists3_mem (M : OMinimalStructure D)
    {I : Set (Power R 1)} {G : Set (Power R 2)}
    (hI : M.S 1 I) (hG : M.S 2 G) :
    M.S 3 (MonoDecCounterExists3 D I G) := by
  simpa [MonoDecCounterExists3] using!
    (M.existsLast_mem (n := 3) (m := 4)
      (monoDecCounter7_mem (R := R) (D := D) M hI hG))

def MonoIncGood3 (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 3) :=
  setInter
    (NeighbourhoodAt D (1 : Fin 3) (0 : Fin 3) (2 : Fin 3))
    (setCompl (MonoIncCounterExists3 D I G))

def MonoDecGood3 (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 3) :=
  setInter
    (NeighbourhoodAt D (1 : Fin 3) (0 : Fin 3) (2 : Fin 3))
    (setCompl (MonoDecCounterExists3 D I G))

theorem monoIncGood3_mem (M : OMinimalStructure D)
    {I : Set (Power R 1)} {G : Set (Power R 2)}
    (hI : M.S 1 I) (hG : M.S 2 G) :
    M.S 3 (MonoIncGood3 D I G) := by
  have hNhd : M.S 3 (NeighbourhoodAt D (1 : Fin 3) (0 : Fin 3) (2 : Fin 3)) :=
    neighbourhoodAt_mem (R := R) (D := D) M (1 : Fin 3) (0 : Fin 3) (2 : Fin 3)
  have hNoCounter : M.S 3 (setCompl (MonoIncCounterExists3 D I G)) :=
    M.compl_mem (monoIncCounterExists3_mem (R := R) (D := D) M hI hG)
  exact M.inter_mem hNhd hNoCounter

theorem monoDecGood3_mem (M : OMinimalStructure D)
    {I : Set (Power R 1)} {G : Set (Power R 2)}
    (hI : M.S 1 I) (hG : M.S 2 G) :
    M.S 3 (MonoDecGood3 D I G) := by
  have hNhd : M.S 3 (NeighbourhoodAt D (1 : Fin 3) (0 : Fin 3) (2 : Fin 3)) :=
    neighbourhoodAt_mem (R := R) (D := D) M (1 : Fin 3) (0 : Fin 3) (2 : Fin 3)
  have hNoCounter : M.S 3 (setCompl (MonoDecCounterExists3 D I G)) :=
    M.compl_mem (monoDecCounterExists3_mem (R := R) (D := D) M hI hG)
  exact M.inter_mem hNhd hNoCounter

def MonoIncGoodPoint1 (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 1) :=
  fun x => exists cd : Power R 2,
    MonoIncGood3 D I G (Power.append x cd)

def MonoDecGoodPoint1 (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 1) :=
  fun x => exists cd : Power R 2,
    MonoDecGood3 D I G (Power.append x cd)

theorem monoIncGoodPoint1_mem (M : OMinimalStructure D)
    {I : Set (Power R 1)} {G : Set (Power R 2)}
    (hI : M.S 1 I) (hG : M.S 2 G) :
    M.S 1 (MonoIncGoodPoint1 D I G) := by
  simpa [MonoIncGoodPoint1] using!
    (M.existsLast_mem (n := 1) (m := 2)
      (monoIncGood3_mem (R := R) (D := D) M hI hG))

theorem monoDecGoodPoint1_mem (M : OMinimalStructure D)
    {I : Set (Power R 1)} {G : Set (Power R 2)}
    (hI : M.S 1 I) (hG : M.S 2 G) :
    M.S 1 (MonoDecGoodPoint1 D I G) := by
  simpa [MonoDecGoodPoint1] using!
    (M.existsLast_mem (n := 1) (m := 2)
      (monoDecGood3_mem (R := R) (D := D) M hI hG))

def LocallyIncreasingPoints (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 1) :=
  setInter I (MonoIncGoodPoint1 D I G)

def LocallyDecreasingPoints (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 1) :=
  setInter I (MonoDecGoodPoint1 D I G)

theorem locallyIncreasingPoints_mem (M : OMinimalStructure D)
    {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) :
    M.S 1 (LocallyIncreasingPoints D I
      (FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun)) := by
  have hGood : M.S 1 (MonoIncGoodPoint1 D I
      (FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun)) :=
    monoIncGoodPoint1_mem (R := R) (D := D) M f.domain_mem f.graph_mem
  exact M.inter_mem f.domain_mem hGood

theorem locallyDecreasingPoints_mem (M : OMinimalStructure D)
    {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) :
    M.S 1 (LocallyDecreasingPoints D I
      (FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun)) := by
  have hGood : M.S 1 (MonoDecGoodPoint1 D I
      (FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun)) :=
    monoDecGoodPoint1_mem (R := R) (D := D) M f.domain_mem f.graph_mem
  exact M.inter_mem f.domain_mem hGood


theorem empty_definable (M : OMinimalStructure D) (n : Nat) :
    Definable M (setEmpty : Set (Power R n)) :=
  M.empty_mem n

theorem order_definable (M : OMinimalStructure D) :
    Definable M (fun p : Power R 2 => D.lt (Power.coord2_0 p) (Power.coord2_1 p)) :=
  M.lt_mem

open Classical


def ListSet {R : Type u} (L : List R) : Set (Power R 1) :=
  fun x => Power.coord1 x ∈ L

def IsLowerBound1 {R : Type u} (D : DenseLinearOrderNoEndpoints R) (A : Set (Power R 1)) (b : R) : Prop :=
  forall x : Power R 1, A x -> (D.lt b (Power.coord1 x) \/ Power.coord1 x = b)

def IsUpperBound1 {R : Type u} (D : DenseLinearOrderNoEndpoints R) (A : Set (Power R 1)) (b : R) : Prop :=
  forall x : Power R 1, A x -> (D.lt (Power.coord1 x) b \/ Power.coord1 x = b)

def IsMaximum1 {R : Type u} (D : DenseLinearOrderNoEndpoints R) (A : Set (Power R 1)) (M : R) : Prop :=
  A (fun _ => M) /\ IsUpperBound1 D A M

def IsMinimum1 {R : Type u} (D : DenseLinearOrderNoEndpoints R) (A : Set (Power R 1)) (m : R) : Prop :=
  A (fun _ => m) /\ IsLowerBound1 D A m


noncomputable def max1 {R : Type u} (D : DenseLinearOrderNoEndpoints R) (a b : R) : R :=
  if D.lt a b then b else a

noncomputable def min1 {R : Type u} (D : DenseLinearOrderNoEndpoints R) (a b : R) : R :=
  if D.lt a b then a else b

/-
=========================================================
Extrema of Finite Sets
=========================================================
-/
theorem extrema_of_finite_sets {R : Type u} (D : DenseLinearOrderNoEndpoints R) (L : List R)
    (hNotEmpty : L ≠ []) :
    ∃ m M : R, IsMinimum1 D (ListSet L) m ∧ IsMaximum1 D (ListSet L) M := by

  induction L with
  | nil =>

      contradiction

  | cons x B ih =>

      by_cases hB : B = []
      ·
        subst hB
        use x, x
        constructor
        ·
          constructor
          · exact List.Mem.head _
          · intro y hy
            simp [ListSet, Power.coord1] at hy
            right
            exact hy
        ·
          constructor
          · exact List.Mem.head _
          · intro y hy
            simp [ListSet, Power.coord1] at hy
            right
            exact hy

      ·
        have hB_not_empty : B ≠ [] := hB


        rcases ih hB_not_empty with ⟨m_B, M_B, ⟨hmB_in, hmB_lower⟩, ⟨hMB_in, hMB_upper⟩⟩


        let M_A := max1 D M_B x
        let m_A := min1 D m_B x

        use m_A, M_A

        constructor
        ·
          constructor
          ·
            dsimp [m_A, min1]
            split_ifs
            · exact List.Mem.tail _ hmB_in
            · exact List.Mem.head _
          ·
            intro y hy
            simp [ListSet, Power.coord1] at hy
            cases hy with
            | inl hy_eq_x =>
                dsimp [Power.coord1]
                rw [hy_eq_x]
                dsimp [m_A, min1]
                split_ifs with h
                · left; exact h
                · right; rfl
            | inr hy_in_B =>
                have hy_bound := hmB_lower y hy_in_B
                dsimp [m_A, min1]
                split_ifs with h
                · exact hy_bound
                · rcases D.trichotomy x m_B with ⟨hxm, _, _⟩ | ⟨h_eq, _, _⟩ | ⟨_, _, hmx⟩
                  · cases hy_bound with
                    | inl hmy => left; exact D.trans hxm hmy
                    | inr hmy_eq => left; rw [hmy_eq]; exact hxm
                  · rw [h_eq]; exact hy_bound
                  · contradiction

        ·
          constructor
          ·
            dsimp [M_A, max1]
            split_ifs
            · exact List.Mem.head _
            · exact List.Mem.tail _ hMB_in
          ·
            intro y hy
            simp [ListSet, Power.coord1] at hy
            cases hy with
            | inl hy_eq_x =>
                dsimp [Power.coord1]
                rw [hy_eq_x]
                dsimp [M_A, max1]
                split_ifs with h
                · right; rfl
                · rcases D.trichotomy x M_B with ⟨hxM, _, _⟩ | ⟨h_eq, _, _⟩ | ⟨_, _, hMx⟩
                  · left; exact hxM
                  · right; exact h_eq
                  · contradiction
            | inr hy_in_B =>
                have hy_bound := hMB_upper y hy_in_B
                dsimp [M_A, max1]
                split_ifs with h
                · cases hy_bound with
                  | inl hyM => left; exact D.trans hyM h
                  | inr hy_eq => left; rw [hy_eq]; exact h
                · exact hy_bound


/-
=========================================================
Supremum of a Union of Two Sets
=========================================================
-/

def NonEmpty1 {R : Type u} (A : Set (Power R 1)) : Prop :=
  exists x : Power R 1, A x


def BoundedAbove1 {R : Type u} (D : DenseLinearOrderNoEndpoints R) (A : Set (Power R 1)) : Prop :=
  exists b : R, IsUpperBound1 D A b


def IsSupremum1 {R : Type u} (D : DenseLinearOrderNoEndpoints R) (A : Set (Power R 1)) (s : R) : Prop :=
  IsUpperBound1 D A s /\
  forall b : R, IsUpperBound1 D A b -> (D.lt s b \/ s = b)


theorem supremum_of_union {R : Type u} (D : DenseLinearOrderNoEndpoints R)
    (A B : Set (Power R 1)) (sA sB : R)
    (hSupA : IsSupremum1 D A sA)
    (hSupB : IsSupremum1 D B sB) :
    IsSupremum1 D (setUnion A B) (max1 D sA sB) := by


  rcases hSupA with ⟨h_sA_upper, h_sA_least⟩
  rcases hSupB with ⟨h_sB_upper, h_sB_least⟩

  constructor
  ·
    intro x hx
    dsimp [max1]
    split_ifs with h

    · cases hx with
      | inl hxA =>

          have h1 := h_sA_upper x hxA
          cases h1 with
          | inl hlt => left; exact D.trans hlt h
          | inr heq => left; rw [heq]; exact h
      | inr hxB =>

          exact h_sB_upper x hxB


    · cases hx with
      | inl hxA =>

          exact h_sA_upper x hxA
      | inr hxB =>

          have h2 := h_sB_upper x hxB

          rcases D.trichotomy sA sB with ⟨hlt, _, _⟩ | ⟨heq, _, _⟩ | ⟨hgt, _, _⟩
          · contradiction
          ·
            cases h2 with
            | inl hlt2 => left; rw [heq]; exact hlt2
            | inr heq2 => right; rw [heq]; exact heq2
          ·
            cases h2 with
            | inl hlt2 => left; exact D.trans hlt2 hgt
            | inr heq2 => left; rw [heq2]; exact hgt

  ·
    intro b hb


    have hbA : IsUpperBound1 D A b := fun x hx => hb x (Or.inl hx)
    have hbB : IsUpperBound1 D B b := fun x hx => hb x (Or.inr hx)


    have hA_le_b := h_sA_least b hbA
    have hB_le_b := h_sB_least b hbB

    dsimp [max1]
    split_ifs with h
    ·
      exact hB_le_b
    ·
      exact hA_le_b


/-
=========================================================
Supremum of a Bounded Open Interval
=========================================================
-/
theorem supremum_of_open_interval {R : Type u} (D : DenseLinearOrderNoEndpoints R)
    (a : Endpoint R) (b : R)
    (hNotEmpty : NonEmpty1 (openInterval D a (Endpoint.finite b))) :
    IsSupremum1 D (openInterval D a (Endpoint.finite b)) b := by
  constructor
  ·
    intro x hx

    left
    exact hx.right

  ·
    intro y hy

    rcases D.trichotomy b y with ⟨hby, _, _⟩ | ⟨heq, _, _⟩ | ⟨hyb, _, _⟩
    · left; exact hby
    · right; exact heq
    ·
      rcases hNotEmpty with ⟨x0, hx0_left, hx0_right⟩


      let m := max1 D y (Power.coord1 x0)


      have hm_lt_b : D.lt m b := by
        dsimp [m, max1]
        split_ifs with h
        · exact hx0_right
        · exact hyb


      rcases D.dense hm_lt_b with ⟨z, hm_lt_z, hz_lt_b⟩

      have ha_lt_z : Endpoint.lt D a (Endpoint.finite z) := by
        dsimp [m, max1] at hm_lt_z
        split_ifs at hm_lt_z with h
        ·
          cases a with
          | negInf => exact trivial
          | finite val =>

              exact D.trans hx0_left hm_lt_z
          | posInf => contradiction
        ·
          have hx0_le_y : D.lt (Power.coord1 x0) y \/ Power.coord1 x0 = y := by
            rcases D.trichotomy (Power.coord1 x0) y with ⟨h1, _, _⟩ | ⟨h2, _, _⟩ | ⟨h3, _, _⟩
            · left; exact h1
            · right; exact h2
            · contradiction

          have hx0_lt_z : D.lt (Power.coord1 x0) z := by
            cases hx0_le_y with
            | inl hlt => exact D.trans hlt hm_lt_z
            | inr heq => rw [heq]; exact hm_lt_z

          cases a with
          | negInf => exact trivial
          | finite val => exact D.trans hx0_left hx0_lt_z
          | posInf => contradiction


      let z_pow : Power R 1 := fun _ => z


      have hz_in_interval : openInterval D a (Endpoint.finite b) z_pow :=
        ⟨ha_lt_z, hz_lt_b⟩


      have hz_le_y := hy z_pow hz_in_interval


      have hy_lt_z : D.lt y z := by
        dsimp [m, max1] at hm_lt_z
        split_ifs at hm_lt_z with h
        ·
          exact D.trans h hm_lt_z
        ·
          exact hm_lt_z

      cases hz_le_y with
      | inl h_lt =>

          change D.lt z y at h_lt

          have h_trans := D.trans hy_lt_z h_lt
          exact False.elim (D.irrefl y h_trans)

      | inr h_eq =>

          change z = y at h_eq

          rw [h_eq] at hy_lt_z
          exact False.elim (D.irrefl y hy_lt_z)

/-
=========================================================
Definable Completeness
=========================================================
-/

lemma bounded_subset {R : Type u} (D : DenseLinearOrderNoEndpoints R)
    {A B : Set (Power R 1)} (hSubset : forall x, A x -> B x) (hBound : BoundedAbove1 D B) :
    BoundedAbove1 D A := by
  rcases hBound with ⟨b, hb⟩
  exact ⟨b, fun x hx => hb x (hSubset x hx)⟩

lemma definable_completeness_core {R : Type u} (D : DenseLinearOrderNoEndpoints R)
    (A : Set (Power R 1))
    (hDef : FiniteUnionOfPointsAndIntervals D A) :
    BoundedAbove1 D A ->
    (∀ x, ¬ A x) ∨ (∃ s : R, IsSupremum1 D A s) := by

  intro hBounded
  induction hDef with

  | empty =>
      left
      intro x hx
      exact hx
  | point a =>
      right
      use a
      constructor
      ·
        intro x hx

        right
        exact hx
      ·
        intro b hb
        let x_a : Power R 1 := fun _ => a
        have hx_in_set : pointSet a x_a := by rfl
        exact hb x_a hx_in_set

  | interval a b =>
      cases b with
      | negInf =>
          left
          intro x hx
          exact hx.right

      | finite val =>
          by_cases hEmpty : NonEmpty1 (openInterval D a (Endpoint.finite val))
          ·
            right
            use val
            exact supremum_of_open_interval D a val hEmpty
          ·
            left
            intro x hx
            exact hEmpty ⟨x, hx⟩

      | posInf =>
          by_cases hEmpty : NonEmpty1 (openInterval D a Endpoint.posInf)
          · rcases hEmpty with ⟨x0, hx0_left, _⟩
            rcases hBounded with ⟨M, hM_upper⟩

            let m := max1 D M (Power.coord1 x0)
            rcases D.no_right_endpoint m with ⟨y, hmy⟩

            have hM_lt_y : D.lt M y := by
              dsimp [m, max1] at hmy
              split_ifs at hmy with h
              · exact D.trans h hmy
              · exact hmy

            have hy_gt_a : Endpoint.lt D a (Endpoint.finite y) := by
              dsimp [m, max1] at hmy
              split_ifs at hmy with h
              · cases a with
                | negInf => exact trivial
                | finite a_val => exact D.trans hx0_left hmy
                | posInf => contradiction
              · have hx0_le_M : D.lt (Power.coord1 x0) M \/ Power.coord1 x0 = M := by
                  rcases D.trichotomy (Power.coord1 x0) M with ⟨h1, _, _⟩ | ⟨h2, _, _⟩ | ⟨h3, _, _⟩
                  · left; exact h1
                  · right; exact h2
                  · contradiction
                have hx0_lt_y : D.lt (Power.coord1 x0) y := by
                  cases hx0_le_M with
                  | inl hlt => exact D.trans hlt hM_lt_y
                  | inr heq => rw [heq]; exact hM_lt_y
                cases a with
                | negInf => exact trivial
                | finite a_val => exact D.trans hx0_left hx0_lt_y
                | posInf => contradiction

            let y_pow : Power R 1 := fun _ => y
            have hy_in : openInterval D a Endpoint.posInf y_pow := ⟨hy_gt_a, trivial⟩

            have hy_le_M := hM_upper y_pow hy_in

            cases hy_le_M with
            | inl hlt =>
                change D.lt y M at hlt
                exact False.elim (D.irrefl M (D.trans hM_lt_y hlt))
            | inr heq =>

                change y = M at heq
                rw [heq] at hM_lt_y
                exact False.elim (D.irrefl M hM_lt_y)
          ·
            left
            intro x hx
            exact hEmpty ⟨x, hx⟩
  | union hA hB ihA ihB =>
      have hBoundA := bounded_subset D (fun x hx => Or.inl hx) hBounded
      have hBoundB := bounded_subset D (fun x hx => Or.inr hx) hBounded

      have hResA := ihA hBoundA
      have hResB := ihB hBoundB

      cases hResA with
      | inl hEmptyA =>
          cases hResB with
          | inl hEmptyB =>
              left
              intro x hx
              cases hx with
              | inl hxA => exact hEmptyA x hxA
              | inr hxB => exact hEmptyB x hxB
          | inr hSupB =>
              right
              rcases hSupB with ⟨sB, hsB_upper, hsB_least⟩
              use sB
              constructor
              · intro x hx
                cases hx with
                | inl hxA => exact False.elim (hEmptyA x hxA)
                | inr hxB => exact hsB_upper x hxB
              · intro b hb
                have hbB : IsUpperBound1 D _ b := fun x hx => hb x (Or.inr hx)
                exact hsB_least b hbB
      | inr hSupA =>
          cases hResB with
          | inl hEmptyB =>
              right
              rcases hSupA with ⟨sA, hsA_upper, hsA_least⟩
              use sA
              constructor
              · intro x hx
                cases hx with
                | inl hxA => exact hsA_upper x hxA
                | inr hxB => exact False.elim (hEmptyB x hxB)
              · intro b hb
                have hbA : IsUpperBound1 D _ b := fun x hx => hb x (Or.inl hx)
                exact hsA_least b hbA
          | inr hSupB =>
              right
              rcases hSupA with ⟨sA, hsA⟩
              rcases hSupB with ⟨sB, hsB⟩

              use max1 D sA sB

              exact supremum_of_union D _ _ sA sB hsA hsB

theorem definable_completeness {R : Type u} (D : DenseLinearOrderNoEndpoints R)
    (A : Set (Power R 1))
    (hDef : FiniteUnionOfPointsAndIntervals D A)
    (hNotEmpty : NonEmpty1 A)
    (hBounded : BoundedAbove1 D A) :
    ∃ s : R, IsSupremum1 D A s := by

  have hCore := definable_completeness_core D A hDef hBounded
  cases hCore with
  | inl hEmpty =>
      rcases hNotEmpty with ⟨x, hx⟩
      exact False.elim (hEmpty x hx)
  | inr hSup =>
      exact hSup

/-
=========================================================
Cardinality Definitions
=========================================================
-/

def IsFinite1 {R : Type u} (A : Set (Power R 1)) : Prop :=
  exists L : List R, forall x : Power R 1, A x <-> Power.coord1 x ∈ L

def IsInfinite1 {R : Type u} (A : Set (Power R 1)) : Prop :=
  Not (IsFinite1 A)

/-
=========================================================
Intervals in Dense Orders are Infinite
=========================================================
-/
theorem interval_is_infinite {R : Type u} (D : DenseLinearOrderNoEndpoints R)
    (a b : R) (hab : D.lt a b) :
    IsInfinite1 (openInterval D (Endpoint.finite a) (Endpoint.finite b)) := by

  intro hFinite
  rcases hFinite with ⟨L, hL⟩

  rcases D.dense hab with ⟨x_val, hax, hxb⟩
  let x_pow : Power R 1 := fun _ => x_val
  have hx_in : openInterval D (Endpoint.finite a) (Endpoint.finite b) x_pow := ⟨hax, hxb⟩

  by_cases hL_empty : L = []
  ·
    subst hL_empty
    have hx_notin_L := (hL x_pow).mp hx_in
    cases hx_notin_L
  ·
    rcases extrema_of_finite_sets D L hL_empty with ⟨m, M, hMin, hMax⟩
    rcases hMax with ⟨hM_in_L_val, hM_upper⟩

    let M_pow : Power R 1 := fun _ => M
    have hM_in_L_pow : Power.coord1 M_pow ∈ L := hM_in_L_val
    have hM_in_int := (hL M_pow).mpr hM_in_L_pow

    have hMb : D.lt M b := hM_in_int.right

    rcases D.dense hMb with ⟨z, hMz, hzb⟩
    let z_pow : Power R 1 := fun _ => z

    have haz : D.lt a z := D.trans (hM_in_int.left) hMz
    have hz_in_int : openInterval D (Endpoint.finite a) (Endpoint.finite b) z_pow := ⟨haz, hzb⟩

    have hz_in_L := (hL z_pow).mp hz_in_int
    have hz_in_ListSet : ListSet L z_pow := hz_in_L

    have hz_le_M := hM_upper z_pow hz_in_ListSet

    cases hz_le_M with
    | inl hlt =>
        change D.lt z M at hlt
        exact False.elim (D.irrefl M (D.trans hMz hlt))
    | inr heq =>
        change z = M at heq
        rw [heq] at hMz
        exact False.elim (D.irrefl M hMz)

/-
=========================================================
Infinite Sets Contain an Interval
=========================================================
-/
theorem infinite_contains_interval {R : Type u} (D : DenseLinearOrderNoEndpoints R)
    (A : Set (Power R 1))
    (hDef : FiniteUnionOfPointsAndIntervals D A)
    (hInf : IsInfinite1 A) :
    exists a b : Endpoint R,
      Endpoint.lt D a b /\
      forall x, openInterval D a b x -> A x := by

  induction hDef with
  | empty =>
      have hFin : IsFinite1 (setEmpty : Set (Power R 1)) := by
        use []
        intro x
        constructor
        · intro hx; exact False.elim hx
        · intro hx; cases hx
      exact False.elim (hInf hFin)

  | point p =>
      have hFin : IsFinite1 (pointSet p) := by
        use [p]
        intro x
        constructor
        · intro hx
          change Power.coord1 x = p at hx
          rw [hx]
          exact List.Mem.head _
        · intro hx
          cases hx with
          | head => rfl
          | tail _ h_false => cases h_false
      exact False.elim (hInf hFin)

  | interval a b =>
      -- Exhaustively check endpoints to guarantee safety
      cases a with
      | posInf =>
          have hFin : IsFinite1 (openInterval D Endpoint.posInf b) := by
            use []
            intro x
            constructor
            · intro hx; exact False.elim hx.left
            · intro hx; cases hx
          exact False.elim (hInf hFin)
      | negInf =>
          cases b with
          | negInf =>
              have hFin : IsFinite1 (openInterval D Endpoint.negInf Endpoint.negInf) := by
                use []
                intro x
                constructor
                · intro hx; exact False.elim hx.right
                · intro hx; cases hx
              exact False.elim (hInf hFin)
          | finite val_b =>
              use Endpoint.negInf, Endpoint.finite val_b
              exact ⟨trivial, fun x hx => hx⟩
          | posInf =>
              use Endpoint.negInf, Endpoint.posInf
              exact ⟨trivial, fun x hx => hx⟩
      | finite val_a =>
          cases b with
          | negInf =>
              have hFin : IsFinite1 (openInterval D (Endpoint.finite val_a) Endpoint.negInf) := by
                use []
                intro x
                constructor
                · intro hx; exact False.elim hx.right
                · intro hx; cases hx
              exact False.elim (hInf hFin)
          | posInf =>
              use Endpoint.finite val_a, Endpoint.posInf
              exact ⟨trivial, fun x hx => hx⟩
          | finite val_b =>
              by_cases hab : D.lt val_a val_b
              · use Endpoint.finite val_a, Endpoint.finite val_b
                exact ⟨hab, fun x hx => hx⟩
              ·
                have hFin : IsFinite1 (openInterval D (Endpoint.finite val_a) (Endpoint.finite val_b)) := by
                  use []
                  intro x
                  constructor
                  · intro hx
                    have htrans := D.trans hx.left hx.right
                    exact False.elim (hab htrans)
                  · intro hx; cases hx
                exact False.elim (hInf hFin)

  | union hA hB ihA ihB =>
      rename_i S1 S2

      by_cases hA_inf : IsInfinite1 S1
      · rcases ihA hA_inf with ⟨a, b, hab, hSub⟩
        use a, b
        exact ⟨hab, fun x hx => Or.inl (hSub x hx)⟩
      · by_cases hB_inf : IsInfinite1 S2
        · rcases ihB hB_inf with ⟨a, b, hab, hSub⟩
          use a, b
          exact ⟨hab, fun x hx => Or.inr (hSub x hx)⟩
        ·
          have hA_fin : IsFinite1 S1 := Classical.not_not.mp hA_inf
          have hB_fin : IsFinite1 S2 := Classical.not_not.mp hB_inf

          rcases hA_fin with ⟨LA, hLA⟩
          rcases hB_fin with ⟨LB, hLB⟩

          have hUnion_fin : IsFinite1 (setUnion S1 S2) := by
            use LA ++ LB
            intro x
            constructor
            · intro hx
              cases hx with
              | inl hAx => exact List.mem_append.mpr (Or.inl ((hLA x).mp hAx))
              | inr hBx => exact List.mem_append.mpr (Or.inr ((hLB x).mp hBx))
            · intro hx
              cases List.mem_append.mp hx with
              | inl hLAx => exact Or.inl ((hLA x).mpr hLAx)
              | inr hLBx => exact Or.inr ((hLB x).mpr hLBx)

          exact False.elim (hInf hUnion_fin)

/-
=========================================================
Lemma 1 (not done yet)
=========================================================
-/

-- 1. Az intervallum általános definíciója
def is_interval {R : Type*} [D : DenseLinearOrderNoEndpoints R] (S : Set R) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ z, (D.lt x z ∨ x = z) → (D.lt z y ∨ z = y) → z ∈ S

-- 3. ConstantOn és InjectiveOn definíciója
def ConstantOn {R : Type*} (f : R → R) (J : Set R) : Prop :=
  ∀ x ∈ J, ∀ y ∈ J, f x = f y

def InjectiveOn {R : Type*} (f : R → R) (J : Set R) : Prop :=
  ∀ x ∈ J, ∀ y ∈ J, f x = f y → x = y

noncomputable def myInf {R : Type*} [LinearOrder R] [Nonempty R] (S : Set R) : R :=
  Classical.epsilon (fun x => x ∈ S ∧ ∀ y ∈ S, x ≤ y)

lemma myInf_spec {R : Type*} [LinearOrder R] [Nonempty R] {S : Set R}
    (hfin : S.Finite) (hne : S.Nonempty) :
    myInf S ∈ S ∧ ∀ z ∈ S, myInf S ≤ z := by
  have hex : ∃ x, x ∈ S ∧ ∀ y ∈ S, x ≤ y := by
    obtain ⟨x0, hx0⟩ := hne
    have hx0' : x0 ∈ hfin.toFinset := hfin.mem_toFinset.mpr hx0
    have hs_ne : hfin.toFinset.Nonempty := ⟨x0, hx0'⟩
    exact ⟨hfin.toFinset.min' hs_ne,
      hfin.mem_toFinset.mp (Finset.min'_mem _ hs_ne),
      fun z hz => Finset.min'_le _ z (hfin.mem_toFinset.mpr hz)⟩
  exact Classical.epsilon_spec hex

lemma lemma_1 {R : Type*} [LinearOrder R] [Nonempty R] {I : Set R}
  (_hI : is_interval I) (hI_inf : Set.Infinite I)
  (f : R → R) (_hf_def : DefinableFunction f) :
  ∃ J ⊆ I, is_interval J ∧ (ConstantOn f J ∨ InjectiveOn f J) := by

  by_cases h_inf_preimage : ∃ y : R, Set.Infinite (f ⁻¹' {y} ∩ I)

  · rcases h_inf_preimage with ⟨y, hy_inf⟩

    have h_contains_interval : ∃ J ⊆ (f ⁻¹' {y} ∩ I), is_interval J := by
      rcases o_minimal_contains_interval hy_inf with ⟨J, hJ_sub, hJ_int, _⟩
      exact ⟨J, hJ_sub, hJ_int⟩

    rcases h_contains_interval with ⟨J, hJ_sub, hJ_int⟩

    use J
    refine ⟨?_, hJ_int, Or.inl ?_⟩
    exact Set.Subset.trans hJ_sub Set.inter_subset_right

    unfold ConstantOn
    intro x hx z hz
    have hx_prop := (hJ_sub hx).left
    have hz_prop := (hJ_sub hz).left
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hx_prop hz_prop
    rw [hx_prop, hz_prop]

  · push Not at h_inf_preimage

    have h_fI_inf : Set.Infinite (f '' I) := by
      intro h_fin_img
      have h_I_fin : I.Finite := by
        apply Set.Finite.subset (Set.Finite.biUnion h_fin_img (fun y _ => h_inf_preimage y))
        intro x hx
        exact Set.mem_biUnion (Set.mem_image_of_mem f hx) ⟨rfl, hx⟩
      exact hI_inf h_I_fin

    -- JAVÍTVA: A 'by exact' szerkezet eltávolítva a linter warning miatt
    have h_fI_contains_interval : ∃ J_img ⊆ (f '' I), is_interval J_img ∧ Set.Infinite J_img :=
      o_minimal_contains_interval h_fI_inf

    rcases h_fI_contains_interval with ⟨J_img, hJ_img_sub, hJ_img_int, hJ_img_inf⟩

    let g : R → R := fun y => myInf {x ∈ I | f x = y}

    have h_finite_preimage : ∀ y : R, {x ∈ I | f x = y}.Finite := by
      intro y
      apply (h_inf_preimage y).subset
      rintro x ⟨hxI, hfx⟩
      exact ⟨hfx, hxI⟩

    have h_g_in_I : ∀ y ∈ J_img, g y ∈ I := by
      intro y hy
      unfold g
      have h_nonempty : {x ∈ I | f x = y}.Nonempty := by
        obtain ⟨x, hxI, hfx⟩ := hJ_img_sub hy
        exact ⟨x, hxI, hfx⟩
      exact (myInf_spec (h_finite_preimage y) h_nonempty).1.1

    have h_fg_eq : ∀ y ∈ J_img, f (g y) = y := by
      intro y hy
      unfold g
      have h_nonempty : {x ∈ I | f x = y}.Nonempty := by
        obtain ⟨x, hxI, hfx⟩ := hJ_img_sub hy
        exact ⟨x, hxI, hfx⟩
      exact (myInf_spec (h_finite_preimage y) h_nonempty).1.2

    have h_g_inj : Set.InjOn g J_img := by
      intro y1 hy1 y2 hy2 h_eq
      have h1 := h_fg_eq y1 hy1
      have h2 := h_fg_eq y2 hy2
      rw [← h1, ← h2, h_eq]

    have h_gJ_inf : Set.Infinite (g '' J_img) := infinite_image_of_injOn hJ_img_inf h_g_inj
    have h_gJ_contains_interval : ∃ J ⊆ (g '' J_img), is_interval J := by
      rcases o_minimal_contains_interval h_gJ_inf with ⟨J, hJ_sub, hJ_int, _⟩
      exact ⟨J, hJ_sub, hJ_int⟩

    rcases h_gJ_contains_interval with ⟨J, hJ_sub_gJ, hJ_int⟩

    have hJ_sub_I : J ⊆ I := by
      intro x hx
      rcases hJ_sub_gJ hx with ⟨y, hy, hgy⟩
      rw [← hgy]
      exact h_g_in_I y hy

    use J
    refine ⟨hJ_sub_I, hJ_int, Or.inr ?_⟩
    intro x1 hx1 x2 hx2 h_eq

    rcases hJ_sub_gJ hx1 with ⟨y1, hy1_in, hy1_eq⟩
    rcases hJ_sub_gJ hx2 with ⟨y2, hy2_in, hy2_eq⟩

    rw [← hy1_eq, ← hy2_eq] at h_eq
    rw [← hy1_eq, ← hy2_eq]

    have h1 := h_fg_eq y1 hy1_in
    have h2 := h_fg_eq y2 hy2_in

    have h_y_eq : y1 = y2 := by
      rw [← h1, ← h2]
      exact h_eq

    rw [h_y_eq]

/-
=========================================================
Lemma 2 (not done yet)
=========================================================
-/

variable {R : Type u} {D : DenseLinearOrderNoEndpoints R}

def A_x (D : DenseLinearOrderNoEndpoints R) (f : Power R 1 → Power R 1)
    (a x : Power R 1) : Set (Power R 1) :=
  setInter (openInterval D (Endpoint.finite (Power.coord1 a)) (Endpoint.finite (Power.coord1 x)))
    (fun y => Lt1 D (f y) (f x))

/-- Definability of `A_x`, given the graph of `f` is definable.
    Mirrors `coreAt_mem` / `graphOn_mem` above: build it from `M`'s
    primitive axioms rather than a separate opaque axiom. -/
theorem A_x_mem (M : OMinimalStructure D) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) (a x : Power R 1) :
    M.S 1 (A_x D f.toFun a x) := by
  sorry -- build via `f.graph_mem`, `M.inter_mem`, `M.existsLast_mem`,
        -- exactly as `A_x_is_definable` used `f_less_than_const_definable`
        -- in the small file, but derived instead of axiomatized.

def PhiPlusPlus (D : DenseLinearOrderNoEndpoints R) (f : Power R 1 → Power R 1)
    (I : Set (Power R 1)) (x : Power R 1) : Prop :=
  I x ∧ ∃ c1, I c1 ∧ ∃ c2, I c2 ∧ Lt1 D c1 x ∧ Lt1 D x c2 ∧
    (∀ y, I y → Lt1 D c1 y → Lt1 D y x → Lt1 D (f x) (f y)) ∧
    (∀ y, I y → Lt1 D x y → Lt1 D y c2 → Lt1 D (f x) (f y))

def PhiPlusMinus (D : DenseLinearOrderNoEndpoints R) (f : Power R 1 → Power R 1)
    (I : Set (Power R 1)) (x : Power R 1) : Prop :=
  I x ∧ ∃ c1, I c1 ∧ ∃ c2, I c2 ∧ Lt1 D c1 x ∧ Lt1 D x c2 ∧
    (∀ y, I y → Lt1 D c1 y → Lt1 D y x → Lt1 D (f x) (f y)) ∧
    (∀ y, I y → Lt1 D x y → Lt1 D y c2 → Lt1 D (f y) (f x))

def PhiMinusPlus (D : DenseLinearOrderNoEndpoints R) (f : Power R 1 → Power R 1)
    (I : Set (Power R 1)) (x : Power R 1) : Prop :=
  I x ∧ ∃ c1, I c1 ∧ ∃ c2, I c2 ∧ Lt1 D c1 x ∧ Lt1 D x c2 ∧
    (∀ y, I y → Lt1 D c1 y → Lt1 D y x → Lt1 D (f y) (f x)) ∧
    (∀ y, I y → Lt1 D x y → Lt1 D y c2 → Lt1 D (f x) (f y))

def PhiMinusMinus (D : DenseLinearOrderNoEndpoints R) (f : Power R 1 → Power R 1)
    (I : Set (Power R 1)) (x : Power R 1) : Prop :=
  I x ∧ ∃ c1, I c1 ∧ ∃ c2, I c2 ∧ Lt1 D c1 x ∧ Lt1 D x c2 ∧
    (∀ y, I y → Lt1 D c1 y → Lt1 D y x → Lt1 D (f y) (f x)) ∧
    (∀ y, I y → Lt1 D x y → Lt1 D y c2 → Lt1 D (f y) (f x))

def PsiPlusMinus (D : DenseLinearOrderNoEndpoints R) (f : Power R 1 → Power R 1)
    (I : Set (Power R 1)) (v : Power R 1) : Prop :=
  I v ∧ ∃ v1, I v1 ∧ ∃ v2, I v2 ∧ Lt1 D v1 v ∧ Lt1 D v v2 ∧
    ∀ z1, I z1 → ∀ z2, I z2 →
      Lt1 D v1 z1 → Lt1 D z1 v → Lt1 D v z2 → Lt1 D z2 v2 →
      Lt1 D (f z2) (f z1)

def PsiMinusPlus (D : DenseLinearOrderNoEndpoints R) (f : Power R 1 → Power R 1)
    (I : Set (Power R 1)) (v : Power R 1) : Prop :=
  I v ∧ ∃ u1, I u1 ∧ ∃ u2, I u2 ∧ Lt1 D u1 v ∧ Lt1 D v u2 ∧
    ∀ z1, I z1 → ∀ z2, I z2 →
      Lt1 D u1 z1 → Lt1 D z1 v → Lt1 D v z2 → Lt1 D z2 u2 →
      Lt1 D (f z1) (f z2)

/-- Same combinatorial content as `step_1_partition`; still open. -/
lemma step_1_partition (D : DenseLinearOrderNoEndpoints R)
    (f : Power R 1 → Power R 1) {a b : Power R 1} (hab : Lt1 D a b)
    (hinj : ∀ x, Lt1 D a x → Lt1 D x b →
            ∀ y, Lt1 D a y → Lt1 D y b → f x = f y → x = y) :
    ∃ c d, Lt1 D c d ∧
      (∀ x, Lt1 D c x → Lt1 D x d → Lt1 D a x ∧ Lt1 D x b) ∧
      ( (∀ x, Lt1 D c x → Lt1 D x d →
            PhiPlusPlus D f (fun p => Lt1 D c p ∧ Lt1 D p d) x) ∨
        (∀ x, Lt1 D c x → Lt1 D x d →
            PhiPlusMinus D f (fun p => Lt1 D c p ∧ Lt1 D p d) x) ∨
        (∀ x, Lt1 D c x → Lt1 D x d →
            PhiMinusPlus D f (fun p => Lt1 D c p ∧ Lt1 D p d) x) ∨
        (∀ x, Lt1 D c x → Lt1 D x d →
            PhiMinusMinus D f (fun p => Lt1 D c p ∧ Lt1 D p d) x) ) := by
  sorry

lemma step_2_easy_case_minus_plus (D : DenseLinearOrderNoEndpoints R)
    (f : Power R 1 → Power R 1) {c d : Power R 1} (hcd : Lt1 D c d)
    (h_phi : ∀ x, Lt1 D c x → Lt1 D x d →
      PhiMinusPlus D f (fun p => Lt1 D c p ∧ Lt1 D p d) x) :
    ∀ x, Lt1 D c x → Lt1 D x d →
    ∀ y, Lt1 D c y → Lt1 D y d → Lt1 D x y → Lt1 D (f x) (f y) := by
  sorry

lemma psi_contradiction (D : DenseLinearOrderNoEndpoints R)
    (f : Power R 1 → Power R 1) (I : Set (Power R 1)) (v : Power R 1)
    (h_I_convex : ∀ x y z, I x → I y → (Lt1 D x z ∨ x = z) → (Lt1 D z y ∨ z = y) → I z)
    (h_pm : PsiPlusMinus D f I v) (h_mp : PsiMinusPlus D f I v) : False := by
  sorry -- straight port of `psi_contradiction`; only the `<`/`max`/`min`
        -- lemmas need `D.trans`/`D.trichotomy` instead of Mathlib's order API

lemma step_3_difficult_case_plus_plus_impossible (D : DenseLinearOrderNoEndpoints R)
    (f : Power R 1 → Power R 1) {c d : Power R 1} (hcd : Lt1 D c d)
    (h_phi : ∀ x, Lt1 D c x → Lt1 D x d →
      PhiPlusPlus D f (fun p => Lt1 D c p ∧ Lt1 D p d) x) : False := by
  sorry

/-- Lemma 2 proper, stated so its conclusion feeds `StrictlyMonotoneOn`
    once you restrict `f` to the subinterval (see the restriction helper
    below, which you'll need before calling Lemma 3). -/
theorem lemma_2_injective_implies_strictly_monotone_on_subinterval
    (M : OMinimalStructure D) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B)
    (hinj : ∀ x y (hx : I x) (hy : I y), f.toFun ⟨x, hx⟩ = f.toFun ⟨y, hy⟩ → x = y) :
    ∃ a b : Endpoint R, Endpoint.lt D a b ∧
      (∀ x, openInterval D a b x → I x) ∧
      -- strict monotonicity on the subinterval, phrased so it composes
      -- with `DefinableFunction.restrictToInterval` below
      ( (∀ x y (hx : I x) (hy : I y),
           openInterval D a b x → openInterval D a b y →
           Lt1 D x y → Lt1 D (f.toFun ⟨x,hx⟩).1 (f.toFun ⟨y,hy⟩).1) ∨
        (∀ x y (hx : I x) (hy : I y),
           openInterval D a b x → openInterval D a b y →
           Lt1 D x y → Lt1 D (f.toFun ⟨y,hy⟩).1 (f.toFun ⟨x,hx⟩).1) ) := by
  sorry

/-
=========================================================
Lemma 3
=========================================================
-/

def StrictlyIncreasingOn (D : DenseLinearOrderNoEndpoints R) (I : Set (Power R 1))
    (B : Set (Power R 1)) (f : {x : Power R 1 // I x} -> {y : Power R 1 // B y}) : Prop :=
  forall (x y : Power R 1) (hx : I x) (hy : I y), Lt1 D x y -> Lt1 D (f ⟨x, hx⟩).1 (f ⟨y, hy⟩).1

def StrictlyDecreasingOn (D : DenseLinearOrderNoEndpoints R) (I : Set (Power R 1))
    (B : Set (Power R 1)) (f : {x : Power R 1 // I x} -> {y : Power R 1 // B y}) : Prop :=
  forall (x y : Power R 1) (hx : I x) (hy : I y), Lt1 D x y -> Lt1 D (f ⟨y, hy⟩).1 (f ⟨x, hx⟩).1

def StrictlyMonotoneOn (D : DenseLinearOrderNoEndpoints R) (I : Set (Power R 1))
    (B : Set (Power R 1)) (f : {x : Power R 1 // I x} -> {y : Power R 1 // B y}) : Prop :=
  StrictlyIncreasingOn D I B f \/ StrictlyDecreasingOn D I B f

lemma injective_of_strictly_monotone_on {R : Type u} (D : DenseLinearOrderNoEndpoints R)
    {I B : Set (Power R 1)} (f : {x : Power R 1 // I x} -> {y : Power R 1 // B y})
    (hmono : StrictlyMonotoneOn D I B f) : f.Injective := by
    intro x y h_eq
    by_contra h_ne
    have h_coord_ne : Not (x.val.coord1 = y.val.coord1) := by
      intro h
      apply h_ne
      ext i
      fin_cases i
      exact h
    rcases D.trichotomy x.val.coord1 y.val.coord1 with ⟨hlt, -⟩ | ⟨heq, -⟩ | ⟨hlt, -⟩
    · rcases hmono with hinc | hdec <;> apply D.irrefl
      · simpa [h_eq] using hinc x.val y.val x.2 y.2 hlt
      · simpa [h_eq] using hdec x.val y.val x.2 y.2 hlt
    · exact h_coord_ne heq
    · rcases hmono with hinc | hdec <;> apply D.irrefl
      · simpa [h_eq] using hinc y.val x.val y.2 x.2 hlt
      · simpa [h_eq] using hdec y.val x.val y.2 x.2 hlt

lemma IsInfinite1.image_of_injective {R : Type u}
    {A B : Set (Power R 1)} (f : {x : Power R 1 // A x} -> {y : Power R 1 // B y})
    (hinj : f.Injective) (hA : IsInfinite1 A) :
    IsInfinite1 (FunctionImage (m := 1) (n := 1) (A := A) (B := B) f) := by
  intro hFin
  apply hA
  rcases hFin with ⟨L, hL⟩
  have h_pre (r : R) (hr : L.Mem r) : exists y : A, (f y).val = fun _ => r :=
    let ⟨y, hy, heq⟩ := (hL (fun _ => r)).mpr (by simpa [Power.coord1, hr])
    ⟨⟨y, hy⟩, heq.symm⟩
  choose p hp using h_pre
  refine ⟨L.attach.map fun ⟨r, hr⟩ => (p r hr).val.coord1, fun y => ⟨fun hy => ?_, fun hc => ?_⟩⟩
  · have hrL : L.Mem ((f ⟨y, hy⟩).val.coord1) := (hL (f ⟨y, hy⟩).val).mp ⟨y, hy, rfl⟩
    have hpre : p _ hrL = ⟨y, hy⟩ :=
      hinj (Subtype.ext (by rw [hp _ hrL]; ext i; fin_cases i; rw [Power.coord1]; rfl))
    exact List.mem_map.mpr ⟨⟨_, hrL⟩, L.mem_attach _, by simp [hpre]⟩
  · obtain ⟨⟨r, hr⟩, -, heq⟩ := List.mem_map.mp hc
    rw [show y = (p r hr).val by ext i; fin_cases i; exact heq.symm]
    exact (p r hr).property

lemma exists_two_points_in_open_interval (D : DenseLinearOrderNoEndpoints R) [Nonempty R]
    (a b : Endpoint R) (hab : Endpoint.lt D a b) :
    exists r s : R,
      D.lt r s /\
      openInterval D a b (fun _ => r) /\
      openInterval D a b (fun _ => s) /\
      forall x : Power R 1,
        openInterval D (Endpoint.finite r) (Endpoint.finite s) x ->
        openInterval D a b x := by
  rcases a with (a_neg | a_fin | a_pos)
  · rcases b with (b_neg | b_fin | b_pos)
    · exfalso
      exact hab
    · obtain ⟨p, hp⟩ := D.no_left_endpoint b_fin
      obtain ⟨r, _, hr_b⟩ := D.dense hp
      obtain ⟨s, hrs, hs_b⟩ := D.dense hr_b
      refine ⟨r, s, hrs, ⟨trivial, hr_b⟩, ⟨trivial, hs_b⟩, fun x ⟨_, hx⟩ => ⟨trivial, D.trans hx hs_b⟩⟩
    · obtain ⟨x0⟩ : Nonempty R := inferInstance
      obtain ⟨r, _⟩ := D.no_right_endpoint x0
      obtain ⟨s, hrs⟩ := D.no_right_endpoint r
      refine ⟨r, s, hrs, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩, fun _ _ => ⟨trivial, trivial⟩⟩
  · rcases b with (b_neg | b_fin | b_pos)
    · exfalso
      exact hab
    · obtain ⟨r, har, hrb⟩ := D.dense hab
      obtain ⟨s, hrs, hsb⟩ := D.dense hrb
      refine ⟨r, s, hrs, ⟨har, hrb⟩, ⟨D.trans har hrs, hsb⟩, fun x ⟨hx1, hx2⟩ =>
        ⟨D.trans har hx1, D.trans hx2 hsb⟩⟩
    · obtain ⟨r, har⟩ := D.no_right_endpoint a_fin
      obtain ⟨s, hrs⟩ := D.no_right_endpoint r
      refine ⟨r, s, hrs, ⟨har, trivial⟩, ⟨D.trans har hrs, trivial⟩, fun x ⟨hx, _⟩ =>
        ⟨D.trans har hx, trivial⟩⟩
  · exfalso
    exact hab

lemma nonempty_of_isInfinite1 {A : Set (Power R 1)} (h : IsInfinite1 A) : Nonempty R := by
  by_contra hne
  haveI : IsEmpty R := not_nonempty_iff.mp hne
  exact h ⟨[], fun x => ⟨isEmptyElim (x 0), fun h => by cases h⟩⟩

lemma exists_order_preserving_bijection_interval
    (M : OMinimalStructure D) {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    (hmono : StrictlyMonotoneOn D I B f.toFun)
    {c d : Power R 1} (hc : I c) (hd : I d)
    {r s : R} (hrs : D.lt r s)
    (hcr : (f.toFun ⟨c, hc⟩).1 = (fun _ => r))
    (hds : (f.toFun ⟨d, hd⟩).1 = (fun _ => s))
    (hValueInterval : (openInterval D (Endpoint.finite r) (Endpoint.finite s)).Subset
      (FunctionImage (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun)) :
    exists a b : Endpoint R,
      Endpoint.lt D a b /\
      (openInterval D a b).Subset I /\
      (forall x, openInterval D a b x ->
        exists hx : I x,
          openInterval D (Endpoint.finite r) (Endpoint.finite s) (f.toFun ⟨x, hx⟩).1) /\
      (forall y, openInterval D (Endpoint.finite r) (Endpoint.finite s) y ->
        exists x, openInterval D a b x /\
          exists hx : I x, (f.toFun ⟨x, hx⟩).1 = y) := by
  sorry

lemma continuous_of_interval_bijection
    (M : OMinimalStructure D) {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    {a b : Endpoint R} (hab : Endpoint.lt D a b)
    (hDomain : (openInterval D a b).Subset I)
    {r s : R} (hrs : D.lt r s)
    (hMapsTo : forall x, openInterval D a b x ->
        exists hx : I x,
          openInterval D (Endpoint.finite r) (Endpoint.finite s) (f.toFun ⟨x, hx⟩).1)
    (hSurj : forall y, openInterval D (Endpoint.finite r) (Endpoint.finite s) y ->
        exists x, openInterval D a b x /\
          exists hx : I x, (f.toFun ⟨x, hx⟩).1 = y) :
    (openInterval D a b).Subset
      (ContinuousPoints D I
        (FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun)) := by
  sorry

theorem strictly_monotone_definable_continuous_on_subinterval
    (M : OMinimalStructure D)
    {I B : Set (Power R 1)}
    (f : DefinableFunction M I B)
    (hmono : StrictlyMonotoneOn D I B f.toFun)
    (hInf : IsInfinite1 I) :
    exists a b : Endpoint R,
      Endpoint.lt D a b /\
      (openInterval D a b).Subset I /\
      (openInterval D a b).Subset (ContinuousPoints D I
        (FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun)) := by
  have hinj : f.toFun.Injective := injective_of_strictly_monotone_on D f.toFun hmono
  let fIm := FunctionImage (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
  have hImageInf : IsInfinite1 fIm := hInf.image_of_injective f.toFun hinj
  have hFImDef : M.S 1 fIm := functionImage_mem M f
  have hFImFin : FiniteUnionOfPointsAndIntervals D fIm := (M.ominimal fIm).mp hFImDef
  obtain ⟨a0, b0, hab0, hSubJ⟩ := infinite_contains_interval D fIm hFImFin hImageInf
  haveI : Nonempty R := nonempty_of_isInfinite1 hInf
  obtain ⟨r, s, hrs, hrJ, hsJ, hSubRS⟩ := exists_two_points_in_open_interval D a0 b0 hab0
  have hValueInterval : (openInterval D (Endpoint.finite r) (Endpoint.finite s)).Subset fIm :=
    fun x hx => hSubJ x (hSubRS x hx)
  have hIm_r : exists c : Power R 1, exists hc : I c, (f.toFun ⟨c, hc⟩).val = fun _ => r := by
    have hmem := hSubJ (fun _ => r) hrJ
    simpa [fIm, FunctionImage, eq_comm] using hmem
  obtain ⟨c, hc, hcr⟩ := hIm_r
  have hIm_s : exists d : Power R 1, exists hd : I d, (f.toFun ⟨d, hd⟩).val = fun _ => s := by
    have hmem := hSubJ (fun _ => s) hsJ
    simpa [fIm, FunctionImage, eq_comm] using hmem
  obtain ⟨d, hd, hds⟩ := hIm_s
  obtain ⟨a, b, hab, hDomain, hMapsTo, hSurj⟩ :=
    exists_order_preserving_bijection_interval M f hmono hc hd hrs hcr hds hValueInterval
  have hCont := continuous_of_interval_bijection M f hab hDomain hrs hMapsTo hSurj
  exact ⟨a, b, hab, hDomain, hCont⟩

/-
=========================================================
Monotonicity Case 1
=========================================================
-/

open Set

variable {α β R : Type*} [D : DenseLinearOrderNoEndpoints R]

def IsConstantOn (f : α → β) (S : Set α) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, f x = f y

theorem constant_union {f : α → β} {S T : Set α} {c : α}
  (hcS : c ∈ S) (hcT : c ∈ T)
  (hS : IsConstantOn f S) (hT : IsConstantOn f T) :
  IsConstantOn f (S ∪ T) := by
  intro x hx y hy
  cases hx with
  | inl hxS =>
    cases hy with
    | inl hyS =>
      exact hS x hxS y hyS
    | inr hyT =>
      have h1 : f x = f c := hS x hxS c hcS
      have h2 : f c = f y := hT c hcT y hyT
      rw [h1, h2]
  | inr hxT =>
    cases hy with
    | inl hyS =>
      have h1 : f x = f c := hT x hxT c hcT
      have h2 : f c = f y := hS c hcS y hyS
      rw [h1, h2]
    | inr hyT =>
      exact hT x hxT y hyT

def IsLocallyConstantAt (f : R → R) (x : R) : Prop :=
  ∃ c d : R, (D.lt c x) ∧ (D.lt x d) ∧ IsConstantOn f (Power.coord1 '' openInterval D (Endpoint.finite c) (Endpoint.finite d))

def IsUpperBoundR (S : Set R) (b : R) : Prop :=
  ∀ x ∈ S, D.lt x b ∨ x = b

def BoundedAboveR (S : Set R) : Prop :=
  ∃ b, IsUpperBoundR S b

def IsSupremumR (S : Set R) (s : R) : Prop :=
  IsUpperBoundR S s ∧ ∀ b, IsUpperBoundR S b → D.lt s b ∨ s = b

theorem monotonicity_case1 (a b : R) (hab : D.lt a b) (f : R → R)
  (h_case1 : ∀ x ∈ (Power.coord1 '' openInterval D (Endpoint.finite a) (Endpoint.finite b)), IsLocallyConstantAt f x) :
  IsConstantOn f (Power.coord1 '' openInterval D (Endpoint.finite a) (Endpoint.finite b)) := by
  have h_right : ∀ x₀ ∈ openInterval D (Endpoint.finite a) (Endpoint.finite b), IsConstantOn f (Power.coord1 '' closedOpenInterval D (Power.coord1 x₀) b) := by
    intro x₀ hx₀
    -- Definition of S: the set of points x for which the function is constant on [x₀, x]
    let S := {x | D.lt (Power.coord1 x₀) x ∧ (D.lt x b ∨ x = b) ∧ IsConstantOn f (Power.coord1 '' closedOpenInterval D (Power.coord1 x₀) x)}

    -- S is bounded above by b
    have hb_upper : IsUpperBoundR S b := by
      intro y hy
      exact hy.2.1

    have hS_bdd : BoundedAboveR S := ⟨b, hb_upper⟩

    -- S is non-empty because f is locally constant at x₀
    have hS_nonempty : S.Nonempty := by
      rcases h_case1 (Power.coord1 x₀) (Set.mem_image_of_mem Power.coord1 hx₀) with ⟨c, d, hc_lt_x0, hx0_lt_d, h_const_cd⟩
      -- The exact proof steps go here (proving denseness and interval subsets)
      sorry

    -- Getting an actual supremum of `S` needs `S` to be a finite union of
    -- points/intervals (so `definable_completeness` applies), which in turn
    -- needs `f` to be definable in `M` on the relevant range — not currently
    -- a hypothesis of this theorem. Left open on purpose.
    obtain ⟨s, hs_sup⟩ : ∃ s, IsSupremumR S s := sorry

    -- Proof by contradiction: show that s = b
    have hs_eq_b : s = b := by
      by_contra h_neq
      have hs_le_b : D.lt s b ∨ s = b := hs_sup.2 b hb_upper
      have hs_lt_b : D.lt s b := hs_le_b.resolve_right h_neq

      have hs_in_Ioo : s ∈ (Power.coord1 '' openInterval D (Endpoint.finite a) (Endpoint.finite b)) := by
        -- Proof that a < s and s < b
        sorry

      rcases h_case1 s hs_in_Ioo with ⟨c, d, hc_lt_s, hs_lt_d, h_const_cd⟩

      have h_overlap : ∃ x ∈ S, D.lt c x := by
        --exact exists_lt_of_lt_csSup
        -- Using the supremum property (exists_lt_of_lt_csSup)
        sorry

      -- Completing the contradiction (proving y is constant up to a point > s, meaning y ∈ S)
      sorry

    -- Extension to b (using continuity or boundary properties)
    sorry

  have h_left : ∀ x₀ ∈ openInterval D (Endpoint.finite a) (Endpoint.finite b), IsConstantOn f (Power.coord1 '' closedOpenInterval D a (Power.coord1 x₀)) := by
    intro x₀ hx₀
    -- Analogous infimum (sInf) argument going leftwards towards a
    sorry

  -- Proving global equality by gluing the left and right intervals together
  intro x hx y hy
  sorry

end OMinimalStructure

end OMinimal
