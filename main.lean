import mathlib
open Nat
open Finset
open BigOperators

/- SMALL TASKS -/

-- 1.
def catalanNumber : (n: ℕ) → ℕ
| 0 => 1
| n+1 => ∑ i : Fin n.succ, (catalanNumber i) * (catalanNumber (n - i))

-- 2.
inductive PlaneTree : Type
| nodes : (List PlaneTree) → PlaneTree

-- 3.
inductive BinaryTree : Type
| leaf
| node : (T₁ T₂ : BinaryTree) → BinaryTree

def BinaryTree.numNodes : BinaryTree → ℕ
| leaf => 1
| node T₁ T₂ => T₁.numNodes + T₂.numNodes + 1

-- 4.
def NBinaryTree (n : ℕ) : Type :=
  { T : BinaryTree // T.numNodes = n}


-- 5.

def BallotSequence : List ℤ → ℤ → Bool
| [], sum => sum ≥ 0
| x :: xs, sum => (sum + x) ≥ 0 ∧ BallotSequence xs (sum + x)

def generateSequences : Nat → List (List ℤ)
| 0 => [[]]
| n + 1 => generateSequences n >>= fun seq => [1 :: seq, -1 :: seq]

def generateBallotSequences (n : Nat) : List (List ℤ) :=
   (generateSequences n).filter (fun seq => BallotSequence seq 0)


------------------------------------------------

/- BIG TASKS -/


-- 4.

def PlaneTree.children : PlaneTree -> List PlaneTree
| nodes T => T

def fromChildren : List PlaneTree -> PlaneTree
| T => PlaneTree.nodes T

theorem ListPlaneTree2PlaneTree :
  ∀ (l : List PlaneTree),
  l = (fromChildren l).children:= by
  intro childrenList
  cases childrenList
  . case _ => rfl
  . case cons head tail => rfl

theorem PlaneTree2ListPlaneTree :
  ∀ (tree : PlaneTree),
  tree = fromChildren (tree.children) := by
  intro tree
  cases tree
  . case nodes children => rfl

------------------------

-- 5.

def BinaryTree.children : BinaryTree → PlaneTree
| leaf => PlaneTree.nodes List.nil
| node T₁ T₂ =>
  PlaneTree.nodes (List.cons (BinaryTree.children T₁) (BinaryTree.children T₂).children)

def PlaneTree.children2 : PlaneTree → BinaryTree
  | nodes List.nil => BinaryTree.leaf
  | nodes (head :: tail) => BinaryTree.node (PlaneTree.children2 head) (PlaneTree.children2 (PlaneTree.nodes tail))

theorem BinaryTree2PlaneTree_inverse :
  ∀ (T : BinaryTree),
  T = PlaneTree.children2 (BinaryTree.children T) := by
intro T
induction T with
| leaf => rfl
| node T₁ T₂ H₁ H₂ =>
  simp [BinaryTree.children, PlaneTree.children2, PlaneTree.children]
  rw[← H₁]
  apply And.intro
  tauto
  split
  case node type T =>
    rw[← T, ← H₂]

theorem PlaneTree2BinaryTree_inverse :
  ∀ (T : PlaneTree),
  T = BinaryTree.children (PlaneTree.children2 T) := by
  intro T
  cases T with
  | nodes l =>
    cases l with
    | nil => rfl
    | cons T l =>
      rw [PlaneTree.children2]
      simp [BinaryTree.children]
      apply And.intro
      rw [← PlaneTree2BinaryTree_inverse]
      rw [← PlaneTree2BinaryTree_inverse, PlaneTree.children]
