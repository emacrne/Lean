import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorization.Basic

open Nat
open Finset
open BigOperators


/- SMALL TASKS -/

-- 1. Recursive definition of catalan numbers
def catalanNumber : (n: ℕ) → ℕ
| 0 => 1
| n+1 => ∑ i : Fin n.succ, (catalanNumber i) * (catalanNumber (n - i))

-- 2. Plane trees
inductive PlaneTree : Type
| nodes : (List PlaneTree) → PlaneTree

-- 3. Full binary trees
inductive BinaryTree : Type
| leaf
| node : (T₁ T₂ : BinaryTree) → BinaryTree

def BinaryTree.numNodes : BinaryTree → ℕ
| leaf => 1
| node T₁ T₂ => T₁.numNodes + T₂.numNodes + 1

-- 4. Full binary trees with n nodes
def NBinaryTree (n : ℕ) : Type :=
  { T : BinaryTree // T.numNodes = n}

-- 5. Ballot sequences of length n
def NBallotSequences (n : ℕ) : List (List ℕ) :=
  let rec BallotSequence : List ℕ → ℕ → Bool
  | [], sum => sum ≥ 0
  | head :: tail, sum => (sum + head) ≥ 0 ∧ BallotSequence tail (sum + head)
  let rec Sequences : ℕ → List (List ℕ)
  | 0 => [[]]
  | n + 1 => Sequences n >>= fun seq => [1 :: seq, 0 :: seq]
  (Sequences n).filter (fun seq => BallotSequence seq 0)


------------------------------------------------

/- BIG TASKS -/


-- 4.

section

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

end

------------------------

-- 5.

section

def BinaryTree.children : BinaryTree → PlaneTree
| leaf => PlaneTree.nodes List.nil
| node T₁ T₂ =>
  PlaneTree.nodes (List.cons (BinaryTree.children T₁) (BinaryTree.children T₂).children)

def PlaneTree.children2 : PlaneTree → BinaryTree
  | nodes List.nil => BinaryTree.leaf
  | nodes (head :: tail) => BinaryTree.node (PlaneTree.children2 head) (PlaneTree.children2 (PlaneTree.nodes tail))

theorem BinaryTree2PlaneTree :
  ∀ (T : BinaryTree),
  T = PlaneTree.children2 (BinaryTree.children T) := by
intro T
induction T with
| leaf => rfl
| node T₁ T₂ H₁ H₂ =>
  simp [BinaryTree.children, PlaneTree.children2, PlaneTree.children]
  rw[← H₁]
  apply And.intro
  simp[PlaneTree.children]
  split
  case node type T =>
    rw[← T]
    rw[← H₂]

theorem PlaneTree2BinaryTree :
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
      rw [← PlaneTree2BinaryTree]
      rw [← PlaneTree2BinaryTree]
      rw [PlaneTree.children]

end

------------------------

-- 6.

section

theorem div_refl {n m : ℕ} (h : n = m) : n ∣ m := by
  rw [h]

theorem div_trans_2 {n m k : ℕ} (a: n ∣ m) (b : m = k) : n ∣ k :=
  dvd_trans a (div_refl b)


theorem task {n : ℕ} : (n + 1) ∣ (2 * n).choose n :=

  have h3 : (1 + n) * (n * 2).choose (1 + n) = n * (n * 2).choose n := by
    sorry

  have h2 : (n * 2).choose (1 + n) - n * ((n * 2).choose n - (n * 2).choose (1 + n)) = 0 := by
    sorry

  have h : (n + 1) * ((2 * n).choose n - (2 * n).choose (n + 1)) = (2 * n).choose n := by
    ring_nf
    rw [add_comm]
    -- have key := add_right_eq_zero
    sorry
    -- rw [add_left_cancel_iff]

  let z := dvd_mul_right (n + 1) ((2 * n).choose n - (2 * n).choose (n + 1))
  div_trans_2 z h

end
