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


------------------------------------------------

/- BIG TASKS -/

def listPlaneTreeEquivPlaneTree: List PlaneTree ≃ PlaneTree :=
{
  toFun := PlaneTree.nodes,
  invFun := fun t => match t with
                     | PlaneTree.nodes l => l,
  left_inv := fun _ => rfl,
  right_inv := fun t => match t with
                        | PlaneTree.nodes _ => rfl
}

def PlaneTree.children : PlaneTree -> List PlaneTree
| nodes l => l

def fromChildren : List PlaneTree -> PlaneTree
| l => PlaneTree.nodes l

theorem fromChildren_to_children :
  ∀ (l : List PlaneTree),
  l = (fromChildren l).children:= by
  intro childrenList
  cases childrenList
  . case _ => rfl
  . case cons head tail => rfl

theorem children_fromChildren :
  ∀ (tree : PlaneTree),
  tree = fromChildren (tree.children) := by
  intro tree
  cases tree
  . case nodes children => rfl

------------------------
