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


------------------------
