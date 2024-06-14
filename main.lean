import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorization.Basic

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
  tauto
  split
  case node type T =>
    rw[← T, ← H₂]

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
      rw [← PlaneTree2BinaryTree, PlaneTree.children]

end

------------------------

-- 6.

section


theorem div_refl {n m : ℕ} (h : n = m) : n ∣ m := by
  rw [h]


theorem div_trans_2 {n m k : ℕ} (a: n ∣ m) (b : m = k) : n ∣ k :=
  dvd_trans a (div_refl b)


theorem cancel_left_div {b c : ℕ} (a : ℕ) (p : a ≠ 0) (h : a * b ∣ a * c) : b ∣ c :=
  /-
  exists_eq_mul_right_of_dvd h
  rw -- pokrajšaj a-je, uporabi p
  Dvd.intro 
  -/
  sorry


theorem rewrite_desc_fact (n : ℕ) : (2 * n).descFactorial n = (Nat.factorial n) * ((2 * n).choose n) := 
    descFactorial_eq_factorial_mul_choose (2 * n) n


theorem div_from_primes (n m : ℕ) (h1 : n ≠ 0) (h2 : m ≠ 0) (h : ∀ p : ℕ, p.Prime -> (n.factorization p <= m.factorization p)) : n ∣ m :=
  Iff.mp (factorization_prime_le_iff_dvd h1 h2) h


open Nat


def k (p : ℕ) (n' : ℕ) := n'.factorization p
def c (p : ℕ) (n : ℕ) (n' : ℕ) := n - n % (p ^ (k p n'))
def f (p : ℕ) (n : ℕ) (n' : ℕ) := n' + (c p n n') * p ^ (k p n')


theorem main_part (p : ℕ) (n : ℕ) : ((n !).factorization p <= ((2 * n).descFactorial (n - 1)).factorization p) :=
  -- funkcija f slika faktorje iz n! v faktorje 2n * (2n - 1) * ... * (n + 2), tako da slika v tiste faktorje, ki imajo enako faktorjev p (enako valuacijo p)
  -- če faktor ni deljiv s p, ga spustimo
  -- funkcija je injektivna za vse p, torej n! deli 2n * (2n - 1) * ... * (n + 2)

  have h1 : ∀ m : ℕ, m.factorization p = (f p n m).factorization p := 
    -- slika f ima isto valuacijo kot slikan element
    sorry
  have h2 : ∀ m : ℕ, (2 <= m) -> (m <= n) -> (k m > 0) -> ((n + 2 <= f p n m) ∧ (f p n m <= 2 * n)) :=
    -- f slika iz [2, n] v [n + 2, 2n]
    sorry
  --have f injective on [2, n] :=
  --  sorry
  sorry
  
theorem aux (n : ℕ) : (∀ p : ℕ, p.Prime -> (n !).factorization p <= ((2 * n).descFactorial (n - 1)).factorization p) := by
  --(∀ p : ℕ, p.Prime -> main_part p n)

  --intro p
  -- p.Prime
  --exact main_part p n
  sorry


theorem modus_tollens (hpq : p → q) (hnq : ¬q) : ¬p :=
  fun hp : p =>
  show False from hnq (hpq hp)


theorem simplify_ineq (n : ℕ) : ¬(2 * n < n - 1) :=
  fun hp : (2 * n < n - 1) =>
  show False from by
    sorry


theorem combine_everything (n : ℕ) : ((n !) ∣ (2 * n).descFactorial (n - 1)) :=
  div_from_primes (n !) ((2 * n).descFactorial (n - 1)) (factorial_ne_zero n) (modus_tollens (Iff.mp descFactorial_eq_zero_iff_lt) (simplify_ineq n)) (aux n)


theorem change_order {a b c : ℕ} (h : a = b * c) : c * b = a := by 
  rw [← mul_comm]
  apply Eq.symm
  rw [h]


theorem simplify_desc_fact {n : ℕ} (h : (2 * n).descFactorial (n - 1 + 1) = (2 * n - (n - 1)) * (2 * n).descFactorial (n - 1)) : (2 * n).descFactorial n = (n + 1) * (2 * n).descFactorial (n - 1) :=
  sorry


theorem task {n : ℕ} : (n + 1) ∣ (2 * n).choose n :=

  have h1 : (n !) * (n + 1) ∣ (2 * n).descFactorial n :=
    div_trans_2 (mul_dvd_mul_right (combine_everything n) (n + 1)) (change_order (
      simplify_desc_fact ((2 * n).descFactorial_succ (n - 1))
    ))
  have h2 : (2 * n).descFactorial n = (Nat.factorial n) * (2 * n).choose n :=
    rewrite_desc_fact n

  cancel_left_div (Nat.factorial n) (factorial_ne_zero n) (div_trans_2 h1 h2)

end
