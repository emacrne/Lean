import mathlib

/-- The type of binary trees:
  just a leaf or
  unary node or
  binary node -/
inductive binary_tree : Type
| leaf : binary_tree
| node₁ : binary_tree → binary_tree
| node₂ : binary_tree → binary_tree → binary_tree

/-- The height of a binary tree -/
def binary_tree.height : binary_tree → ℕ
| leaf => 1
| node₁ T => T.height + 1
| node₂ T₁ T₂ => max T₁.height T₂.height + 1

/-- The number of nodes in binary tree -/
def binary_tree.number_of_nodes : binary_tree → ℕ
| leaf => 1
| node₁ T => T.number_of_nodes + 1
| node₂ T₁ T₂ => T₁.number_of_nodes + T₂.number_of_nodes + 1


/-- The type of full binary trees -/
inductive full_binary_tree : Type
| leaf : full_binary_tree
| node : (T₁ T₂ : full_binary_tree) → full_binary_tree

/-- The height of a full binary tree -/
def full_binary_tree.height : full_binary_tree → ℕ
| leaf => 1
| node T₁ T₂ => max T₁.height T₂.height + 1

/-- The number of nodes in full binary tree -/
def full_binary_tree.number_of_nodes : full_binary_tree → ℕ
| leaf => 1
| node T₁ T₂ => T₁.number_of_nodes + T₂.number_of_nodes + 1

def binary_tree_of_full_binary_tree : full_binary_tree → binary_tree
| .leaf => .leaf
| .node T₁ T₂ => .node₂ (binary_tree_of_full_binary_tree T₁) (binary_tree_of_full_binary_tree T₂)


theorem eq_height_binary_tree_of_full_binary_tree :
  (T : full_binary_tree) →
  T.height = (binary_tree_of_full_binary_tree T).height := by
intro T
induction T with
| leaf => rfl
| node T1 T2 HT1 HT2 =>
  simp [full_binary_tree.height, binary_tree.height]
  rw [HT1, HT2]

theorem eq_number_of_nodes_binary_tree_of_full_binary_tree :
  (T : full_binary_tree) →
  T.number_of_nodes = (binary_tree_of_full_binary_tree T).number_of_nodes := by
intro T
induction T with
| leaf => rfl
| node T1 T2 HT1 HT2 =>
  simp [full_binary_tree.number_of_nodes, binary_tree.number_of_nodes]
  rw [HT1, HT2]


/-- Paramaterized inductive types -/
inductive binary_tree_with_nodes : ℕ → Type
| leaf : binary_tree_with_nodes 1
| node₁ : {n : ℕ} → binary_tree_with_nodes n → binary_tree_with_nodes (n + 1)
| node₂ : {m n : ℕ} → binary_tree_with_nodes m → binary_tree_with_nodes n → binary_tree_with_nodes (m + n + 1)

inductive vector (A : Type) : (n : ℕ) → Type
| nil : vector A 0
| cons : (n : ℕ) → vector A n → vector A (n + 1)


def binary_tree_of_binary_tree_with_nodes {n : ℕ} : binary_tree_with_nodes n → binary_tree
| .leaf => .leaf
| .node₁ T => .node₁ (binary_tree_of_binary_tree_with_nodes T)
| .node₂ T₁ T₂ => .node₂ (binary_tree_of_binary_tree_with_nodes T₁) (binary_tree_of_binary_tree_with_nodes T₂)


theorem eq_number_of_nodes_binary_tree_of_binary_tree_with_nodes :
  ∀ (n : ℕ) (T : binary_tree_with_nodes n),
  n = (binary_tree_of_binary_tree_with_nodes T).number_of_nodes := by
intros n T
induction T with
| leaf => rfl
| node₁ T HT =>
  simp [binary_tree.number_of_nodes]
  exact HT
| node₂ T1 T1 HT1 HT2 =>
  simp [binary_tree.number_of_nodes]
  rw [← HT1, ← HT2]
