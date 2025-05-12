import MyProject.CellComplex

open Topology
open BigOperators
namespace Chp5
open CellComplexClass
-- We shall not rule out the possiblity where X is empty, so is skeleton and subcomplex
structure is_disconnection {X: Type*} [TopologicalSpace X] (s: Set X) (x1 : Set X) (x2: Set X) : Prop where
  left_open: IsOpen x1
  right_open: IsOpen x2
  cover: s ⊆ x1 ∪ x2
  left_inter: (s ∩ x1).Nonempty
  right_inter: (s ∩ x2).Nonempty
  disjoint: Disjoint s (x1 ∩ x2)

theorem connected_1_skeleton_of_connected {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] [CW: CWComplexClass X] [PreconnectedSpace X] : IsPreconnected ((Skeleton X 1): Set X) := by
  by_contra! h
  simp [IsPreconnected] at h
  have aux_induction {n: ℕ} {X1 X2: Set X} (h: is_disconnection (Skeleton X n) X1 X2) (hn: 1 < n): ∃ X1': Set X, ∃ X2' : Set X, is_disconnection (Skeleton X (n + 1)) X1' X2' ∧ X1 ⊆ X1' ∧ X2 ⊆ X2':= by
    have aux_inter_only_1 : ∀ e ∈ C.sets, e ⊆ (Skeleton X (n + 1)) → ((closure e ∩ X1).Nonempty ∨ (closure e ∩ X2).Nonempty) ∧ Disjoint (closure e) (X1 ∩ X2) := by
      intro e e_in_sets e_sub_skeleton_np1
      have : C.dim_map ⟨e, e_in_sets⟩ ≤ n ∨ C.dim_map ⟨e, e_in_sets⟩ = n + 1 := by
        have : C.dim_map ⟨e, e_in_sets⟩ ≤ n + 1 := (sub_skeleton_iff ⟨e, e_in_sets⟩).mp e_sub_skeleton_np1
        exact Nat.le_or_eq_of_le_succ this
      match this with
      | Or.inl h_e_dim =>
        have e_sub_Xn: e ⊆ Skeleton X n := by
          rw [sub_skeleton_iff ⟨e, e_in_sets⟩]
          exact h_e_dim
        have ce_sub_Xn: closure e ⊆ Skeleton X n := by
          apply (Skeleton X n).cell_closure_incl e e_in_sets e_sub_Xn
        sorry
      | Or.inr h_e_dim =>
        sorry
    sorry
  sorry

#check IsPreconnected.subset_or_subset
#check IsInducing.isPreconnected_image
theorem aux_sub_one_partition_of_connected {X: Type*} [TopologicalSpace X] {s X1 X2: Set X} (h: is_disconnection s X1 X2) {r: Set X} (hr: r ⊆ s) (h_r_preconnected: IsPreconnected r) : r ⊆ X1 ∨ r ⊆ X2 := by
  let g : s → X := (↑)
  let r' := g ⁻¹' r
  have h_r'_mpr: r = g '' r' := by
    ext x
    simp[g]
    constructor
    case mp=>
      intro hx
      use hr hx, hx
    case mpr =>
      intro hx
      rcases hx with ⟨h1, h2⟩
      exact h2
  have r'_preconnected: IsPreconnected r' := by
    rw [h_r'_mpr] at h_r_preconnected
    have : IsInducing g := by exact Topology.IsInducing.subtypeVal
    rw [IsInducing.isPreconnected_image this] at h_r_preconnected
    exact h_r_preconnected
  let X1' := g ⁻¹' X1
  let X2' := g ⁻¹' X2
  have hX1': X1' = g ⁻¹' (s ∩ X1) := Eq.symm (Subtype.preimage_coe_self_inter s X1)
  have hX2': X2' = g ⁻¹' (s ∩ X2) := Eq.symm (Subtype.preimage_coe_self_inter s X2)
  have X1'_open : IsOpen X1' := subset_open_of_open h.left_open
  have X2'_open : IsOpen X2' := subset_open_of_open h.right_open
  have disjoint_X1'_X2' : Disjoint X1' X2' := by
    rw [hX1', hX2']
    refine Disjoint.preimage g ?_
    rw [Set.disjoint_iff]
    have : s ∩ (X1) ∩ (s ∩ X2) = s ∩ (X1 ∩ X2) := by exact Eq.symm (Set.inter_inter_distrib_left s X1 X2)
    simpa [Set.disjoint_iff, this] using h.disjoint
  have r'_in_X1'_and_X2' : r' ⊆ X1' ∪ X2' := by
    have : X1' ∪ X2' = Set.univ := by
      ext x
      constructor
      case mp => intro hx; trivial
      case mpr =>
        intro hx
        show g x ∈ X1 ∪ X2
        exact h.cover x.2
    rw [this]
    exact fun ⦃a⦄ a ↦ trivial
  have r'_in_X1'_or_r'_in_X2' : r' ⊆ X1' ∨ r' ⊆ X2' := IsPreconnected.subset_or_subset X1'_open X2'_open disjoint_X1'_X2' r'_in_X1'_and_X2' r'_preconnected
  match r'_in_X1'_or_r'_in_X2' with
  | Or.inl hr' =>
    left
    intro x hx
    rw [h_r'_mpr] at hx
    rcases hx with ⟨x', hx', rfl⟩
    exact hr' hx'
  | Or.inr hr' =>
    right
    intro x hx
    rw [h_r'_mpr] at hx
    rcases hx with ⟨x', hx', rfl⟩
    exact hr' hx'
end Chp5

example {X Y: Type*} [TopologicalSpace X] [TopologicalSpace Y] {sx: Set X} (hsx: IsConnected sx) {f: X → Y} (hf: Continuous f) : (IsConnected (f '' sx)) := by
  refine IsConnected.image hsx f ?_
  exact Continuous.continuousOn hf
