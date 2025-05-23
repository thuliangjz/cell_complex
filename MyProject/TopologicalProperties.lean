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

theorem aux_is_disconnection_comm_left {X: Type*} [TopologicalSpace X] {s X1 X2 : Set X} : is_disconnection s X1 X2 → is_disconnection s X2 X1 := by
  intro h
  exact {
    left_open := h.right_open
    right_open := h.left_open
    cover := by simpa [Set.union_comm] using h.cover
    left_inter := h.right_inter
    right_inter := h.left_inter
    disjoint := by simpa [Set.inter_comm] using h.disjoint
  }

theorem aux_is_disconnection_comm {X: Type*} [TopologicalSpace X] {s X1 X2 : Set X} : is_disconnection s X1 X2 ↔ is_disconnection s X2 X1 := by
  constructor
  <;> apply aux_is_disconnection_comm_left

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

section topo_prop_helper
variable {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X]
theorem aux_cell_closure_inter_1_partition {n : ℕ} (hn: 1 ≤ n) {X1 X2: Set X} (h: is_disconnection (Skeleton X n) X1 X2) (hX1: X1 ⊆ (Skeleton X n)) (hX2: X2 ⊆ (Skeleton X n)) : ∀ e ∈ C.sets, e ⊆ (Skeleton X (n + 1)) → ((closure e ∩ X1).Nonempty ∨ (closure e ∩ X2).Nonempty) ∧ ¬(((closure e ∩ X1).Nonempty ∧ (closure e ∩ X2).Nonempty)) := by
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
    have ce_pre_connected: IsPreconnected (closure e) := by
      exact IsConnected.isPreconnected (cell_closure_connected e e_in_sets)
    have ce_in_either : closure e ⊆ X1 ∨ closure e ⊆ X2 := by
      apply aux_sub_one_partition_of_connected h ce_sub_Xn ce_pre_connected
    wlog ce_in_X1: closure e ⊆ X1 generalizing X1 X2 h ce_in_either
    case inr =>
      rw [or_comm, @and_comm (closure e ∩ X1).Nonempty (closure e ∩ X2).Nonempty]
      apply this (aux_is_disconnection_comm_left h) hX2 hX1 (ce_in_either.symm) (ce_in_either.resolve_left ce_in_X1)
    have h1: (closure e ∩ X1).Nonempty := by
      rcases C.nonempty e e_in_sets with ⟨x₀, hx₀⟩
      use x₀
      exact ⟨subset_closure hx₀, ce_in_X1 (subset_closure hx₀)⟩
    have h2: ¬(closure e ∩ X2).Nonempty := by
      by_contra! h0
      rcases h0 with ⟨x₀, hx₀⟩
      have : x₀ ∈ X1 ∩ X2 := ⟨ce_in_X1 hx₀.1 , hx₀.2⟩
      apply Set.disjoint_iff.mp h.disjoint ⟨ce_sub_Xn hx₀.1, this⟩
    rw [not_and_or]
    exact ⟨Or.inl h1, Or.inr h2⟩
  | Or.inr h_e_dim =>
    let boundary := Set.range (cb_boundary_map (C.characteristic_map ⟨e, e_in_sets⟩))
    have boundary_connected : IsConnected boundary := by
      simp [boundary, boundary_map_range]
      apply IsConnected.image
      case H =>
        apply cb_boundary_connected
        rw [h_e_dim]
        linarith
      case hf =>
        apply Continuous.continuousOn
        exact characteristic_map_continuous ⟨e, e_in_sets⟩
    have boundary_sub_Xn : boundary ⊆ Skeleton X n := by
      trans ⋃ p:C.sets, ⋃ _:(C.dim_map p < C.dim_map ⟨e, e_in_sets⟩), p.val
      apply C.characteristic_map_boundary
      have : ∀ p : C.sets, C.dim_map p < C.dim_map ⟨e, e_in_sets⟩ → p.val ⊆ Skeleton X n := by
        intro p hp
        rw [h_e_dim] at hp
        rw [sub_skeleton_iff]
        exact Nat.le_of_lt_succ hp
      simpa using this
    have boundary_in_either : boundary ⊆ X1 ∨ boundary ⊆ X2 := by
      apply aux_sub_one_partition_of_connected h boundary_sub_Xn boundary_connected.isPreconnected
    wlog boundary_in_X1 : boundary ⊆ X1 generalizing X1 X2
    case inr =>
      rw [or_comm, @and_comm (closure e ∩ X1).Nonempty (closure e ∩ X2).Nonempty]
      apply this (aux_is_disconnection_comm_left h) hX2 hX1 (boundary_in_either.symm) (boundary_in_either.resolve_left boundary_in_X1)
    have boundary_sub_ce : boundary ⊆ closure e := by
      rw [←C.characteristic_map_range ⟨e, e_in_sets⟩]
      simp [boundary, boundary_map_range]
    have boundary_nonempty : boundary.Nonempty := by
      exact IsConnected.nonempty boundary_connected
    have h1: (closure e ∩ X1).Nonempty := by
      rcases boundary_nonempty with ⟨x₀, hx₀⟩
      use x₀
      exact ⟨boundary_sub_ce hx₀, boundary_in_X1 hx₀⟩
    have h2: ¬(closure e ∩ X2).Nonempty := by
      have ce_decomp: closure e = e ∪ boundary := by
        show closure e  = ((⟨e, e_in_sets⟩: C.sets):Set X) ∪ boundary
        rw [←C.characteristic_map_inner_range ⟨e, e_in_sets⟩, ←characteristic_map_range ⟨e, e_in_sets⟩, Set.union_comm]
        apply cb_map_range_decomposition
      have e_inter_empty: e ∩ X2 = ∅ := by
        match (Skeleton X n).cell_incl_or_disjoint e e_in_sets with
        | Or.inl h_e_in_Xn =>
          by_contra
          have : C.dim_map ⟨e, e_in_sets⟩ ≤ n := by
            rw [←sub_skeleton_iff ⟨e, e_in_sets⟩]
            simpa using h_e_in_Xn
          linarith
        | Or.inr h_e_not_in_Xn =>
          rw [Set.disjoint_iff] at h_e_not_in_Xn
          have : e ∩ X2 ⊆ e ∩ (Skeleton X n) := by
            intro x hx
            exact ⟨hx.1, hX2 hx.2⟩
          exact Set.subset_empty_iff.mp fun ⦃a⦄ a_1 ↦ h_e_not_in_Xn (this a_1)
      have boundary_inter_empty: boundary ∩ X2 = ∅ := by
        have h0: boundary ∩ X2 ⊆ X1 ∩ X2 := Set.inter_subset_inter boundary_in_X1 fun ⦃a⦄ a ↦ a
        have h1: X1 ∩ X2 = ∅ := by
          have : X1 ∩ X2 = ((Skeleton X n):Set X) ∩ (X1 ∩ X2) := by
            have : X1 ∩ X2 ⊆ (Skeleton X n) := by
              intro x hx
              exact hX1 hx.1
            exact Eq.symm (Set.inter_eq_self_of_subset_right this)
          rw [this]
          simpa [Set.disjoint_iff_inter_eq_empty] using h.disjoint
        exact Set.subset_eq_empty h0 h1
      by_contra!
      rcases this with ⟨x, hx⟩
      rw [ce_decomp, Set.inter_comm, Set.inter_union_distrib_left] at hx
      rw [Set.inter_comm, e_inter_empty, Set.inter_comm, boundary_inter_empty] at hx
      simp at hx
    rw [not_and_or]
    exact ⟨Or.inl h1, Or.inr h2⟩
end topo_prop_helper

theorem connected_1_skeleton_of_connected {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] [CW: CWComplexClass X] [PreconnectedSpace X] : IsPreconnected ((Skeleton X 1): Set X) := by
  by_contra! hc
  simp [IsPreconnected] at hc
  have aux_induction {n: ℕ} {X1 X2: Set X} (h: is_disconnection (Skeleton X n) X1 X2) (hX1: X1 ⊆ (Skeleton X n)) (hX2: X2 ⊆ (Skeleton X n)) (hn: 1 ≤ n): ∃ X1': Set X, ∃ X2' : Set X, is_disconnection (Skeleton X (n + 1)) X1' X2' ∧ X1 ⊆ X1' ∧ X2 ⊆ X2' ∧ X1' ⊆ (Skeleton X (n + 1)) ∧ X2' ⊆ (Skeleton X (n + 1)):= by
    have aux_inter_only_1 : ∀ e ∈ C.sets, e ⊆ (Skeleton X (n + 1)) → ((closure e ∩ X1).Nonempty ∨ (closure e ∩ X2).Nonempty) ∧ ¬(((closure e ∩ X1).Nonempty ∧ (closure e ∩ X2).Nonempty)) := by
      apply aux_cell_closure_inter_1_partition hn h hX1 hX2
    set X1' : Set X := ⋃ e:C.sets, ⋃ _: e.1 ⊆ (Skeleton X (n + 1)) ∧ (closure e.1 ∩ X1).Nonempty, e.1 with X1'_def
    set X2' : Set X := ⋃ e:C.sets, ⋃ _: e.1 ⊆ (Skeleton X (n + 1)) ∧ (closure e.1 ∩ X2).Nonempty, e.1 with X2'_def
    use X1', X2'
    have X1'X2'_sub_Xnp1 : X1' ⊆ Skeleton X (n + 1) ∧ X2' ⊆ Skeleton X (n + 1):= by
      constructor
      repeat
      intro x hx
      simp [X1'_def, X2'_def] at hx
      rcases hx with ⟨e, he⟩
      exact he.1.1 he.2.2
    have aux_Xi_sub_Xi': ∀ Xi: (Set X), Xi ⊆ (Skeleton X n) → Xi ⊆ ⋃ e:C.sets, ⋃ (_ : e.1 ⊆ ↑(Skeleton X (n + 1)) ∧ (closure e.1 ∩ Xi).Nonempty), e.1 := by
      intro Xi hXi
      intro x hx
      simp
      rcases mem_sub_complex_iff.mp (hXi hx) with ⟨e, e_in_sets, ⟨x_in_e, e_sub_Xn⟩⟩
      have e_sub_Xnp1 : e ⊆ Skeleton X (n + 1) := by
        rw [sub_skeleton_iff ⟨e, e_in_sets⟩]
        rw [sub_skeleton_iff ⟨e, e_in_sets⟩] at e_sub_Xn
        linarith
      have ce_inter_X1_nonempty : (closure e ∩ Xi).Nonempty := by
        use x
        exact ⟨subset_closure x_in_e, hx⟩
      use e
    have X1_sub_X1' : X1 ⊆ X1' := by apply aux_Xi_sub_Xi' _ hX1
    have X2_sub_X2' : X2 ⊆ X2' := by apply aux_Xi_sub_Xi' _ hX2
    have X1'X2'_eq_Xnp1 : X1' ∪ X2' = Skeleton X (n + 1) := by
      ext x
      constructor
      case h.mp =>
        intro hx
        rcases hx with x_in_X1' | x_in_X2'
        . exact X1'X2'_sub_Xnp1.1 x_in_X1'
        exact X1'X2'_sub_Xnp1.2 x_in_X2'
      case h.mpr =>
        intro hx
        rcases mem_sub_complex_iff.mp hx with ⟨e, e_in_sets, x_in_e, e_sub_Xnp1⟩
        match (aux_inter_only_1 e e_in_sets e_sub_Xnp1).1 with
        | Or.inl h_ce_X1 => left; simp [X1'_def]; use e
        | Or.inr h_ce_X2 => right; simp [X2'_def]; use e
    have X1'X2'_disjoint: X1' ∩ X2' = ∅ := by
      by_contra! h'
      rcases h' with ⟨x, x_in_X1', x_in_X2'⟩
      simp [X1'_def] at x_in_X1'
      rcases x_in_X1' with ⟨e1, ⟨he1_sub_Xnp1, ce1_inter_X1⟩, e1_in_sets, x_in_e1⟩
      simp [X2'_def] at x_in_X2'
      rcases x_in_X2' with ⟨e2, ⟨he2_sub_Xnp1, ce2_inter_X2⟩, e2_in_sets, x_in_e2⟩
      have e1_eq_e2 : e1 = e2 := by apply same_cell_of_mem e1_in_sets e2_in_sets x_in_e1 x_in_e2
      rw [←e1_eq_e2] at ce2_inter_X2
      exact (aux_inter_only_1 e1 e1_in_sets he1_sub_Xnp1).2 ⟨ce1_inter_X1, ce2_inter_X2⟩
    sorry
  sorry

end Chp5
example {X: Type*} {s1 s2 s3: Set x} : (s1 ∪ s2) ∩ s3 = (s1 ∩ s3) ∪ (s2 ∩ s3) := by exact Set.union_inter_distrib_right s1 s2 s3
example {X Y: Type*} [TopologicalSpace X] [TopologicalSpace Y] {sx: Set X} (hsx: IsConnected sx) {f: X → Y} (hf: Continuous f) : (IsConnected (f '' sx)) := by
  refine IsConnected.image hsx f ?_
  exact Continuous.continuousOn hf
