import MyProject.CellComplex
open Topology
open BigOperators
namespace Chp5
open CellComplexClass
-- We shall not rule out the possiblity where X is empty, so is skeleton and subcomplex
structure is_disconnection {X: Type*} [TopologicalSpace X] (s: Set X) (x1 : Set X) (x2: Set X) : Prop where
  left_open: IsOpen (((↑): s → X) ⁻¹' x1)
  right_open: IsOpen (((↑): s → X) ⁻¹' x2)
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
  have X1'_open : IsOpen X1' := h.left_open
  have X2'_open : IsOpen X2' := h.right_open
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

-- bassically follow the method of previous theorem
theorem aux_cell_frontier_sub_left_partition {n : ℕ} (hn: 1 ≤ n) {X1 X2: Set X} (h: is_disconnection (Skeleton X n) X1 X2) (hX1: X1 ⊆ Skeleton X n) : ∀ e ∈ C.sets, e ⊆ (Skeleton X (n + 1)) → (closure e ∩ X1).Nonempty → (closure e \ e) ⊆ X1 := by
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
    intro hce_inter_X1_nonempty
    match ce_in_either with
    | Or.inl ce_in_X1 =>
      trans closure e
      exact diff_subset_closure_iff.mpr fun ⦃a⦄ a ↦ a
      exact ce_in_X1
    | Or.inr ce_in_X2 =>
      apply False.elim
      rcases hce_inter_X1_nonempty with ⟨x, hx⟩
      have hx_in_X1X2: x ∈ X1 ∩ X2 := ⟨hx.2, ce_in_X2 hx.1⟩
      have hx_in_Xn: x ∈ (Skeleton X n) := hX1 hx.2
      apply Set.disjoint_iff.mp h.disjoint ⟨hx_in_Xn, hx_in_X1X2⟩
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
    have boundary_sub_ce : boundary ⊆ closure e := by
      rw [←C.characteristic_map_range ⟨e, e_in_sets⟩]
      simp [boundary, boundary_map_range]
    have boundary_nonempty : boundary.Nonempty := by
      exact IsConnected.nonempty boundary_connected
    have ce_decomp: closure e = e ∪ boundary := by
      show closure e  = ((⟨e, e_in_sets⟩: C.sets):Set X) ∪ boundary
      rw [←C.characteristic_map_inner_range ⟨e, e_in_sets⟩, ←characteristic_map_range ⟨e, e_in_sets⟩, Set.union_comm]
      apply cb_map_range_decomposition
    have e_inter_Xn_empty : e ∩ (Skeleton X n) = ∅ := by
      show e ∩ (⋃s: C.sets, ⋃ _:(C.dim_map s ≤ n), s.val) = ∅
      rw [Set.inter_iUnion₂]
      simp
      show ∀ (i : Set X) (i_1 : i ∈ sets), dim_map ⟨i, i_1⟩ ≤ n → e ∩ i = ∅ -- we keep this show here to make simp's goal explicit
      intro s s_in_sets s_dim_less_n
      rw [←Set.disjoint_iff_inter_eq_empty]
      apply C.disjoint e_in_sets s_in_sets
      contrapose! s_dim_less_n
      have : C.dim_map ⟨s, s_in_sets⟩ = C.dim_map ⟨e, e_in_sets⟩ := by
        congr!
        exact s_dim_less_n.symm
      rw [this]
      linarith
    have e_inter_boundary_empty: e ∩ boundary = ∅ := by
      have : e ∩ boundary ⊆ e ∩ (Skeleton X n) := Set.inter_subset_inter (fun ⦃a⦄ a ↦ a) boundary_sub_Xn
      rw [e_inter_Xn_empty] at this
      exact Set.subset_eq_empty this rfl
    have ce_sub_e_eq_boundary: closure e \ e = boundary := by
      rw [ce_decomp]
      apply Set.union_diff_cancel_left
      exact Set.subset_empty_iff.mpr e_inter_boundary_empty
    have X1X2_disjoint : X1 ∩ X2 = ∅ := by
      have : X1 ∩ X2 = ((Skeleton X n): Set X) ∩ (X1 ∩ X2) := by
        apply Set.right_eq_inter.mpr
        intro x hx
        exact hX1 hx.1
      rw [this, ←Set.disjoint_iff_inter_eq_empty]
      exact h.disjoint
    intro h_ce_inter_X1
    rw [ce_sub_e_eq_boundary]
    match boundary_in_either with
    | Or.inl bX1 => exact bX1
    | Or.inr bX2 =>
      rcases h_ce_inter_X1 with ⟨x, hx⟩
      have : x ∈ boundary ∩ X1 := by
        rw [ce_decomp] at hx
        have : X1 ∩ e = ∅ := by
          rw [Set.inter_comm]
          have : e ∩ X1 ⊆ e ∩ (Skeleton X n) := Set.inter_subset_inter (fun ⦃a⦄ a ↦ a) hX1
          exact Set.subset_eq_empty this e_inter_Xn_empty
        rw [Set.inter_comm, Set.inter_union_distrib_left, this, Set.empty_union, Set.inter_comm] at hx
        exact hx
      have : x ∈ X1 ∩ X2 := ⟨this.2, bX2 this.1⟩
      rw [X1X2_disjoint] at this
      apply False.elim
      exact this
end topo_prop_helper

theorem connected_1_skeleton_of_connected {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] [CW: CWComplexClass X] [PreconnectedSpace X] : IsPreconnected ((Skeleton X 1): Set X) := by
  by_contra! hc
  simp [IsPreconnected] at hc
  have aux_induction {n: ℕ} {X1 X2: Set X} (h: is_disconnection (Skeleton X n) X1 X2) (hX1: X1 ⊆ (Skeleton X n)) (hX2: X2 ⊆ (Skeleton X n)) (hn: 1 ≤ n): ∃ X1': Set X, ∃ X2' : Set X, is_disconnection (Skeleton X (n + 1)) X1' X2' ∧ X1 ⊆ X1' ∧ X2 ⊆ X2' ∧ X1' ⊆ (Skeleton X (n + 1)) ∧ X2' ⊆ (Skeleton X (n + 1)):= by
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
    have aux_inter_only_1 : ∀ e ∈ C.sets, e ⊆ (Skeleton X (n + 1)) → ((closure e ∩ X1).Nonempty ∨ (closure e ∩ X2).Nonempty) ∧ ¬(((closure e ∩ X1).Nonempty ∧ (closure e ∩ X2).Nonempty)) := by
      apply aux_cell_closure_inter_1_partition hn h hX1 hX2
    have X1X2_sub_corresponding : X1 ⊆ X1' ∧ X2 ⊆ X2' := by
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
      constructor
      . apply aux_Xi_sub_Xi' _ hX1
      apply aux_Xi_sub_Xi' _ hX2
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
    have X1'X2'_disjoint_Xnp1 : Disjoint ((Skeleton X (n + 1)): Set X) (X1' ∩ X2') := by
      rw [Set.disjoint_iff_inter_eq_empty, X1'X2'_disjoint]
      apply Set.inter_empty
    have aux_sub_only_1 : ∀ e ∈ C.sets, e ⊆ (Skeleton X (n + 1)) → (closure e) ⊆ X1' ∨ (closure e) ⊆ X2' := by
      intro e e_in_sets e_sub_Xnp1
      have ce_sub_Xnp1 : closure e ⊆ (Skeleton X (n + 1)) := by
        have : IsClosed ((Skeleton X (n + 1)) : Set X) := by apply sub_cw_cell_complex_closed
        rw [IsClosed.closure_subset_iff this]
        exact e_sub_Xnp1
      match (aux_inter_only_1 e e_in_sets e_sub_Xnp1).1 with
      | Or.inl he =>
        left
        have e_in_X1' : e ⊆ X1' := by
          intro x hx
          simp [X1'_def]
          use e
        have be_in_X1' : (closure e \ e) ⊆ X1' := by
          trans X1
          apply aux_cell_frontier_sub_left_partition hn h hX1 e e_in_sets e_sub_Xnp1 he
          exact X1X2_sub_corresponding.1
        rw [←(Set.union_diff_cancel' (fun ⦃a⦄ a ↦ a) subset_closure)]
        exact Set.union_subset e_in_X1' be_in_X1'
      | Or.inr he =>
        right
        have e_in_X2' : e ⊆ X2' := by
          intro x hx
          simp [X2'_def]
          use e
        have be_in_X2' : (closure e \ e) ⊆ X2' := by
          trans X2
          apply aux_cell_frontier_sub_left_partition hn (aux_is_disconnection_comm_left h) hX2 e e_in_sets e_sub_Xnp1 he
          exact X1X2_sub_corresponding.2
        rw [←(Set.union_diff_cancel' (fun ⦃a⦄ a ↦ a) subset_closure)]
        exact Set.union_subset e_in_X2' be_in_X2'
    let g : Skeleton X (n + 1) → X := (↑)
    have X1'X2'_open_in_Xnp1: IsOpen (g ⁻¹' X1') ∧ IsOpen (g ⁻¹' X2') := by
      have X1'_closed_in_Xnp1 : IsClosed (g ⁻¹' X1') := by
        have sub_X1'_or_disjoint: ∀ e ∈ C.sets, e ⊆ (Skeleton X (n + 1)) → ((closure e) ∩ X1' = closure e) ∨ ((closure e) ∩ X1' = ∅) := by
          intro e e_in_sets e_sub_Xnp1
          match aux_sub_only_1 e e_in_sets e_sub_Xnp1 with
          | Or.inl he =>
            left
            rw [Set.inter_eq_left]
            exact he
          | Or.inr he =>
            right
            have :closure e ∩ X1' ⊆ X2' ∩ X1' := Set.inter_subset_inter he fun ⦃a⦄ a ↦ a
            rw [Set.inter_comm X2', X1'X2'_disjoint] at this
            exact Set.subset_eq_empty this rfl
        let Y1 := g ⁻¹' X1'
        show IsClosed Y1
        -- note that we implicitly use the fact that Skeleton X (n + 1) is also a CW complex
        apply closed_crit_of_coeherent CWComplexClass.coeherent
        rintro _ ⟨e, e_in_Xnp1_sets, rfl⟩
        let φ : closure e → (Skeleton X (n + 1)) := (↑)
        show IsClosed (φ ⁻¹' Y1)
        let e₀ := g '' e
        have e₀_in_sets : e₀ ∈ C.sets := e_in_Xnp1_sets
        have e₀_sub_Xnp1 : e₀ ⊆ (Skeleton X (n + 1)) := by
          rintro x ⟨y, hy, rfl⟩
          exact Subtype.coe_prop y
        have ce₀_eq_ce_img : closure e₀ = g '' (closure e) := by
          apply IsClosedMap.closure_image_eq_of_continuous
          case f_closed =>
            apply IsClosed.isClosedMap_subtype_val
            apply sub_cw_cell_complex_closed
          case f_cont =>
            exact continuous_subtype_val
        have gφ_range : Set.range (g ∘ φ) = closure e₀ := by
          rw [ce₀_eq_ce_img, Set.range_comp]
          congr!
          exact Subtype.range_coe
        have : φ ⁻¹' Y1 = (g ∘ φ) ⁻¹' X1' := by ext x;exact Set.mem_preimage
        rw [this, ←Set.preimage_inter_range, gφ_range, Set.inter_comm]
        match sub_X1'_or_disjoint e₀ e₀_in_sets e₀_sub_Xnp1 with
        | Or.inl he₀ =>
          rw [he₀, ←gφ_range, Set.preimage_range]
          exact isClosed_univ
        | Or.inr he₀ =>
          rw [he₀]
          exact isClosed_empty
      have X2'_closed_in_Xnp1 : IsClosed (g ⁻¹' X2') := by
        have sub_X2'_or_disjoint: ∀ e ∈ C.sets, e ⊆ (Skeleton X (n + 1)) → ((closure e) ∩ X2' = closure e) ∨ ((closure e) ∩ X2' = ∅) := by
          intro e e_in_sets e_sub_Xnp1
          match aux_sub_only_1 e e_in_sets e_sub_Xnp1 with
          | Or.inr he =>
            left
            rw [Set.inter_eq_left]
            exact he
          | Or.inl he =>
            right
            have :closure e ∩ X2' ⊆ X2' ∩ X1' := by
              rw [Set.inter_comm]
              exact Set.inter_subset_inter (fun ⦃a⦄ a ↦ a) he
            rw [Set.inter_comm X2', X1'X2'_disjoint] at this
            exact Set.subset_eq_empty this rfl
        let Y2 := g ⁻¹' X2'
        show IsClosed Y2
        apply closed_crit_of_coeherent CWComplexClass.coeherent
        rintro _ ⟨e, e_in_Xnp1_sets, rfl⟩
        let φ : closure e → (Skeleton X (n + 1)) := (↑)
        show IsClosed (φ ⁻¹' Y2)
        let e₀ := g '' e
        let e₀ := g '' e
        have e₀_in_sets : e₀ ∈ C.sets := e_in_Xnp1_sets
        have e₀_sub_Xnp1 : e₀ ⊆ (Skeleton X (n + 1)) := by
          rintro x ⟨y, hy, rfl⟩
          exact Subtype.coe_prop y
        have ce₀_eq_ce_img : closure e₀ = g '' (closure e) := by
          apply IsClosedMap.closure_image_eq_of_continuous
          case f_closed =>
            apply IsClosed.isClosedMap_subtype_val
            apply sub_cw_cell_complex_closed
          case f_cont =>
            exact continuous_subtype_val
        have gφ_range : Set.range (g ∘ φ) = closure e₀ := by
          rw [ce₀_eq_ce_img, Set.range_comp]
          congr!
          exact Subtype.range_coe
        have : φ ⁻¹' Y2 = (g ∘ φ) ⁻¹' X2' := by ext x;exact Set.mem_preimage
        rw [this, ←Set.preimage_inter_range, gφ_range, Set.inter_comm]
        match sub_X2'_or_disjoint e₀ e₀_in_sets e₀_sub_Xnp1 with
        | Or.inl he₀ =>
          rw [he₀, ←gφ_range, Set.preimage_range]
          exact isClosed_univ
        | Or.inr he₀ =>
          rw [he₀]
          exact isClosed_empty
      have g_inv_X1'X2'_rel_compl : g ⁻¹' X1' = (g ⁻¹' X2')ᶜ ∧ g ⁻¹' X2' = (g ⁻¹' X1')ᶜ  := by
        have sub_X1'X2'_eq_Xnp1: (g ⁻¹' X1') ∪ (g ⁻¹' X2') = Set.univ := by
          rw [←Set.preimage_union, X1'X2'_eq_Xnp1, ←Set.preimage_range g]
          congr!
          exact Eq.symm Subtype.range_coe
        have sub_X1'X2'_disjoint: (g ⁻¹' X1') ∩ (g ⁻¹' X2') = ∅ := by
          rw  [←Set.preimage_inter, X1'X2'_disjoint]
          rfl
        have : g ⁻¹' X1' = (g ⁻¹' X2')ᶜ := by
          refine Eq.symm (compl_unique ?disj ?union)
          case disj =>
            show (g ⁻¹' X2') ∩ (g ⁻¹' X1') = ∅
            rw [Set.inter_comm]
            exact sub_X1'X2'_disjoint
          case union =>
            show (g ⁻¹' X2') ∪ (g ⁻¹' X1') = Set.univ
            rw [Set.union_comm]
            exact sub_X1'X2'_eq_Xnp1
        constructor
        . exact this
        rw [eq_compl_comm]
        exact this
      have X1'_open_in_Xnp1 : IsOpen (g ⁻¹' X1') := by
        rw [g_inv_X1'X2'_rel_compl.1]
        exact IsClosed.isOpen_compl
      have X2'_open_in_Xnp1 : IsOpen (g ⁻¹' X2') := by
        rw [g_inv_X1'X2'_rel_compl.2]
        exact IsClosed.isOpen_compl
      exact ⟨X1'_open_in_Xnp1, X2'_open_in_Xnp1⟩
    constructor
    . exact {
        left_open := X1'X2'_open_in_Xnp1.1
        right_open := X1'X2'_open_in_Xnp1.2
        cover := by rw [X1'X2'_eq_Xnp1]
        left_inter := sorry
        right_inter := sorry
        disjoint := X1'X2'_disjoint_Xnp1
      }
    tauto
  sorry

end Chp5

section
variable {X Y: Type*} [TopologicalSpace X] [TopologicalSpace Y]
example {f: X → Y} (hf: IsClosedMap f) (fc: Continuous f) {s: Set X} : f '' (closure s) = closure (f '' s) := by exact Eq.symm (IsClosedMap.closure_image_eq_of_continuous hf fc s)
example {s : Set X} (hs: IsClosed s) : let g : s → X := (↑); IsClosedMap g := by
  exact IsClosed.isClosedMap_subtype_val hs
example {f: X → Y} (t: Set Y) : f ⁻¹' t = f ⁻¹' (t ∩ Set.range f) := by
  exact Eq.symm Set.preimage_inter_range
example {f: X → Y} : f ⁻¹' (Set.range f) = Set.univ := by
  exact Set.preimage_range f
example {s1 s2 : Set X} (h0: s1 ⊆ s2) (h1: IsClosed s2) : closure s1 ⊆ s2 := by
  exact (IsClosed.closure_subset_iff h1).mpr h0
example {s1 s2 s3: Set X} (h0: s1 = s2 ∪ s3) (h1: s2 ∩ s3 = ∅) : s1 \ s2 = s3 := by
  rw [h0]
  apply Set.union_diff_cancel_left ?_
  exact Set.subset_empty_iff.mpr h1
example {s: Set X} : closure s = s ∪ (closure s \ s) := by
  exact Eq.symm (Set.union_diff_cancel' (fun ⦃a⦄ a ↦ a) subset_closure)
example {f: X → Y}: f ⁻¹' ∅ = ∅ := by exact rfl
example {s1 s2: Set X} (h: s1 ∩ s2 = ∅) (h': s1 ∪ s2 = Set.univ) : s1 = s2ᶜ ↔ s2 = s1ᶜ := by
  exact eq_compl_comm
example {s1 s2 s3: Set X} : s1 ∩ s2 ∩ s3 = (s1 ∩ s3) ∩ s2 := Set.inter_right_comm s1 s2 s3

end
