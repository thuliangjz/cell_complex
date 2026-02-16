import STCC.TopologicalProperties
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.PartitionOfUnity
namespace Chp5

section helper
universe u
lemma paracompact_of_exist_partition_of_unity {X: Type u} [TopologicalSpace X] (hX: ∀ (α: Type u) (s: α → Set X), (∀ a, IsOpen (s a)) → (⋃ a, s a = Set.univ) → ∃ p:(PartitionOfUnity α X), p.IsSubordinate s): ParacompactSpace X := by
  constructor
  intro α s hs_open hs_cover
  obtain ⟨p, hp⟩ := hX α s hs_open hs_cover
  refine ⟨α, fun a => Function.support (p a), ?openness, ?covering, ?locally_finite, ?refinement⟩
  case openness =>
    intro b
    exact isOpen_ne.preimage (map_continuous (p b))
  case covering =>
    rw [Set.iUnion_eq_univ_iff]
    intro x
    obtain ⟨a, ha⟩ := p.exists_pos (Set.mem_univ x)
    exact ⟨a, ne_of_gt ha⟩
  case locally_finite =>
    exact p.locallyFinite
  case refinement =>
    intro b
    exact ⟨b, subset_closure.trans (hp b)⟩
end helper
section
variable {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] [CW: CWComplexClass X]
open CellComplexClass
open Classical

structure CompatibleSkeletonPOU (α : Type*) (s : α → Set X) (n : ℕ) where
  toFun : α → C(Skeleton X n, ℝ)
  nonneg : ∀ a (x : Skeleton X n), 0 ≤ toFun a x
  sum_eq_one : ∀ x : Skeleton X n, ∑ᶠ a, toFun a x = 1
  locallyFinite : LocallyFinite (fun a => Function.support (toFun a))
  subordinate : ∀ a, tsupport (toFun a) ⊆ (Subtype.val ⁻¹' (s a))

noncomputable def skeleton_pou_zero
    (s : α → Set X) (_hs_open : ∀ a, IsOpen (s a)) (hs_cover : ⋃ a, s a = Set.univ) :
    CompatibleSkeletonPOU α s 0 := by
  haveI : DiscreteTopology (Skeleton X 0) := skeleton0_discrete
  -- For each point in the 0-skeleton, choose a covering index
  have h_mem : ∀ x : Skeleton X 0, ∃ a : α, (x : X) ∈ s a := by
    intro x
    have : (x : X) ∈ ⋃ a, s a := hs_cover ▸ Set.mem_univ _
    exact Set.mem_iUnion.mp this
  let idx : Skeleton X 0 → α := fun x => (h_mem x).choose
  have h_idx : ∀ x, (x : X) ∈ s (idx x) := fun x => (h_mem x).choose_spec
  refine ⟨fun a => ⟨fun x => if idx x = a then 1 else 0, continuous_of_discreteTopology⟩,
    ?_, ?_, ?_, ?_⟩
  · -- nonneg
    intro a x
    simp only [ContinuousMap.coe_mk]
    split_ifs <;> norm_num
  · -- sum_eq_one
    intro x
    simp only [ContinuousMap.coe_mk]
    convert finsum_eq_single _ (idx x) (fun b hb => ?_) using 1
    · simp
    · simp [Ne.symm hb]
  · -- locallyFinite
    intro x
    refine ⟨{x}, (isOpen_discrete _).mem_nhds rfl, ?_⟩
    apply Set.Finite.subset (Set.finite_singleton (idx x))
    intro a ha
    simp only [Set.mem_singleton_iff]
    obtain ⟨y, hy_supp, hy_mem⟩ := ha
    rw [Set.mem_singleton_iff] at hy_mem
    subst hy_mem
    rw [Function.mem_support] at hy_supp
    simp only [ContinuousMap.coe_mk] at hy_supp
    by_contra h
    exact hy_supp (if_neg (Ne.symm h))
  · -- subordinate
    intro a
    apply subset_trans (closure_minimal (fun x hx => ?_) (isClosed_discrete _))
      (le_refl _)
    rw [Function.mem_support] at hx
    simp only [ContinuousMap.coe_mk] at hx
    simp only [Set.mem_preimage]
    have h_eq : idx x = a := by
      by_contra h
      exact hx (if_neg h)
    rw [← h_eq]
    exact h_idx x

instance instCWComplexParacompactSpace : ParacompactSpace X := by
  apply paracompact_of_exist_partition_of_unity
  intro α s hs_open hs_cover
  sorry


end

end Chp5
