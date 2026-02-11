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

#check PartitionOfUnity

instance instCWComplexParacompactSpace : ParacompactSpace X := by
  sorry

end

end Chp5
