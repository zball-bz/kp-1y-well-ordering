import KP1Y.SatisfactionInstruction

/-! 四个不同的实际小自然数操作码及其集合；无额外无限标签集假设。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory
universe u

structure DistinctTags (α : Type u) (a n i q : α) : Prop where
  atom_neg : a≠n
  atom_imp : a≠i
  atom_all : a≠q
  neg_imp : n≠i
  neg_all : n≠q
  imp_all : i≠q

private theorem ne_of_mem {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {a b : M.Domain} (h : M.mem a b) : a≠b := by
  intro he
  subst a
  exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) b h

theorem opcode_set_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω : M.Domain} (hω : M.IsOmega ω) :
    ∃ Tags a n i q, DistinctTags M.Domain a n i q ∧
      M.mem a ω ∧ M.mem n ω ∧ M.mem i ω ∧ M.mem q ω ∧
      ∀ x, M.mem x Tags ↔ x=a ∨ x=n ∨ x=i ∨ x=q := by
  have hw := KP1Y.models_weakKP hM
  obtain ⟨a,_,ha⟩ := hω.1.1
  obtain ⟨n,hnSucc,hn⟩ := hω.1.2 a ha
  obtain ⟨i,hiSucc,hi⟩ := hω.1.2 n hn
  obtain ⟨q,hqSucc,hq⟩ := hω.1.2 i hi
  have han := hnSucc.predecessor_mem
  have hni := hiSucc.predecessor_mem
  have hiq := hqSucc.predecessor_mem
  have hai := (hiSucc a).mpr (Or.inl han)
  have haq := (hqSucc a).mpr (Or.inl hai)
  have hnq := (hqSucc n).mpr (Or.inl hni)
  obtain ⟨L,hL⟩ := SetTheory.KP.exists_pair hw a n
  obtain ⟨R,hR⟩ := SetTheory.KP.exists_pair hw i q
  obtain ⟨Tags,hTags⟩ := SetTheory.KP.exists_unionOfTwo hw L R
  refine ⟨Tags,a,n,i,q,⟨ne_of_mem hM han,ne_of_mem hM hai,ne_of_mem hM haq,
    ne_of_mem hM hni,ne_of_mem hM hnq,ne_of_mem hM hiq⟩,ha,hn,hi,hq,?_⟩
  intro x
  rw [hTags x,hL x,hR x]
  exact or_assoc

end KP1Y.Satisfaction
