import KP1Y.SkolemOperationsSyntax
import KP1Y.SkolemClosure

/-! 实际 Skolem 函数改写成可数元数据索引下的全定义有限元组操作族。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Cardinal
universe u

structure SkolemOperation (M : SetTheory.Structure.{u}) (C : Context M.Domain) (I : EvaluationData M.Domain)
    (K : SkolemBounds M.Domain) (Ops F Keys G : M.Domain) : Prop where
  keys : IsProduct M Keys Ops I.assignments
  graph : Graph M G Keys I.carrier
  rows : ∀ key x, MemPair M G key x ↔ M.mem key Keys ∧ M.mem x I.carrier ∧ SkolemApply M C I K Ops F key x

theorem skolem_operation_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} {I : EvaluationData M.Domain} (hI : I.Valid C) {K : SkolemBounds M.Domain}
    (hK : SkolemBoundsValid M C I K) {F Ops : M.Domain} (hF : Graph M F K.keys I.carrier)
    (hOps : IsProduct M Ops K.programNodes C.omega) : ∃ Keys G, SkolemOperation M C I K Ops F Keys G := by
  obtain ⟨Keys,hKeys⟩ := product_exists hM Ops I.assignments
  obtain ⟨G,hSupport,hRaw⟩ := relation_comprehension_d hM skolemOperationSchema ((skolemEnv C I K Ops).push F) Keys I.carrier
  have hRows (key x : M.Domain) : MemPair M G key x ↔ M.mem key Keys ∧ M.mem x I.carrier ∧ SkolemApply M C I K Ops F key x := by
    simpa only [skolemOperationSchema_iff hM.1] using hRaw key x
  refine ⟨Keys,G,hKeys,⟨hSupport,?_,?_⟩,hRows⟩
  · intro key hKey
    obtain ⟨op,hOp,s,hs,hCode⟩ := (hKeys key).mp hKey
    obtain ⟨pj,hPJ,v,hv,hOpCode⟩ := (hOps op).mp hOp
    obtain ⟨p,hp,j,hj,hPJCode⟩ := (hK.programNodes pj).mp hPJ
    obtain ⟨bound,hb,hS⟩ := (hI.assignments_exact s).mp hs
    obtain ⟨oldKey,hOldKey,hOldCode⟩ := skolem_key_exists_d hM hK hp hj hs hb hv
    obtain ⟨x,hx,hAt⟩ := hF.total oldKey hOldKey
    have hApply : SkolemApply M C I K Ops F key x :=
      ⟨op,hOp,s,hs,hCode,p,hp,j,hj,v,hv,⟨pj,hPJ,hOpCode,hPJCode⟩,bound,hb,hS,oldKey,hOldKey,hOldCode,hAt⟩
    exact ⟨x,hx,(hRows key x).mpr ⟨hKey,hx,hApply⟩⟩
  · intro key x y hX hY
    obtain ⟨_,_,op,_,s,_,hCode,p,_,j,_,v,_,hMeta,bound,_,hS,oldKey,_,hOld,hAt⟩ := (hRows key x).mp hX
    obtain ⟨_,_,op',_,s',_,hCode',p',_,j',_,v',_,hMeta',bound',_,hS',oldKey',_,hOld',hAt'⟩ := (hRows key y).mp hY
    obtain ⟨hOps,hSs⟩ := codes_injective hM.1 hCode hCode'
    subst op'
    subst s'
    obtain ⟨hPs,hJs,hVs⟩ := metadata_unique hM.1 hMeta hMeta'
    subst p'
    subst j'
    subst v'
    have hBounds := KP1Y.Assignments.domain_unique hM.1 hS hS'
    subst bound'
    have hKeysEq := key_code_value_unique hM.1 hOld hOld'
    subst oldKey'
    exact hF.unique oldKey x y hAt hAt'

theorem skolem_operations_countable_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {I : EvaluationData M.Domain} (hI : I.Valid C)
    {K : SkolemBounds M.Domain} (hK : SkolemBoundsValid M C I K) {F EPrograms : M.Domain}
    (hF : Graph M F K.keys I.carrier) (hPrograms : Onto M EPrograms C.omega C.programs) :
    ∃ Ops EOps Keys G, IsProduct M Ops K.programNodes C.omega ∧ Onto M EOps C.omega Ops ∧ SkolemOperation M C I K Ops F Keys G := by
  obtain ⟨EOmega,hEOmega⟩ := identity_onto_d hM C.omega
  obtain ⟨EPJ,hEPJ⟩ := countable_existing_product_d hM hC.omega hPrograms hEOmega hK.programNodes
  obtain ⟨Ops,EOps,hOps,hEOps⟩ := countable_product_d hM hC.omega hEPJ hEOmega
  obtain ⟨Keys,G,hG⟩ := skolem_operation_exists_d hM hI hK hF hOps
  exact ⟨Ops,EOps,Keys,G,hOps,hEOps,hG⟩

theorem operation_closed_skolem_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} {I : EvaluationData M.Domain} (hI : I.Valid C)
    {K : SkolemBounds M.Domain} (hK : SkolemBoundsValid M C I K)
    {F Ops Keys G X : M.Domain} (hF : Graph M F K.keys I.carrier)
    (hOps : IsProduct M Ops K.programNodes C.omega) (hG : SkolemOperation M C I K Ops F Keys G)
    (hSub : M.MemberSubset X I.carrier)
    (hClosed : ∀ op, M.mem op Ops → ∀ n, M.mem n C.omega → ∀ t, Graph M t n X →
      ∀ key, Codes M key op t → ∀ x, MemPair M G key x → M.mem x X) : SkolemClosed M C K F X := by
  intro p hp j hj bound hb v hv s hS oldKey hOldCode x hAt
  have hSBig := hS.mono_values hSub
  have hs := (hI.assignments_exact s).mpr ⟨bound,hb,hSBig⟩
  obtain ⟨pj,hPJCode⟩ := codes_total hM p j
  have hPJ := (hK.programNodes pj).mpr ⟨p,hp,j,hj,hPJCode⟩
  obtain ⟨op,hOpCode⟩ := codes_total hM pj v
  have hOp := (hOps op).mpr ⟨pj,hPJ,v,hv,hOpCode⟩
  obtain ⟨key,hCode⟩ := codes_total hM op s
  have hKey := (hG.keys key).mpr ⟨op,hOp,s,hs,hCode⟩
  have hOldKey := (key_members hK oldKey).mpr ⟨p,hp,j,hj,s,hs,bound,hb,v,hv,hOldCode⟩
  have hApply : SkolemApply M C I K Ops F key x :=
    ⟨op,hOp,s,hs,hCode,p,hp,j,hj,v,hv,⟨pj,hPJ,hOpCode,hPJCode⟩,bound,hb,hSBig,oldKey,hOldKey,hOldCode,hAt⟩
  exact hClosed op hOp bound hb s hS key hCode x ((hG.rows key x).mpr ⟨hKey,(hF.bounds hM.1 hAt).2,hApply⟩)

end KP1Y.Satisfaction
