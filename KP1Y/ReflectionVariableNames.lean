import KP1Y.CountableProducts
import KP1Y.CountableNamedSpaces
import KP1Y.CountableRank
import KP1Y.FiniteNaturalRange

/-! 用实际自然数对排名分配互不碰撞的变量族，内部有限族有实际自然数作用域界。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Ranking KP1Y.Cardinal
universe u

theorem pair_name_basis_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {ω Pairs : M.Domain}
    (hω : M.IsOmega ω) (hPairs : IsProduct M Pairs ω ω) : ∃ F, OrdinalRank M F Pairs ω := by
  obtain ⟨I,hI⟩ := identity_onto_d hM ω
  obtain ⟨E,hE⟩ := countable_existing_product_d hM hω hI hI hPairs
  exact countable_rank_d hM hω hE

def VarName (M : SetTheory.Structure.{u}) (Pairs F tag i v : M.Domain) : Prop :=
  ∃ key, M.mem key Pairs ∧ Codes M key tag i ∧ MemPair M F key v

def varNameFormula {d : Nat} (Pairs F tag i v : Project.Term d) : Project.Formula 1 d :=
  Project.Formula.existsMem Pairs (.conj (codeFormula (.bound 0) tag.weaken i.weaken) (memPairFormula F.weaken (.bound 0) v.weaken))

theorem varNameFormula_delta0 {d : Nat} (Pairs F tag i v : Project.Term d) : (varNameFormula Pairs F tag i v).IsDelta0 :=
  .existsMem _ (.conj (codeFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _))

theorem varNameFormula_freeClosed {d : Nat} (Pairs F tag i v : Project.Term d)
    (hPairs : Pairs.freeSupport=[]) (hF : F.freeSupport=[]) (hTag : tag.freeSupport=[])
    (hi : i.freeSupport=[]) (hv : v.freeSupport=[]) : (varNameFormula Pairs F tag i v).FreeClosed := by
  simp [varNameFormula,codeFormula,pairFormula,memPairFormula,Project.Formula.existsMem,Project.Formula.forallMem,
    Definitional.Formula.FreeClosed,hPairs,hF,hTag,hi,hv]

theorem varNameFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {d : Nat} (e : Env M d)
    (Pairs F tag i v : Project.Term d) : Project.Formula.satisfies e (varNameFormula Pairs F tag i v) ↔
      VarName M (Pairs.eval e) (F.eval e) (tag.eval e) (i.eval e) (v.eval e) := by
  simp only [varNameFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    codeFormula_iff he,memPairFormula_iff he,Term.eval_weaken]
  rfl

theorem var_name_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {ω Pairs F tag i : M.Domain}
    (hPairs : IsProduct M Pairs ω ω) (hF : Graph M F Pairs ω) (hTag : M.mem tag ω) (hi : M.mem i ω) :
    ∃ v, M.mem v ω ∧ VarName M Pairs F tag i v := by
  obtain ⟨key,hKey⟩ := codes_total hM tag i
  have hk := (hPairs key).mpr ⟨tag,hTag,i,hi,hKey⟩
  obtain ⟨v,hv,hAt⟩ := hF.total key hk
  exact ⟨v,hv,key,hk,hKey,hAt⟩

theorem VarName.natural {M : SetTheory.Structure.{u}} (he : Extensional M) {ω Pairs F tag i v : M.Domain}
    (hF : Graph M F Pairs ω) (h : VarName M Pairs F tag i v) : M.mem v ω := by
  obtain ⟨_,_,_,hAt⟩ := h
  exact (hF.bounds he hAt).2

theorem VarName.unique {M : SetTheory.Structure.{u}} (he : Extensional M) {ω Pairs F tag i v v' : M.Domain}
    (hF : Graph M F Pairs ω) (h : VarName M Pairs F tag i v) (h' : VarName M Pairs F tag i v') : v=v' := by
  obtain ⟨key,_,hCode,hAt⟩ := h
  obtain ⟨key',_,hCode',hAt'⟩ := h'
  have hkk' := codes_unique he hCode hCode'
  subst key'
  exact hF.unique key v v' hAt hAt'

theorem VarName.injective {M : SetTheory.Structure.{u}} (he : Extensional M) {ω Pairs F tag tag' i j v : M.Domain}
    (hF : OrdinalRank M F Pairs ω) (h : VarName M Pairs F tag i v) (h' : VarName M Pairs F tag' j v) : tag=tag' ∧ i=j := by
  obtain ⟨key,_,hCode,hAt⟩ := h
  obtain ⟨key',_,hCode',hAt'⟩ := h'
  have hkk' := hF.injective key key' v hAt hAt'
  subst key'
  exact codes_injective he hCode hCode'

private def nameSchema : Project.Delta0BinarySchema 3 where
  body := varNameFormula (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := varNameFormula_freeClosed _ _ _ _ _ rfl rfl rfl rfl rfl
  delta0 := varNameFormula_delta0 _ _ _ _ _

theorem name_family_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {ω Pairs F tag n : M.Domain}
    (hω : M.IsOmega ω) (hPairs : IsProduct M Pairs ω ω) (hF : Graph M F Pairs ω)
    (hTag : M.mem tag ω) (hn : M.mem n ω) : ∃ G, Graph M G n ω ∧
      ∀ i v, MemPair M G i v ↔ M.mem i n ∧ VarName M Pairs F tag i v := by
  have hφ (i v : M.Domain) : Project.Formula.satisfies (((((oneEnv Pairs).push F).push tag).push i).push v) nameSchema.body ↔
      VarName M Pairs F tag i v := by
    rw [nameSchema,varNameFormula_iff hM.1]
    rfl
  obtain ⟨G,hSupport,hRaw⟩ := relation_comprehension_d hM nameSchema (((oneEnv Pairs).push F).push tag) n ω
  have hRows (i v : M.Domain) : MemPair M G i v ↔ M.mem i n ∧ VarName M Pairs F tag i v := by
    have h := hRaw i v
    rw [hφ] at h
    exact h.trans ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,h.2.natural hM.1 hF,h.2⟩⟩
  refine ⟨G,⟨hSupport,?_,?_⟩,hRows⟩
  · intro i hi
    obtain ⟨v,hv,hName⟩ := var_name_exists_d hM hPairs hF hTag ((KP1Y.Naturals.omega_isOrdinal_d hM hω).transitive n hn i hi)
    exact ⟨v,hv,(hRows i v).mpr ⟨hi,hName⟩⟩
  · intro i v v' hAt hAt'
    exact ((hRows i v).mp hAt).2.unique hM.1 hF ((hRows i v').mp hAt').2

theorem name_family_bounded_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {ω Pairs F tag n : M.Domain}
    (hω : M.IsOmega ω) (hPairs : IsProduct M Pairs ω ω) (hF : Graph M F Pairs ω)
    (hTag : M.mem tag ω) (hn : M.mem n ω) : ∃ G bound, M.mem bound ω ∧ Graph M G n bound ∧
      ∀ i v, MemPair M G i v ↔ M.mem i n ∧ VarName M Pairs F tag i v := by
  obtain ⟨G,hG,hRows⟩ := name_family_exists_d hM hω hPairs hF hTag hn
  obtain ⟨bound,hb,hBound⟩ := KP1Y.Naturals.finite_natural_range_bounded_d hM hω hn hG
  refine ⟨G,bound,hb,⟨?_,?_,hG.unique⟩,hRows⟩
  · intro p hp
    obtain ⟨i,hi,v,_,hCode⟩ := hG.support p hp
    exact ⟨i,hi,v,hBound i v ⟨p,hp,hCode⟩,hCode⟩
  · intro i hi
    obtain ⟨v,_,hAt⟩ := hG.total i hi
    exact ⟨v,hBound i v hAt,hAt⟩

end KP1Y.ReflectionModel
