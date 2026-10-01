import KP1Y.OneYAncestry
import KP1Y.FunctionalImage
import KP1Y.RelationTables

/-! 内部有限父森林的实际集合空间；通过有限序列解码的精确像集构造，不假设幂集。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Bounded
universe u

structure ForestDecode (M : SetTheory.Structure.{u}) (m E P : M.Domain) : Prop where
  support : RelationSupport M P m m
  rows : ∀ c p, M.mem c m → M.mem p m → (MemPair M P c p ↔ M.mem p c ∧ MemPair M E c p)

def forestDecodeFormula {n : Nat} (m E P : Project.Term n) : Project.Formula 1 n :=
  .conj (relationSupportFormula P m m) (Project.Formula.forallMem m (Project.Formula.forallMem m.weaken
    (.iff (memPairFormula P.weaken.weaken (.bound 1) (.bound 0))
      (.conj (.mem (.bound 0) (.bound 1)) (memPairFormula E.weaken.weaken (.bound 1) (.bound 0))))))

theorem forestDecodeFormula_delta0 {n : Nat} (m E P : Project.Term n) : (forestDecodeFormula m E P).IsDelta0 :=
  .conj (relationSupportFormula_delta0 _ _ _) (.forallMem _ (.forallMem _
    (.iff (memPairFormula_delta0 _ _ _) (.conj (.mem _ _) (memPairFormula_delta0 _ _ _)))))

theorem forestDecodeFormula_freeClosed {n : Nat} (m E P : Project.Term n)
    (hm : m.freeSupport=[]) (hE : E.freeSupport=[]) (hP : P.freeSupport=[]) : (forestDecodeFormula m E P).FreeClosed := by
  simp [forestDecodeFormula,relationSupportFormula,memPairFormula,codeFormula,pairFormula,
    Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hm,hE,hP]

theorem forestDecodeFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (m E P : Project.Term n) :
    Project.Formula.satisfies e (forestDecodeFormula m E P) ↔ ForestDecode M (m.eval e) (E.eval e) (P.eval e) := by
  simp only [forestDecodeFormula,Project.Formula.satisfies_conj_iff,relationSupportFormula_iff he,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_iff_iff,memPairFormula_iff he,
    Project.Formula.satisfies_mem_iff,Term.eval_weaken]
  exact ⟨fun h => ⟨h.1,fun c p hc hp => h.2 c hc p hp⟩,fun h => ⟨h.support,fun c hc p hp => h.rows c p hc hp⟩⟩

private def decodeEdgeSchema : Project.Delta0BinarySchema 1 where
  body := .conj (.mem (.bound 0) (.bound 1)) (memPairFormula (.bound 2) (.bound 1) (.bound 0))
  freeClosed := by
    simp [memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := .conj (.mem _ _) (memPairFormula_delta0 _ _ _)

theorem forest_decode_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (m E : M.Domain) :
    ∃ P, ForestDecode M m E P := by
  have hφ (c p : M.Domain) : Project.Formula.satisfies (((oneEnv E).push c).push p) decodeEdgeSchema.body ↔
      M.mem p c ∧ MemPair M E c p := by
    simp only [decodeEdgeSchema,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,memPairFormula_iff hM.1]
    rfl
  obtain ⟨P,hSupport,hRows⟩ := relation_comprehension_d hM decodeEdgeSchema (oneEnv E) m m
  refine ⟨P,hSupport,?_⟩
  intro c p hc hp
  have hr := hRows c p
  rw [hφ] at hr
  exact hr.trans ⟨fun h => h.2.2,fun h => ⟨hc,hp,h⟩⟩

theorem ForestDecode.unique {M : SetTheory.Structure.{u}} (he : Extensional M) {m E P Q : M.Domain}
    (h : ForestDecode M m E P) (h' : ForestDecode M m E Q) : P=Q := by
  apply relation_ext he h.support h'.support
  intro c p
  classical
  by_cases hc : M.mem c m
  · by_cases hp : M.mem p m
    · exact (h.rows c p hc hp).trans (h'.rows c p hc hp).symm
    · exact iff_of_false (fun hAt => hp (h.support.bounds he hAt).2) (fun hAt => hp (h'.support.bounds he hAt).2)
  · exact iff_of_false (fun hAt => hc (h.support.bounds he hAt).1) (fun hAt => hc (h'.support.bounds he hAt).1)

theorem ForestDecode.forest {M : SetTheory.Structure.{u}} (he : Extensional M) {w m E P n : M.Domain}
    (h : ForestDecode M m E P) (hm : M.mem m w) (hE : Graph M E n w) : Forest M w m P := by
  refine ⟨hm,h.support,?_,?_⟩
  · intro c p q hcp hcq
    obtain ⟨hc,hp⟩ := h.support.bounds he hcp
    have hq := (h.support.bounds he hcq).2
    exact hE.unique c p q ((h.rows c p hc hp).mp hcp).2 ((h.rows c q hc hq).mp hcq).2
  · intro c p hcp
    obtain ⟨hc,hp⟩ := h.support.bounds he hcp
    exact ((h.rows c p hc hp).mp hcp).1

private def parentEncodingSchema : Project.Delta0BinarySchema 2 where
  body := .disj (memPairFormula (.bound 3) (.bound 1) (.bound 0))
    (.conj (Project.Formula.extensionalEq (.bound 0) (.bound 2)) (noParentFormula (.bound 2) (.bound 3) (.bound 1)))
  freeClosed := by
    simp [noParentFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,
      Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := .disj (memPairFormula_delta0 _ _ _) (.conj (.atom _ _ _) (noParentFormula_delta0 _ _ _))

theorem forest_encoding_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P : M.Domain} (hF : Forest M C.omega m P) :
    ∃ E, Graph M E m C.omega ∧ ForestDecode M m E P ∧
      ∀ c, M.mem c m → (MemPair M E c m ↔ NoParent M m P c) := by
  have hφ (c p : M.Domain) : Project.Formula.satisfies ((((oneEnv P).push m).push c).push p) parentEncodingSchema.body ↔
      MemPair M P c p ∨ (p=m ∧ NoParent M m P c) := by
    simp only [parentEncodingSchema,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_conj_iff,
      memPairFormula_iff hM.1,Project.Formula.satisfies_extensionalEq_iff_eq hM.1,noParentFormula_iff hM.1]
    rfl
  obtain ⟨E,hSupport,hRaw⟩ := relation_comprehension_d hM parentEncodingSchema ((oneEnv P).push m) m C.omega
  have hRows (c p : M.Domain) : MemPair M E c p ↔ M.mem c m ∧
      (MemPair M P c p ∨ (p=m ∧ NoParent M m P c)) := by
    have hr := hRaw c p
    rw [hφ] at hr
    refine hr.trans ⟨fun h => ⟨h.1,h.2.2⟩,?_⟩
    rintro ⟨hc,hCase⟩
    refine ⟨hc,?_,hCase⟩
    rcases hCase with hAt | ⟨rfl,_⟩
    · exact (KP1Y.Naturals.omega_isOrdinal_d hM hC.omega).transitive m hF.width p (hF.bounds hM.1 hAt).2
    · exact hF.width
  have hGraph : Graph M E m C.omega := by
    classical
    refine ⟨hSupport,?_,?_⟩
    · intro c hc
      by_cases hNo : NoParent M m P c
      · exact ⟨m,hF.width,(hRows c m).mpr ⟨hc,Or.inr ⟨rfl,hNo⟩⟩⟩
      · have hSome : ∃ p, M.mem p m ∧ MemPair M P c p := by
          apply Classical.byContradiction
          intro hNot
          exact hNo (fun p hp hAt => hNot ⟨p,hp,hAt⟩)
        obtain ⟨p,hp,hAt⟩ := hSome
        exact ⟨p,(KP1Y.Naturals.omega_isOrdinal_d hM hC.omega).transitive m hF.width p hp,
          (hRows c p).mpr ⟨hc,Or.inl hAt⟩⟩
    · intro c p q hcp hcq
      rcases ((hRows c p).mp hcp).2 with hP | ⟨hp,hNo⟩ <;>
        rcases ((hRows c q).mp hcq).2 with hQ | ⟨hq,hNo'⟩
      · exact hF.unique c p q hP hQ
      · exact False.elim (hNo' p (hF.bounds hM.1 hP).2 hP)
      · exact False.elim (hNo q (hF.bounds hM.1 hQ).2 hQ)
      · exact hp.trans hq.symm
  refine ⟨E,hGraph,⟨hF.support,?_⟩,?_⟩
  · intro c p hc hp
    constructor
    · intro hAt
      exact ⟨hF.left c p hAt,(hRows c p).mpr ⟨hc,Or.inl hAt⟩⟩
    · rintro ⟨_,hAt⟩
      rcases ((hRows c p).mp hAt).2 with hP | ⟨he,_⟩
      · exact hP
      · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) m (he ▸ hp))
  · intro c hc
    constructor
    · intro hAt
      rcases ((hRows c m).mp hAt).2 with hP | ⟨_,hNo⟩
      · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) m (hF.bounds hM.1 hP).2)
      · exact hNo
    · intro hNo
      exact (hRows c m).mpr ⟨hc,Or.inr ⟨rfl,hNo⟩⟩

private def forestDecodeSchema : Project.Delta0BinarySchema 1 where
  body := forestDecodeFormula (.bound 2) (.bound 1) (.bound 0)
  freeClosed := forestDecodeFormula_freeClosed _ _ _ rfl rfl rfl
  delta0 := forestDecodeFormula_delta0 _ _ _

theorem forest_space_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} (hm : M.mem m C.omega) :
    ∃ Forests, ∀ P, M.mem P Forests ↔ Forest M C.omega m P := by
  have hφ (E P : M.Domain) : Project.Formula.satisfies (((oneEnv m).push E).push P) forestDecodeSchema.body ↔
      ForestDecode M m E P := forestDecodeFormula_iff hM.1 _ _ _ _
  obtain ⟨Forests,hForests⟩ := KP1Y.functional_image_d hM forestDecodeSchema (oneEnv m) C.sequences
    (fun E _ => by
      obtain ⟨P,hP⟩ := forest_decode_exists_d hM m E
      exact ⟨P,(hφ E P).mpr hP⟩)
    (fun E _ P Q hP hQ => ((hφ E P).mp hP).unique hM.1 ((hφ E Q).mp hQ))
  refine ⟨Forests,fun P => ?_⟩
  have hMem : M.mem P Forests ↔ ∃ E, M.mem E C.sequences ∧ ForestDecode M m E P := by
    simpa only [hφ] using hForests P
  apply hMem.trans
  constructor
  · rintro ⟨E,hE,hP⟩
    obtain ⟨n,_,hGraph⟩ := (hC.sequences E).mp hE
    exact hP.forest hM.1 hm hGraph
  · intro hP
    obtain ⟨E,hE,hDecode,_⟩ := forest_encoding_exists_d hM hC hP
    exact ⟨E,(hC.sequences E).mpr ⟨m,hm,hE⟩,hDecode⟩

end KP1Y.OneYFinite
