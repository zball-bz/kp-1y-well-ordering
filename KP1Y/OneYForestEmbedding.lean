import KP1Y.OneYFrameTransport

/-! 只在嵌入像上要求父行对应的路径运输；目标森林允许另外包含其他副本。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments KP1Y.Naturals
universe u

theorem ParentPath.map_with_edges_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {m n P Q J f len a c x y : M.Domain}
    (hJ : Graph M J m n) (hPath : ParentPath M C m P f len a c)
    (hax : MemPair M J a x) (hcy : MemPair M J c y)
    (hEdges : ∀ c p u v, MemPair M P c p → MemPair M J c u → MemPair M J p v → MemPair M Q u v) :
    ∃ g, ParentPath M C n Q g len x y := by
  obtain ⟨g,hG⟩ := tuple_value_exists_d hM hPath.graph hJ
  obtain ⟨last,hl,hSucc,hFirst,hLast⟩ := hPath.endpoints
  refine ⟨g,hPath.length,hG.values,⟨last,hl,hSucc,?_,?_⟩,?_⟩
  · exact (hG.rows C.zero (hPath.graph.bounds hM.1 hFirst).1 a (hPath.graph.bounds hM.1 hFirst).2 x
      (hJ.bounds hM.1 hax).2 hFirst).mpr hax
  · exact (hG.rows last hl c (hPath.graph.bounds hM.1 hLast).2 y (hJ.bounds hM.1 hcy).2 hLast).mpr hcy
  · intro i j u v hi hj hIu hJv hs
    obtain ⟨p,hp,hIp⟩ := hPath.graph.total i hi
    obtain ⟨c,hc,hJc⟩ := hPath.graph.total j hj
    exact hEdges c p v u (hPath.edges i j p c hi hj hIp hJc hs)
      ((hG.rows j hj c hc v (hG.values.bounds hM.1 hJv).2 hJc).mp hJv)
      ((hG.rows i hi p hp u (hG.values.bounds hM.1 hIu).2 hIp).mp hIu)

private def startBoundEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (m P : M.Domain) : Env M 7 :=
  ((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push m).push P

private def startBoundSchema : Project.UnarySchema 7 where
  body := .forallE (.forallE (.forallE (.imp
    (parentPathFormula ⟨.bound 10,.bound 9,.bound 8,.bound 7,.bound 6⟩ (.bound 5) (.bound 4) (.bound 2) (.bound 3) (.bound 1) (.bound 0))
    (.forallE (.forallE (.imp (memPairFormula (.bound 4) (.bound 1) (.bound 0))
      (.disj (Project.Formula.extensionalEq (.bound 3) (.bound 0)) (.mem (.bound 3) (.bound 0)))))))))
  freeClosed := by
    have hPath := parentPathFormula_freeClosed
      (show (⟨.bound 10,.bound 9,.bound 8,.bound 7,.bound 6⟩ : ExpressionData (Project.Term 11)).Closed from ⟨rfl,rfl,rfl,rfl,rfl⟩)
      (.bound 5) (.bound 4) (.bound 2) (.bound 3) (.bound 1) (.bound 0) rfl rfl rfl rfl rfl rfl
    simp [Definitional.Formula.FreeClosed,hPath,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem]

private theorem startBoundSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (m P len : M.Domain) :
    Project.Formula.satisfies ((startBoundEnv C m P).push len) startBoundSchema.body ↔
      ∀ f a c, ParentPath M C m P f len a c → ∀ i x, MemPair M f i x → a=x ∨ M.mem a x := by
  simp only [startBoundSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,Project.Formula.satisfies_mem_iff,
    parentPathFormula_iff he,memPairFormula_iff he]
  rfl

theorem ParentPath.values_above_start_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P f len a c : M.Domain}
    (hP : Forest M C.omega m P) (hPath : ParentPath M C m P f len a c) :
    ∀ i x, MemPair M f i x → a=x ∨ M.mem a x := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hAll := natural_induction_d hM startBoundSchema (startBoundEnv C m P) hC.omega
    (fun zero hEmpty => (startBoundSchema_iff hM.1 C m P zero).mpr (by
      intro f a c hPath
      exact False.elim (hEmpty C.zero (hPath.zero_in_length hM.1))))
    (fun len hLen ih next hs => (startBoundSchema_iff hM.1 C m P next).mpr (by
      intro f a c hPath i x hAt
      rcases hPath.peel_d hM hC with ⟨_,hac,hSingle⟩ | ⟨prev,g,b,hPrev,_,hPrefix,hOld,hParent⟩
      · exact Or.inl (hac.trans (hSingle i x hAt).2.symm)
      · have hPrevEq := Structure.SuccessorOf.predecessor_eq hM.1 (hw.mem hLen) hs hPrev
        subst prev
        rcases (hs i).mp (hPath.graph.bounds hM.1 hAt).1 with hi | he
        · exact (startBoundSchema_iff hM.1 C m P len).mp ih g a b hOld i x
            ((hPrefix.all_rows hM.1 hPath.graph i hi x).mpr hAt)
        · have hiEq := hM.1.eq_of_same_members i len he
          subst i
          obtain ⟨last,_,hLast,_,hEnd⟩ := hPath.endpoints
          have hLastEq := Structure.SuccessorOf.predecessor_eq hM.1 (hw.mem hLen) hs hLast
          subst last
          have hxc := hPath.graph.unique len x c hAt hEnd
          subst x
          rcases hOld.endpoints_ordered_d hM hC hP with he | hab
          · exact Or.inr (he ▸ hP.left c b hParent)
          · exact Or.inr ((hw.mem (hw.transitive m hP.width c (hP.bounds hM.1 hParent).1)).transitive
              b (hP.left c b hParent) a hab)))
  exact (startBoundSchema_iff hM.1 C m P len).mp (hAll len hPath.length) f a c hPath

/-- 只规定映射源节点的父行；目标上其他副本或额外节点的父行不受限制。 -/
def ParentCorrespondence (M : SetTheory.Structure.{u}) (m P Q J : M.Domain) : Prop :=
  ∀ c x, MemPair M J c x → ∀ y, MemPair M Q x y ↔ ∃ p, M.mem p m ∧ MemPair M P c p ∧ MemPair M J p y

private def localPullbackCore {d : Nat} (C : ExpressionData (Project.Term d)) (m n P Q J len : Project.Term d) : Project.Formula 1 d :=
  Project.Formula.forallMem C.sequences (Project.Formula.forallMem m.weaken
    (Project.Formula.forallMem m.weaken.weaken (Project.Formula.forallMem n.weaken.weaken.weaken
      (Project.Formula.forallMem n.weaken.weaken.weaken.weaken
        (.imp (.conj (memPairFormula J.weaken.weaken.weaken.weaken.weaken (.bound 3) (.bound 1))
          (.conj (memPairFormula J.weaken.weaken.weaken.weaken.weaken (.bound 2) (.bound 0))
            (parentPathFormula C.weaken.weaken.weaken.weaken.weaken n.weaken.weaken.weaken.weaken.weaken
              Q.weaken.weaken.weaken.weaken.weaken (.bound 4) len.weaken.weaken.weaken.weaken.weaken (.bound 1) (.bound 0))))
          (Project.Formula.existsMem C.sequences.weaken.weaken.weaken.weaken.weaken
            (parentPathFormula C.weaken.weaken.weaken.weaken.weaken.weaken m.weaken.weaken.weaken.weaken.weaken.weaken
              P.weaken.weaken.weaken.weaken.weaken.weaken (.bound 0) len.weaken.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 3))))))))

private def localPullbackEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (m n P Q J : M.Domain) : Env M 10 :=
  (((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push m).push n).push P).push Q).push J

private def localPullbackSchema : Project.UnarySchema 10 where
  body := localPullbackCore ⟨.bound 10,.bound 9,.bound 8,.bound 7,.bound 6⟩ (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := by
    simp [localPullbackCore,parentPathFormula,ExpressionData.weaken,ExpressionData.map,graphFormula,
      KP1Y.Bounded.successorFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,
      Project.Formula.existsMem,Definitional.Formula.FreeClosed]

private theorem localPullbackSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (m n P Q J len : M.Domain) :
    Project.Formula.satisfies ((localPullbackEnv C m n P Q J).push len) localPullbackSchema.body ↔
      ∀ f, M.mem f C.sequences → ∀ a, M.mem a m → ∀ c, M.mem c m → ∀ x, M.mem x n → ∀ y, M.mem y n →
        MemPair M J a x ∧ MemPair M J c y ∧ ParentPath M C n Q f len x y → ∃ g, M.mem g C.sequences ∧ ParentPath M C m P g len a c := by
  simp only [localPullbackSchema,localPullbackCore,Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_existsMem_iff,
    memPairFormula_iff he,parentPathFormula_iff he,ExpressionData.eval_weaken,Term.eval_weaken]
  rfl

theorem ParentPath.pullback_local_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m n P J Q f len a c x y : M.Domain}
    (hP : Forest M C.omega m P) (hn : M.mem n C.omega) (hJ : ColumnEmbedding M m n J)
    (hCorr : ParentCorrespondence M m P Q J) (hPath : ParentPath M C n Q f len x y)
    (hax : MemPair M J a x) (hcy : MemPair M J c y) : ∃ g, ParentPath M C m P g len a c := by
  have hAll := natural_induction_d hM localPullbackSchema (localPullbackEnv C m n P Q J) hC.omega
    (fun zero hEmpty => (localPullbackSchema_iff hM.1 C m n P Q J zero).mpr (by
      intro f _ a _ c _ x _ y _ hAnte
      exact False.elim (hEmpty C.zero (hAnte.2.2.zero_in_length hM.1))))
    (fun last hLast ih next hNext => (localPullbackSchema_iff hM.1 C m n P Q J next).mpr (by
      intro f _ a ha c hc x hx y _ hAnte
      obtain ⟨hax,hcy,hPath⟩ := hAnte
      rcases hPath.peel_d hM hC with ⟨hOne,hxy,_⟩ | ⟨prev,g,b,hPrev,hPrevNat,_,hOld,hYb⟩
      · subst y
        have hac := hJ.injective_d hM hC.omega hP.width hax hcy
        subst c
        obtain ⟨g,hG⟩ := parent_path_singleton_d (P := P) hM hC ha
        have hG' : ParentPath M C m P g next a a := Eq.mpr (congrArg (fun l => ParentPath M C m P g l a a) hOne) hG
        exact ⟨g,hG'.sequence_member_d hM hC hP.width,hG'⟩
      · have hPrevLast := Structure.SuccessorOf.predecessor_eq hM.1 ((omega_isOrdinal_d hM hC.omega).mem hPrevNat) hPrev hNext
        subst prev
        obtain ⟨p,hp,hcp,hpb⟩ := (hCorr c y hcy b).mp hYb
        obtain ⟨source,_,hSource⟩ := (localPullbackSchema_iff hM.1 C m n P Q J last).mp ih
          g (hOld.sequence_member_d hM hC hn) a ha p hp x hx b (hOld.end_bound hM.1) ⟨hax,hpb,hOld⟩
        obtain ⟨next',g',hNext',hG'⟩ := hSource.append_d hM hC hc hcp
        have hNextEq := Structure.SuccessorOf.eq hM.1 hNext' hNext
        subst next'
        exact ⟨g',hG'.sequence_member_d hM hC hP.width,hG'⟩))
  obtain ⟨g,_,hG⟩ := (localPullbackSchema_iff hM.1 C m n P Q J len).mp (hAll len hPath.length)
    f (hPath.sequence_member_d hM hC hn) a (hJ.graph.bounds hM.1 hax).1 c (hJ.graph.bounds hM.1 hcy).1
      x (hJ.graph.bounds hM.1 hax).2 y (hJ.graph.bounds hM.1 hcy).2 ⟨hax,hcy,hPath⟩
  exact ⟨g,hG⟩

theorem ancestor_correspondence_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m n P J Q a c x y : M.Domain}
    (hP : Forest M C.omega m P) (hn : M.mem n C.omega) (hJ : ColumnEmbedding M m n J)
    (hCorr : ParentCorrespondence M m P Q J) (hax : MemPair M J a x) (hcy : MemPair M J c y) :
    Ancestor M C n Q x y ↔ Ancestor M C m P a c := by
  constructor
  · rintro ⟨hxy,len,_,f,_,hPath⟩
    obtain ⟨g,hG⟩ := hPath.pullback_local_d hM hC hP hn hJ hCorr hax hcy
    rcases hG.endpoints_ordered_d hM hC hP with he | hac
    · subst c
      have hxyEq := hJ.graph.unique a x y hax hcy
      exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) y (hxyEq ▸ hxy))
    · exact ⟨hac,len,hG.length,g,hG.sequence_member_d hM hC hP.width,hG⟩
  · rintro ⟨hac,len,_,f,_,hPath⟩
    obtain ⟨g,hG⟩ := hPath.map_with_edges_d hM hJ.graph hax hcy (by
      intro c p u v hCP hCu hPv
      exact (hCorr c u hCu v).mpr ⟨p,(hP.bounds hM.1 hCP).2,hCP,hPv⟩)
    exact ⟨hJ.strict a (hJ.graph.bounds hM.1 hax).1 c (hJ.graph.bounds hM.1 hcy).1 hac x y hax hcy,
      len,hG.length,g,hG.sequence_member_d hM hC hn,hG⟩

end KP1Y.OneYFinite
