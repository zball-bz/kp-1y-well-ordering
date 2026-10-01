import KP1Y.OneYForestEmbedding
import KP1Y.OneYForestClosure

/-! 全内部自然数上的实际列图只在给定有限路径上使用；目标宽度由末点收紧。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments KP1Y.Naturals
universe u

private def pathAncestorEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (m P : M.Domain) : Env M 7 :=
  ((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push m).push P

private def pathAncestorSchema : Project.UnarySchema 7 where
  body := .forallE (.forallE (.forallE (.imp
    (parentPathFormula ⟨.bound 10,.bound 9,.bound 8,.bound 7,.bound 6⟩ (.bound 5) (.bound 4) (.bound 2) (.bound 3) (.bound 1) (.bound 0))
    (.forallE (.forallE (.imp (memPairFormula (.bound 4) (.bound 1) (.bound 0))
      (.disj (Project.Formula.extensionalEq (.bound 0) (.bound 2))
        (ancestorFormula ⟨.bound 12,.bound 11,.bound 10,.bound 9,.bound 8⟩ (.bound 7) (.bound 6) (.bound 0) (.bound 2)))))))))
  freeClosed := by
    have hPath := parentPathFormula_freeClosed
      (show (⟨.bound 10,.bound 9,.bound 8,.bound 7,.bound 6⟩ : ExpressionData (Project.Term 11)).Closed from ⟨rfl,rfl,rfl,rfl,rfl⟩)
      (.bound 5) (.bound 4) (.bound 2) (.bound 3) (.bound 1) (.bound 0) rfl rfl rfl rfl rfl rfl
    have hAnc := ancestorFormula_freeClosed
      (show (⟨.bound 12,.bound 11,.bound 10,.bound 9,.bound 8⟩ : ExpressionData (Project.Term 13)).Closed from ⟨rfl,rfl,rfl,rfl,rfl⟩)
      (.bound 7) (.bound 6) (.bound 0) (.bound 2) rfl rfl rfl rfl
    simp [Definitional.Formula.FreeClosed,hPath,hAnc,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem]

private theorem pathAncestorSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (m P len : M.Domain) :
    Project.Formula.satisfies ((pathAncestorEnv C m P).push len) pathAncestorSchema.body ↔
      ∀ f a c, ParentPath M C m P f len a c → ∀ i x, MemPair M f i x → x=c ∨ Ancestor M C m P x c := by
  simp only [pathAncestorSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,
    parentPathFormula_iff he,memPairFormula_iff he,ancestorFormula_iff he]
  rfl

theorem ParentPath.values_ancestor_end_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P f len a c : M.Domain}
    (hP : Forest M C.omega m P) (hPath : ParentPath M C m P f len a c) :
    ∀ i x, MemPair M f i x → x=c ∨ Ancestor M C m P x c := by
  have hAll := natural_induction_d hM pathAncestorSchema (pathAncestorEnv C m P) hC.omega
    (fun z hz => (pathAncestorSchema_iff hM.1 C m P z).mpr (by
      intro f a c hPath
      exact False.elim (hz C.zero (hPath.zero_in_length hM.1))))
    (fun len hLen ih next hs => (pathAncestorSchema_iff hM.1 C m P next).mpr (by
      intro f a c hPath i x hAt
      rcases hPath.peel_d hM hC with ⟨_,_,hSingle⟩ | ⟨prev,g,b,hPrev,_,hPrefix,hOld,hParent⟩
      · exact Or.inl (hSingle i x hAt).2
      · have he := Structure.SuccessorOf.predecessor_eq hM.1 ((omega_isOrdinal_d hM hC.omega).mem hLen) hs hPrev
        subst prev
        rcases (hs i).mp (hPath.graph.bounds hM.1 hAt).1 with hi | he
        · have hIX := (hPrefix.all_rows hM.1 hPath.graph i hi x).mpr hAt
          rcases (pathAncestorSchema_iff hM.1 C m P len).mp ih g a b hOld i x hIX with he | hAnc
          · exact Or.inr (he.symm ▸ ancestor_direct_d hM hC hP hParent)
          · exact Or.inr (ancestor_step_d hM hC hP hAnc hParent)
        · have hi := hM.1.eq_of_same_members i len he
          subst i
          obtain ⟨last,_,hLast,_,hEnd⟩ := hPath.endpoints
          have hl := Structure.SuccessorOf.predecessor_eq hM.1 ((omega_isOrdinal_d hM hC.omega).mem hLen) hs hLast
          subst last
          exact Or.inl (hPath.graph.unique len x c hAt hEnd)))
  exact (pathAncestorSchema_iff hM.1 C m P len).mp (hAll len hPath.length) f a c hPath

/-- 只运输这条路径实际经过的父边，允许目标另外包含其他副本。 -/
theorem ParentPath.map_global_bounded_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m n P Q J f len a c x y : M.Domain}
    (hP : Forest M C.omega m P) (hn : M.mem n C.omega) (hJ : ColumnEmbedding M C.omega C.omega J)
    (hPath : ParentPath M C m P f len a c) (hax : MemPair M J a x) (hcy : MemPair M J c y) (hy : M.mem y n)
    (hEdges : ∀ d p u v, (d=c ∨ Ancestor M C m P d c) → MemPair M P d p →
      MemPair M J d u → MemPair M J p v → MemPair M Q u v) :
    ∃ g, ParentPath M C n Q g len x y := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hmω : M.MemberSubset m C.omega := fun z hz => hw.transitive m hP.width z hz
  obtain ⟨g,hG⟩ := tuple_value_exists_d hM (hPath.graph.mono_values hmω) hJ.graph
  have hBound (i z : M.Domain) (hIZ : MemPair M g i z) : M.mem z n := by
    obtain ⟨v,hv,hIV⟩ := hPath.graph.total i (hG.values.bounds hM.1 hIZ).1
    have hVZ := (hG.rows i (hPath.graph.bounds hM.1 hIV).1 v (hmω v hv) z
      (hG.values.bounds hM.1 hIZ).2 hIV).mp hIZ
    rcases hPath.values_below_last_d hM hC hP i v hIV with he | hvc
    · subst v
      exact (hJ.graph.unique c z y hVZ hcy).symm ▸ hy
    · exact (hw.mem hn).transitive y hy z
        (hJ.strict v (hmω v hv) c (hmω c (hPath.end_bound hM.1)) hvc z y hVZ hcy)
  have hGraph : Graph M g len n := by
    refine ⟨?_,?_,hG.values.unique⟩
    · intro e he
      obtain ⟨i,hi,z,_,hCode⟩ := hG.values.support e he
      exact ⟨i,hi,z,hBound i z ⟨e,he,hCode⟩,hCode⟩
    · intro i hi
      obtain ⟨z,_,hIZ⟩ := hG.values.total i hi
      exact ⟨z,hBound i z hIZ,hIZ⟩
  obtain ⟨last,hl,hSucc,hFirst,hLast⟩ := hPath.endpoints
  refine ⟨g,hPath.length,hGraph,⟨last,hl,hSucc,?_,?_⟩,?_⟩
  · exact (hG.rows C.zero (hPath.graph.bounds hM.1 hFirst).1 a (hmω a (hPath.start_bound hM.1)) x
      (hJ.graph.bounds hM.1 hax).2 hFirst).mpr hax
  · exact (hG.rows last hl c (hmω c (hPath.end_bound hM.1)) y (hJ.graph.bounds hM.1 hcy).2 hLast).mpr hcy
  · intro i j u v hi hj hIU hJV hs
    obtain ⟨p,hp,hIP⟩ := hPath.graph.total i hi
    obtain ⟨d,hd,hJD⟩ := hPath.graph.total j hj
    exact hEdges d p v u (hPath.values_ancestor_end_d hM hC hP j d hJD)
      (hPath.edges i j p d hi hj hIP hJD hs)
      ((hG.rows j hj d (hmω d hd) v (hG.values.bounds hM.1 hJV).2 hJD).mp hJV)
      ((hG.rows i hi p (hmω p hp) u (hG.values.bounds hM.1 hIU).2 hIP).mp hIU)

theorem ancestor_map_global_bounded_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m n P Q J a c x y : M.Domain}
    (hP : Forest M C.omega m P) (hn : M.mem n C.omega) (hJ : ColumnEmbedding M C.omega C.omega J)
    (hAnc : Ancestor M C m P a c) (hax : MemPair M J a x) (hcy : MemPair M J c y) (hy : M.mem y n)
    (hEdges : ∀ d p u v, (d=c ∨ Ancestor M C m P d c) → MemPair M P d p →
      MemPair M J d u → MemPair M J p v → MemPair M Q u v) : Ancestor M C n Q x y := by
  obtain ⟨hac,len,_,f,_,hPath⟩ := hAnc
  obtain ⟨g,hG⟩ := hPath.map_global_bounded_d hM hC hP hn hJ hax hcy hy hEdges
  exact ⟨hJ.strict a (hJ.graph.bounds hM.1 hax).1 c (hJ.graph.bounds hM.1 hcy).1 hac x y hax hcy,
    len,hG.length,g,hG.sequence_member_d hM hC hn,hG⟩

theorem root_map_global_bounded_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m n P Q J a c x y : M.Domain}
    (hP : Forest M C.omega m P) (hn : M.mem n C.omega) (hJ : ColumnEmbedding M C.omega C.omega J)
    (hRoot : Root M C m P c a) (hax : MemPair M J a x) (hcy : MemPair M J c y) (hy : M.mem y n)
    (hNo : NoParent M n Q x)
    (hEdges : ∀ d p u v, (d=c ∨ Ancestor M C m P d c) → MemPair M P d p →
      MemPair M J d u → MemPair M J p v → MemPair M Q u v) : Root M C n Q y x := by
  rcases hRoot.2.2 with he | hAnc
  · subst a
    have hxy := hJ.graph.unique c x y hax hcy
    subst x
    exact ⟨hy,hNo,Or.inl rfl⟩
  · have hXY := ancestor_map_global_bounded_d hM hC hP hn hJ hAnc hax hcy hy hEdges
    exact ⟨(hXY.bounds hM.1).1,hNo,Or.inr hXY⟩

end KP1Y.OneYFinite
