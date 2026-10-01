import KP1Y.OneYCopyPathTransport
import KP1Y.OneYNaturalDifferenceAddition

/-! Lower规范性所需的通用深度/路径工具：深度沿实际父路径相加，并在映射路径上比较。
全部长度均为内部ω元素，归纳只施于明确的对象公式。 -/
namespace KP1Y.OneYFinite.LowerCanon
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
open KP1Y.OneYFinite
universe u

private def depthPathEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (m P : M.Domain) : Env M 7 :=
  ((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push m).push P

private def depthPathSchema : Project.UnarySchema 7 where
  body := .forallE (.forallE (.forallE (.forallE (.forallE (.forallE
    (.imp (parentPathFormula ⟨.bound 13,.bound 12,.bound 11,.bound 10,.bound 9⟩ (.bound 8) (.bound 7)
        (.bound 5) (.bound 6) (.bound 4) (.bound 3))
      (.imp (successorFormula (.bound 6) (.bound 2))
        (.imp (depthFormula ⟨.bound 13,.bound 12,.bound 11,.bound 10,.bound 9⟩ (.bound 8) (.bound 7) (.bound 4) (.bound 1))
          (.imp (depthFormula ⟨.bound 13,.bound 12,.bound 11,.bound 10,.bound 9⟩ (.bound 8) (.bound 7) (.bound 3) (.bound 0))
            (sumFormula (.bound 1) (.bound 2) (.bound 0)))))))))))
  freeClosed := by
    have hC : (⟨.bound 13,.bound 12,.bound 11,.bound 10,.bound 9⟩ : ExpressionData (Project.Term 14)).Closed :=
      ⟨rfl,rfl,rfl,rfl,rfl⟩
    have hPath := parentPathFormula_freeClosed hC (.bound 8) (.bound 7) (.bound 5) (.bound 6) (.bound 4) (.bound 3)
      rfl rfl rfl rfl rfl rfl
    have hDA := depthFormula_freeClosed hC (.bound 8) (.bound 7) (.bound 4) (.bound 1) rfl rfl rfl rfl
    have hDC := depthFormula_freeClosed hC (.bound 8) (.bound 7) (.bound 3) (.bound 0) rfl rfl rfl rfl
    have hSum := sumFormula_freeClosed (n := 14) (.bound 1) (.bound 2) (.bound 0) rfl rfl rfl
    simp [Definitional.Formula.FreeClosed,hPath,hDA,hDC,hSum,successorFormula,Project.Formula.forallMem,
      Project.Formula.subset]

private theorem depthPathSchema_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (C : ExpressionData M.Domain) (m P len : M.Domain) :
    Project.Formula.satisfies ((depthPathEnv C m P).push len) depthPathSchema.body ↔
      ∀ f a c e da dc, ParentPath M C m P f len a c → M.SuccessorOf len e →
        Depth M C m P a da → Depth M C m P c dc → Sum M da e dc := by
  simp only [depthPathSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    parentPathFormula_iff hM.1,successorFormula_iff hM.1,depthFormula_iff hM.1,sumFormula_iff hM]
  rfl

/-- 实际路径长度为e+1时，末点深度恰为起点深度加e。 -/
theorem depth_path_sum_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P f len a c e da dc : M.Domain}
    (hF : Forest M C.omega m P) (hPath : ParentPath M C m P f len a c) (hLen : M.SuccessorOf len e)
    (hA : Depth M C m P a da) (hCD : Depth M C m P c dc) : Sum M da e dc := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hAll := natural_induction_d hM depthPathSchema (depthPathEnv C m P) hC.omega
    (fun z hz => (depthPathSchema_iff hM C m P z).mpr (by
      intro f a c e da dc hPath _ _ _
      exact False.elim (hz C.zero (hPath.zero_in_length hM.1))))
    (fun len hLen ih next hs => (depthPathSchema_iff hM C m P next).mpr (by
      intro f a c e da dc hPath hNextE hA hCD
      have heq : len=e := Structure.SuccessorOf.predecessor_eq hM.1 (hw.mem hLen) hs hNextE
      subst e
      rcases hPath.peel_d hM hC with ⟨hOne,hac,_⟩ | ⟨last,g,b,hSucc,_,_,hOld,hParent⟩
      · subst c
        have hda := depth_unique_d hM hC hF hA hCD
        subst dc
        have hLenZero : len=C.zero := Structure.SuccessorOf.predecessor_eq hM.1 (hw.mem hLen) hs (hOne ▸ hC.one_succ)
        subst len
        exact sum_zero_d hM da hC.zero_empty
      · have hll : len=last := Structure.SuccessorOf.predecessor_eq hM.1 (hw.mem hLen) hs hSucc
        subst last
        rcases natural_cases hM hC.omega hLen with hEmpty | ⟨e',_,hE'⟩
        · exact False.elim (hEmpty C.zero (hOld.zero_in_length hM.1))
        · obtain ⟨db,hDB⟩ := depth_exists_d hM hC hF (hF.bounds hM.1 hParent).2
          have hIH := (depthPathSchema_iff hM C m P len).mp ih g a b e' da db hOld hE' hA hDB
          have hCB := depth_parent_successor_d hM hC hF hParent hCD hDB
          have hdaNat : M.mem da C.omega := hA.1
          obtain ⟨γ,_,hγ⟩ := natural_sum_exists_d hM hC.omega hdaNat hLen
          have hγb := sum_successor_d hM hE' hIH hγ
          have he := Structure.SuccessorOf.eq hM.1 hγb hCB
          exact he ▸ hγ))
  exact (depthPathSchema_iff hM C m P len).mp (hAll len hPath.length) f a c e da dc hPath hLen hA hCD

/-- 只运输路径上父项不低于起点的边；起点以下的父关系不作任何要求。 -/
theorem path_map_above_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m n P Q J f len a c x y : M.Domain}
    (hP : Forest M C.omega m P) (hn : M.mem n C.omega) (hJ : ColumnEmbedding M C.omega C.omega J)
    (hPath : ParentPath M C m P f len a c) (hax : MemPair M J a x) (hcy : MemPair M J c y) (hy : M.mem y n)
    (hEdges : ∀ d p u v, (d=c ∨ Ancestor M C m P d c) → (a=p ∨ M.mem a p) → MemPair M P d p →
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
      (hPath.values_above_start_d hM hC hP i p hIP)
      (hPath.edges i j p d hi hj hIP hJD hs)
      ((hG.rows j hj d (hmω d hd) v (hG.values.bounds hM.1 hJV).2 hJD).mp hJV)
      ((hG.rows i hi p (hmω p hp) u (hG.values.bounds hM.1 hIU).2 hIP).mp hIU)

/-- 映射链两端的深度增量相同；起点以下不比较。 -/
theorem depth_mapped_diff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m n P Q J a c x y da dc dx dy : M.Domain}
    (hP : Forest M C.omega m P) (hQ : Forest M C.omega n Q) (hJ : ColumnEmbedding M C.omega C.omega J)
    (hAC : a=c ∨ Ancestor M C m P a c) (hax : MemPair M J a x) (hcy : MemPair M J c y) (hy : M.mem y n)
    (hEdges : ∀ d p u v, (d=c ∨ Ancestor M C m P d c) → (a=p ∨ M.mem a p) → MemPair M P d p →
      MemPair M J d u → MemPair M J p v → MemPair M Q u v)
    (hDA : Depth M C m P a da) (hDC : Depth M C m P c dc) (hDX : Depth M C n Q x dx) (hDY : Depth M C n Q y dy) :
    ∃ e, M.mem e C.omega ∧ Sum M da e dc ∧ Sum M dx e dy := by
  rcases hAC with he | hAnc
  · subst c
    have hxy := hJ.graph.unique a x y hax hcy
    subst y
    have h1 := depth_unique_d hM hC hP hDA hDC
    have h2 := depth_unique_d hM hC hQ hDX hDY
    subst dc
    subst dy
    exact ⟨C.zero,hC.zero_nat,sum_zero_d hM da hC.zero_empty,sum_zero_d hM dx hC.zero_empty⟩
  · obtain ⟨_,len,hLen,f,_,hPath⟩ := hAnc
    obtain ⟨g,hG⟩ := path_map_above_d hM hC hP hQ.width hJ hPath hax hcy hy hEdges
    rcases natural_cases hM hC.omega hLen with hEmpty | ⟨e,he,hE⟩
    · exact False.elim (hEmpty C.zero (hPath.zero_in_length hM.1))
    · exact ⟨e,he,depth_path_sum_d hM hC hP hPath hE hDA hDC,depth_path_sum_d hM hC hQ hG hE hDX hDY⟩

/-- 若整条到根的链及根的无父性都被映射保持，则深度完全相等。 -/
theorem depth_mapped_eq_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m n P Q J c y d : M.Domain}
    (hP : Forest M C.omega m P) (hQ : Forest M C.omega n Q) (hJ : ColumnEmbedding M C.omega C.omega J)
    (hcy : MemPair M J c y) (hy : M.mem y n)
    (hEdges : ∀ d p u v, (d=c ∨ Ancestor M C m P d c) → MemPair M P d p →
      MemPair M J d u → MemPair M J p v → MemPair M Q u v)
    (hRoots : ∀ q x, (q=c ∨ Ancestor M C m P q c) → NoParent M m P q → MemPair M J q x → NoParent M n Q x)
    (hD : Depth M C m P c d) : Depth M C n Q y d := by
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨hd,q,hq,len,hLen,f,hf,hNo,hPath,hs⟩ := hD
  obtain ⟨x,_,hqx⟩ := hJ.graph.total q (hw.transitive m hP.width q hq)
  obtain ⟨g,hG⟩ := hPath.map_global_bounded_d hM hC hP hQ.width hJ hqx hcy hy hEdges
  have hQC : q=c ∨ Ancestor M C m P q c := by
    rcases hPath.endpoints_ordered_d hM hC hP with he | hlt
    · exact Or.inl he
    · exact Or.inr ⟨hlt,len,hLen,f,hf,hPath⟩
  exact ⟨hd,x,hG.start_bound hM.1,len,hLen,g,hG.sequence_member_d hM hC hQ.width,hRoots q x hQC hNo hqx,hG,hs⟩

/-- 两个同基加法的比较只由增量决定。 -/
theorem sum_compare_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {base e e' s t : M.Domain}
    (hb : M.mem base C.omega) (he : M.mem e C.omega) (he' : M.mem e' C.omega)
    (hS : Sum M base e s) (hT : Sum M base e' t) : (s=t ↔ e=e') ∧ (M.mem s t ↔ M.mem e e') := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hs := natural_sum_closed_d hM hC.omega hb he hS
  have ht := natural_sum_closed_d hM hC.omega hb he' hT
  refine ⟨⟨fun hst => natural_sum_cancel_left_d hM hC hb he he' hS (hst ▸ hT),fun hee => sum_unique_d hM hS (hee ▸ hT)⟩,
    ⟨fun hst => ?_,fun hlt => sum_strict_right_d hM (hw.mem hb) hS hT hlt⟩⟩
  rcases hw.wellOrder.linear.compare e he e' he' with heq | hlt | hgt
  · have hee := hM.1.eq_of_same_members e e' heq
    subst e'
    have := sum_unique_d hM hS hT
    subst t
    exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) s hst)
  · exact hlt
  · have hts := sum_strict_right_d hM (hw.mem hb) hT hS hgt
    exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) t ((hw.mem ht).transitive s hst t hts))

/-- 两组加法有同一对增量时，比较关系完全相同。 -/
theorem sum_pair_compare_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {base base' e e' s t s' t' : M.Domain}
    (hb : M.mem base C.omega) (hb' : M.mem base' C.omega) (he : M.mem e C.omega) (he' : M.mem e' C.omega)
    (hS : Sum M base e s) (hT : Sum M base e' t) (hS' : Sum M base' e s') (hT' : Sum M base' e' t') :
    (s=t ↔ s'=t') ∧ (M.mem s t ↔ M.mem s' t') := by
  have h1 := sum_compare_iff_d hM hC hb he he' hS hT
  have h2 := sum_compare_iff_d hM hC hb' he he' hS' hT'
  exact ⟨h1.1.trans h2.1.symm,h1.2.trans h2.2.symm⟩

/-- 严格祖先的深度严格更小。 -/
theorem depth_ancestor_lt_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P a c da dc : M.Domain}
    (hP : Forest M C.omega m P) (hAnc : Ancestor M C m P a c)
    (hDA : Depth M C m P a da) (hDC : Depth M C m P c dc) : M.mem da dc := by
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨hac,len,hLen,f,_,hPath⟩ := hAnc
  rcases natural_cases hM hC.omega hLen with hEmpty | ⟨e,he,hE⟩
  · exact False.elim (hEmpty C.zero (hPath.zero_in_length hM.1))
  · have hSum := depth_path_sum_d hM hC hP hPath hE hDA hDC
    have hePos : ∃ z, M.mem z e := by
      rcases natural_cases hM hC.omega he with hEmpty | ⟨e',_,hE'⟩
      · have heZ := hM.1.eq_of_same_members e C.zero (fun t => iff_of_false (hEmpty t) (hC.zero_empty t))
        subst e
        have hLenOne := Structure.SuccessorOf.eq hM.1 hE hC.one_succ
        subst len
        obtain ⟨last,hl,hLast,hFirst,hEnd⟩ := hPath.endpoints
        have hl0 := Structure.SuccessorOf.predecessor_eq hM.1 (hw.mem (hw.transitive C.one hC.one_nat last hl)) hLast hC.one_succ
        subst last
        have hca := hPath.graph.unique C.zero a c hFirst hEnd
        subst c
        exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) a hac)
      · exact ⟨e',hE'.predecessor_mem⟩
    exact sum_base_mem_d hM (hw.mem hDA.1) hSum hePos

end KP1Y.OneYFinite.LowerCanon
