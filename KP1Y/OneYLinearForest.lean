import KP1Y.OneYForestSelection

/-! 共享的内部线性父森林：前驱边、严格祖先等于<、线性前缀的深度等于列号。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
universe u

def LinearForest (M : SetTheory.Structure.{u}) (w m P : M.Domain) : Prop :=
  Forest M w m P ∧ ∀ c p, MemPair M P c p ↔ M.mem c m ∧ M.SuccessorOf c p

/-- k 可以大于载域宽度；只要求载域中位于 k 以前的列为线性前驱行。 -/
def LinearPrefix (M : SetTheory.Structure.{u}) (m P k : M.Domain) : Prop :=
  ∀ c, M.mem c m → M.mem c k → ∀ p, MemPair M P c p ↔ M.SuccessorOf c p

private def linearParentSchema : Project.Delta0BinarySchema 0 where
  body := successorFormula (.bound 1) (.bound 0)
  freeClosed := by simp [successorFormula,Project.Formula.forallMem,Definitional.Formula.FreeClosed]
  delta0 := successorFormula_delta0 _ _

private theorem linearParentSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (e : Env M 0) (c p : M.Domain) :
    Project.Formula.satisfies ((e.push c).push p) linearParentSchema.body ↔ M.SuccessorOf c p := by
  rw [linearParentSchema,successorFormula_iff he]
  rfl

theorem linear_forest_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {w m : M.Domain} (hw : M.IsOmega w) (hm : M.mem m w) : ∃ P, LinearForest M w m P := by
  let e : Env M 0 := ⟨Fin.elim0,fun _ => w⟩
  obtain ⟨P,hSupport,hP⟩ := relation_comprehension_d hM linearParentSchema e m m
  have hRows : ∀ c p, MemPair M P c p ↔ M.mem c m ∧ M.SuccessorOf c p := by
    intro c p
    have h := hP c p
    rw [linearParentSchema_iff hM.1] at h
    exact h.trans ⟨fun h => ⟨h.1,h.2.2⟩,fun h =>
      ⟨h.1,((omega_isOrdinal_d hM hw).mem hm).transitive c h.1 p h.2.predecessor_mem,h.2⟩⟩
  refine ⟨P,⟨hm,hSupport,?_,?_⟩,hRows⟩
  · intro c p q hcp hcq
    have hp := (hRows c p).mp hcp
    have hq := (hRows c q).mp hcq
    have hpm := ((omega_isOrdinal_d hM hw).mem hm).transitive c hp.1 p hp.2.predecessor_mem
    exact Structure.SuccessorOf.predecessor_eq hM.1 (((omega_isOrdinal_d hM hw).mem hm).mem hpm) hp.2 hq.2
  · intro c p hcp
    exact ((hRows c p).mp hcp).2.predecessor_mem

theorem linear_forest_unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {w m P Q : M.Domain} (hP : LinearForest M w m P) (hQ : LinearForest M w m Q) : P=Q :=
  hP.1.ext he hQ.1 (fun c p => (hP.2 c p).trans (hQ.2 c p).symm)

theorem LinearForest.prefix {M : SetTheory.Structure.{u}} {w m P k : M.Domain}
    (hP : LinearForest M w m P) : LinearPrefix M m P k :=
  fun c hc _ p => (hP.2 c p).trans ⟨And.right,fun hs => ⟨hc,hs⟩⟩

private def linearEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (m P k : M.Domain) : Env M 8 :=
  (((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push m).push P).push k

private def linearAncestorSchema : Project.UnarySchema 8 where
  body := .imp (.mem (.bound 0) (.bound 3)) (.imp (.mem (.bound 0) (.bound 1))
    (Project.Formula.forallMem (.bound 0)
      (ancestorFormula ⟨.bound 9,.bound 8,.bound 7,.bound 6,.bound 5⟩ (.bound 4) (.bound 3) (.bound 0) (.bound 1))))
  freeClosed := by
    have hAnc := ancestorFormula_freeClosed
      (show (⟨.bound 9,.bound 8,.bound 7,.bound 6,.bound 5⟩ : ExpressionData (Project.Term 10)).Closed from ⟨rfl,rfl,rfl,rfl,rfl⟩)
      (.bound 4) (.bound 3) (.bound 0) (.bound 1) rfl rfl rfl rfl
    simp [Project.Formula.forallMem,Definitional.Formula.FreeClosed,hAnc]

private theorem linearAncestorSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (m P k c : M.Domain) :
    Project.Formula.satisfies ((linearEnv C m P k).push c) linearAncestorSchema.body ↔
      (M.mem c m → M.mem c k → ∀ a, M.mem a c → Ancestor M C m P a c) := by
  simp only [linearAncestorSchema,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_forallMem_iff,ancestorFormula_iff he]
  rfl

theorem linear_prefix_ancestor_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P k a c : M.Domain}
    (hP : Forest M C.omega m P) (hk : M.mem k C.omega) (hLinear : LinearPrefix M m P k)
    (hc : M.mem c m) (hck : M.mem c k) (hac : M.mem a c) : Ancestor M C m P a c := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hAll := KP1Y.induction_d hM linearAncestorSchema (linearEnv C m P k)
    (fun c ih => (linearAncestorSchema_iff hM.1 C m P k c).mpr (by
      intro hc hck a hac
      have hcw := hw.transitive m hP.width c hc
      rcases natural_cases hM hC.omega hcw with he | ⟨p,_,hs⟩
      · exact False.elim (he a hac)
      · have hpm := (hw.mem hP.width).transitive c hc p hs.predecessor_mem
        have hpk := (hw.mem hk).transitive c hck p hs.predecessor_mem
        have hParent := (hLinear c hc hck p).mpr hs
        rcases (hs a).mp hac with hap | hap
        · exact ancestor_step_d hM hC hP
            ((linearAncestorSchema_iff hM.1 C m P k p).mp (ih p hs.predecessor_mem) hpm hpk a hap) hParent
        · have he := hM.1.eq_of_same_members a p hap
          subst a
          exact ancestor_direct_d hM hC hP hParent))
  exact (linearAncestorSchema_iff hM.1 C m P k c).mp (hAll c) hc hck a hac

theorem linear_prefix_ancestor_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P k a c : M.Domain}
    (hP : Forest M C.omega m P) (hk : M.mem k C.omega) (hLinear : LinearPrefix M m P k)
    (hc : M.mem c m) (hck : M.mem c k) : Ancestor M C m P a c ↔ M.mem a c :=
  ⟨And.left,fun hac => linear_prefix_ancestor_d hM hC hP hk hLinear hc hck hac⟩

theorem linear_forest_ancestor_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P a c : M.Domain}
    (hP : LinearForest M C.omega m P) (hc : M.mem c m) : Ancestor M C m P a c ↔ M.mem a c :=
  linear_prefix_ancestor_iff_d hM hC hP.1 hP.1.width hP.prefix hc hc

private def linearDepthSchema : Project.UnarySchema 8 where
  body := .imp (.mem (.bound 0) (.bound 1)) (.forallE (.imp
    (depthFormula ⟨.bound 9,.bound 8,.bound 7,.bound 6,.bound 5⟩ (.bound 4) (.bound 3) (.bound 1) (.bound 0))
    (Project.Formula.extensionalEq (.bound 0) (.bound 1))))
  freeClosed := by
    have hDepth := depthFormula_freeClosed
      (show (⟨.bound 9,.bound 8,.bound 7,.bound 6,.bound 5⟩ : ExpressionData (Project.Term 10)).Closed from ⟨rfl,rfl,rfl,rfl,rfl⟩)
      (.bound 4) (.bound 3) (.bound 1) (.bound 0) rfl rfl rfl rfl
    simp [Definitional.Formula.FreeClosed,hDepth]

private theorem linearDepthSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (m P k c : M.Domain) :
    Project.Formula.satisfies ((linearEnv C m P k).push c) linearDepthSchema.body ↔
      (M.mem c k → ∀ d, Depth M C m P c d → d=c) := by
  simp only [linearDepthSchema,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_forall_iff,depthFormula_iff he,Project.Formula.satisfies_extensionalEq_iff_eq he]
  rfl

theorem linear_prefix_depth_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P k c d : M.Domain}
    (hP : Forest M C.omega m P) (hk : M.mem k C.omega) (hLinear : LinearPrefix M m P k)
    (hck : M.mem c k) (hd : Depth M C m P c d) : d=c := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hAll := KP1Y.induction_d hM linearDepthSchema (linearEnv C m P k)
    (fun c ih => (linearDepthSchema_iff hM.1 C m P k c).mpr (by
      intro hck d hd
      have hc := hd.column_bound hM.1
      have hcw := hw.transitive m hP.width c hc
      rcases natural_cases hM hC.omega hcw with he | ⟨p,_,hs⟩
      · have hNo : NoParent M m P c := fun p _ hcp => he p (hP.left c p hcp)
        have hdz := depth_of_no_parent_d hM hC hP hNo hd
        have hcz := hM.1.eq_of_same_members c C.zero (fun x => iff_of_false (he x) (hC.zero_empty x))
        exact hdz.trans hcz.symm
      · have hpk := (hw.mem hk).transitive c hck p hs.predecessor_mem
        have hParent := (hLinear c hc hck p).mpr hs
        obtain ⟨e,he,hSucc⟩ := depth_parent_predecessor_d hM hC hP hParent hd
        have hep := (linearDepthSchema_iff hM.1 C m P k p).mp (ih p hs.predecessor_mem) hpk e he
        subst e
        exact Structure.SuccessorOf.eq hM.1 hSucc hs))
  exact (linearDepthSchema_iff hM.1 C m P k c).mp (hAll c) hck d hd

theorem linear_forest_depth_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P c d : M.Domain}
    (hP : LinearForest M C.omega m P) (hd : Depth M C m P c d) : d=c :=
  linear_prefix_depth_d hM hC hP.1 hP.1.width hP.prefix (hd.column_bound hM.1) hd

/-- 任意祖先都不在直接父的右边，供 Frame 的最右深度选择使用。 -/
theorem ancestor_le_parent_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P a c p : M.Domain}
    (hP : Forest M C.omega m P) (hParent : MemPair M P c p)
    (hAnc : Ancestor M C m P a c) : a=p ∨ M.mem a p := by
  obtain ⟨q,hq,ha⟩ := ancestor_parent_cases_d hM hC hP hAnc
  have hqp := hP.unique c q p hq hParent
  subst q
  exact ha.imp id And.left

end KP1Y.OneYFinite
