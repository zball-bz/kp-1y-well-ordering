import KP1Y.ReflectionInitialRepresentation
import KP1Y.ReflectionLabelDomain
import KP1Y.AssignmentTuple

/-! 任意实际有限根图的最小可实现末标签；全局图秩由对象集合分离构造。 -/
namespace KP1Y.OneYRank
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Cardinal KP1Y.Assignments
open KP1Y.Reflection KP1Y.ReflectionModel
universe u

def LastValue (M : SetTheory.Structure.{u}) (zero m f a : M.Domain) : Prop :=
  (m=zero ∧ a=zero) ∨ ∃ last, M.mem last m ∧ M.SuccessorOf m last ∧ MemPair M f last a

def lastValueFormula {n : Nat} (zero m f a : Project.Term n) : Project.Formula 1 n :=
  .disj (.conj (Project.Formula.extensionalEq m zero) (Project.Formula.extensionalEq a zero))
    (Project.Formula.existsMem m (.conj (successorFormula m.weaken (.bound 0)) (memPairFormula f.weaken (.bound 0) a.weaken)))

theorem lastValueFormula_delta0 {n : Nat} (zero m f a : Project.Term n) : (lastValueFormula zero m f a).IsDelta0 :=
  .disj (.conj (.atom _ _ _) (.atom _ _ _)) (.existsMem _ (.conj (successorFormula_delta0 _ _) (memPairFormula_delta0 _ _ _)))

theorem lastValueFormula_freeClosed {n : Nat} (zero m f a : Project.Term n)
    (hz : zero.freeSupport=[]) (hm : m.freeSupport=[]) (hf : f.freeSupport=[]) (ha : a.freeSupport=[]) :
    (lastValueFormula zero m f a).FreeClosed := by
  simp [lastValueFormula,successorFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,
    Project.Formula.existsMem,Definitional.Formula.FreeClosed,hz,hm,hf,ha]

theorem lastValueFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (zero m f a : Project.Term n) : Project.Formula.satisfies e (lastValueFormula zero m f a) ↔
      LastValue M (zero.eval e) (m.eval e) (f.eval e) (a.eval e) := by
  simp only [lastValueFormula,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he,Project.Formula.satisfies_existsMem_iff,
    successorFormula_iff he,memPairFormula_iff he,Term.eval_weaken]
  rfl

theorem last_value_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {m f : M.Domain} (hLabel : Labeling M C.reflection m f) : ∃ a, M.mem a C.reflection.cap ∧ LastValue M (C.numbers 0) m f a := by
  rcases natural_cases hM hC.numerals.omega hLabel.length with hEmpty | ⟨last,_,hSucc⟩
  · have hm0 := hM.1.eq_of_same_members m (C.numbers 0) (fun x => iff_of_false (hEmpty x) (hC.numerals.zero_empty x))
    exact ⟨C.numbers 0,hC.reflection.cap.transitive C.top hC.cap.predecessor_mem _ (hC.number_top 0),Or.inl ⟨hm0,rfl⟩⟩
  · obtain ⟨a,ha,hAt⟩ := hLabel.graph.total last hSucc.predecessor_mem
    exact ⟨a,ha,Or.inr ⟨last,hSucc.predecessor_mem,hSucc,hAt⟩⟩

theorem LastValue.empty_value {M : SetTheory.Structure.{u}} {zero m f a : M.Domain} (hZero : ∀ x, ¬M.mem x zero)
    (hEmpty : m=zero) (h : LastValue M zero m f a) : a=zero := by
  rcases h with ⟨_,ha⟩ | ⟨last,hlast,_,_⟩
  · exact ha
  · exact False.elim (hZero last (hEmpty ▸ hlast))

theorem LastValue.all_values_le_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {m f a i x : M.Domain} (hLabel : Labeling M C.reflection m f) (h : LastValue M (C.numbers 0) m f a)
    (hAt : MemPair M f i x) : x=a ∨ M.mem x a := by
  have hi := (hLabel.graph.bounds hM.1 hAt).1
  rcases h with ⟨hm,_⟩ | ⟨last,hlast,hSucc,hLast⟩
  · exact False.elim (hC.numerals.zero_empty i (hm ▸ hi))
  · rcases (hSucc i).mp hi with hilast | he
    · exact Or.inr (hLabel.increasing i hi last hlast hilast x (hLabel.graph.bounds hM.1 hAt).2 a
        (hLabel.graph.bounds hM.1 hLast).2 hAt hLast)
    · have hilast := hM.1.eq_of_same_members i last he
      subst i
      exact Or.inl (hLabel.graph.unique last x a hAt hLast)

def RealizesLast (M : SetTheory.Structure.{u}) (C : ArticleData M.Domain) (m A a : M.Domain) : Prop :=
  ∃ f, M.mem f C.reflection.labels ∧ Representation M C.reflection C.table m A f ∧ LastValue M (C.numbers 0) m f a

def realizesLastFormula {n : Nat} (C : ArticleData (Project.Term n)) (m A a : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem C.reflection.labels
    (.conj (representationFormula C.reflection.weaken C.table.weaken m.weaken A.weaken (.bound 0))
      (lastValueFormula (C.numbers 0).weaken m.weaken (.bound 0) a.weaken))

theorem realizesLastFormula_delta0 {n : Nat} (C : ArticleData (Project.Term n)) (m A a : Project.Term n) :
    (realizesLastFormula C m A a).IsDelta0 := .existsMem _
      (.conj (representationFormula_delta0 _ _ _ _ _) (lastValueFormula_delta0 _ _ _ _))

theorem realizesLastFormula_freeClosed {n : Nat} {C : ArticleData (Project.Term n)} (hC : C.Closed)
    (m A a : Project.Term n) (hm : m.freeSupport=[]) (hA : A.freeSupport=[]) (ha : a.freeSupport=[]) :
    (realizesLastFormula C m A a).FreeClosed := by
  have hRep := representationFormula_freeClosed hC.reflection.weaken C.table.weaken m.weaken A.weaken (.bound 0)
    (by simpa using hC.table) (by simpa using hm) (by simpa using hA) rfl
  have hLast := lastValueFormula_freeClosed (C.numbers 0).weaken m.weaken (.bound 0) a.weaken
    (by simpa using hC.numbers 0) (by simpa using hm) rfl (by simpa using ha)
  simp [realizesLastFormula,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hC.reflection.labels,hRep,hLast]

theorem realizesLastFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ArticleData (Project.Term n)) (m A a : Project.Term n) : Project.Formula.satisfies e (realizesLastFormula C m A a) ↔
      RealizesLast M (C.eval e) (m.eval e) (A.eval e) (a.eval e) := by
  simp only [realizesLastFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    representationFormula_iff he,lastValueFormula_iff he,Data.eval_weaken,ArticleData.eval_reflection,Term.eval_weaken]
  rfl

theorem RealizesLast.in_cap_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {m A a : M.Domain} (h : RealizesLast M C m A a) : M.mem a C.reflection.cap := by
  obtain ⟨f,_,hRep,⟨_,ha⟩ | ⟨last,_,_,hLast⟩⟩ := h
  · exact ha ▸ hC.reflection.cap.transitive C.top hC.cap.predecessor_mem _ (hC.number_top 0)
  · exact (hRep.labeling.graph.bounds hM.1 hLast).2

def DiagramMinimum (M : SetTheory.Structure.{u}) (C : ArticleData M.Domain) (m A a : M.Domain) : Prop :=
  RealizesLast M C m A a ∧ ∀ b, M.mem b C.reflection.cap → RealizesLast M C m A b → a=b ∨ M.mem a b

def diagramMinimumFormula {n : Nat} (C : ArticleData (Project.Term n)) (m A a : Project.Term n) : Project.Formula 1 n :=
  .conj (realizesLastFormula C m A a) (Project.Formula.forallMem C.reflection.cap
    (.imp (realizesLastFormula C.weaken m.weaken A.weaken (.bound 0))
      (.disj (Project.Formula.extensionalEq a.weaken (.bound 0)) (.mem a.weaken (.bound 0)))))

theorem diagramMinimumFormula_delta0 {n : Nat} (C : ArticleData (Project.Term n)) (m A a : Project.Term n) :
    (diagramMinimumFormula C m A a).IsDelta0 := .conj (realizesLastFormula_delta0 _ _ _ _)
      (.forallMem _ (.imp (realizesLastFormula_delta0 _ _ _ _) (.disj (.atom _ _ _) (.mem _ _))))

theorem diagramMinimumFormula_freeClosed {n : Nat} {C : ArticleData (Project.Term n)} (hC : C.Closed)
    (m A a : Project.Term n) (hm : m.freeSupport=[]) (hA : A.freeSupport=[]) (ha : a.freeSupport=[]) :
    (diagramMinimumFormula C m A a).FreeClosed := by
  have hSelf := realizesLastFormula_freeClosed hC m A a hm hA ha
  have hOther := realizesLastFormula_freeClosed hC.weaken m.weaken A.weaken (.bound 0) (by simpa using hm) (by simpa using hA) rfl
  simp [diagramMinimumFormula,Project.Formula.forallMem,Definitional.Formula.FreeClosed,hC.reflection.cap,ha,hSelf,hOther]

theorem diagramMinimumFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ArticleData (Project.Term n)) (m A a : Project.Term n) : Project.Formula.satisfies e (diagramMinimumFormula C m A a) ↔
      DiagramMinimum M (C.eval e) (m.eval e) (A.eval e) (a.eval e) := by
  simp only [diagramMinimumFormula,Project.Formula.satisfies_conj_iff,realizesLastFormula_iff he,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he,Project.Formula.satisfies_mem_iff,ArticleData.eval_weaken,Term.eval_weaken]
  rfl

private def realizesLastSchema : Project.Delta0UnarySchema 26 where
  body := realizesLastFormula articleTerms.weaken.weaken.weaken (.bound 2) (.bound 1) (.bound 0)
  freeClosed := realizesLastFormula_freeClosed articleTerms_closed.weaken.weaken.weaken _ _ _ rfl rfl rfl
  delta0 := realizesLastFormula_delta0 _ _ _ _

theorem realized_last_set_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (C : ArticleData M.Domain) (m A : M.Domain) :
    ∃ Values, ∀ a, M.mem a Values ↔ M.mem a C.reflection.cap ∧ RealizesLast M C m A a := by
  let e := ((articleEnv C).push m).push A
  have hφ (a : M.Domain) : Project.Formula.satisfies (e.push a) realizesLastSchema.body ↔ RealizesLast M C m A a := by
    rw [realizesLastSchema,realizesLastFormula_iff hM.1]
    rfl
  obtain ⟨Values,hValues⟩ := SetTheory.KP.separation_exists_d (KP1Y.models_weakKP hM) realizesLastSchema e C.reflection.cap
  exact ⟨Values,fun a => by simpa only [hφ] using hValues a⟩

theorem diagram_minimum_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {S : ArticleStructure M.Domain} (hS : S.Valid M C) (hκ : UncountableOrdinal M C.reflection.omega C.top)
    {m A : M.Domain} (hDiagram : Diagram M C.reflection m A) : ∃ a, M.mem a C.top ∧ DiagramMinimum M C m A a := by
  obtain ⟨f,hf,hRep,hBelow⟩ := initial_representation_exists_d hM hC hS hκ hDiagram
  obtain ⟨b,hb,hLast⟩ := last_value_exists_d hM hC hRep.labeling
  have hbTop : M.mem b C.top := by
    rcases hLast with ⟨_,he⟩ | ⟨last,_,_,hAt⟩
    · exact he ▸ hC.number_top 0
    · exact hBelow.at hM.1 hRep.labeling.graph hAt
  obtain ⟨Values,hValues⟩ := realized_last_set_exists_d hM C m A
  obtain ⟨a,ha,hLeast⟩ := hC.reflection.cap.wellOrder.least Values
    (fun x hx => ((hValues x).mp hx).1) ⟨b,(hValues b).mpr ⟨hb,f,hf,hRep,hLast⟩⟩
  have hMin : DiagramMinimum M C m A a := by
    refine ⟨((hValues a).mp ha).2,?_⟩
    intro x hx hRealized
    rcases hLeast x ((hValues x).mpr ⟨hx,hRealized⟩) with he | hLess
    · exact Or.inl (hM.1.eq_of_same_members a x he)
    · exact Or.inr hLess
  have hAB := hMin.2 b hb ⟨f,hf,hRep,hLast⟩
  have haTop : M.mem a C.top := by
    rcases hAB with he | hLess
    · exact he.symm ▸ hbTop
    · exact hC.top.transitive b hbTop a hLess
  exact ⟨a,haTop,hMin⟩

theorem DiagramMinimum.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {m A a b : M.Domain} (hA : DiagramMinimum M C m A a) (hB : DiagramMinimum M C m A b) : a=b := by
  rcases hA.2 b (hB.1.in_cap_d hM hC) hB.1 with he | hab
  · exact he
  · rcases hB.2 a (hA.1.in_cap_d hM hC) hA.1 with he | hba
    · exact he.symm
    · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) a
        ((hC.reflection.cap.mem (hA.1.in_cap_d hM hC)).transitive b hba a hab))

theorem DiagramMinimum.empty_value {M : SetTheory.Structure.{u}} {C : ArticleData M.Domain} (hC : C.Valid M)
    {m A a : M.Domain} (h : DiagramMinimum M C m A a) (hm : m=C.numbers 0) : a=C.numbers 0 := by
  obtain ⟨_,_,_,hLast⟩ := h.1
  exact hLast.empty_value hC.numerals.zero_empty hm

theorem DiagramMinimum.nonempty_above_omega_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (_hC : C.Valid M) {m A a : M.Domain} (h : DiagramMinimum M C m A a)
    (hm : m≠C.numbers 0) : M.mem C.reflection.omega a := by
  obtain ⟨f,_,hRep,⟨he,_⟩ | ⟨last,hlast,_,hLast⟩⟩ := h.1
  · exact False.elim (hm he)
  · exact hRep.labeling.above last hlast a (hRep.labeling.graph.bounds hM.1 hLast).2 hLast

theorem DiagramMinimum.realized_below_top_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {m A a : M.Domain} (h : DiagramMinimum M C m A a) (ha : M.mem a C.top) :
    ∃ f, M.mem f C.reflection.labels ∧ Representation M C.reflection C.table m A f ∧
      Below M C.reflection m f C.top ∧ LastValue M (C.numbers 0) m f a := by
  obtain ⟨f,hf,hRep,hLast⟩ := h.1
  refine ⟨f,hf,hRep,?_,hLast⟩
  intro i _ x _ hAt
  rcases hLast.all_values_le_d hM hC hRep.labeling hAt with he | hLess
  · exact he.symm ▸ ha
  · exact hC.top.transitive a ha x hLess

theorem DiagramMinimum.in_top_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    (hκ : UncountableOrdinal M C.reflection.omega C.top) {m A a : M.Domain} (h : DiagramMinimum M C m A a) : M.mem a C.top := by
  obtain ⟨f,_,hRep,_⟩ := h.1
  obtain ⟨S,hS⟩ := article_structure_exists_d hM hC
  obtain ⟨b,hb,hMin⟩ := diagram_minimum_exists_d hM hC hS hκ hRep.diagram
  exact (h.unique_d hM hC hMin).symm ▸ hb

theorem DiagramMinimum.nonempty_positive_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {m A a : M.Domain} (h : DiagramMinimum M C m A a)
    (hm : m≠C.numbers 0) : M.mem (C.numbers 0) a :=
  (hC.reflection.cap.mem (h.1.in_cap_d hM hC)).transitive C.reflection.omega (h.nonempty_above_omega_d hM hC hm)
    (C.numbers 0) (hC.numerals.natural 0)

theorem DiagramMinimum.le_representation_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {m A a f b : M.Domain} (h : DiagramMinimum M C m A a)
    (hRep : Representation M C.reflection C.table m A f) (hLast : LastValue M (C.numbers 0) m f b) : a=b ∨ M.mem a b := by
  have hRealizes : RealizesLast M C m A b := ⟨f,hRep.labeling.sequence hC.reflection,hRep,hLast⟩
  exact h.2 b (hRealizes.in_cap_d hM hC) hRealizes

def HasDiagramCode (M : SetTheory.Structure.{u}) (C : ArticleData M.Domain) (code : M.Domain) : Prop :=
  ∃ m, M.mem m C.reflection.omega ∧ ∃ A, M.mem A C.reflection.edgeLists ∧ Codes M code m A ∧ Diagram M C.reflection m A

def DiagramCodeSpace (M : SetTheory.Structure.{u}) (C : ArticleData M.Domain) (D : M.Domain) : Prop :=
  ∀ code, M.mem code D ↔ HasDiagramCode M C code

def diagramCodeFormula {n : Nat} (C : ArticleData (Project.Term n)) (code : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem C.reflection.omega (Project.Formula.existsMem C.reflection.edgeLists.weaken
    (.conj (codeFormula code.weaken.weaken (.bound 1) (.bound 0)) (diagramFormula C.reflection.weaken.weaken (.bound 1) (.bound 0))))

theorem diagramCodeFormula_delta0 {n : Nat} (C : ArticleData (Project.Term n)) (code : Project.Term n) :
    (diagramCodeFormula C code).IsDelta0 := .existsMem _ (.existsMem _ (.conj (codeFormula_delta0 _ _ _) (diagramFormula_delta0 _ _ _)))

theorem diagramCodeFormula_freeClosed {n : Nat} {C : ArticleData (Project.Term n)} (hC : C.Closed)
    (code : Project.Term n) (hcode : code.freeSupport=[]) : (diagramCodeFormula C code).FreeClosed := by
  have hDiagram := diagramFormula_freeClosed hC.reflection.weaken.weaken (.bound 1) (.bound 0) rfl rfl
  simp [diagramCodeFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,
    Definitional.Formula.FreeClosed,hC.reflection.omega,hC.reflection.edgeLists,hcode,hDiagram]

theorem diagramCodeFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ArticleData (Project.Term n)) (code : Project.Term n) : Project.Formula.satisfies e (diagramCodeFormula C code) ↔ HasDiagramCode M (C.eval e) (code.eval e) := by
  simp only [diagramCodeFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,codeFormula_iff he,
    diagramFormula_iff he,Data.eval_weaken,ArticleData.eval_reflection,Term.eval_weaken]
  rfl

private def diagramCodeSchema : Project.Delta0UnarySchema 24 where
  body := diagramCodeFormula articleTerms.weaken (.bound 0)
  freeClosed := diagramCodeFormula_freeClosed articleTerms_closed.weaken _ rfl
  delta0 := diagramCodeFormula_delta0 _ _

theorem diagram_code_space_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (C : ArticleData M.Domain) :
    ∃ D, DiagramCodeSpace M C D := by
  obtain ⟨Pairs,hPairs⟩ := product_exists hM C.reflection.omega C.reflection.edgeLists
  obtain ⟨D,hD⟩ := SetTheory.KP.separation_exists_d (KP1Y.models_weakKP hM) diagramCodeSchema (articleEnv C) Pairs
  have hφ (code : M.Domain) : Project.Formula.satisfies ((articleEnv C).push code) diagramCodeSchema.body ↔ HasDiagramCode M C code := by
    rw [diagramCodeSchema,diagramCodeFormula_iff hM.1]
    rfl
  refine ⟨D,?_⟩
  intro code
  have hd := hD code
  rw [hφ] at hd
  refine hd.trans ⟨And.right,?_⟩
  rintro hCode
  obtain ⟨m,hm,A,hA,hPair,hDiagram⟩ := hCode
  exact ⟨(hPairs code).mpr ⟨m,hm,A,hA,hPair⟩,m,hm,A,hA,hPair,hDiagram⟩

def CodedMinimum (M : SetTheory.Structure.{u}) (C : ArticleData M.Domain) (code a : M.Domain) : Prop :=
  ∃ m, M.mem m C.reflection.omega ∧ ∃ A, M.mem A C.reflection.edgeLists ∧ Codes M code m A ∧ DiagramMinimum M C m A a

def codedMinimumFormula {n : Nat} (C : ArticleData (Project.Term n)) (code a : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem C.reflection.omega (Project.Formula.existsMem C.reflection.edgeLists.weaken
    (.conj (codeFormula code.weaken.weaken (.bound 1) (.bound 0)) (diagramMinimumFormula C.weaken.weaken (.bound 1) (.bound 0) a.weaken.weaken)))

theorem codedMinimumFormula_delta0 {n : Nat} (C : ArticleData (Project.Term n)) (code a : Project.Term n) :
    (codedMinimumFormula C code a).IsDelta0 := .existsMem _ (.existsMem _ (.conj (codeFormula_delta0 _ _ _) (diagramMinimumFormula_delta0 _ _ _ _)))

theorem codedMinimumFormula_freeClosed {n : Nat} {C : ArticleData (Project.Term n)} (hC : C.Closed)
    (code a : Project.Term n) (hcode : code.freeSupport=[]) (ha : a.freeSupport=[]) : (codedMinimumFormula C code a).FreeClosed := by
  have hMin := diagramMinimumFormula_freeClosed hC.weaken.weaken (.bound 1) (.bound 0) a.weaken.weaken rfl rfl (by simpa using ha)
  simp [codedMinimumFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,
    Definitional.Formula.FreeClosed,hC.reflection.omega,hC.reflection.edgeLists,hcode,hMin]

theorem codedMinimumFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ArticleData (Project.Term n)) (code a : Project.Term n) : Project.Formula.satisfies e (codedMinimumFormula C code a) ↔
      CodedMinimum M (C.eval e) (code.eval e) (a.eval e) := by
  simp only [codedMinimumFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,codeFormula_iff he,
    diagramMinimumFormula_iff he,ArticleData.eval_weaken,Term.eval_weaken]
  rfl

theorem CodedMinimum.has_code {M : SetTheory.Structure.{u}} {C : ArticleData M.Domain} {code a : M.Domain}
    (h : CodedMinimum M C code a) : HasDiagramCode M C code := by
  obtain ⟨m,hm,A,hA,hCode,hMin⟩ := h
  obtain ⟨_,_,hRep,_⟩ := hMin.1
  exact ⟨m,hm,A,hA,hCode,hRep.diagram⟩

theorem coded_minimum_at_code_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ArticleData M.Domain}
    {code m A a : M.Domain} (hCode : Codes M code m A) : CodedMinimum M C code a ↔ DiagramMinimum M C m A a := by
  constructor
  · rintro ⟨m',_,A',_,hCode',hMin⟩
    obtain ⟨hmm,hAA⟩ := codes_injective he hCode hCode'
    subst m'
    subst A'
    exact hMin
  · intro hMin
    obtain ⟨_,_,hRep,_⟩ := hMin.1
    exact ⟨m,hRep.diagram.1,A,hRep.diagram.2.1,hCode,hMin⟩

theorem CodedMinimum.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {code a b : M.Domain} (h : CodedMinimum M C code a) (h' : CodedMinimum M C code b) : a=b := by
  obtain ⟨_,_,_,_,hCode,hMin⟩ := h
  exact hMin.unique_d hM hC ((coded_minimum_at_code_iff hM.1 hCode).mp h')

theorem CodedMinimum.in_top_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    (hκ : UncountableOrdinal M C.reflection.omega C.top) {code a : M.Domain} (h : CodedMinimum M C code a) : M.mem a C.top := by
  obtain ⟨_,_,_,_,_,hMin⟩ := h
  exact hMin.in_top_d hM hC hκ

private def codedMinimumSchema : Project.Delta0BinarySchema 24 where
  body := codedMinimumFormula articleTerms.weaken.weaken (.bound 1) (.bound 0)
  freeClosed := codedMinimumFormula_freeClosed articleTerms_closed.weaken.weaken _ _ rfl rfl
  delta0 := codedMinimumFormula_delta0 _ _ _

theorem diagram_minimum_rank_graph_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    (hκ : UncountableOrdinal M C.reflection.omega C.top) {D : M.Domain} (hD : DiagramCodeSpace M C D) :
    ∃ Rank, Graph M Rank D C.top ∧ ∀ code a, MemPair M Rank code a ↔ CodedMinimum M C code a := by
  obtain ⟨S,hS⟩ := article_structure_exists_d hM hC
  have hφ (code a : M.Domain) : Project.Formula.satisfies (((articleEnv C).push code).push a) codedMinimumSchema.body ↔ CodedMinimum M C code a := by
    rw [codedMinimumSchema,codedMinimumFormula_iff hM.1]
    rfl
  obtain ⟨Rank,hSupport,hRaw⟩ := relation_comprehension_d hM codedMinimumSchema (articleEnv C) D C.top
  have hRows (code a : M.Domain) : MemPair M Rank code a ↔ CodedMinimum M C code a := by
    have hr := hRaw code a
    rw [hφ] at hr
    exact hr.trans ⟨fun h => h.2.2,fun h => ⟨(hD code).mpr h.has_code,h.in_top_d hM hC hκ,h⟩⟩
  refine ⟨Rank,⟨hSupport,?_,?_⟩,hRows⟩
  · intro code hcode
    obtain ⟨m,hm,A,hA,hCode,hDiagram⟩ := (hD code).mp hcode
    obtain ⟨a,ha,hMin⟩ := diagram_minimum_exists_d hM hC hS hκ hDiagram
    exact ⟨a,ha,(hRows code a).mpr ⟨m,hm,A,hA,hCode,hMin⟩⟩
  · intro code a b hA hB
    exact ((hRows code a).mp hA).unique_d hM hC ((hRows code b).mp hB)

theorem diagram_minimum_rank_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    (hκ : UncountableOrdinal M C.reflection.omega C.top) : ∃ D Rank, DiagramCodeSpace M C D ∧ Graph M Rank D C.top ∧
      ∀ code a, MemPair M Rank code a ↔ CodedMinimum M C code a := by
  obtain ⟨D,hD⟩ := diagram_code_space_exists_d hM C
  obtain ⟨Rank,hRank,hRows⟩ := diagram_minimum_rank_graph_d hM hC hκ hD
  exact ⟨D,Rank,hD,hRank,hRows⟩

theorem diagram_function_rank_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) (hκ : UncountableOrdinal M C.reflection.omega C.top)
    {X D F : M.Domain} (hD : DiagramCodeSpace M C D) (hF : Graph M F X D) :
    ∃ μ, Graph M μ X C.top ∧ ∀ x, M.mem x X → ∀ code, MemPair M F x code → ∀ m A, Codes M code m A →
      ∀ a, MemPair M μ x a ↔ DiagramMinimum M C m A a := by
  obtain ⟨Rank,hRank,hRankRows⟩ := diagram_minimum_rank_graph_d hM hC hκ hD
  obtain ⟨μ,hμ⟩ := tuple_value_exists_d hM hF hRank
  refine ⟨μ,hμ.values,?_⟩
  intro x hx code hCodeAt m A hCode a
  classical
  by_cases ha : M.mem a C.top
  · exact (hμ.rows x hx code (hF.bounds hM.1 hCodeAt).2 a ha hCodeAt).trans
      ((hRankRows code a).trans (coded_minimum_at_code_iff hM.1 hCode))
  · exact iff_of_false (fun hAt => ha (hμ.values.bounds hM.1 hAt).2) (fun hMin => ha (hMin.in_top_d hM hC hκ))

end KP1Y.OneYRank
