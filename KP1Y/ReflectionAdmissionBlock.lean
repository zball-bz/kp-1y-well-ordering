import KP1Y.ReflectionBinaryBlockTruth
import KP1Y.ReflectionGroundParameters

/-! Adm 的实际原子块：较低层为真等式，同层 cut 前比较根标签，其余为假自小于。
K 仅用于构造固定代码图，不是结构常元。本模块不限制内部图边的层号。
-/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments KP1Y.Satisfaction KP1Y.Reflection
open KP1Y.Ranking
universe u

def AdmissionCode (M : SetTheory.Structure.{u}) (zero one two Variables scope K cut k q name root code : M.Domain) : Prop := by
  classical
  exact if M.mem k K then BinaryCode false M zero one two Variables scope name name code
    else if k=K ∧ M.mem q cut then BinaryCode true M zero one two Variables scope name root code
    else BinaryCode true M zero one two Variables scope name name code

def admissionCodeFormula {d : Nat} (zero one two Variables scope K cut k q name root code : Project.Term d) : Project.Formula 1 d :=
  .disj (.conj (.mem k K) (binaryCodeFormula false zero one two Variables scope name name code))
    (.conj (.neg (.mem k K))
      (.disj (.conj (.conj (Project.Formula.extensionalEq k K) (.mem q cut))
          (binaryCodeFormula true zero one two Variables scope name root code))
        (.conj (.neg (.conj (Project.Formula.extensionalEq k K) (.mem q cut)))
          (binaryCodeFormula true zero one two Variables scope name name code))))

theorem admissionCodeFormula_delta0 {d : Nat} (zero one two Variables scope K cut k q name root code : Project.Term d) :
    (admissionCodeFormula zero one two Variables scope K cut k q name root code).IsDelta0 :=
  .disj (.conj (.mem _ _) (binaryCodeFormula_delta0 _ _ _ _ _ _ _ _ _))
    (.conj (.neg (.mem _ _)) (.disj (.conj (.conj (.atom _ _ _) (.mem _ _))
      (binaryCodeFormula_delta0 _ _ _ _ _ _ _ _ _))
      (.conj (.neg (.conj (.atom _ _ _) (.mem _ _))) (binaryCodeFormula_delta0 _ _ _ _ _ _ _ _ _))))

theorem admissionCodeFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {d : Nat}
    (e : Env M d) (zero one two Variables scope K cut k q name root code : Project.Term d) :
    Project.Formula.satisfies e (admissionCodeFormula zero one two Variables scope K cut k q name root code) ↔
      AdmissionCode M (zero.eval e) (one.eval e) (two.eval e) (Variables.eval e) (scope.eval e)
        (K.eval e) (cut.eval e) (k.eval e) (q.eval e) (name.eval e) (root.eval e) (code.eval e) := by
  classical
  simp only [admissionCodeFormula, Project.Formula.satisfies_disj_iff, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff, Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he, binaryCodeFormula_iff he]
  by_cases hk : M.mem (k.eval e) (K.eval e)
  · simp only [AdmissionCode,hk,↓reduceIte,true_and,not_true_eq_false,false_and,or_false]
  · simp only [AdmissionCode,hk,↓reduceIte,false_and,not_false_eq_true,true_and,false_or]
    by_cases hs : k.eval e=K.eval e ∧ M.mem (q.eval e) (cut.eval e) <;>
      simp only [hs,↓reduceIte,true_and,not_true_eq_false,false_and,or_false,not_false_eq_true,false_or]

theorem admission_code_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {A : M.Domain} {D : RelationalData M.Domain}
    (hD : ArticleInterpretation M C A D) {scope K cut k q name root : M.Domain}
    (hb : M.mem scope D.omega) (hn : M.mem name scope) (hr : M.mem root scope) :
    ∃ code, AdmissionCode M (C.numbers 0) (C.numbers 1) (C.numbers 2) D.variables scope K cut k q name root code := by
  classical
  by_cases hk : M.mem k K
  · simpa only [AdmissionCode,hk,↓reduceIte] using binary_code_exists_d hM hC hD false hb hn hn
  · by_cases hs : k=K ∧ M.mem q cut
    · simp only [AdmissionCode,hk,↓reduceIte]
      simpa only [if_pos hs] using binary_code_exists_d hM hC hD true hb hn hr
    · simp only [AdmissionCode,hk,↓reduceIte]
      simpa only [if_neg hs] using binary_code_exists_d hM hC hD true hb hn hn

theorem AdmissionCode.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {D : RelationalData M.Domain}
    {scope K cut k q name root a b : M.Domain}
    (h : AdmissionCode M (C.numbers 0) (C.numbers 1) (C.numbers 2) D.variables scope K cut k q name root a)
    (h' : AdmissionCode M (C.numbers 0) (C.numbers 1) (C.numbers 2) D.variables scope K cut k q name root b) : a=b := by
  classical
  by_cases hk : M.mem k K
  · simp only [AdmissionCode,hk,↓reduceIte] at h h'
    exact h.unique_d hM hC h'
  · simp only [AdmissionCode,hk,↓reduceIte] at h h'
    by_cases hs : k=K ∧ M.mem q cut
    · simp only [if_pos hs] at h h'
      exact h.unique_d hM hC h'
    · simp only [if_neg hs] at h h'
      exact h.unique_d hM hC h'

theorem AdmissionCode.scoped_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {A : M.Domain} {D : RelationalData M.Domain}
    (hD : ArticleInterpretation M C A D) {scope K cut k q name root a : M.Domain}
    (hb : M.mem scope D.omega)
    (h : AdmissionCode M (C.numbers 0) (C.numbers 1) (C.numbers 2) D.variables scope K cut k q name root a) :
    ScopedAtom M D a scope := by
  classical
  by_cases hk : M.mem k K
  · simp only [AdmissionCode,hk,↓reduceIte] at h
    exact h.scoped_d hM hC hD hb
  · simp only [AdmissionCode,hk,↓reduceIte] at h
    by_cases hs : k=K ∧ M.mem q cut
    · simp only [if_pos hs] at h
      exact h.scoped_d hM hC hD hb
    · simp only [if_neg hs] at h
      exact h.scoped_d hM hC hD hb

private def admissionBlockSchema : Project.Delta0BinarySchema 13 where
  body := Project.Formula.existsMem (.bound 3) (Project.Formula.existsMem (.bound 3)
    (Project.Formula.existsMem (.bound 4) (Project.Formula.existsMem (.bound 13)
      (.conj (Project.Formula.existsMem (.bound 10)
          (.conj (memPairFormula (.bound 12) (.bound 6) (.bound 0))
            (packetFormula (.bound 0) (.bound 4) (.bound 3) (.bound 2))))
        (.conj (memPairFormula (.bound 9) (.bound 2) (.bound 0))
          (admissionCodeFormula (.bound 15) (.bound 16) (.bound 17) (.bound 18) (.bound 14)
            (.bound 13) (.bound 12) (.bound 3) (.bound 2) (.bound 0) (.bound 8) (.bound 4)))))))
  freeClosed := by
    simp [admissionCodeFormula,binaryCodeFormula,graphFormula,packetFormula,memPairFormula,codeFormula,pairFormula,
      Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (.existsMem _ (.conj (memPairFormula_delta0 _ _ _) (packetFormula_delta0 _ _ _ _)))
      (.conj (memPairFormula_delta0 _ _ _) (admissionCodeFormula_delta0 _ _ _ _ _ _ _ _ _ _ _ _))))))

structure AdmissionBlock (M : SetTheory.Structure.{u}) (C : ArticleData M.Domain) (D : RelationalData M.Domain)
    (T : TemplateShape M.Domain) (K scope names root B : M.Domain) : Prop where
  graph : Graph M B T.needLength D.codes
  rows : ∀ i k q p, NeedEntry M C.reflection T.template i k q p →
    ∀ u, MemPair M names q u → ∀ a, MemPair M B i a ↔
      AdmissionCode M (C.numbers 0) (C.numbers 1) (C.numbers 2) D.variables scope K T.cut k q u root a

theorem admission_block_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {A : M.Domain} {D : RelationalData M.Domain}
    (hD : ArticleInterpretation M C A D) {T : TemplateShape M.Domain} (hT : T.Valid M C)
    {K scope names root : M.Domain} (hb : M.mem scope D.omega)
    (hNames : Graph M names T.width scope) (hr : M.mem root scope) :
    ∃ B, AdmissionBlock M C D T K scope names root B := by
  let e0 := ((((oneEnv D.variables).push (C.numbers 2)).push (C.numbers 1)).push (C.numbers 0)).push scope
  let e := (((((((e0.push K).push T.cut).push T.template).push C.reflection.needCodes).push names).push root).push C.reflection.omega).push T.width
  have hφ (i a : M.Domain) : Project.Formula.satisfies ((e.push i).push a) admissionBlockSchema.body ↔
      ∃ k, M.mem k C.reflection.omega ∧ ∃ q, M.mem q T.width ∧ ∃ p, M.mem p T.width ∧
        ∃ u, M.mem u scope ∧ NeedEntry M C.reflection T.template i k q p ∧ MemPair M names q u ∧
          AdmissionCode M (C.numbers 0) (C.numbers 1) (C.numbers 2) D.variables scope K T.cut k q u root a := by
    simp only [admissionBlockSchema,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
      memPairFormula_iff hM.1,packetFormula_iff hM.1,admissionCodeFormula_iff hM.1]
    rfl
  obtain ⟨B,hSupport,hRaw⟩ := relation_comprehension_d hM admissionBlockSchema e T.needLength D.codes
  have hRows (i a : M.Domain) : MemPair M B i a ↔ M.mem i T.needLength ∧ M.mem a D.codes ∧
      ∃ k, M.mem k C.reflection.omega ∧ ∃ q, M.mem q T.width ∧ ∃ p, M.mem p T.width ∧
        ∃ u, M.mem u scope ∧ NeedEntry M C.reflection T.template i k q p ∧ MemPair M names q u ∧
          AdmissionCode M (C.numbers 0) (C.numbers 1) (C.numbers 2) D.variables scope K T.cut k q u root a := by
    simpa only [hφ] using hRaw i a
  have hEntryK (i k q p : M.Domain) (hEntry : NeedEntry M C.reflection T.template i k q p) : M.mem k C.reflection.omega := by
    obtain ⟨code,hCode,_,hPacket⟩ := hEntry
    obtain ⟨k',hk,pair,_,hCode'⟩ := (hC.reflection.needCodes code).mp hCode
    obtain ⟨pair',hCode'',_⟩ := hPacket
    exact (codes_injective hM.1 hCode'' hCode').1 ▸ hk
  have codeMem (k q u a : M.Domain)
      (h : AdmissionCode M (C.numbers 0) (C.numbers 1) (C.numbers 2) D.variables scope K T.cut k q u root a) : M.mem a D.codes :=
    (h.scoped_d hM hC hD hb).code_mem hD.spaces
  have hGraph : Graph M B T.needLength D.codes := by
    refine ⟨hSupport,?_,?_⟩
    · intro i hi
      obtain ⟨k,q,p,hEntry⟩ := need_entry_exists hC.reflection hT.needs hi
      have hCols := hT.need_columns_d hM hC hEntry
      obtain ⟨u,hu,hName⟩ := hNames.total q hCols.1
      obtain ⟨a,hCode⟩ := admission_code_exists_d hM hC hD hb hu hr (K := K) (cut := T.cut) (k := k) (q := q)
      exact ⟨a,codeMem k q u a hCode,(hRows i a).mpr
        ⟨hi,codeMem k q u a hCode,k,hEntryK i k q p hEntry,q,hCols.1,p,hCols.2,u,hu,hEntry,hName,hCode⟩⟩
    · intro i a b hia hib
      obtain ⟨_,_,k,_,q,_,p,_,u,_,hEntry,hName,hCode⟩ := (hRows i a).mp hia
      obtain ⟨_,_,k',_,q',_,p',_,u',_,hEntry',hName',hCode'⟩ := (hRows i b).mp hib
      obtain ⟨hk,hq,_⟩ := hEntry.unique hM.1 hT.needs hEntry'
      subst k'
      subst q'
      have hu := hNames.unique q u u' hName hName'
      subst u'
      exact hCode.unique_d hM hC hCode'
  refine ⟨B,hGraph,?_⟩
  intro i k q p hEntry u hName a
  constructor
  · intro hia
    obtain ⟨_,_,k',_,q',_,p',_,u',_,hEntry',hName',hCode⟩ := (hRows i a).mp hia
    obtain ⟨hk,hq,_⟩ := hEntry.unique hM.1 hT.needs hEntry'
    subst k'
    subst q'
    have hu := hNames.unique q u u' hName hName'
    subst u'
    exact hCode
  · intro hCode
    have hCols := hT.need_columns_d hM hC hEntry
    exact (hRows i a).mpr ⟨hT.need_index hM.1 hEntry,codeMem k q u a hCode,k,hEntryK i k q p hEntry,
      q,hCols.1,p,hCols.2,u,(hNames.bounds hM.1 hName).2,hEntry,hName,hCode⟩

theorem AdmissionBlock.scoped_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {A : M.Domain} {D : RelationalData M.Domain}
    (hD : ArticleInterpretation M C A D) {T : TemplateShape M.Domain} (hT : T.Valid M C)
    {K scope names root B i a : M.Domain} (hb : M.mem scope D.omega)
    (hNames : Graph M names T.width scope) (hB : AdmissionBlock M C D T K scope names root B)
    (hAt : MemPair M B i a) : ScopedAtom M D a scope := by
  obtain ⟨k,q,p,hEntry⟩ := need_entry_exists hC.reflection hT.needs (hB.graph.bounds hM.1 hAt).1
  obtain ⟨u,_,hName⟩ := hNames.total q (hT.need_columns_d hM hC hEntry).1
  exact ((hB.rows i k q p hEntry u hName a).mp hAt).scoped_d hM hC hD hb

private theorem admission_value_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} {D : RelationalData M.Domain}
    {scope K cut k q name root a s Atom x θ : M.Domain}
    (hCode : AdmissionCode M (C.numbers 0) (C.numbers 1) (C.numbers 2) D.variables scope K cut k q name root a)
    (hName : MemPair M s name x) (hRoot : MemPair M s root θ)
    (hEval : ∀ strict v y,
      BinaryCode strict M (C.numbers 0) (C.numbers 1) (C.numbers 2) D.variables scope name v a →
      MemPair M s v y → (MemPair M Atom a s ↔ (if strict then M.mem x y else x=y))) :
    MemPair M Atom a s ↔ M.mem k K ∨ k=K ∧ M.mem q cut ∧ M.mem x θ := by
  classical
  by_cases hk : M.mem k K
  · simp only [AdmissionCode,hk,↓reduceIte] at hCode
    exact ⟨fun _ => Or.inl hk,fun _ => (hEval false name x hCode hName).mpr rfl⟩
  · simp only [AdmissionCode,hk,↓reduceIte] at hCode
    by_cases hs : k=K ∧ M.mem q cut
    · simp only [if_pos hs] at hCode
      exact (hEval true root θ hCode hRoot).trans
        ⟨fun hx => Or.inr ⟨hs.1,hs.2,hx⟩,fun h => (h.resolve_left hk).2.2⟩
    · simp only [if_neg hs] at hCode
      apply iff_of_false
      · intro hTrue
        exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) x ((hEval true name x hCode hName).mp hTrue)
      · intro h
        exact hs ⟨(h.resolve_left hk).1,(h.resolve_left hk).2.1⟩

theorem AdmissionCode.value_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {A : M.Domain} {D : RelationalData M.Domain}
    (hD : ArticleInterpretation M C A D) {Atom : M.Domain} (hAtom : AtomicTable M D Atom)
    {scope K cut k q name root a s x θ : M.Domain} (hSub : M.MemberSubset A C.top)
    (hb : M.mem scope D.omega)
    (hCode : AdmissionCode M (C.numbers 0) (C.numbers 1) (C.numbers 2) D.variables scope K cut k q name root a)
    (hS : Graph M s scope A) (hName : MemPair M s name x) (hRoot : MemPair M s root θ) :
    MemPair M Atom a s ↔ M.mem k K ∨ k=K ∧ M.mem q cut ∧ M.mem x θ :=
  admission_value_iff hM hCode hName hRoot (fun _ _ _ hBin hAt =>
    hBin.value_iff_d hM hC hD hAtom hSub hb hS hName hAt)

theorem Height.admission_value_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {S : ArticleStructure M.Domain} (hS : S.Valid M C)
    {δ : M.Domain} {small : EvaluationData M.Domain} (h : Height M C S δ small)
    {scope K cut k q name root a s x θ : M.Domain} (hb : M.mem scope S.context.omega)
    (hCode : AdmissionCode M (C.numbers 0) (C.numbers 1) (C.numbers 2) S.relations.variables scope K cut k q name root a)
    (hAssign : Graph M s scope small.carrier) (hName : MemPair M s name x) (hRoot : MemPair M s root θ) :
    MemPair M small.atomic a s ↔ M.mem k K ∨ k=K ∧ M.mem q cut ∧ M.mem x θ :=
  admission_value_iff hM hCode hName hRoot (fun _ _ _ hBin hAt =>
    h.binary_value_iff_d hM hC hS hb hBin hAssign hName hAt)

private theorem admission_block_truth_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {D : RelationalData M.Domain} {PC : Context M.Domain}
    {T : TemplateShape M.Domain} (hT : T.Valid M C) {K scope names root B A s f θ : M.Domain}
    (hB : AdmissionBlock M C D T K scope names root B) (hF : TupleValue M f names s T.width scope A)
    (hSubCap : M.MemberSubset A C.reflection.cap)
    (hEval : ∀ k q u a x,
      AdmissionCode M (C.numbers 0) (C.numbers 1) (C.numbers 2) D.variables scope K T.cut k q u root a →
      MemPair M s u x → (MemPair M PC.atomic a s ↔ M.mem k K ∨ k=K ∧ M.mem q T.cut ∧ M.mem x θ)) :
    AllAtoms M PC D B T.needLength s ↔ Admissible M C.reflection K θ T.template f T.cut := by
  constructor
  · intro hAll k _ q _ p _ hNeed x _ hFx
    obtain ⟨i,_,hEntry⟩ := hNeed
    have hCols := hT.need_columns_d hM hC hEntry
    obtain ⟨u,hu,hName⟩ := hF.variables.total q hCols.1
    obtain ⟨a,_,hAt,hTrue⟩ := hAll i (hT.need_index hM.1 hEntry)
    have hCode := (hB.rows i k q p hEntry u hName a).mp hAt
    exact (hEval k q u a x hCode ((hF.rows q hCols.1 u hu x (hF.values.bounds hM.1 hFx).2 hName).mp hFx)).mp hTrue
  · intro hAdm i hi
    obtain ⟨k,q,p,hEntry⟩ := need_entry_exists hC.reflection hT.needs hi
    have hNeed := hEntry.occurs ((KP1Y.Naturals.omega_isOrdinal_d hM hC.numerals.omega).transitive T.needLength hT.needLength i hi)
    obtain ⟨hk,hq,hp⟩ := hNeed.bounds hM.1 hC.reflection
    have hCols := hT.need_columns_d hM hC hEntry
    obtain ⟨u,hu,hName⟩ := hF.variables.total q hCols.1
    obtain ⟨x,hx,hFx⟩ := hF.values.total q hCols.1
    obtain ⟨a,ha,hAt⟩ := hB.graph.total i hi
    have hCode := (hB.rows i k q p hEntry u hName a).mp hAt
    refine ⟨a,ha,hAt,?_⟩
    apply (hEval k q u a x hCode ((hF.rows q hCols.1 u hu x hx hName).mp hFx)).mpr
    exact hAdm k hk q hq p hp hNeed x (hSubCap x hx) hFx

theorem AdmissionBlock.all_atoms_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {A : M.Domain} {D : RelationalData M.Domain}
    (hD : ArticleInterpretation M C A D) {PC : Context M.Domain} (hAtom : AtomicTable M D PC.atomic)
    {T : TemplateShape M.Domain} (hT : T.Valid M C) {K scope names root B s f θ : M.Domain}
    (hB : AdmissionBlock M C D T K scope names root B) (hSub : M.MemberSubset A C.top)
    (hb : M.mem scope D.omega) (hF : TupleValue M f names s T.width scope A) (hRoot : MemPair M s root θ) :
    AllAtoms M PC D B T.needLength s ↔ Admissible M C.reflection K θ T.template f T.cut :=
  admission_block_truth_iff hM hC hT hB hF
    (fun x hx => hC.reflection.cap.transitive C.top hC.cap.predecessor_mem x (hSub x hx))
    (fun _ _ _ _ _ hCode hName => hCode.value_iff_d hM hC hD hAtom hSub hb hF.source hName hRoot)

theorem Height.admission_block_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {S : ArticleStructure M.Domain} (hS : S.Valid M C)
    {δ : M.Domain} {small : EvaluationData M.Domain} (h : Height M C S δ small)
    {T : TemplateShape M.Domain} (hT : T.Valid M C) {K scope names root B s f θ : M.Domain}
    (hB : AdmissionBlock M C S.relations T K scope names root B)
    (hb : M.mem scope S.context.omega) (hF : TupleValue M f names s T.width scope small.carrier)
    (hRoot : MemPair M s root θ) :
    AllAtoms M (small.context S.context) S.relations B T.needLength s ↔
      Admissible M C.reflection K θ T.template f T.cut := by
  have hSub : M.MemberSubset small.carrier C.reflection.cap := by
    intro x hx
    exact hC.reflection.cap.transitive C.top hC.cap.predecessor_mem x
      (Eq.mp (congrArg (M.mem x) hS.carrier) (h.elementary.carrier_subset x hx))
  exact admission_block_truth_iff hM hC hT hB hF hSub
    (fun _ _ _ _ _ hCode hName => h.admission_value_iff_d hM hC hS hb hCode hF.source hName hRoot)

theorem shape_admission_block_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {A : M.Domain} {D : RelationalData M.Domain}
    (hD : ArticleInterpretation M C A D) {T : TemplateShape M.Domain} (hT : T.Valid M C)
    {F : M.Domain} {V : NameFrame M.Domain} (hV : V.Valid M C F T.width T.edgeLength T.needLength) (K : M.Domain) :
    ∃ root B, MemPair M V.scalars (C.numbers 2) root ∧ AdmissionBlock M C D T K V.scope V.inputs root B := by
  obtain ⟨root,hr,hRoot⟩ := hV.scalars.graph.total (C.numbers 2) (hC.numerals.lt (by decide : (2:Nat)<3))
  have hb : M.mem V.scope D.omega := Eq.mpr (congrArg (M.mem V.scope) hD.omega) hV.scope
  obtain ⟨B,hB⟩ := admission_block_exists_d hM hC hD hT hb hV.inputs.graph hr (K := K)
  exact ⟨root,B,hRoot,hB⟩

theorem AdmissionBlock.ground_atoms_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {A : M.Domain} {D : RelationalData M.Domain}
    (hD : ArticleInterpretation M C A D) {PC : Context M.Domain} (hAtom : AtomicTable M D PC.atomic)
    {T : TemplateShape M.Domain} (hT : T.Valid M C) {F : M.Domain} {V : NameFrame M.Domain}
    (hV : V.Valid M C F T.width T.edgeLength T.needLength) {K root B a θ s f : M.Domain}
    (hRoot : MemPair M V.scalars (C.numbers 2) root) (hB : AdmissionBlock M C D T K V.scope V.inputs root B)
    (hSub : M.MemberSubset A C.top) (hP : GroundParameters M C T V a θ A s)
    (hF : TupleValue M f V.inputs s T.width V.scope A) :
    AllAtoms M PC D B T.needLength s ↔ Admissible M C.reflection K θ T.template f T.cut :=
  hB.all_atoms_iff_d hM hC hD hAtom hT hSub
    (Eq.mpr (congrArg (M.mem V.scope) hD.omega) hV.scope) hF (hP.root root hRoot)

theorem Height.ground_admission_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {S : ArticleStructure M.Domain} (hS : S.Valid M C)
    {δ : M.Domain} {small : EvaluationData M.Domain} (h : Height M C S δ small)
    {T : TemplateShape M.Domain} (hT : T.Valid M C) {F : M.Domain} {V : NameFrame M.Domain}
    (hV : V.Valid M C F T.width T.edgeLength T.needLength) {K root B a θ s f : M.Domain}
    (hRoot : MemPair M V.scalars (C.numbers 2) root) (hB : AdmissionBlock M C S.relations T K V.scope V.inputs root B)
    (hP : GroundParameters M C T V a θ small.carrier s) (hF : TupleValue M f V.inputs s T.width V.scope small.carrier) :
    AllAtoms M (small.context S.context) S.relations B T.needLength s ↔
      Admissible M C.reflection K θ T.template f T.cut :=
  h.admission_block_iff_d hM hC hS hT hB
    (Eq.mpr (congrArg (M.mem V.scope) hS.omega) hV.scope) hF (hP.root root hRoot)

end KP1Y.ReflectionModel
