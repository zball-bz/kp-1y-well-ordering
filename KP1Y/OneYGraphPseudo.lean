import KP1Y.OneYGraphPseudoDefs
import KP1Y.OneYLowerCopy

/-! 任意实际局部高度山形的伪父算法；存在性不要求数值性或行嵌套。 -/
namespace KP1Y.OneYFinite.CopiedMountain
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
universe u

private def rootHeightSchema : Project.UnarySchema 9 where
  body := Project.Formula.forallMem (.bound 4) (Project.Formula.forallMem (.bound 10) (Project.Formula.forallMem (.bound 11)
    (.imp (rootFormula ⟨.bound 12,.bound 11,.bound 10,.bound 9,.bound 8⟩ (.bound 7) (.bound 6) (.bound 3) (.bound 2))
      (.imp (memPairFormula (.bound 5) (.bound 2) (.bound 1))
        (.imp (memPairFormula (.bound 5) (.bound 3) (.bound 0))
          (.imp (.disj (Project.Formula.extensionalEq (.bound 4) (.bound 0)) (.mem (.bound 4) (.bound 0)))
            (Project.Formula.extensionalEq (.bound 1) (.bound 4))))))))
  freeClosed := by
    have hRoot := rootFormula_freeClosed (n := 13) (C := ⟨.bound 12,.bound 11,.bound 10,.bound 9,.bound 8⟩)
      ⟨rfl,rfl,rfl,rfl,rfl⟩ (.bound 7) (.bound 6) (.bound 3) (.bound 2) rfl rfl rfl rfl
    simp [Project.Formula.forallMem,Definitional.Formula.FreeClosed,memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,hRoot]

private def rootHeightEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (m Q Heights r : M.Domain) : Env M 9 :=
  ((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push m).push Q).push Heights).push r

private theorem rootHeightSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (C : ExpressionData M.Domain)
    (m Q Heights r c : M.Domain) : Project.Formula.satisfies ((rootHeightEnv C m Q Heights r).push c) rootHeightSchema.body ↔
      ∀ q, M.mem q m → ∀ hq, M.mem hq C.omega → ∀ hc, M.mem hc C.omega → Root M C m Q c q →
        MemPair M Heights q hq → MemPair M Heights c hc → (r=hc ∨ M.mem r hc) → hq=r := by
  simp only [rootHeightSchema,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    rootFormula_iff he,memPairFormula_iff he,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he,Project.Formula.satisfies_mem_iff]
  rfl

/-- 有父行的根高度恰等于行号，只使用已证明的source和endpoint公理形状。 -/
theorem graph_root_height_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {X : Data M.Domain} (hX : X.Valid M C)
    {r F c q hc hq : M.Domain} (hAt : MemPair M X.parents r F)
    (hRoot : Root M C X.width F c q) (hHC : MemPair M X.heights c hc) (hHQ : MemPair M X.heights q hq)
    (hLe : r=hc ∨ M.mem r hc) : hq=r := by
  have hF := hX.forest r F hAt
  have hFMem := (hX.parents.bounds hM.1 hAt).2
  have hAll := KP1Y.ordinal_induction_d hM rootHeightSchema (rootHeightEnv C X.width F X.heights r) (by
    intro c _ ih
    apply (rootHeightSchema_iff hM.1 C X.width F X.heights r c).mpr
    intro q _ hq _ hc _ hRoot hHQ hHC hLe
    classical
    by_cases hNo : NoParent M X.width F c
    · have hqc := root_of_no_parent_d hM hC hF hNo hRoot
      subst q
      have hh := hX.heights.unique c hq hc hHQ hHC
      have hNot : ¬M.mem r hc := by
        intro hlt
        obtain ⟨p,G,_,hG,hParent⟩ := (hX.source r c hc hHC).mpr hlt
        have hGF := hX.parents.unique r G F hG hAt
        subst G
        exact hNo p (hF.bounds hM.1 hParent).2 hParent
      exact hh.trans (hLe.resolve_right hNot).symm
    · have hSome : ∃p, M.mem p X.width ∧ MemPair M F c p := by
        apply Classical.byContradiction
        intro hNone
        exact hNo (fun p hp hParent => hNone ⟨p,hp,hParent⟩)
      obtain ⟨p,hp,hParent⟩ := hSome
      obtain ⟨hpHeight,hpNat,hHP⟩ := hX.heights.total p hp
      have hRootP := (root_parent_iff_d hM hC hF hParent).mp hRoot
      have hLeP := hX.endpoint r c p hpHeight ⟨F,hFMem,hAt,hParent⟩ hHP
      exact (rootHeightSchema_iff hM.1 C X.width F X.heights r p).mp (ih p (hF.left c p hParent))
        q hRootP.1 hq (hX.heights.bounds hM.1 hHQ).2 hpHeight hpNat hRootP hHQ hHP hLeP)
  have hcNat := (omega_isOrdinal_d hM hC.omega).transitive X.width hX.width c (hX.heights.bounds hM.1 hHC).1
  exact (rootHeightSchema_iff hM.1 C X.width F X.heights r c).mp (hAll c ((omega_isOrdinal_d hM hC.omega).mem hcNat))
    q hRoot.1 hq (hX.heights.bounds hM.1 hHQ).2 hc (hX.heights.bounds hM.1 hHC).2 hRoot hHQ hHC hLe

theorem graph_pseudo_candidate_of_successor_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {X : Data M.Domain} (hX : X.Valid M C)
    {c height r : M.Domain} (hHeight : MemPair M X.heights c height) (hR : M.mem r C.omega)
    (hSucc : M.SuccessorOf height r) : ∃p, GraphPseudoCandidate M C X c p := by
  obtain ⟨F,hFMem,hAt⟩ := hX.parents.total r hR
  obtain ⟨q,hRoot⟩ := root_exists_d hM hC (hX.forest r F hAt) (hX.heights.bounds hM.1 hHeight).1
  obtain ⟨hq,hqNat,hHQ⟩ := hX.heights.total q hRoot.1
  have hEq := graph_root_height_d hM hC hX hAt hRoot hHeight hHQ (Or.inr hSucc.predecessor_mem)
  have hAnc : Ancestor M C X.width F q c := by
    rcases hRoot.2.2 with he | hAnc
    · subst q
      have hh := hX.heights.unique c hq height hHQ hHeight
      exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) r
        ((hh.symm.trans hEq) ▸ hSucc.predecessor_mem))
    · exact hAnc
  exact ⟨q,height,(hX.heights.bounds hM.1 hHeight).2,hq,hqNat,r,hR,hHeight,hHQ,hSucc,F,hFMem,hAt,hAnc,Or.inr hEq⟩

theorem graph_pseudo_candidate_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {X : Data M.Domain} (hX : X.Valid M C)
    {c height : M.Domain} (hHeight : MemPair M X.heights c height) (hPos : M.mem C.zero height) :
    ∃p, GraphPseudoCandidate M C X c p := by
  rcases natural_cases hM hC.omega (hX.heights.bounds hM.1 hHeight).2 with hEmpty | ⟨r,hr,hSucc⟩
  · exact False.elim (hEmpty C.zero hPos)
  · exact graph_pseudo_candidate_of_successor_d hM hC hX hHeight hr hSucc

private def candidateSchema : Project.Delta0UnarySchema 10 where
  body := graphPseudoCandidateFormula ⟨.bound 10,.bound 9,.bound 8,.bound 7,.bound 6⟩
    ⟨.bound 5,.bound 4,.bound 3,.bound 2⟩ (.bound 1) (.bound 0)
  freeClosed := graphPseudoCandidateFormula_freeClosed ⟨rfl,rfl,rfl,rfl,rfl⟩ ⟨rfl,rfl,rfl,rfl⟩ _ _ rfl rfl
  delta0 := graphPseudoCandidateFormula_delta0 _ _ _ _

private def candidateEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (X : Data M.Domain) (c : M.Domain) : Env M 10 :=
  (((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push X.width).push X.heights).push X.forests).push X.parents).push c

/-- 每列候选集是实际Δ₀分离子集。 -/
theorem graph_pseudo_candidate_set_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (C : ExpressionData M.Domain) (X : Data M.Domain) (c : M.Domain) :
    ∃A, ∀p, M.mem p A ↔ GraphPseudoCandidate M C X c p := by
  obtain ⟨A,hA⟩ := SetTheory.KP.separation_exists_d (KP1Y.models_weakKP hM) candidateSchema (candidateEnv C X c) c
  have hφ (p : M.Domain) : Project.Formula.satisfies ((candidateEnv C X c).push p) candidateSchema.body ↔ GraphPseudoCandidate M C X c p :=
    graphPseudoCandidateFormula_iff hM.1 _ _ _ _ _
  refine ⟨A,fun p => ?_⟩
  rw [hA p,hφ p]
  exact ⟨And.right,fun h => ⟨(h.bounds hM.1).2.2,h⟩⟩

theorem graph_pseudo_parent_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {X : Data M.Domain} (hX : X.Valid M C)
    {c height : M.Domain} (hHeight : MemPair M X.heights c height) (hPos : M.mem C.zero height) :
    ∃p, GraphPseudoParent M C X c p := by
  obtain ⟨A,hA⟩ := graph_pseudo_candidate_set_exists_d hM C X c
  obtain ⟨p,hCandidate⟩ := graph_pseudo_candidate_exists_d hM hC hX hHeight hPos
  have hc := (omega_isOrdinal_d hM hC.omega).transitive X.width hX.width c (hX.heights.bounds hM.1 hHeight).1
  obtain ⟨q,hq,hMax⟩ := bounded_nat_max_d hM hC.omega hc (fun p hp => ((hA p).mp hp).bounds hM.1 |>.2.2)
    ⟨p,(hA p).mpr hCandidate⟩
  exact ⟨q,(hA q).mp hq,fun p _ hP => hMax p ((hA p).mpr hP)⟩

theorem GraphPseudoCandidate.positive_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {X : Data M.Domain} (hX : X.Valid M C)
    {c p height : M.Domain} (h : GraphPseudoCandidate M C X c p) (hHeight : MemPair M X.heights c height) : M.mem C.zero height := by
  obtain ⟨hc,hcNat,_,_,r,_,hHC,_,hSucc,_⟩ := h
  have hh := hX.heights.unique c hc height hHC hHeight
  subst hc
  exact (hC.zero_mem_iff hM hcNat).mpr (fun he => hC.zero_empty r (he ▸ hSucc.predecessor_mem))

theorem GraphPseudoCandidate.parent_heights {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain}
    {X : Data M.Domain} (hX : X.Valid M C) {c p hc hp : M.Domain} (h : GraphPseudoCandidate M C X c p)
    (hHC : MemPair M X.heights c hc) (hHP : MemPair M X.heights p hp) : hp=hc ∨ M.SuccessorOf hc hp := by
  obtain ⟨hc',_,hp',_,r,_,hHC',hHP',hSucc,_,_,_,_,hRel⟩ := h
  have hcc := hX.heights.unique c hc' hc hHC' hHC
  have hpp := hX.heights.unique p hp' hp hHP' hHP
  subst hc'
  subst hp'
  exact hRel.elim Or.inl (fun he => Or.inr (he.symm ▸ hSucc))

structure GraphPseudoForest (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (X : Data M.Domain) (P : M.Domain) : Prop where
  forest : Forest M C.omega X.width P
  rows : ∀c p, MemPair M P c p ↔ GraphPseudoParent M C X c p

private def parentSchema : Project.Delta0BinarySchema 9 where
  body := graphPseudoParentFormula ⟨.bound 10,.bound 9,.bound 8,.bound 7,.bound 6⟩
    ⟨.bound 5,.bound 4,.bound 3,.bound 2⟩ (.bound 1) (.bound 0)
  freeClosed := graphPseudoParentFormula_freeClosed ⟨rfl,rfl,rfl,rfl,rfl⟩ ⟨rfl,rfl,rfl,rfl⟩ _ _ rfl rfl
  delta0 := graphPseudoParentFormula_delta0 _ _ _ _

private def parentEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (X : Data M.Domain) : Env M 9 :=
  ((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push X.width).push X.heights).push X.forests).push X.parents

theorem graph_pseudo_forest_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {X : Data M.Domain} (hX : X.Valid M C) :
    ∃P, GraphPseudoForest M C X P := by
  have hφ (c p : M.Domain) : Project.Formula.satisfies (((parentEnv C X).push c).push p) parentSchema.body ↔
      GraphPseudoParent M C X c p := graphPseudoParentFormula_iff hM.1 _ _ _ _ _
  obtain ⟨P,hSupport,hRaw⟩ := relation_comprehension_d hM parentSchema (parentEnv C X) X.width X.width
  have hRows (c p : M.Domain) : MemPair M P c p ↔ GraphPseudoParent M C X c p := by
    rw [hRaw c p,hφ]
    exact ⟨fun h => h.2.2,fun h => ⟨(h.1.bounds hM.1).2.1,(h.1.bounds hM.1).1,h⟩⟩
  exact ⟨P,⟨hX.width,hSupport,fun c p q hp hq => ((hRows c p).mp hp).unique_d hM hC hX ((hRows c q).mp hq),
    fun c p hp => (((hRows c p).mp hp).1.bounds hM.1).2.2⟩,hRows⟩

theorem GraphPseudoForest.unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {X : Data M.Domain} {P Q : M.Domain}
    (hP : GraphPseudoForest M C X P) (hQ : GraphPseudoForest M C X Q) : P=Q :=
  relation_ext he hP.forest.support hQ.forest.support (fun c p => (hP.rows c p).trans (hQ.rows c p).symm)

theorem GraphPseudoForest.no_parent_iff_height_zero_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {X : Data M.Domain} (hX : X.Valid M C)
    {P c height : M.Domain} (hP : GraphPseudoForest M C X P) (hHeight : MemPair M X.heights c height) :
    NoParent M X.width P c ↔ height=C.zero := by
  constructor
  · intro hNo
    classical
    apply Classical.byContradiction
    intro hNot
    have hPos := (hC.zero_mem_iff hM (hX.heights.bounds hM.1 hHeight).2).mpr hNot
    obtain ⟨p,hParent⟩ := graph_pseudo_parent_exists_d hM hC hX hHeight hPos
    exact hNo p (hParent.1.bounds hM.1).1 ((hP.rows c p).mpr hParent)
  · intro he p _ hAt
    exact hC.zero_empty C.zero (he ▸ ((hP.rows c p).mp hAt).1.positive_d hM hC hX hHeight)

theorem GraphPseudoForest.source_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {X : Data M.Domain} (hX : X.Valid M C)
    {P c height : M.Domain} (hP : GraphPseudoForest M C X P) (hHeight : MemPair M X.heights c height) :
    (∃p, MemPair M P c p) ↔ M.mem C.zero height := by
  constructor
  · rintro ⟨p,hAt⟩
    exact ((hP.rows c p).mp hAt).1.positive_d hM hC hX hHeight
  · intro hPos
    obtain ⟨p,hParent⟩ := graph_pseudo_parent_exists_d hM hC hX hHeight hPos
    exact ⟨p,(hP.rows c p).mpr hParent⟩

theorem GraphPseudoForest.root_height_zero_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {X : Data M.Domain} (hX : X.Valid M C)
    {P c q hq : M.Domain} (hP : GraphPseudoForest M C X P) (hRoot : Root M C X.width P c q)
    (hHQ : MemPair M X.heights q hq) : hq=C.zero :=
  (hP.no_parent_iff_height_zero_d hM hC hX hHQ).mp hRoot.2.1

theorem GraphPseudoForest.roots_graph_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {X : Data M.Domain} {P : M.Domain} (hP : GraphPseudoForest M C X P) :
    ∃Roots, Graph M Roots X.width X.width ∧ ∀c q, MemPair M Roots c q ↔ Root M C X.width P c q :=
  root_graph_exists_d hM hC hP.forest

theorem graph_pseudo_parent_of_successor_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {X : Data M.Domain} (hX : X.Valid M C)
    {c height r : M.Domain} (hHeight : MemPair M X.heights c height) (hSucc : M.SuccessorOf height r) :
    ∃p, GraphPseudoParent M C X c p :=
  graph_pseudo_parent_exists_d hM hC hX hHeight
    ((hC.zero_mem_iff hM (hX.heights.bounds hM.1 hHeight).2).mpr
      (fun he => hC.zero_empty r (he ▸ hSucc.predecessor_mem)))

theorem GraphPseudoCandidate.root_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {X : Data M.Domain} (hX : X.Valid M C)
    {c p height r F q : M.Domain} (h : GraphPseudoCandidate M C X c p)
    (hHeight : MemPair M X.heights c height) (hSucc : M.SuccessorOf height r)
    (hAt : MemPair M X.parents r F) : Root M C X.width F c q ↔ Root M C X.width F p q := by
  obtain ⟨hc,_,_,_,r',hr',hHC,_,hSucc',F',_,hAt',hAnc,_⟩ := h
  have hh := hX.heights.unique c hc height hHC hHeight
  subst hc
  have hrr := Structure.SuccessorOf.predecessor_eq hM.1 ((omega_isOrdinal_d hM hC.omega).mem hr') hSucc' hSucc
  subst r'
  have hFF := hX.parents.unique r F' F hAt' hAt
  subst F'
  exact root_ancestor_iff_d hM hC (hX.forest r F hAt) hAnc

end KP1Y.OneYFinite.CopiedMountain
