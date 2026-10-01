import KP1Y.OneYSelectionOrder
import KP1Y.OneYLinearForest

/-! LANE-B helper：通用森林/选择工具。父边封闭集合含全部祖先；候选森林的精化选择；
选择的自身幂等；单根收缩的选择不变（原 SingleContraction）。全部列/行均为内部 ω 元素。 -/
namespace KP1Y.OneYFinite.LowerHelp
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite
universe u

theorem nat_le_antisymm_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b : M.Domain} (ha : M.mem a C.omega)
    (hab : a=b ∨ M.mem a b) (hba : b=a ∨ M.mem b a) : a=b := by
  rcases hab with he | hab
  · exact he
  · rcases hba with he | hba
    · exact he.symm
    · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) a
        (((omega_isOrdinal_d hM hC.omega).mem ha).transitive b hba a hab))

private def closureEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (n G S : M.Domain) : Env M 8 :=
  (((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push n).push G).push S

private def closureSchema : Project.UnarySchema 8 where
  body := .imp (.mem (.bound 0) (.bound 1)) (Project.Formula.forallMem (.bound 3)
    (.imp (ancestorFormula ⟨.bound 9,.bound 8,.bound 7,.bound 6,.bound 5⟩ (.bound 4) (.bound 3) (.bound 0) (.bound 1))
      (.mem (.bound 0) (.bound 2))))
  freeClosed := by
    have hAnc := ancestorFormula_freeClosed (n := 10) (C := ⟨.bound 9,.bound 8,.bound 7,.bound 6,.bound 5⟩)
      ⟨rfl,rfl,rfl,rfl,rfl⟩ (.bound 4) (.bound 3) (.bound 0) (.bound 1) rfl rfl rfl rfl
    simp [Project.Formula.forallMem,Definitional.Formula.FreeClosed,hAnc]

private theorem closureSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (n G S c : M.Domain) :
    Project.Formula.satisfies ((closureEnv C n G S).push c) closureSchema.body ↔
      (M.mem c S → ∀ a, M.mem a n → Ancestor M C n G a c → M.mem a S) := by
  simp only [closureSchema,closureEnv,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_forallMem_iff,ancestorFormula_iff he]
  rfl

/-- 对父边封闭的实际集合包含其中任一点的全部祖先（对列作对象集合归纳）。 -/
theorem ancestor_closed_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {n G S : M.Domain} (hG : Forest M C.omega n G)
    (hClosed : ∀ q p, M.mem q S → MemPair M G q p → M.mem p S) {c a : M.Domain}
    (hc : M.mem c S) (hAnc : Ancestor M C n G a c) : M.mem a S := by
  have hAll := KP1Y.induction_d hM closureSchema (closureEnv C n G S) (by
    intro c ih
    apply (closureSchema_iff hM.1 C n G S c).mpr
    intro hcS a _ hAnc
    obtain ⟨p,hParent,hTail⟩ := ancestor_parent_cases_d hM hC hG hAnc
    have hpS := hClosed c p hcS hParent
    rcases hTail with he | hAP
    · exact he ▸ hpS
    · exact (closureSchema_iff hM.1 C n G S p).mp (ih p (hG.left c p hParent)) hpS a (hAP.bounds hM.1).1 hAP)
  exact (closureSchema_iff hM.1 C n G S c).mp (hAll c) hc a (hAnc.bounds hM.1).1 hAnc

private def chainEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (n F c : M.Domain) : Env M 8 :=
  (((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push n).push F).push c

private def chainSchema : Project.Delta0UnarySchema 8 where
  body := .disj (Project.Formula.extensionalEq (.bound 0) (.bound 1))
    (ancestorFormula ⟨.bound 8,.bound 7,.bound 6,.bound 5,.bound 4⟩ (.bound 3) (.bound 2) (.bound 0) (.bound 1))
  freeClosed := by
    have hAnc := ancestorFormula_freeClosed (n := 9) (C := ⟨.bound 8,.bound 7,.bound 6,.bound 5,.bound 4⟩)
      ⟨rfl,rfl,rfl,rfl,rfl⟩ (.bound 3) (.bound 2) (.bound 0) (.bound 1) rfl rfl rfl rfl
    simp [Definitional.Formula.FreeClosed,hAnc]
  delta0 := .disj (.atom _ _ _) (ancestorFormula_delta0 _ _ _ _ _)

/-- 祖先或自身的实际集合（Δ₀ 分离）。 -/
theorem chain_set_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (C : ExpressionData M.Domain) (n F c : M.Domain) :
    ∃ S, ∀ a, M.mem a S ↔ M.mem a n ∧ (a=c ∨ Ancestor M C n F a c) := by
  obtain ⟨S,hS⟩ := SetTheory.KP.separation_exists_d (KP1Y.models_weakKP hM) chainSchema (chainEnv C n F c) n
  refine ⟨S,fun a => (hS a).trans (and_congr_right fun _ => ?_)⟩
  simp only [chainSchema,chainEnv,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq hM.1,
    ancestorFormula_iff hM.1]
  rfl

/-- 若Q的每条父边都在F中为祖先（仅在c的F祖先链上要求），则c的Q祖先都是F祖先。 -/
theorem ancestor_transfer_on_chain_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {n F Q c a : M.Domain}
    (hF : Forest M C.omega n F) (hQ : Forest M C.omega n Q)
    (hEdges : ∀ z p, (z=c ∨ Ancestor M C n F z c) → MemPair M Q z p → Ancestor M C n F p z)
    (hAnc : Ancestor M C n Q a c) : Ancestor M C n F a c := by
  obtain ⟨S,hS⟩ := chain_set_exists_d hM C n F c
  have hc : M.mem c n := (hAnc.bounds hM.1).2
  have haS := ancestor_closed_d hM hC hQ (S := S) (by
    intro z p hz hZP
    obtain ⟨_,hzc⟩ := (hS z).mp hz
    have hPZ := hEdges z p hzc hZP
    refine (hS p).mpr ⟨(hPZ.bounds hM.1).1,Or.inr ?_⟩
    rcases hzc with he | hAZ
    · exact he ▸ hPZ
    · exact ancestor_trans_d hM hC hF hPZ hAZ) ((hS c).mpr ⟨hc,Or.inl rfl⟩) hAnc
  rcases ((hS a).mp haS).2 with he | hAF
  · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) c (he ▸ hAnc.1))
  · exact hAF

theorem candidate_true_false_iff {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {m F V c p : M.Domain}
    (hPos : ∀ c v, MemPair M V c v → M.mem C.zero v) :
    ParentCandidate true M C m F V c p ↔ ParentCandidate false M C m F V c p := by
  constructor
  · rintro ⟨hAnc,x,hx,y,hy,hX,hY,hxy,_⟩
    exact ⟨hAnc,x,hx,y,hy,hX,hY,hxy,trivial⟩
  · rintro ⟨hAnc,x,hx,y,hy,hX,hY,hxy,_⟩
    exact ⟨hAnc,x,hx,y,hy,hX,hY,hxy,hPos p x hX⟩

theorem restricted_true_false_iff {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {m F V c p : M.Domain}
    (hPos : ∀ c v, MemPair M V c v → M.mem C.zero v) :
    RestrictedParent true M C m F V c p ↔ RestrictedParent false M C m F V c p := by
  simp only [RestrictedParent,candidate_true_false_iff hPos]

theorem selects_to_false {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {m F V P : M.Domain}
    (hS : Selects true M C m F V P) (hPos : ∀ c v, MemPair M V c v → M.mem C.zero v) : Selects false M C m F V P :=
  ⟨hS.inherited,hS.values,hS.forest,fun c p => (hS.parents c p).trans (restricted_true_false_iff hPos)⟩

/-- 细帧的祖先都是粗帧祖先，且粗帧选择的边都是细帧祖先，则两者选择相同。 -/
theorem select_of_refinements_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m Fc Ff V S : M.Domain}
    (hFine : Forest M C.omega m Ff) (hRefine : ∀ a c, Ancestor M C m Ff a c → Ancestor M C m Fc a c)
    (hSel : Selects true M C m Fc V S) (hSelRefines : ForestRefines M C m S Ff) : Selects true M C m Ff V S := by
  have hForward (c p : M.Domain) (hcp : MemPair M S c p) : RestrictedParent true M C m Ff V c p := by
    obtain ⟨⟨_,hValues⟩,hMax⟩ := (hSel.parents c p).mp hcp
    exact ⟨⟨hSelRefines c p hcp,hValues⟩,fun q hq hQ => hMax q hq ⟨hRefine q c hQ.1,hQ.2⟩⟩
  refine ⟨hFine,hSel.values,hSel.forest,fun c p => ⟨hForward c p,fun hRP => ?_⟩⟩
  obtain ⟨p',hRP'⟩ := restricted_parent_exists_d hM true hC hSel.inherited ⟨p,⟨hRefine p c hRP.1.1,hRP.1.2⟩⟩
  have hS := (hSel.parents c p').mpr hRP'
  have he := restricted_parent_unique_d hM true hC hFine hRP (hForward c p' hS)
  exact he ▸ hS

/-- 选择结果对自身幂等：已选父边就是最近的较小候选。 -/
theorem selects_self_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m F V P : M.Domain}
    (hS : Selects true M C m F V P) : Selects true M C m P V P := by
  have hBack (c p : M.Domain) (hcp : MemPair M P c p) : RestrictedParent true M C m P V c p :=
    ⟨⟨ancestor_direct_d hM hC hS.forest hcp,(hS.parents c p).mp hcp |>.1.2⟩,
      fun q _ hQ => ancestor_le_parent_d hM hC hS.forest hcp hQ.1⟩
  refine ⟨hS.forest,hS.values,hS.forest,fun c p => ⟨hBack c p,fun hRP => ?_⟩⟩
  obtain ⟨p',hP',_⟩ := ancestor_parent_cases_d hM hC hS.forest hRP.1.1
  have he := restricted_parent_unique_d hM true hC hS.forest hRP (hBack c p' hP')
  exact he ▸ hP'

private def selAncEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (n F G V : M.Domain) : Env M 9 :=
  ((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push n).push F).push G).push V

private def selAncSchema : Project.UnarySchema 9 where
  body := Project.Formula.forallMem (.bound 4)
    (.imp (restrictedParentFormula true ⟨.bound 10,.bound 9,.bound 8,.bound 7,.bound 6⟩ (.bound 5) (.bound 3) (.bound 2) (.bound 1) (.bound 0))
      (ancestorFormula ⟨.bound 10,.bound 9,.bound 8,.bound 7,.bound 6⟩ (.bound 5) (.bound 4) (.bound 0) (.bound 1)))
  freeClosed := by
    have hC : (⟨.bound 10,.bound 9,.bound 8,.bound 7,.bound 6⟩ : ExpressionData (Project.Term 11)).Closed := ⟨rfl,rfl,rfl,rfl,rfl⟩
    have hR := restrictedParentFormula_freeClosed true hC (.bound 5) (.bound 3) (.bound 2) (.bound 1) (.bound 0) rfl rfl rfl rfl rfl
    have hA := ancestorFormula_freeClosed hC (.bound 5) (.bound 4) (.bound 0) (.bound 1) rfl rfl rfl rfl
    simp [Project.Formula.forallMem,Definitional.Formula.FreeClosed,hR,hA]

private theorem selAncSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (n F G V c : M.Domain) :
    Project.Formula.satisfies ((selAncEnv C n F G V).push c) selAncSchema.body ↔
      ∀ p, M.mem p n → RestrictedParent true M C n G V c p → Ancestor M C n F p c := by
  simp only [selAncSchema,selAncEnv,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    restrictedParentFormula_iff he,ancestorFormula_iff he]
  rfl

/-- 原 select_eq_single_contraction：F 与 G 除收缩列外父行相同；收缩列的 F 父为 y，
y 是 G 祖先，且 G 的选择父在 y 之前。则两者的正值最近较小选择相同。 -/
theorem single_contraction_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {n F G V y : M.Domain}
    (hF : Forest M C.omega n F) (hG : Forest M C.omega n G) (hV : Graph M V n C.omega)
    (hPos : ∀ c v, MemPair M V c v → M.mem C.zero v) (hy : M.mem y C.omega)
    (hPrefix : ∀ c, (c=y ∨ M.mem c y) → ∀ p, MemPair M F c p ↔ MemPair M G c p)
    (hContract : ∀ c, M.mem c n → (∀ p, MemPair M F c p ↔ MemPair M G c p) ∨
      (MemPair M F c y ∧ Ancestor M C n G y c ∧ ∀ p, RestrictedParent true M C n G V c p → M.mem p y)) :
    ∀ c p, RestrictedParent true M C n F V c p ↔ RestrictedParent true M C n G V c p := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hRefFG : ForestRefines M C n F G := by
    intro c p hcp
    rcases hContract c (hF.bounds hM.1 hcp).1 with hEq | ⟨hY,hAnc,_⟩
    · exact ancestor_direct_d hM hC hG ((hEq p).mp hcp)
    · exact (hF.unique c p y hcp hY) ▸ hAnc
  have hPrefixAnc (c a : M.Domain) (hcy : c=y ∨ M.mem c y) (hAnc : Ancestor M C n G a c) : Ancestor M C n F a c := by
    refine ancestor_transfer_on_chain_d hM hC hF hG (fun z p hz hZP => ?_) hAnc
    have hzy : z=y ∨ M.mem z y := by
      rcases hz with he | hZC
      · exact he ▸ hcy
      · rcases hcy with he | hcy
        · exact Or.inr (he ▸ hZC.1)
        · exact Or.inr ((hw.mem hy).transitive c hcy z hZC.1)
    exact ancestor_direct_d hM hC hF ((hPrefix z hzy p).mpr hZP)
  obtain ⟨S,hS⟩ := select_forest_exists_d hM true hC hG hV
  have hSf := selects_to_false hS hPos
  have hAll := KP1Y.induction_d hM selAncSchema (selAncEnv C n F G V) (by
    intro c ih
    apply (selAncSchema_iff hM.1 C n F G V c).mpr
    intro p _ hRP
    have hpAnc := hRP.1.1
    have hc : M.mem c n := (hpAnc.bounds hM.1).2
    rcases hContract c hc with hEq | ⟨hY,hYAnc,hBelow⟩
    · obtain ⟨q,hCQ,hTail⟩ := ancestor_parent_cases_d hM hC hG hpAnc
      have hFCQ := (hEq q).mpr hCQ
      rcases hTail with he | hPQ
      · exact he ▸ ancestor_direct_d hM hC hF hFCQ
      · have hSP : MemPair M S c p := (hS.parents c p).mpr hRP
        have hSAnc := Selects.ancestor_of_between_d hM hC hSf hSP (ancestor_direct_d hM hC hG hCQ) hPQ.1
        have hqc : M.mem q c := hG.left c q hCQ
        have hFPQ : Ancestor M C n F p q := by
          refine ancestor_transfer_on_chain_d hM hC hF hS.forest (fun z z' hz hZZ => ?_) hSAnc
          have hzc : M.mem z c := by
            rcases hz with he | hZQ
            · exact he ▸ hqc
            · exact (hw.mem (hw.transitive n hG.width c hc)).transitive q hqc z hZQ.1
          exact (selAncSchema_iff hM.1 C n F G V z).mp (ih z hzc) z' (hS.forest.bounds hM.1 hZZ).2
            ((hS.parents z z').mp hZZ)
        exact ancestor_trans_d hM hC hF hFPQ (ancestor_direct_d hM hC hF hFCQ)
    · have hpy := hBelow p hRP
      have hPY := ancestor_between_d hM hC hG hpAnc hYAnc hpy
      exact ancestor_trans_d hM hC hF (hPrefixAnc y p (Or.inl rfl) hPY) (ancestor_direct_d hM hC hF hY))
  have hSelAnc (c p : M.Domain) (h : RestrictedParent true M C n G V c p) : Ancestor M C n F p c :=
    (selAncSchema_iff hM.1 C n F G V c).mp (hAll c) p (h.1.1.bounds hM.1).1 h
  intro c p
  constructor
  · intro hRP
    have hCandG : ParentCandidate true M C n G V c p := ⟨ancestor_refines_d hM hC hG hRefFG hRP.1.1,hRP.1.2⟩
    obtain ⟨p',hRP'⟩ := restricted_parent_exists_d hM true hC hG ⟨p,hCandG⟩
    have hp'F : ParentCandidate true M C n F V c p' := ⟨hSelAnc c p' hRP',hRP'.1.2⟩
    have hle1 := hRP.2 p' hRP'.1.1.1 hp'F
    have hle2 := hRP'.2 p hRP.1.1.1 hCandG
    have hpω := hw.transitive n hF.width p (hRP.1.1.bounds hM.1).1
    have he := nat_le_antisymm_d hM hC hpω hle2 hle1
    exact he ▸ hRP'
  · intro hRP
    exact ⟨⟨hSelAnc c p hRP,hRP.1.2⟩,fun q hq hQ => hRP.2 q hq ⟨ancestor_refines_d hM hC hG hRefFG hQ.1,hQ.2⟩⟩

/-- 严格单调映射在候选对应下保持“最大候选”。 -/
theorem greatest_map_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {s c : M.Domain} (hs : M.mem s C.omega) (hc : M.mem c C.omega)
    (CandX CandY : M.Domain → Prop) (φ : M.Domain → M.Domain → Prop)
    (hFun : ∀ a q q', φ a q → φ a q' → q=q')
    (hMono : ∀ a a' q q', φ a q → φ a' q' → M.mem a a' → M.mem q q')
    (hTot : ∀ a, CandX a → ∃ q, φ a q)
    (hCorr : ∀ q, CandY q ↔ ∃ a, CandX a ∧ φ a q)
    (hBX : ∀ a, CandX a → M.mem a s) (hBY : ∀ q, CandY q → M.mem q c) (q : M.Domain) :
    (CandY q ∧ ∀ q', M.mem q' c → CandY q' → q'=q ∨ M.mem q' q) ↔
      ∃ a, (CandX a ∧ ∀ a', M.mem a' s → CandX a' → a'=a ∨ M.mem a' a) ∧ φ a q := by
  have hw := omega_isOrdinal_d hM hC.omega
  constructor
  · rintro ⟨hq,hMax⟩
    obtain ⟨a,ha,hφ⟩ := (hCorr q).mp hq
    refine ⟨a,⟨ha,fun a' _ ha' => ?_⟩,hφ⟩
    obtain ⟨q',hφ'⟩ := hTot a' ha'
    have hq' : CandY q' := (hCorr q').mpr ⟨a',ha',hφ'⟩
    have hle := hMax q' (hBY q' hq') hq'
    have haω := hw.transitive s hs a (hBX a ha)
    have ha'ω := hw.transitive s hs a' (hBX a' ha')
    have hqω := hw.transitive c hc q (hBY q hq)
    rcases hw.wellOrder.linear.compare a' ha'ω a haω with he | hlt | hgt
    · exact Or.inl (hM.1.eq_of_same_members a' a he)
    · exact Or.inr hlt
    · have hqq := hMono a a' q q' hφ hφ' hgt
      rcases hle with he | hlt
      · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) q (he ▸ hqq))
      · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) q ((hw.mem hqω).transitive q' hlt q hqq))
  · rintro ⟨a,⟨ha,hMaxA⟩,hφ⟩
    refine ⟨(hCorr q).mpr ⟨a,ha,hφ⟩,fun q' _ hq' => ?_⟩
    obtain ⟨a',ha',hφ'⟩ := (hCorr q').mp hq'
    rcases hMaxA a' (hBX a' ha') ha' with he | hlt
    · subst a'
      exact Or.inl (hFun a q' q hφ' hφ)
    · exact Or.inr (hMono a' a q' q hφ' hφ hlt)

private def belowEnv {M : SetTheory.Structure.{u}} (w Hts hc : M.Domain) : Env M 3 :=
  ((oneEnv w).push Hts).push hc

private def belowSchema : Project.Delta0UnarySchema 3 where
  body := Project.Formula.existsMem (.bound 3) (.conj (memPairFormula (.bound 3) (.bound 1) (.bound 0)) (.mem (.bound 0) (.bound 2)))
  freeClosed := by
    simp [memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.conj (memPairFormula_delta0 _ _ _) (.mem _ _))

/-- 每条父边严格降低高度，则全部祖先严格降低高度。 -/
theorem ancestor_height_decrease_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {n P Hts : M.Domain} (hP : Forest M C.omega n P)
    (hH : Graph M Hts n C.omega)
    (hEdge : ∀ c p hc hp, MemPair M P c p → MemPair M Hts c hc → MemPair M Hts p hp → M.mem hp hc)
    {a c ha hc : M.Domain} (hAnc : Ancestor M C n P a c) (hHA : MemPair M Hts a ha) (hHC : MemPair M Hts c hc) :
    M.mem ha hc := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hcω := (hH.bounds hM.1 hHC).2
  obtain ⟨S,hS⟩ := SetTheory.KP.separation_exists_d (KP1Y.models_weakKP hM) belowSchema (belowEnv C.omega Hts hc) n
  have hRows (z : M.Domain) : M.mem z S ↔ M.mem z n ∧ ∃ h, M.mem h C.omega ∧ MemPair M Hts z h ∧ M.mem h hc := by
    refine (hS z).trans (and_congr_right fun _ => ?_)
    simp only [belowSchema,belowEnv,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
      memPairFormula_iff hM.1,Project.Formula.satisfies_mem_iff]
    rfl
  obtain ⟨p0,hP0,hTail⟩ := ancestor_parent_cases_d hM hC hP hAnc
  obtain ⟨h0,h0ω,hH0⟩ := hH.total p0 (hP.bounds hM.1 hP0).2
  have hp0S := (hRows p0).mpr ⟨(hP.bounds hM.1 hP0).2,h0,h0ω,hH0,hEdge c p0 hc h0 hP0 hHC hH0⟩
  have haS : M.mem a S := by
    rcases hTail with he | hAP
    · exact he ▸ hp0S
    · refine ancestor_closed_d hM hC hP (fun z z' hz hZZ => ?_) hp0S hAP
      obtain ⟨_,hz,hzω,hHZ,hzc⟩ := (hRows z).mp hz
      obtain ⟨hz',hz'ω,hHZ'⟩ := hH.total z' (hP.bounds hM.1 hZZ).2
      exact (hRows z').mpr ⟨(hP.bounds hM.1 hZZ).2,hz',hz'ω,hHZ',
        (hw.mem hcω).transitive hz hzc hz' (hEdge z z' hz hz' hZZ hHZ hHZ')⟩
  obtain ⟨_,h,_,hHa,hlt⟩ := (hRows a).mp haS
  exact (hH.unique a h ha hHa hHA) ▸ hlt

end KP1Y.OneYFinite.LowerHelp
