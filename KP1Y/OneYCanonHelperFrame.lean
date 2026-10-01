import KP1Y.OneYCanonHelperOrder

/-! 外部继承帧F的实际水平复制F'与目标第0行P0的结构事实：前缀行一致、P0细化F'、
源第0行祖先沿同块复制运输到P0、低行root复制链，以及活动层0时root副本的父项与底值。 -/
namespace KP1Y.OneYFinite.TerminalBase
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
open ReconstructionCanonical Reconstruction MountainReconstruction ReconstructionRecovery
universe u

theorem restricted_true_iff_false {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {m F V c p : M.Domain}
    (hPos : ∀ c v, MemPair M V c v → M.mem C.zero v) :
    RestrictedParent true M C m F V c p ↔ RestrictedParent false M C m F V c p := by
  have hCand (q : M.Domain) : ParentCandidate true M C m F V c q ↔ ParentCandidate false M C m F V c q := by
    constructor
    · rintro ⟨hAnc,x,hx,y,hy,hX,hY,hxy,_⟩
      exact ⟨hAnc,x,hx,y,hy,hX,hY,hxy,trivial⟩
    · rintro ⟨hAnc,x,hx,y,hy,hX,hY,hxy,_⟩
      exact ⟨hAnc,x,hx,y,hy,hX,hY,hxy,by simpa [PositiveValue] using hPos q x hX⟩
  constructor
  · rintro ⟨h1,h2⟩
    exact ⟨(hCand p).mp h1,fun q hq hQ => h2 q hq ((hCand q).mpr hQ)⟩
  · rintro ⟨h1,h2⟩
    exact ⟨(hCand p).mpr h1,fun q hq hQ => h2 q hq ((hCand q).mp hQ)⟩

theorem selects_false_of_true {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {m F V P : M.Domain}
    (hS : Selects true M C m F V P) (hPos : ∀ c v, MemPair M V c v → M.mem C.zero v) : Selects false M C m F V P :=
  ⟨hS.inherited,hS.values,hS.forest,fun c p => (hS.parents c p).trans (restricted_true_iff_false hPos)⟩

/-- 有限前缀内，最右较小值选择只读该前缀的帧行与数值。 -/
theorem restricted_prefix_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) (positive : Bool) {m n F G V W cut c p : M.Domain}
    (hF : Forest M C.omega m F) (hG : Forest M C.omega n G) (hCut : M.mem cut C.omega)
    (hCutM : M.MemberSubset cut m) (hCutN : M.MemberSubset cut n) (hc : M.mem c cut)
    (hRows : RowsAgreeOn M F G cut) (hVals : RowsAgreeOn M V W cut) :
    RestrictedParent positive M C m F V c p ↔ RestrictedParent positive M C n G W c p := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hCand (q : M.Domain) : ParentCandidate positive M C m F V c q ↔ ParentCandidate positive M C n G W c q := by
    have hAnc := ancestor_common_prefix_iff_d hM hC hF hG hCut hCutM hCutN hc hRows (a := q)
    constructor
    · rintro ⟨hA,x,hx,y,hy,hX,hY,hxy,hPos⟩
      have hq : M.mem q cut := (hw.mem hCut).transitive c hc q hA.1
      exact ⟨hAnc.mp hA,x,hx,y,hy,(hVals q hq x).mp hX,(hVals c hc y).mp hY,hxy,hPos⟩
    · rintro ⟨hA,x,hx,y,hy,hX,hY,hxy,hPos⟩
      have hq : M.mem q cut := (hw.mem hCut).transitive c hc q hA.1
      exact ⟨hAnc.mpr hA,x,hx,y,hy,(hVals q hq x).mpr hX,(hVals c hc y).mpr hY,hxy,hPos⟩
  constructor
  · rintro ⟨h1,h2⟩
    exact ⟨(hCand p).mp h1,fun q hq hQ => h2 q hq ((hCand q).mpr hQ)⟩
  · rintro ⟨h1,h2⟩
    exact ⟨(hCand p).mpr h1,fun q hq hQ => h2 q hq ((hCand q).mp hQ)⟩

theorem parent_copy_strict_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) {b a c x y : M.Domain} (hac : M.mem a c)
    (hx : CopyCoordinates.ParentCopy M C T A b a x) (hy : CopyCoordinates.ParentCopy M C T A b c y) : M.mem x y := by
  obtain ⟨J,hJ,hRows⟩ := CopyCoordinates.parent_copy_graph_exists_d hM hC hT hA hx.2.1
  exact hJ.strict a hx.1 c hy.1 hac x y ((hRows a x).mpr hx) ((hRows c y).mpr hy)

private def rootChainSchema : Project.UnarySchema 17 where
  body := .forallE (.imp (CopyCoordinates.parentCopyFormula ⟨.bound 18,.bound 17,.bound 16,.bound 15,.bound 14⟩
      ⟨.bound 13,.bound 12,.bound 11,.bound 10,.bound 9,.bound 8⟩ ⟨.bound 7,.bound 6,.bound 5,.bound 4⟩
      (.bound 1) (.bound 6) (.bound 0))
    (.imp (.mem (.bound 0) (.bound 3)) (.disj (Project.Formula.extensionalEq (.bound 6) (.bound 0))
      (ancestorFormula ⟨.bound 18,.bound 17,.bound 16,.bound 15,.bound 14⟩ (.bound 3) (.bound 2) (.bound 6) (.bound 0)))))
  freeClosed := by
    have hC : (⟨.bound 18,.bound 17,.bound 16,.bound 15,.bound 14⟩ : ExpressionData (Project.Term 19)).Closed := ⟨rfl,rfl,rfl,rfl,rfl⟩
    have hMap := CopyCoordinates.parentCopyFormula_freeClosed hC
      (T := ⟨.bound 13,.bound 12,.bound 11,.bound 10,.bound 9,.bound 8⟩) ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
      (A := ⟨.bound 7,.bound 6,.bound 5,.bound 4⟩) ⟨rfl,rfl,rfl,rfl⟩ (.bound 1) (.bound 6) (.bound 0) rfl rfl rfl
    have hAnc := ancestorFormula_freeClosed hC (.bound 3) (.bound 2) (.bound 6) (.bound 0) rfl rfl rfl rfl
    simp [Definitional.Formula.FreeClosed,hMap,hAnc]

private def rootChainEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : CopyCoordinates.Context M.Domain) (W G : M.Domain) : Env M 17 :=
  ((((((((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push T.addPairs).push T.plus).push T.mulPairs).push T.times).push T.diffPairs).push T.difference).push A.last).push A.root).push A.length).push A.first).push W).push G

private theorem rootChainSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (A : CopyCoordinates.Context M.Domain) (W G b : M.Domain) :
    Project.Formula.satisfies ((rootChainEnv C T A W G).push b) rootChainSchema.body ↔
      ∀ t, CopyCoordinates.ParentCopy M C T A b A.root t → M.mem t W → (A.root=t ∨ Ancestor M C W G A.root t) := by
  simp only [rootChainSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    CopyCoordinates.parentCopyFormula_iff he,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he,ancestorFormula_iff he]
  rfl

section
variable {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain}
  {m V P H level index n OldTop NewTop Bottom : M.Domain} {R : RowStateSpace M.Domain}
  {X Y : CopiedMountain.Data M.Domain} {A : CopyCoordinates.Context M.Domain}

theorem Base.source_parents_zero (hM : M.Models KP1Y.theory)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) : MemPair M X.parents C.zero P :=
  (h.fromRun.parents C.zero P).mpr ⟨V,h.run.initial_row_at_d hM⟩

theorem Base.zero_le_level (hM : M.Models KP1Y.theory) (hC : C.Valid M)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) : C.zero=level ∨ M.mem C.zero level := by
  classical
  by_cases he : level=C.zero
  · exact Or.inl he.symm
  · exact Or.inr ((hC.zero_mem_iff hM (h.level_nat hM hC)).mpr he)

/-- 源第0行中root是末列的祖先。 -/
theorem Base.root_last_d (hM : M.Models KP1Y.theory) (hC : C.Valid M)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) : Ancestor M C m P A.root A.last := by
  have hAnc := CopiedMountain.Terminal.source_root_ancestor_last_d hM hC h.source h.run h.fromRun (h.active_d hM hC)
    (h.source_parents_zero hM) (h.zero_le_level hM hC)
  exact h.fromRun.width ▸ hAnc

/-- 源第0行末列父项不在root左侧。 -/
theorem Base.last_parent_bad_d (hM : M.Models KP1Y.theory) (hC : C.Valid M)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) {p : M.Domain}
    (hP : MemPair M P A.last p) : A.root=p ∨ M.mem A.root p :=
  ancestor_le_parent_d hM hC h.run.base.forest hP (h.root_last_d hM hC)

/-- 源第0行祖先沿同块复制运输到目标第0行（低活动层：允许末列为终点）。 -/
theorem Base.target_ancestor_low_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) {P0 : M.Domain}
    (hP0 : MemPair M Y.parents C.zero P0) (hLow : M.mem C.zero level) {a q b a' q' : M.Domain}
    (hAnc : Ancestor M C m P a q) (hq : q=A.last ∨ M.mem q A.last)
    (hMapA : CopyCoordinates.ParentCopy M C T A b a a') (hMapQ : CopyCoordinates.ParentCopy M C T A b q q')
    (hq' : M.mem q' n) : Ancestor M C n P0 a' q' := by
  have hAncX : Ancestor M C X.width P a q := h.fromRun.width.symm ▸ hAnc
  have hRes := h.copies.low_ancestor_parent_copy_d hM hC hT h.coords h.source h.target h.run h.fromRun (h.active_d hM hC)
    hLow (h.source_parents_zero hM) hP0 hAncX hq hMapA hMapQ (h.width_eq.symm ▸ hq')
  exact h.width_eq ▸ hRes

/-- 源第0行祖先沿同块复制运输到目标第0行（终点在末列左侧，任意活动层）。 -/
theorem Base.target_ancestor_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) {P0 : M.Domain}
    (hP0 : MemPair M Y.parents C.zero P0) {a q b a' q' : M.Domain}
    (hAnc : Ancestor M C m P a q) (hq : M.mem q A.last)
    (hMapA : CopyCoordinates.ParentCopy M C T A b a a') (hMapQ : CopyCoordinates.ParentCopy M C T A b q q')
    (hq' : M.mem q' n) : Ancestor M C n P0 a' q' := by
  rcases h.zero_le_level hM hC with hZero | hLow
  · have hAncX : Ancestor M C X.width P a q := h.fromRun.width.symm ▸ hAnc
    have hRes := h.copies.high_ancestor_parent_copy_d hM hC hT h.coords h.source h.target
      (h.fromRun.width.symm ▸ h.last_m) (Or.inl hZero.symm) (h.source_parents_zero hM) hP0 hAncX hq hMapA hMapQ
      (h.width_eq.symm ▸ hq')
    exact h.width_eq ▸ hRes
  · exact h.target_ancestor_low_d hM hC hT hP0 hLow hAnc (Or.inr hq) hMapA hMapQ hq'

/-- 低活动层：目标第0行中root是它的每个同列复制的祖先（或等于）。 -/
theorem Base.root_chain_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) {P0 : M.Domain}
    (hP0 : MemPair M Y.parents C.zero P0) (hLow : M.mem C.zero level) {b c : M.Domain}
    (hMap : CopyCoordinates.ParentCopy M C T A b A.root c) (hc : M.mem c n) :
    A.root=c ∨ Ancestor M C n P0 A.root c := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hNotRoot : ¬M.mem A.root A.root := SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.root
  have hNotLast : ¬M.mem A.last A.root := fun hl => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.root
    ((hw.mem h.coords.root).transitive A.last hl A.root h.coords.below)
  have hAll := natural_induction_d hM rootChainSchema (rootChainEnv C T A n P0) hC.omega
    (fun z hz => (rootChainSchema_iff hM.1 C T A n P0 z).mpr (by
      intro t hMapT _
      have hZ := hM.1.eq_of_same_members z C.zero (fun a => iff_of_false (hz a) (hC.zero_empty a))
      subst z
      exact Or.inl (parent_copy_unique_d hM hC hT h.coords
        (CopyCoordinates.parent_copy_zero_d hM hC hT h.coords h.coords.root) hMapT)))
    (fun b hb ih next hSucc => (rootChainSchema_iff hM.1 C T A n P0 next).mpr (by
      intro t hMapT ht
      obtain ⟨boundary,_,hWidth⟩ := CopyCoordinates.encode_exists_d hM hC hT h.coords h.coords.last hb
      have hEq := CopyCoordinates.encode_unique hM.1 hT ((CopyCoordinates.parent_copy_bad_iff hNotRoot).mp hMapT)
        (CopyCoordinates.width_is_next_cut_d hM hC hT h.coords hSucc hWidth)
      subst hEq
      obtain ⟨cut,_,hCut⟩ := CopyCoordinates.encode_exists_d hM hC hT h.coords h.coords.root hb
      have hRootCopy : CopyCoordinates.ParentCopy M C T A b A.root cut := (CopyCoordinates.parent_copy_bad_iff hNotRoot).mpr hCut
      have hLastCopy : CopyCoordinates.ParentCopy M C T A b A.last t := (CopyCoordinates.parent_copy_bad_iff hNotLast).mpr hWidth
      have hCutT := CopyCoordinates.cut_lt_width_d hM hC hT h.coords hWidth hCut
      have hCutN := (hw.mem h.n_nat).transitive t ht cut hCutT
      have hStep := h.target_ancestor_low_d hM hC hT hP0 hLow (h.root_last_d hM hC) (Or.inl rfl) hRootCopy hLastCopy ht
      rcases (rootChainSchema_iff hM.1 C T A n P0 b).mp ih cut hRootCopy hCutN with he | hAnc
      · exact Or.inr (he ▸ hStep)
      · have hForest : Forest M C.omega n P0 := h.width_eq ▸ h.target.forest C.zero P0 hP0
        exact Or.inr (ancestor_trans_d hM hC hForest hAnc hStep)))
  exact (rootChainSchema_iff hM.1 C T A n P0 b).mp (hAll b hMap.2.1) c hMap hc

/-- 活动层0：root的任一复制列在目标第0行的父项就是源root的父项（不平移）。 -/
theorem Base.root_copy_high_parent_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) (hZero : level=C.zero) {P0 : M.Domain}
    (hP0 : MemPair M Y.parents C.zero P0) {b c p : M.Domain}
    (hMap : CopyCoordinates.ParentCopy M C T A b A.root c) (hc : M.mem c n) :
    MemPair M P0 c p ↔ MemPair M P A.root p := by
  rw [← h.target_zero_iff hM hP0 c p,h.copies.parents C.zero c p,
    CopiedMountain.Terminal.parent_copied_root_high_iff_d hM hC hT h.coords (Or.inl hZero) hMap,h.source_zero_iff hM]
  exact ⟨And.right,fun hp => ⟨hc,hp⟩⟩

/-- 活动层0：root的任一复制列的目标底值就是源root的底值。 -/
theorem Base.root_copy_high_value_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) (hZero : level=C.zero) {b c : M.Domain}
    (hMap : CopyCoordinates.ParentCopy M C T A b A.root c) (hc : M.mem c n) (v : M.Domain) :
    MemPair M Bottom c v ↔ MemPair M V A.root v := by
  have hRootN := h.last_subset_d hM hC hT A.root h.coords.below
  have hcY : M.mem c Y.width := h.width_eq ▸ hc
  have hRootY : M.mem A.root Y.width := h.width_eq ▸ hRootN
  have hRows : ∀ r, M.mem r C.omega → ∀ p, CopiedMountain.ParentAt M Y r c p ↔ CopiedMountain.ParentAt M Y r A.root p := by
    intro r hr p
    have hHigh : level=r ∨ M.mem level r := by
      rw [hZero]
      classical
      by_cases he : r=C.zero
      · exact Or.inl he.symm
      · exact Or.inr ((hC.zero_mem_iff hM hr).mpr he)
    rw [h.copies.parents r c p,CopiedMountain.Terminal.parent_copied_root_high_iff_d hM hC hT h.coords hHigh hMap,
      h.copies.original_parents_d hM hC h.coords hRootN h.coords.below]
    exact ⟨And.right,fun hp => ⟨hc,hp⟩⟩
  have hTops : ∀ t, MemPair M NewTop c t ↔ MemPair M NewTop A.root t := fun t =>
    (h.newTop.parent_copy_iff_d hM hC hT h.coords h.coords.below hcY hMap).trans
      (h.newTop.prefix_iff_d hM hC hT h.coords hRootY h.coords.below).symm
  exact (h.twin_value_d hM hC hT hcY hRootY hRows hTops v).trans (h.prefix_values_d hM hC hT A.root h.coords.below v)

theorem Base.zero_le_index (hM : M.Models KP1Y.theory) (hC : C.Valid M)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) : C.zero=index ∨ M.mem C.zero index := by
  classical
  by_cases he : index=C.zero
  · exact Or.inl he.symm
  · exact Or.inr ((hC.zero_mem_iff hM h.indexNat).mpr he)

theorem count_mem_of_le {count index b : M.Domain} (hCount : M.SuccessorOf count index)
    (hb : b=index ∨ M.mem b index) : M.mem b count := by
  rcases hb with he | hlt
  · subst he
    exact (hCount b).mpr (Or.inr (fun _ => Iff.rfl))
  · exact (hCount b).mpr (Or.inl hlt)

theorem successor_le_of_mem_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) {b next index : M.Domain}
    (hIndex : M.mem index C.omega) (hNext : M.SuccessorOf next b) (hb : M.mem b index) : next=index ∨ M.mem next index := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hbNat := hw.transitive index hIndex b hb
  exact ordinal_subset_cases_d hM (hw.mem (natural_successor_mem_d hM hC hbNat hNext)) (hw.mem hIndex) (fun t ht => by
    rcases (hNext t).mp ht with htb | he
    · exact (hw.mem hIndex).transitive b hb t htb
    · exact (hM.1.eq_of_same_members t b he).symm ▸ hb)

/-- 外部帧复制在源末列以前与原帧逐行相同。 -/
theorem Base.frame_prefix_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) {F F' : M.Domain}
    (hF : Forest M C.omega m F) (hF' : FrameCopy.Copies M C T A F index n F') : RowsAgreeOn M F F' A.last := by
  obtain ⟨count,hCount,hCF⟩ := hF'
  exact hCF.parent_prefix_d hM hC hT h.coords hF hCF.count_nat (count_mem_of_le hCount (h.zero_le_index hM hC))

/-- 目标中末列及其右侧的列都是某个源列(root,last]的同块ParentCopy像。 -/
theorem Base.decode_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) {c : M.Domain}
    (hc : M.mem c n) (hNot : ¬M.mem c A.last) :
    ∃ s b, CopyCoordinates.Source M A s ∧ CopyCoordinates.Encode M C T A s b c ∧
      CopyCoordinates.ParentCopy M C T A b s c := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hcNat := hw.transitive n h.n_nat c hc
  have hAfter : M.mem A.root c := by
    rcases hw.wellOrder.linear.compare c hcNat A.last h.coords.last with he | hlt | hgt
    · exact (hM.1.eq_of_same_members c A.last he).symm ▸ h.coords.below
    · exact False.elim (hNot hlt)
    · exact (hw.mem hcNat).transitive A.last hgt A.root h.coords.below
  obtain ⟨s,b,hRaw⟩ := CopyCoordinates.raw_decode_exists_d hM hC hT h.coords hcNat
  obtain ⟨hSource,hEncode⟩ := (CopyCoordinates.raw_decoded_active_iff hAfter).mp hRaw
  have hNotGood : ¬M.mem s A.root := fun hg => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.root
    ((hw.mem h.coords.root).transitive s hg A.root hSource.1)
  exact ⟨s,b,hSource,hEncode,(CopyCoordinates.parent_copy_bad_iff hNotGood).mpr hEncode⟩

/-- seam列是root的下一副本像。 -/
theorem seam_root_copy_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (hA : A.Valid M C) {b next c : M.Domain} (hSucc : M.SuccessorOf next b)
    (hEncode : CopyCoordinates.Encode M C T A A.last b c) : CopyCoordinates.ParentCopy M C T A next A.root c :=
  (CopyCoordinates.parent_copy_bad_iff (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.root)).mpr
    (CopyCoordinates.width_is_next_cut_d hM hC hT hA hSucc hEncode)

/-- 目标第0行细化外部帧的复制：每条P0边都是F'中的祖先关系。 -/
theorem Base.zero_refines_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) {F F' P0 : M.Domain}
    (hF : Selects true M C m F V P) (hF' : FrameCopy.Copies M C T A F index n F')
    (hP0 : MemPair M Y.parents C.zero P0) {c p : M.Domain} (hCP : MemPair M P0 c p) : Ancestor M C n F' p c := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hForest0 : Forest M C.omega n P0 := h.width_eq ▸ h.target.forest C.zero P0 hP0
  have hc : M.mem c n := (hForest0.bounds hM.1 hCP).1
  have hPrefix := h.frame_prefix_d hM hC hT hF.inherited hF'
  have hLastM : M.MemberSubset A.last m := fun t ht => (hw.mem h.m_nat).transitive A.last h.last_m t ht
  have hFF' := hF'.forest
  obtain ⟨count,hCount,hCF⟩ := hF'
  have hRootLast : M.mem C.zero C.one → Ancestor M C m F A.root A.last :=
    fun _ => hF.ancestor_inherited_d hM hC (h.root_last_d hM hC)
  classical
  by_cases hcl : M.mem c A.last
  · have hPc := (h.source_zero_iff hM c p).mp ((h.copies.original_parents_d hM hC h.coords hc hcl).mp
      ((h.target_zero_iff hM hP0 c p).mpr hCP))
    exact (ancestor_common_prefix_iff_d hM hC hF.inherited hFF' h.coords.last hLastM (h.last_subset_d hM hC hT) hcl hPrefix).mp
      (hF.parent_ancestor hPc)
  · obtain ⟨s,b,hSource,hEncode,hMap⟩ := h.decode_d hM hC hT hc hcl
    rcases hSource.2 with hsl | hs
    · have hEnc : CopyCoordinates.Encode M C T A A.last b c := hsl ▸ hEncode
      have hbIndex := (CopyCoordinates.seam_lt_width_iff_d hM hC hT h.coords hEnc h.widthN).mp hc
      obtain ⟨next,_,hSucc,hPos⟩ := CopyCoordinates.encode_seam_bms_d hM hC hT h.coords hEnc
      have hNextCount := count_mem_of_le hCount (successor_le_of_mem_d hM hC h.indexNat hSucc hbIndex)
      rcases h.zero_le_level hM hC with hZ | hLow
      · have hRootMap := seam_root_copy_d hM hC hT h.coords hSucc hEnc
        have hPRoot := (h.root_copy_high_parent_d hM hC hT hZ.symm hP0 hRootMap hc).mp hCP
        have hGood := h.run.base.forest.left A.root p hPRoot
        exact (MatrixCopy.CopyForest.ancestor_good_iff_d hM hC hT h.coords hF.inherited hCF h.last_m hNextCount hGood
          hRootLast h.coords.below hRootMap).mpr (hF.parent_ancestor hPRoot)
      · obtain ⟨p0,_,hP0X,hMapP⟩ := (CopiedMountain.Terminal.low_seam_parent_iff_d hM hC hT h.coords h.copies hEnc hc
          (h.level_nat hM hC) hLow).mp ((h.target_zero_iff hM hP0 c p).mpr hCP)
        have hLP := (h.source_zero_iff hM A.last p0).mp hP0X
        exact (MatrixCopy.CopyForest.ancestor_previous_root_iff_d hM hC hT h.coords hF.inherited hCF h.last_m hNextCount
          hEnc.2.1 hSucc hC.one_succ.predecessor_mem (h.last_parent_bad_d hM hC hLP) (h.run.base.forest.left A.last p0 hLP)
          hMapP hPos).mpr (hF.parent_ancestor hLP)
    · obtain ⟨q,hSQ,hMapQ⟩ := (h.nonroot_iff_d hM hC hT hP0 hSource.1 hs hMap hc).mp hCP
      have hbCount := count_mem_of_le hCount (h.block_bound_d hM hC hT hSource.1 (Or.inr hs) hMap hc)
      have hq : M.mem q A.last := (hw.mem h.coords.last).transitive s hs q (h.run.base.forest.left s q hSQ)
      exact (MatrixCopy.CopyForest.ancestor_copy_iff_d hM hC hT h.coords hF.inherited hCF h.last_m hbCount hRootLast hq hs
        hMapQ hMap).mpr (hF.parent_ancestor hSQ)

end

end KP1Y.OneYFinite.TerminalBase
