import KP1Y.OneYLowerHelpRoot
import KP1Y.OneYLowerPseudoTransport

/-! LANE-B helper：目标伪父森林的选择等于源伪父帧复制的选择（原 `pseudo_select_eq_frameCopy`）。
新列伪父公式以命题 `PseudoCopyFormula` 给出（原 `pseudo_parent_parentCopy`）；收缩列的上层选择在好部
由真实上层出口 `UpperSelect` 与源提取的同高Top单调性导出。 -/
namespace KP1Y.OneYFinite.LowerHelp
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite KP1Y.OneYFinite.CopiedMountain KP1Y.OneYFinite.CopyCoordinates KP1Y.OneYFinite.TowerCanon
universe u

/-- 新列 c=Encode s b（root<s≤last）的目标伪父：源伪父为 root 且 s 与 root 同高时收缩到 root，
否则为源伪父的 ParentCopy 像（原 `pseudo_parent_parentCopy`）。 -/
def PseudoCopyFormula (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (D : Lower.Context M.Domain) (Y : Data M.Domain) : Prop :=
  ∀ s b c, M.mem D.coordinates.root s → (s=D.coordinates.last ∨ M.mem s D.coordinates.last) →
    Encode M C T D.coordinates s b c → M.mem c Y.width → M.mem D.coordinates.last c →
    ∀ q, GraphPseudoParent M C Y c q ↔ ∃ p, GraphPseudoParent M C D.mountain s p ∧
      ((MemPair M D.mountain.heights s D.floor ∧ p=D.coordinates.root ∧ q=D.coordinates.root) ∨
        (¬(MemPair M D.mountain.heights s D.floor ∧ p=D.coordinates.root) ∧ ParentCopy M C T D.coordinates b p q))

/-- 单收缩：目标伪父森林与源伪父帧复制的受限父逐列相同。`hGood` 为收缩列的上层选择在好部。 -/
theorem pseudo_select_eq_frame_copy_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Lower.Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Lower.Copies M C T D n Y) {F N F' G newTop : M.Domain}
    (hFG : GraphPseudoForest M C D.mountain F) (hF' : FrameCopy.Copies M C T D.coordinates F N n F')
    (hG : GraphPseudoForest M C Y G) (hNew : Graph M newTop n C.omega)
    (hPos : ∀ c v, MemPair M newTop c v → M.mem C.zero v)
    (hRoot : Ancestor M C D.mountain.width F D.coordinates.root D.coordinates.last)
    (hFormula : PseudoCopyFormula M C T D Y)
    (hGood : ∀ s b c, M.mem D.coordinates.root s → M.mem s D.coordinates.last → Encode M C T D.coordinates s b c →
      M.mem c n → MemPair M D.mountain.heights s D.floor → MemPair M F s D.coordinates.root →
      ∀ p, RestrictedParent true M C n F' newTop c p → M.mem p D.coordinates.root) :
    ∀ c p, RestrictedParent true M C n G newTop c p ↔ RestrictedParent true M C n F' newTop c p := by
  have hω := omega_isOrdinal_d hM hC.omega
  have hA := hD.coordinates
  have hGn : Forest M C.omega n G := hCopy.width ▸ hG.forest
  have hF'f := FrameCopy.Copies.forest hF'
  have hnNat := hF'f.width
  have hRootLast := hA.below
  have hOrig (c : M.Domain) (hc : M.mem c n) (hOld : c=D.coordinates.last ∨ M.mem c D.coordinates.last) (p : M.Domain) :
      MemPair M G c p ↔ MemPair M F' c p :=
    (hG.rows c p).trans ((hCopy.pseudo_parent_original_iff_d hM hC hD hY hc hOld).trans ((hFG.rows c p).symm.trans
      (FrameCopy.Copies.original_parent_iff_d hM hC hT hA hFG.forest hF' hOld hc p).symm))
  have hOff (c : M.Domain) (hc : ¬M.mem c n) (p : M.Domain) : MemPair M G c p ↔ MemPair M F' c p :=
    iff_of_false (fun h => hc (hGn.bounds hM.1 h).1) (fun h => hc (hF'f.bounds hM.1 h).1)
  apply single_contraction_d hM hC hGn hF'f hNew hPos hA.root
  · intro c hcy p
    classical
    by_cases hc : M.mem c n
    · exact hOrig c hc (Or.inr (hcy.elim (fun he => he ▸ hRootLast)
        (fun h => (hω.mem (hA.last)).transitive D.coordinates.root hRootLast c h))) p
    · exact hOff c hc p
  · intro c hc
    have hcNat := hω.transitive n hnNat c hc
    rcases hω.wellOrder.linear.compare c hcNat D.coordinates.last hA.last with he | hlt | hgt
    · exact Or.inl (hOrig c hc (Or.inl (hM.1.eq_of_same_members _ _ he)))
    · exact Or.inl (hOrig c hc (Or.inr hlt))
    · have hRootC : M.mem D.coordinates.root c := (hω.mem hcNat).transitive D.coordinates.last hgt D.coordinates.root hRootLast
      obtain ⟨s,b,hRaw⟩ := raw_decode_exists_d hM hC hT hA hcNat
      obtain ⟨hSource,hEnc⟩ := (raw_decoded_active_iff hRootC).mp hRaw
      have hcY : M.mem c Y.width := by rw [hCopy.width]; exact hc
      have hNewRows := hFormula s b c hSource.1 hSource.2 hEnc hcY hgt
      have hCopyRows := FrameCopy.Copies.encoded_parent_iff_d hM hC hT hA hFG.forest hF' hSource hEnc hc
      have hPLast (p : M.Domain) (hSP : MemPair M F s p) : M.mem p D.coordinates.last :=
        hSource.2.elim (fun he => he ▸ hFG.forest.left s p hSP)
          (fun h => (hω.mem hA.last).transitive s h p (hFG.forest.left s p hSP))
      classical
      by_cases hSpecial : MemPair M D.mountain.heights s D.floor ∧ MemPair M F s D.coordinates.root
      · right
        obtain ⟨hHS,hSY⟩ := hSpecial
        have hsLast : M.mem s D.coordinates.last := by
          rcases hSource.2 with he | h
          · subst s
            obtain ⟨h,_,hHL,hFH,_⟩ := hD.rise
            have hhf := hD.mountain.heights.unique D.coordinates.last h D.floor hHL hHS
            subst h
            exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) D.floor hFH)
          · exact h
        refine ⟨(hG.rows c D.coordinates.root).mpr ((hNewRows D.coordinates.root).mpr
          ⟨D.coordinates.root,(hFG.rows s D.coordinates.root).mp hSY,Or.inl ⟨hHS,rfl,rfl⟩⟩),?_,
          hGood s b c hSource.1 hsLast hEnc hc hHS hSY⟩
        have hNotRoot : ¬M.mem D.coordinates.root D.coordinates.root :=
          SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) D.coordinates.root
        obtain ⟨w,_,hW⟩ := encode_exists_d hM hC hT hA hA.root hEnc.2.1
        have hMapW : ParentCopy M C T D.coordinates b D.coordinates.root w := (parent_copy_bad_iff hNotRoot).mpr hW
        have hCW : MemPair M F' c w := (hCopyRows w).mpr ⟨D.coordinates.root,hRootLast,hSY,hMapW⟩
        have hAncW := ancestor_direct_d hM hC hF'f hCW
        rcases frame_root_seam_d hM hC hT hA hFG.forest hD.last hF' hRoot hMapW (hF'f.bounds hM.1 hCW).2 with he | hAnc
        · exact he ▸ hAncW
        · exact ancestor_trans_d hM hC hF'f hAnc hAncW
      · left
        intro q
        rw [hG.rows c q,hNewRows q,hCopyRows q]
        constructor
        · rintro ⟨p,hPP,⟨hHS,hpy,_⟩ | ⟨_,hMap⟩⟩
          · subst p
            exact False.elim (hSpecial ⟨hHS,(hFG.rows s D.coordinates.root).mpr hPP⟩)
          · have hSP := (hFG.rows s p).mpr hPP
            exact ⟨p,hPLast p hSP,hSP,hMap⟩
        · rintro ⟨p,_,hSP,hMap⟩
          refine ⟨p,(hFG.rows s p).mp hSP,Or.inr ⟨?_,hMap⟩⟩
          rintro ⟨hHS,hpy⟩
          subst p
          exact hSpecial ⟨hHS,hSP⟩

/-- `extract` 字段，以新列伪父公式为参数。 -/
theorem lower_layer_extract_of_formula_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H K level N n : M.Domain} {A : CopyCoordinates.Context M.Domain}
    (hLayers : LayerRun M C m L V P H) (hBad : BadAt M C m L H K level A.last A.root)
    (hN : CopyCoordinates.Width M C T A N n)
    {k W Q J oldTop Qnext newTop Pnext G : M.Domain} {D : Lower.Context M.Domain} {Y : Data M.Domain}
    (hData : LowerLayerData M C T A m L H K k n W Q J oldTop Qnext D Y)
    (hNew : Graph M newTop n C.omega) (hPos : ∀ c v, MemPair M newTop c v → M.mem C.zero v)
    (hInputs : LowerInputs M C T D m N n oldTop Qnext newTop Pnext) (hG : GraphPseudoForest M C Y G)
    (hFormula : PseudoCopyFormula M C T D Y) :
    ∃ F F', Selects true M C m F oldTop Qnext ∧ FrameCopy.Copies M C T A F N n F' ∧
      ∀ Q', Selects true M C n G newTop Q' ↔ Selects true M C n F' newTop Q' := by
  have hD := hData.context
  have hRootQ := lower_layer_next_root_d hM hC hLayers hBad hData
  obtain ⟨F,hFG,hFP,hTop,hSel,hWPos⟩ := lower_layer_source_d hM hC hLayers hData
  have hAD := hData.coordinates
  subst hAD
  have hRootF : Ancestor M C D.mountain.width F D.coordinates.root D.coordinates.last := by
    rw [hData.from_run.width]
    exact hSel.ancestor_inherited_d hM hC hRootQ
  obtain ⟨F',hF'⟩ := FrameCopy.copies_exists_d hM hC hT hD.coordinates hFG.forest hN
  refine ⟨F,F',hSel,hF',?_⟩
  have hSelN := hInputs.select.1 F F' hSel hF'
  have hω := omega_isOrdinal_d hM hC.omega
  have hRP := pseudo_select_eq_frame_copy_d hM hC hT hD hData.target hData.copies hFG hF' hG hNew hPos hRootF hFormula
    (by
      intro s b c hRootS hsLast hEnc hc hHS hSY p hRPc
      have hNotGood : ¬M.mem s D.coordinates.root := fun h => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM)
        s ((hω.mem hEnc.1).transitive D.coordinates.root hRootS s h)
      have hMapSC : ParentCopy M C T D.coordinates b s c := (parent_copy_bad_iff hNotGood).mpr hEnc
      obtain ⟨q,hq,hMapQ⟩ := (hInputs.select.2 s b c hRootS hsLast hMapSC hc p).mp ((hSelN.parents c p).mpr hRPc)
      have hqRoot := contracted_selected_good_d hM hC hData.run hData.from_run.heights hTop hFP hWPos hSel hSY hHS hD.floor hq
      have hpq := (parent_copy_good_iff hMapQ.2.1 hMapQ.1 hqRoot).mp hMapQ
      exact hpq ▸ hqRoot)
  have hGn : Forest M C.omega n G := hData.copies.width ▸ hG.forest
  intro Q'
  constructor
  · intro h
    exact ⟨FrameCopy.Copies.forest hF',h.values,h.forest,fun c p => (h.parents c p).trans (hRP c p)⟩
  · intro h
    exact ⟨hGn,h.values,h.forest,fun c p => (h.parents c p).trans (hRP c p).symm⟩

end KP1Y.OneYFinite.LowerHelp
