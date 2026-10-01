import KP1Y.OneYLowerHelpExtract
import KP1Y.OneYLowerTopBound
import KP1Y.OneYLowerCanonDepth

/-! LANE-B helper：lower 层伪父Top界（原 `pseudoTopBound_of_upper_selections` /
`badAtLowerCopiedBase_lowerTopBound`）。源k+1层父图 Qnext 自身作为继承帧，其帧复制的每条边
严格降低目标高度；上层出口选出的 Pnext 因而沿目标伪父选择严格降高度。 -/
namespace KP1Y.OneYFinite.LowerHelp
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite KP1Y.OneYFinite.CopiedMountain KP1Y.OneYFinite.CopyCoordinates KP1Y.OneYFinite.TowerCanon
universe u

/-- 真实提取父图的帧复制：每条边严格降低 Lower 复制目标的高度。 -/
theorem frame_next_height_decrease_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Lower.Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} {n : M.Domain}
    (hCopy : Lower.Copies M C T D n Y) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H Top Qs N FQ : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain) (hExt : Extraction M C m V P Top Qs)
    (hPositive : ∀ i v, MemPair M V i v → M.mem C.zero v) (hFQ : FrameCopy.Copies M C T D.coordinates Qs N n FQ) :
    ∀ c p hc hp, MemPair M FQ c p → MemPair M Y.heights c hc → MemPair M Y.heights p hp → M.mem hp hc := by
  have hω := omega_isOrdinal_d hM hC.omega
  have hA := hD.coordinates
  have hQs := hExt.numeric_row.forest
  have hFQf := FrameCopy.Copies.forest hFQ
  have hDrop (s q hs hq : M.Domain) (hSQ : MemPair M Qs s q) (hHS : MemPair M D.mountain.heights s hs)
      (hHQ : MemPair M D.mountain.heights q hq) :
      M.mem hq hs ∧ ∃ Frow, MemPair M D.mountain.parents hq Frow ∧ Ancestor M C D.mountain.width Frow q s := by
    obtain ⟨U,Frow,hRow⟩ := hRun.at_exists_d (hD.mountain.heights.bounds hM.1 hHQ).2
    obtain ⟨hqs,_,_,hRel⟩ := hExt.ancestor_height_root_d hM hC hRun hFrom.heights hPositive
      (ancestor_direct_d hM hC hQs hSQ) hHQ hHS hRow
    refine ⟨hqs,Frow,(hFrom.parents hq Frow).mpr ⟨U,hRow⟩,?_⟩
    rw [hFrom.width]
    rcases hRel with he | hAnc
    · subst q
      exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) s (hQs.left s s hSQ))
    · exact hAnc
  have hXw (z : M.Domain) (hz : z=D.coordinates.last ∨ M.mem z D.coordinates.last) : M.mem z D.mountain.width :=
    hz.elim (fun he => he ▸ hD.last) (fun h => (hω.mem hD.mountain.width).transitive D.coordinates.last hD.last z h)
  intro c p hc hp hCP hHC hHP
  have hcn := (hFQf.bounds hM.1 hCP).1
  have hpn := (hFQf.bounds hM.1 hCP).2
  have hcNat := hω.transitive n hFQf.width c hcn
  rcases hω.wellOrder.linear.compare c hcNat D.coordinates.last hA.last with he | hlt | hgt
  · have hOld : c=D.coordinates.last ∨ M.mem c D.coordinates.last := Or.inl (hM.1.eq_of_same_members _ _ he)
    have hSQ := (FrameCopy.Copies.original_parent_iff_d hM hC hT hA hQs hFQ hOld hcn p).mp hCP
    have hpOld : p=D.coordinates.last ∨ M.mem p D.coordinates.last := Or.inr (hOld.elim (fun he => he ▸ hQs.left c p hSQ)
      (fun h => (hω.mem hA.last).transitive c h p (hQs.left c p hSQ)))
    exact (hDrop c p hc hp hSQ ((hCopy.original_heights_d hM hC hD hcn hOld).mp hHC)
      ((hCopy.original_heights_d hM hC hD hpn hpOld).mp hHP)).1
  · have hOld : c=D.coordinates.last ∨ M.mem c D.coordinates.last := Or.inr hlt
    have hSQ := (FrameCopy.Copies.original_parent_iff_d hM hC hT hA hQs hFQ hOld hcn p).mp hCP
    have hpOld : p=D.coordinates.last ∨ M.mem p D.coordinates.last :=
      Or.inr ((hω.mem hA.last).transitive c hlt p (hQs.left c p hSQ))
    exact (hDrop c p hc hp hSQ ((hCopy.original_heights_d hM hC hD hcn hOld).mp hHC)
      ((hCopy.original_heights_d hM hC hD hpn hpOld).mp hHP)).1
  · have hRootC : M.mem D.coordinates.root c := (hω.mem hcNat).transitive D.coordinates.last hgt D.coordinates.root hA.below
    obtain ⟨s,b,hRaw⟩ := raw_decode_exists_d hM hC hT hA hcNat
    obtain ⟨hSource,hEnc⟩ := (raw_decoded_active_iff hRootC).mp hRaw
    obtain ⟨q,hqLast,hSQ,hMap⟩ := (FrameCopy.Copies.encoded_parent_iff_d hM hC hT hA hQs hFQ hSource hEnc hcn p).mp hCP
    obtain ⟨hs,_,hHS⟩ := hD.mountain.heights.total s (hXw s hSource.2)
    obtain ⟨hq,_,hHQ⟩ := hD.mountain.heights.total q (hXw q (Or.inr hqLast))
    have hcRows := (hCopy.canon_copy_heights_d hM hC hT hD (Or.inr hSource.1) hSource.2 hEnc hcn hHS).mp hHC
    have hpRows := (hCopy.parent_copy_heights_d hM hC hT hD hqLast hpn hMap hHQ).mp hHP
    obtain ⟨hqs,Frow,hRowX,hAncRow⟩ := hDrop s q hs hq hSQ hHS hHQ
    rcases hcRows with ⟨_,_,_,off,_,hTimes,hAdd⟩ | ⟨hOutS,hcs⟩
    · rcases hpRows with ⟨_,_,_,off',_,hTimes',hAdd'⟩ | ⟨_,hpq⟩
      · have hoo := hT.mul.mul_unique hM.1 hTimes' hTimes
        subst off'
        exact (add_same_right_lt_iff_d hM hC hT hAdd' hAdd).mpr hqs
      · subst hp
        have hsNat := (hD.mountain.heights.bounds hM.1 hHS).2
        have hOffNat := (hAdd.bounds hM.1 hT.add).2.1
        exact KP1Y.Arithmetic.sum_base_subset_d hM (hω.mem hsNat) ((hT.add.add_iff_sum hM hsNat hOffNat).mp hAdd) hq hqs
    · subst hc
      rcases hpRows with ⟨hConeQ,_⟩ | ⟨_,hpq⟩
      · have hFloor : D.floor=hq ∨ M.mem D.floor hq := by
          obtain ⟨h,_,hHQ',hFl,_⟩ := hConeQ
          exact (hD.mountain.heights.unique q h hq hHQ' hHQ) ▸ hFl
        exact False.elim (hOutS ((Lower.in_cone_ancestor_iff_d hM hC hD hRun hFrom hFloor hRowX hAncRow).mp hConeQ))
      · exact hpq ▸ hqs

/-- (H-bound) 以新列伪父公式为参数的 lower 层伪父Top界。 -/
theorem lower_layer_pseudo_top_bound_of_formula_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H K level N n : M.Domain} {A : CopyCoordinates.Context M.Domain}
    (hLayers : LayerRun M C m L V P H) (hBad : BadAt M C m L H K level A.last A.root)
    (hN : CopyCoordinates.Width M C T A N n)
    {k W Q J oldTop Qnext newTop Pnext : M.Domain} {D : Lower.Context M.Domain} {Y : Data M.Domain}
    (hData : LowerLayerData M C T A m L H K k n W Q J oldTop Qnext D Y)
    (hNew : Graph M newTop n C.omega) (hPos : ∀ c v, MemPair M newTop c v → M.mem C.zero v)
    (hInputs : LowerInputs M C T D m N n oldTop Qnext newTop Pnext) (hFormula : PseudoCopyFormula M C T D Y) :
    ReconstructionSelection.PseudoTopBound M C Y newTop := by
  have hD := hData.context
  have hY := hData.target
  have hCopy := hData.copies
  obtain ⟨G,hG⟩ := graph_pseudo_forest_exists_d hM hC hY
  obtain ⟨F,F',hSel,hF',hIff⟩ := lower_layer_extract_of_formula_d hM hC hT hLayers hBad hN hData hNew hPos hInputs hG hFormula
  have hAD := hData.coordinates
  subst hAD
  have hSelG : Selects true M C n G newTop Pnext := (hIff Pnext).mpr (hInputs.select.1 F F' hSel hF')
  obtain ⟨FQ,hFQ⟩ := FrameCopy.copies_exists_d hM hC hT hD.coordinates hSel.forest hN
  have hSelQ := hInputs.select.1 Qnext FQ (selects_self_d hM hC hSel) hFQ
  have hEdge := frame_next_height_decrease_d hM hC hT hD hCopy hData.run hData.from_run hData.extraction
    (hLayers.at_rooted hM.1 hData.layer).positive hFQ
  have hHn : Graph M Y.heights n C.omega := hCopy.width ▸ hY.heights
  have hDec : Lower.ExtractedHeightDecrease M Y Pnext := by
    intro c p hc hp hCP hHC hHP
    exact ancestor_height_decrease_d hM hC (FrameCopy.Copies.forest hFQ) hHn hEdge
      (hSelQ.ancestor_inherited_d hM hC (ancestor_direct_d hM hC hSelQ.forest hCP)) hHP hHC
  have hNewY : Graph M newTop Y.width C.omega := by rw [hCopy.width]; exact hNew
  have hSelY : Selects true M C Y.width G newTop Pnext := by rw [hCopy.width]; exact hSelG
  exact Lower.pseudo_top_bound_of_decreasing_selection_d hM hC hY hNewY hPos hG hSelY hDec

end KP1Y.OneYFinite.LowerHelp
