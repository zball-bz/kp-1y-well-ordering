import KP1Y.OneYMountainRelations

/-! 真实活动父边在所有较低提取层中的祖先及根/高度几何。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals
universe u

theorem LayerRun.active_parent_layer_ancestor_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {L : LayerStateSpace M.Domain}
    {V P H K WK PK k Wk Pk : M.Domain} (hLayers : LayerRun M C m L V P H)
    (hActiveLayer : RowAt M L.states H K WK PK) (hLowerLayer : RowAt M L.states H k Wk Pk)
    {R : RowStateSpace M.Domain} {J d U F x y : M.Domain} (hRows : RowRun M C m R WK PK J)
    (hRow : RowAt M R.states J d U F) (hParent : MemPair M F x y) (hLe : k=K ∨ M.mem k K) :
    Ancestor M C m Pk y x :=
  hLayers.ancestor_lower_d hM hC hLowerLayer hActiveLayer hLe (hRows.parent_refines_base_d hM hC hRow x y hParent)

theorem LayerRun.bad_root_layer_ancestor_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {L : LayerStateSpace M.Domain}
    {V P H K d x y k Wk Pk : M.Domain} (hLayers : LayerRun M C m L V P H)
    (hBad : BadAt M C m L H K d x y) (hLowerLayer : RowAt M L.states H k Wk Pk) (hLe : k=K ∨ M.mem k K) :
    Ancestor M C m Pk y x := by
  obtain ⟨WK,_,PK,_,hActiveLayer,J,hRows,U,_,F,_,hRow,hParent,_⟩ := hBad
  exact hLayers.active_parent_layer_ancestor_d hM hC hActiveLayer hLowerLayer hRows hRow hParent hLe

theorem LayerRun.active_parent_lower_root_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {L : LayerStateSpace M.Domain}
    {V P H K WK PK k Wk Pk : M.Domain} (hLayers : LayerRun M C m L V P H)
    (hActiveLayer : RowAt M L.states H K WK PK) (hLowerLayer : RowAt M L.states H k Wk Pk)
    {RK : RowStateSpace M.Domain} {JK d UK FK x y : M.Domain} (hActiveRows : RowRun M C m RK WK PK JK)
    (hActiveRow : RowAt M RK.states JK d UK FK) (hParent : MemPair M FK x y) (hLess : M.mem k K)
    {Rk : RowStateSpace M.Domain} {Jk Heights hy hx U F : M.Domain} (hLowerRows : RowRun M C m Rk Wk Pk Jk)
    (hHeights : HeightGraph M C m Rk Wk Jk Heights) (hHY : MemPair M Heights y hy) (hHX : MemPair M Heights x hx)
    (hRootRow : RowAt M Rk.states Jk hy U F) : M.mem hy hx ∧ Root M C m F x y := by
  have hk : M.mem k C.omega := by
    obtain ⟨_,_,hAt,_⟩ := hLowerLayer
    exact (hLayers.graph.bounds hM.1 hAt).1
  have hK : M.mem K C.omega := by
    obtain ⟨_,_,hAt,_⟩ := hActiveLayer
    exact (hLayers.graph.bounds hM.1 hAt).1
  obtain ⟨k',hSucc,hk'⟩ := hC.omega.1.2 k hk
  have hLe : k'=K ∨ M.mem k' K := by
    have hKO := (omega_isOrdinal_d hM hC.omega).mem hK
    apply ordinal_subset_cases_d hM ((omega_isOrdinal_d hM hC.omega).mem hk') hKO
    intro z hz
    rcases (hSucc z).mp hz with hzk | he
    · exact hKO.transitive k hLess z hzk
    · exact (hM.1.eq_of_same_members z k he).symm ▸ hLess
  obtain ⟨W',P',hNextLayer⟩ := hLayers.at_exists_d hk'
  have hAncestor := hLayers.active_parent_layer_ancestor_d hM hC hActiveLayer hNextLayer hActiveRows hActiveRow hParent hLe
  have hExtraction := hLayers.at_next hM.1 hSucc hLowerLayer hNextLayer
  exact hExtraction.ancestor_height_root_d hM hC hLowerRows hHeights (hLayers.at_rooted hM.1 hLowerLayer).positive
    hAncestor hHY hHX hRootRow

theorem LayerRun.bad_root_lower_root_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {L : LayerStateSpace M.Domain}
    {V P H K d x y k Wk Pk : M.Domain} (hLayers : LayerRun M C m L V P H) (hBad : BadAt M C m L H K d x y)
    (hLowerLayer : RowAt M L.states H k Wk Pk) (hLess : M.mem k K)
    {Rk : RowStateSpace M.Domain} {Jk Heights hy hx U F : M.Domain} (hLowerRows : RowRun M C m Rk Wk Pk Jk)
    (hHeights : HeightGraph M C m Rk Wk Jk Heights) (hHY : MemPair M Heights y hy) (hHX : MemPair M Heights x hx)
    (hRootRow : RowAt M Rk.states Jk hy U F) : M.mem hy hx ∧ Root M C m F x y := by
  obtain ⟨WK,_,PK,_,hActiveLayer,JK,hActiveRows,UK,_,FK,_,hActiveRow,hParent,_⟩ := hBad
  exact hLayers.active_parent_lower_root_d hM hC hActiveLayer hLowerLayer hActiveRows hActiveRow hParent hLess hLowerRows hHeights hHY hHX hRootRow

end KP1Y.OneYFinite
