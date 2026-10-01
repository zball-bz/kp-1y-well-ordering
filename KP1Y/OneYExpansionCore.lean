import KP1Y.OneYCopyTower
import KP1Y.OneYTowerReconstruction

/-! 原展开算法的实际三分支语义与单点总性；horizon为严格最大界的前驱。 -/
namespace KP1Y.OneYFinite.Expansion
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite
universe u

def Horizon (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (s m horizon : M.Domain) : Prop :=
  ∃strict, M.mem strict C.omega ∧ SequenceBound M C m s strict ∧ M.SuccessorOf strict horizon

theorem Horizon.natural_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {s m horizon : M.Domain} (h : Horizon M C s m horizon) : M.mem horizon C.omega := by
  obtain ⟨strict,hs,_,hSucc⟩ := h
  exact (omega_isOrdinal_d hM hC.omega).transitive strict hs horizon hSucc.predecessor_mem

theorem horizon_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {s m : M.Domain} (hm : M.mem m C.omega) (hS : Graph M s m C.omega)
    (hNe : ∃c, M.mem c m) : ∃horizon, Horizon M C s m horizon := by
  obtain ⟨strict,hStrict⟩ := sequence_bound_exists_d hM hC hm hS
  obtain ⟨horizon,_,hSucc,_⟩ := hStrict.predecessor_max_d hM hC hS hNe
  exact ⟨horizon,strict,hStrict.1.1,hStrict,hSucc⟩

theorem Horizon.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {s m a b : M.Domain} (h : Horizon M C s m a) (h' : Horizon M C s m b) : a=b := by
  have ha := h.natural_d hM hC
  obtain ⟨strict,_,hBound,hSucc⟩ := h
  obtain ⟨strict',_,hBound',hSucc'⟩ := h'
  have hss := hBound.unique_d hM hC hBound'
  subst strict'
  exact Structure.SuccessorOf.predecessor_eq hM.1 ((omega_isOrdinal_d hM hC.omega).mem ha) hSucc hSucc'

theorem Horizon.maximum_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {s m a : M.Domain} (hS : Graph M s m C.omega)
    (hNe : ∃c, M.mem c m) (h : Horizon M C s m a) :
    (∃c, M.mem c m ∧ MemPair M s c a) ∧ ∀c v, MemPair M s c v → v=a ∨ M.mem v a := by
  have ha := h.natural_d hM hC
  obtain ⟨strict,_,hStrict,hSucc⟩ := h
  obtain ⟨b,_,hSucc',hB,hMax⟩ := hStrict.predecessor_max_d hM hC hS hNe
  have hab := Structure.SuccessorOf.predecessor_eq hM.1 ((omega_isOrdinal_d hM hC.omega).mem ha) hSucc hSucc'
  subst b
  exact ⟨hB,hMax⟩

structure SuccessData (α : Type u) where
  linear : α
  initial : α
  space : LayerStateSpace α
  layers : α
  K : α
  level : α
  root : α
  horizon : α
  coordinates : CopyCoordinates.Context α
  width : α
  forests : α
  codes : α
  tower : α
  top : α

structure Successful (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (s m last N t : M.Domain) (W : SuccessData M.Domain) : Prop where
  linear : LinearForest M C.omega m W.linear
  selected : Selects true M C m W.linear s W.initial
  run : LayerRun M C m W.space s W.initial W.layers
  bad : BadAt M C m W.space W.layers W.K W.level last W.root
  horizon : Horizon M C s m W.horizon
  last : W.coordinates.last=last
  root : W.coordinates.root=W.root
  coordinates : W.coordinates.Valid M C
  width : CopyCoordinates.Width M C T W.coordinates N W.width
  tower : CopyTower.Tower M C T W.coordinates m W.space W.layers W.K W.level W.horizon W.width W.forests W.codes W.tower
  top : TowerReconstruction.AllOne M C W.width W.top
  reconstruction : TowerReconstruction.Assembles M C T.addPairs T.plus W.width W.forests W.codes W.tower W.horizon W.top t

def SuccessAt (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (s m last N t : M.Domain) : Prop := ∃W, Successful M C T s m last N t W

def Expands (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (s N t : M.Domain) : Prop :=
  M.mem N C.omega ∧ ∃m, M.mem m C.omega ∧ LegalAt M C.omega C.zero C.one s m ∧
    ((m=C.zero ∧ t=s) ∨ ∃last, M.mem last C.omega ∧ M.SuccessorOf m last ∧
      ((MemPair M s last C.one ∧ Prefix M t s last C.omega) ∨ SuccessAt M C T s m last N t))

theorem positive_ne_one_above_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a : M.Domain} (ha : M.mem a C.omega) (hPos : M.mem C.zero a) (hne : a≠C.one) : M.mem C.one a := by
  rcases (omega_isOrdinal_d hM hC.omega).wellOrder.linear.compare C.one hC.one_nat a ha with he | hlt | hlt
  · exact False.elim (hne (hM.1.eq_of_same_members C.one a he).symm)
  · exact hlt
  · rcases (hC.one_succ a).mp hlt with ha0 | he
    · exact False.elim (hC.zero_empty a ha0)
    · exact False.elim (hC.zero_empty C.zero ((hM.1.eq_of_same_members a C.zero he) ▸ hPos))

theorem success_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {s m last N a : M.Domain} (hLegal : LegalAt M C.omega C.zero C.one s m) (hLast : M.SuccessorOf m last)
    (hN : M.mem N C.omega) (hValue : MemPair M s last a) (hAbove : M.mem C.one a) : ∃t, SuccessAt M C T s m last N t := by
  obtain ⟨F,P,L,H,hF,hP,hLayers⟩ := legal_layers_exists_d hM hC hLegal
  obtain ⟨K,level,root,hBad⟩ := (bad_at_exists_iff_d hM hC hLayers hValue).mpr hAbove
  obtain ⟨horizon,hHorizon⟩ := horizon_exists_d hM hC hLegal.1.1 hLegal.1.2 ⟨last,hLast.predecessor_mem⟩
  obtain ⟨A,n,Forests,Codes,G,hAx,hAy,hA,hWidth,hTower⟩ := CopyTower.tower_from_bad_exists_d hM hC hT hLayers hBad (hHorizon.natural_d hM hC) hN
  obtain ⟨Top,t,hTop,hRebuild,_⟩ := TowerReconstruction.assemble_ones_exists_d hM hC hT.add hTower.width hTower.bound hTower.graph (fun _ _ => hTower.code_valid)
  exact ⟨t,⟨F,P,L,H,K,level,root,horizon,A,n,Forests,Codes,G,Top⟩,hF,hP,hLayers,hBad,hHorizon,hAx,hAy,hA,hWidth,hTower,hTop,hRebuild⟩

theorem Successful.legal_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {s m last N t : M.Domain} {W : SuccessData M.Domain} (h : Successful M C T s m last N t W) :
    LegalAt M C.omega C.zero C.one t W.width :=
  h.reconstruction.legal_d hM hC hT.add h.tower.width h.tower.bound h.tower.graph (fun _ _ => h.tower.code_valid) (h.top.legal_d hM hC h.tower.width)

theorem Expands.legal_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {s N t : M.Domain} (h : Expands M C T s N t) : M.mem s C.expressions ∧ M.mem N C.omega ∧ M.mem t C.expressions := by
  obtain ⟨hN,m,hm,hLegal,hCases⟩ := h
  refine ⟨(hC.expressions s).mpr ⟨m,hm,hLegal⟩,hN,(hC.expressions t).mpr ?_⟩
  rcases hCases with ⟨_,rfl⟩ | ⟨last,hl,hSucc,hDrop | ⟨W,hSuccess⟩⟩
  · exact ⟨m,hm,hLegal⟩
  · exact ⟨last,hl,prefix_legal_d hM hC hLegal hl (fun i hi => (hSucc i).mpr (.inl hi)) hDrop.2⟩
  · exact ⟨W.width,hSuccess.tower.width,hSuccess.legal_d hM hC hT⟩

theorem expands_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {s N : M.Domain} (hs : M.mem s C.expressions) (hN : M.mem N C.omega) : ∃t, Expands M C T s N t := by
  obtain ⟨m,hm,hLegal⟩ := (hC.expressions s).mp hs
  by_cases hm0 : m=C.zero
  · exact ⟨s,hN,m,hm,hLegal,.inl ⟨hm0,rfl⟩⟩
  · rcases natural_cases hM hC.omega hm with hEmpty | ⟨last,hl,hSucc⟩
    · exact False.elim (hm0 (hM.1.eq_of_same_members m C.zero (fun x => iff_of_false (hEmpty x) (hC.zero_empty x))))
    · obtain ⟨a,ha,hValue⟩ := hLegal.1.2.total last hSucc.predecessor_mem
      by_cases ha1 : a=C.one
      · subst a
        obtain ⟨t,hPrefix,_,_⟩ := legal_prefix_d hM hC hLegal hl (fun i hi => (hSucc i).mpr (.inl hi))
        exact ⟨t,hN,m,hm,hLegal,.inr ⟨last,hl,hSucc,.inl ⟨hValue,hPrefix⟩⟩⟩
      · obtain ⟨t,hSuccess⟩ := success_exists_d hM hC hT hLegal hSucc hN hValue (positive_ne_one_above_d hM hC ha (legal_values_positive hM.1 hLegal hValue) ha1)
        exact ⟨t,hN,m,hm,hLegal,.inr ⟨last,hl,hSucc,.inr hSuccess⟩⟩

theorem layer_space_unique {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain} {m : M.Domain}
    {L L' : LayerStateSpace M.Domain} (hL : L.Valid M C m) (hL' : L'.Valid M C m) : L=L' := by
  cases L with
  | mk R States =>
      cases L' with
      | mk R' States' =>
          have hr := row_state_space_unique he hL.rows hL'.rows
          change R=R' at hr
          subst R'
          have hs := he.eq_of_same_members States States' (fun state => (hL.states state).trans (hL'.states state).symm)
          subst States'
          rfl

theorem Successful.not_last_one_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} {s m last N t : M.Domain}
    {W : SuccessData M.Domain} (h : Successful M C T s m last N t W) : ¬MemPair M s last C.one := by
  intro hAt
  have hBad := (bad_at_exists_iff_d hM hC h.run hAt).mp ⟨W.K,W.level,W.root,h.bad⟩
  exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) C.one hBad

theorem Successful.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {s m last N t t' : M.Domain} {W W' : SuccessData M.Domain}
    (h : Successful M C T s m last N t W) (h' : Successful M C T s m last N t' W') : t=t' := by
  rcases W with ⟨F,P,L,H,K,level,root,B,A,n,Forests,Codes,G,Top⟩
  rcases W' with ⟨F',P',L',H',K',level',root',B',A',n',Forests',Codes',G',Top'⟩
  rcases h with ⟨hF,hP,hRun,hBad,hB,hAx,hAy,hA,hWidth,hTower,hTop,hRebuild⟩
  rcases h' with ⟨hF',hP',hRun',hBad',hB',hAx',hAy',hA',hWidth',hTower',hTop',hRebuild'⟩
  dsimp only at *
  have hFF := linear_forest_unique hM.1 hF hF'
  subst F'
  have hPP := hP.unique hM.1 hP'
  subst P'
  have hLL := layer_space_unique hM.1 hRun.space hRun'.space
  subst L'
  have hHH := hRun.unique_d hM hC hRun'
  subst H'
  obtain ⟨hKK,hdd,hRoots⟩ := hBad.unique_d hM hC hRun hBad'
  have hCoordinateRoots := hAy.trans (hRoots.trans hAy'.symm)
  subst K'
  subst level'
  subst root'
  have hBB := hB.unique_d hM hC hB'
  subst B'
  obtain ⟨hAA,hnn,hForests,hCodes,hGG⟩ := CopyTower.full_tower_unique_d hM hC hT hA hA'
    (hAx.trans hAx'.symm) hCoordinateRoots hWidth hWidth' hTower hTower'
  subst A'
  subst n'
  subst Forests'
  subst Codes'
  subst G'
  exact TowerReconstruction.assemble_ones_unique_d hM hC hT.add hTower.width hTower.bound hTower.graph
    (fun _ _ => hTower.code_valid) hTop hTop' hRebuild hRebuild'

theorem Expands.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {s N t t' : M.Domain} (h : Expands M C T s N t) (h' : Expands M C T s N t') : t=t' := by
  obtain ⟨_,m,_,hLegal,hCases⟩ := h
  obtain ⟨_,m',_,hLegal',hCases'⟩ := h'
  have hmm := legal_length_unique hM.1 hLegal hLegal'
  subst m'
  rcases hCases with ⟨hm,ht⟩ | ⟨last,hl,hSucc,hCases⟩ <;> rcases hCases' with ⟨hm',ht'⟩ | ⟨last',hl',hSucc',hCases'⟩
  · exact ht.trans ht'.symm
  · exact False.elim (hC.zero_empty last' (hm ▸ hSucc'.predecessor_mem))
  · exact False.elim (hC.zero_empty last (hm' ▸ hSucc.predecessor_mem))
  · have hll := Structure.SuccessorOf.predecessor_eq hM.1 ((omega_isOrdinal_d hM hC.omega).mem hl) hSucc hSucc'
    subst last'
    rcases hCases with ⟨hOne,hPrefix⟩ | ⟨W,hSuccess⟩ <;> rcases hCases' with ⟨hOne',hPrefix'⟩ | ⟨W',hSuccess'⟩
    · exact hPrefix.graph.ext hM.1 hPrefix'.graph (fun c hc v => (hPrefix.all_rows hM.1 hLegal.1.2 c hc v).trans (hPrefix'.all_rows hM.1 hLegal.1.2 c hc v).symm)
    · exact False.elim (hSuccess'.not_last_one_d hM hC hOne)
    · exact False.elim (hSuccess.not_last_one_d hM hC hOne')
    · exact hSuccess.unique_d hM hC hT hSuccess'

theorem expands_empty_d {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} (hC : C.Valid M)
    (T : MatrixArithmetic M.Domain) {N : M.Domain} (hN : M.mem N C.omega) : Expands M C T C.zero N C.zero :=
  ⟨hN,C.zero,hC.zero_nat,empty_legal_d hC,.inl ⟨rfl,rfl⟩⟩

theorem Expands.empty_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {N t : M.Domain} (hN : M.mem N C.omega) : Expands M C T C.zero N t ↔ t=C.zero :=
  ⟨fun h => h.unique_d hM hC hT (expands_empty_d hC T hN),fun he => he.symm ▸ expands_empty_d hC T hN⟩

theorem no_bad_iff_one_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {L : LayerStateSpace M.Domain} {s P H c a : M.Domain}
    (hLayers : LayerRun M C m L s P H) (hValue : MemPair M s c a) :
    (¬∃k r p, BadAt M C m L H k r c p) ↔ a=C.one := by
  constructor
  · intro hNo
    apply Classical.byContradiction
    intro hne
    exact hNo ((bad_at_exists_iff_d hM hC hLayers hValue).mpr
      (positive_ne_one_above_d hM hC (hLayers.base.row.values.bounds hM.1 hValue).2 (hLayers.base.positive c a hValue) hne))
  · intro he hBad
    have hAbove := (bad_at_exists_iff_d hM hC hLayers hValue).mp hBad
    exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) C.one (he ▸ hAbove)

theorem expands_drop_of_one_d {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} (T : MatrixArithmetic M.Domain)
    {s m last N t : M.Domain} (hLegal : LegalAt M C.omega C.zero C.one s m) (hl : M.mem last C.omega)
    (hSucc : M.SuccessorOf m last) (hN : M.mem N C.omega) (hOne : MemPair M s last C.one) (hPrefix : Prefix M t s last C.omega) :
    Expands M C T s N t := ⟨hN,m,hLegal.1.1,hLegal,.inr ⟨last,hl,hSucc,.inl ⟨hOne,hPrefix⟩⟩⟩

end KP1Y.OneYFinite.Expansion
