import KP1Y.OneYTowerCanonInterface
import KP1Y.OneYReconstructionExtraction
import KP1Y.OneYCopyDiagram
import KP1Y.OneYTowerReconstruction

/-! 由逐层规范性与相邻选择对整个实际提取塔作对象归纳：目标输出t的每个实际层
恰为塔重建行及塔码底父图，塔高处为全1；随后t的全部实际根图原子都是复制塔原子。
这里只使用三项逐层命题(LayerCanon/SelectNext/BaseSelect)，它们由后续模块对
Terminal/普通/lower 各分支实际证明，本模块不假设任何规范性。 -/
namespace KP1Y.OneYFinite.TowerCanon
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite.CopiedMountain
universe u

/-- 塔第k层：底值Hr(k)的实际行运行恰读出塔码山形，并以Hr(k+1)为Top。 -/
def LayerCanon (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (n Forests G Hr k : M.Domain) : Prop :=
  ∀ code heights parents V k' Vn, MemPair M G k code → Codes M code heights parents → MemPair M Hr k V →
    M.SuccessorOf k' k → MemPair M Hr k' Vn →
    ∃ R : RowStateSpace M.Domain, ∃ P Run, RowRun M C n R V P Run ∧
      FromRun M C n R V Run ⟨n,heights,Forests,parents⟩ ∧ TopValueGraph M C n R Run heights Vn

/-- 塔第k层伪父森林在Hr(k+1)上的最右选择恰为塔第k+1层的底父图。 -/
def SelectNext (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (n Forests G Hr B k : M.Domain) : Prop :=
  ∀ k' code heights parents code' heights' parents' Vn P' Pseudo, M.SuccessorOf k' k → M.mem k' B →
    MemPair M G k code → Codes M code heights parents → MemPair M G k' code' → Codes M code' heights' parents' →
    MemPair M Hr k' Vn → MemPair M parents' C.zero P' → GraphPseudoForest M C ⟨n,heights,Forests,parents⟩ Pseudo →
    Selects true M C n Pseudo Vn P'

/-- 线性初始森林在Hr(0)上选出塔第0层底父图。 -/
def BaseSelect (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (n G Hr : M.Domain) : Prop :=
  ∀ F code heights parents V P, LinearForest M C.omega n F → MemPair M G C.zero code → Codes M code heights parents →
    MemPair M Hr C.zero V → MemPair M parents C.zero P → Selects true M C n F V P

private def layerSchema : Project.UnarySchema 5 where
  body := .imp (.mem (.bound 0) (.bound 5)) (.forallE (.forallE (.forallE
    (.imp (memPairFormula (.bound 7) (.bound 3) (.bound 2)) (.imp (codeFormula (.bound 2) (.bound 1) (.bound 0))
      (.conj (memPairFormula (.bound 6) (.bound 3) (.bound 1))
        (.existsE (.conj (memPairFormula (.bound 6) (.bound 4) (.bound 0))
          (.existsE (.existsE (.conj (codeFormula (.bound 2) (.bound 1) (.bound 0))
            (memPairFormula (.bound 0) (.bound 7) (.bound 3)))))))))))))
  freeClosed := by
    simp [memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,
      Definitional.Formula.FreeClosed]

private def layerEnv {M : SetTheory.Structure.{u}} (B H' Hr G zero : M.Domain) : Env M 5 :=
  ((((oneEnv B).push H').push Hr).push G).push zero

private theorem layerSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (B H' Hr G zero k : M.Domain) :
    Project.Formula.satisfies ((layerEnv B H' Hr G zero).push k) layerSchema.body ↔
      (M.mem k B → ∀ state W Q, MemPair M H' k state → Codes M state W Q →
        MemPair M Hr k W ∧ ∃ code, MemPair M G k code ∧ ∃ heights parents, Codes M code heights parents ∧
          MemPair M parents zero Q) := by
  simp only [layerSchema,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    memPairFormula_iff he,codeFormula_iff he]
  rfl

private theorem successor_le_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {r s q : M.Domain} (hr : M.mem r C.omega)
    (hq : M.mem q C.omega) (hSucc : M.SuccessorOf s r) (hrq : M.mem r q) : s=q ∨ M.mem s q := by
  have hw := omega_isOrdinal_d hM hC.omega
  apply ordinal_subset_cases_d hM (hw.mem (natural_successor_mem_d hM hC hr hSucc)) (hw.mem hq)
  intro a ha
  rcases (hSucc a).mp ha with har | he
  · exact (hw.mem hq).transitive r hrq a har
  · exact (hM.1.eq_of_same_members a r he).symm ▸ hrq

/-- 塔码的数据有效性与底父图读取。 -/
theorem tower_code_bottom_d {M : SetTheory.Structure.{u}}
    {C : ExpressionData M.Domain} (hC : C.Valid M) {n Forests CodeSpace G B k : M.Domain}
    (hG : Graph M G B CodeSpace) (hValid : ∀ k code, MemPair M G k code → CodeValid M C n Forests code) (hk : M.mem k B) :
    ∃ code heights parents P, MemPair M G k code ∧ Codes M code heights parents ∧
      (⟨n,heights,Forests,parents⟩ : Data M.Domain).Valid M C ∧ MemPair M parents C.zero P := by
  obtain ⟨code,_,hAt⟩ := hG.total k hk
  obtain ⟨heights,parents,hCode,hY⟩ := hValid k code hAt
  obtain ⟨P,_,hP⟩ := hY.parents.total C.zero hC.zero_nat
  exact ⟨code,heights,parents,P,hAt,hCode,hY,hP⟩

/-- 若源实际运行的底父图读入塔码，则行0父图恰为塔码行0。 -/
private theorem canon_bottom_eq {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {n Forests heights parents V P P' Run : M.Domain} {R : RowStateSpace M.Domain}
    (hY : (⟨n,heights,Forests,parents⟩ : Data M.Domain).Valid M C)
    (hRun : RowRun M C n R V P Run) (hFrom : FromRun M C n R V Run ⟨n,heights,Forests,parents⟩)
    (hP' : MemPair M parents C.zero P') : P=P' := by
  have hP : MemPair M parents C.zero P := (hFrom.parents C.zero P).mpr ⟨V,hRun.initial_row_at_d hM⟩
  exact hY.parents.unique C.zero P P' hP hP'

/-- 实际下一层就是塔第k+1层。 -/
private theorem tower_extraction_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus n Forests CodeSpace G B N Top Hr k k' W Q : M.Domain}
    (hG : Graph M G B CodeSpace) (hValid : ∀ k code, MemPair M G k code → CodeValid M C n Forests code)
    (hRun : TowerReconstruction.Run M C Pairs Plus n Forests CodeSpace G B N Top Hr)
    (hCanon : ∀ k, M.mem k B → LayerCanon M C n Forests G Hr k)
    (hSelect : ∀ k, M.mem k B → SelectNext M C n Forests G Hr B k)
    (hk : M.mem k B) (hs : M.SuccessorOf k' k) (hk' : M.mem k' B) (hW : MemPair M Hr k W)
    {code heights parents : M.Domain} (hAt : MemPair M G k code) (hCode : Codes M code heights parents)
    (hQ : MemPair M parents C.zero Q) :
    ∃ Vn P', MemPair M Hr k' Vn ∧ Extraction M C n W Q Vn P' ∧
      ∃ code' heights' parents', MemPair M G k' code' ∧ Codes M code' heights' parents' ∧ MemPair M parents' C.zero P' := by
  have hY := (hValid k code hAt).read hM.1 hCode
  obtain ⟨Vn,_,hVn⟩ := hRun.graph.total k' ((hRun.length k').mpr (Or.inl hk'))
  obtain ⟨R,P,Run,hRows,hFrom,hTop⟩ := hCanon k hk code heights parents W k' Vn hAt hCode hW hs hVn
  have hPQ := canon_bottom_eq hM hY hRows hFrom hQ
  subst P
  obtain ⟨code',heights',parents',P',hAt',hCode',_,hP'⟩ := tower_code_bottom_d hC hG hValid hk'
  obtain ⟨Pseudo,hPseudo⟩ := graph_pseudo_forest_exists_d hM hC hY
  have hSel := hSelect k hk k' code heights parents code' heights' parents' Vn P' Pseudo hs hk' hAt hCode hAt' hCode' hVn hP' hPseudo
  exact ⟨Vn,P',hVn,ReconstructionExtraction.extraction_from_graph_d hM hC hRows hY hFrom hTop hPseudo hSel,
    code',heights',parents',hAt',hCode',hP'⟩

/-- 对象归纳：t的第k层(k<B)恰为(Hr(k), 塔第k层底父图)。 -/
theorem tower_layers_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M)
    {Pairs Plus n Forests CodeSpace G B N Top Hr t F0 P0 H' : M.Domain} {L' : LayerStateSpace M.Domain}
    (hBnat : M.mem B C.omega) (hG : Graph M G B CodeSpace)
    (hValid : ∀ k code, MemPair M G k code → CodeValid M C n Forests code)
    (hRun : TowerReconstruction.Run M C Pairs Plus n Forests CodeSpace G B N Top Hr) (hT0 : MemPair M Hr C.zero t)
    (hLinear : LinearForest M C.omega n F0) (hP0 : Selects true M C n F0 t P0) (hLayers : LayerRun M C n L' t P0 H')
    (hCanon : ∀ k, M.mem k B → LayerCanon M C n Forests G Hr k)
    (hSelect : ∀ k, M.mem k B → SelectNext M C n Forests G Hr B k) (hBase : BaseSelect M C n G Hr) :
    ∀ k, M.mem k B → ∀ W Q, RowAt M L'.states H' k W Q → MemPair M Hr k W ∧
      ∃ code heights parents, MemPair M G k code ∧ Codes M code heights parents ∧ MemPair M parents C.zero Q := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hAll := natural_induction_d hM layerSchema (layerEnv B H' Hr G C.zero) hC.omega
    (fun z hz => (layerSchema_iff hM.1 B H' Hr G C.zero z).mpr (by
      have hzz := hM.1.eq_of_same_members z C.zero (fun x => iff_of_false (hz x) (hC.zero_empty x))
      subst z
      intro hk state W Q hState hCodeState
      obtain ⟨base,hBaseCode⟩ := codes_total hM t P0
      have hss := hLayers.graph.unique C.zero state base hState (hLayers.initial base hBaseCode)
      subst base
      obtain ⟨hWt,hQP⟩ := codes_injective hM.1 hCodeState hBaseCode
      subst W
      subst Q
      obtain ⟨code,heights,parents,P,hAt,hCode,_,hP⟩ := tower_code_bottom_d hC hG hValid hk
      have hSel := hBase F0 code heights parents t P hLinear hAt hCode hT0 hP
      have hPP := hP0.unique hM.1 hSel
      subst P
      exact ⟨hT0,code,hAt,heights,parents,hCode,hP⟩))
    (fun k hk ih k' hs => (layerSchema_iff hM.1 B H' Hr G C.zero k').mpr (by
      intro hk' state' W' Q' hState' hCode'
      have hkB : M.mem k B := (hw.mem hBnat).transitive k' hk' k hs.predecessor_mem
      obtain ⟨state,hStateMem,hState⟩ := hLayers.graph.total k hk
      obtain ⟨W,Q,hCodeState,_⟩ := (hLayers.space.states state).mp hStateMem
      obtain ⟨hW,code,hAt,heights,parents,hCode,hQ⟩ :=
        (layerSchema_iff hM.1 B H' Hr G C.zero k).mp ih hkB state W Q hState hCodeState
      obtain ⟨V,P,W2,Q2,hIn,hOut,hExtraction⟩ := hLayers.transition k k' state state' hs hState hState'
      obtain ⟨hVW,hPQ⟩ := codes_injective hM.1 hIn hCodeState
      subst V
      subst P
      obtain ⟨hWW,hQQ⟩ := codes_injective hM.1 hOut hCode'
      subst W2
      subst Q2
      obtain ⟨Vn,P',hVn,hNext,code',heights',parents',hAt',hCodeNext,hP'⟩ :=
        tower_extraction_d hM hC hG hValid hRun hCanon hSelect hkB hs hk' hW hAt hCode hQ
      obtain ⟨hTopEq,hQEq⟩ := hExtraction.unique_d hM hC hNext
      subst Vn
      subst P'
      exact ⟨hVn,code',hAt',heights',parents',hCodeNext,hP'⟩))
  intro k hk W Q hRow
  obtain ⟨state,_,hState,hCodeState⟩ := hRow
  have hkω := hw.transitive B hBnat k hk
  obtain ⟨hW,code,hAt,heights,parents,hCode,hQ⟩ :=
    (layerSchema_iff hM.1 B H' Hr G C.zero k).mp (hAll k hkω) hk state W Q hState hCodeState
  exact ⟨hW,code,heights,parents,hAt,hCode,hQ⟩

/-- 塔高B处t的实际层数值恰为外接顶部Top。 -/
theorem tower_top_layer_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M)
    {Pairs Plus n Forests CodeSpace G B N Top Hr t F0 P0 H' : M.Domain} {L' : LayerStateSpace M.Domain}
    (hBnat : M.mem B C.omega) (hNonempty : ∃ k, M.mem k B) (hG : Graph M G B CodeSpace)
    (hValid : ∀ k code, MemPair M G k code → CodeValid M C n Forests code)
    (hRun : TowerReconstruction.Run M C Pairs Plus n Forests CodeSpace G B N Top Hr) (hT0 : MemPair M Hr C.zero t)
    (hLinear : LinearForest M C.omega n F0) (hP0 : Selects true M C n F0 t P0) (hLayers : LayerRun M C n L' t P0 H')
    (hCanon : ∀ k, M.mem k B → LayerCanon M C n Forests G Hr k)
    (hSelect : ∀ k, M.mem k B → SelectNext M C n Forests G Hr B k) (hBase : BaseSelect M C n G Hr)
    {W Q : M.Domain} (hRow : RowAt M L'.states H' B W Q) : W=Top := by
  have hLayersB := tower_layers_d hM hC hBnat hG hValid hRun hT0 hLinear hP0 hLayers hCanon hSelect hBase
  rcases natural_cases hM hC.omega hBnat with hEmpty | ⟨a,ha,hSucc⟩
  · obtain ⟨k,hk⟩ := hNonempty
    exact False.elim (hEmpty k hk)
  · have haB : M.mem a B := hSucc.predecessor_mem
    obtain ⟨Wa,Qa,hRowA⟩ := hLayers.at_exists_d ha
    obtain ⟨hWa,code,heights,parents,hAt,hCode,hQa⟩ := hLayersB a haB Wa Qa hRowA
    have hY := (hValid a code hAt).read hM.1 hCode
    obtain ⟨R,P,Run,hRows,hFrom,hTopRun⟩ := hCanon a haB code heights parents Wa B Top hAt hCode hWa hSucc hRun.top
    have hPQ := canon_bottom_eq hM hY hRows hFrom hQa
    subst P
    obtain ⟨Pseudo,hPseudo⟩ := graph_pseudo_forest_exists_d hM hC hY
    obtain ⟨Q',hQ'⟩ := select_forest_exists_d hM true hC hPseudo.forest hTopRun.graph
    have hExtraction := ReconstructionExtraction.extraction_from_graph_d hM hC hRows hY hFrom hTopRun hPseudo hQ'
    exact (hExtraction.unique_d hM hC (hLayers.at_next hM.1 hSucc hRowA hRow)).1.symm

/-- 目标t的每个实际根图原子都是复制塔(horizon B)在同一层的行原子。 -/
theorem tower_atom_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M)
    {Pairs Plus n Forests CodeSpace G B N Top Hr t F0 P0 H' : M.Domain} {L' : LayerStateSpace M.Domain}
    (hBnat : M.mem B C.omega) (hNonempty : ∃ k, M.mem k B) (hG : Graph M G B CodeSpace)
    (hForests : ∀ F, M.mem F Forests ↔ Forest M C.omega n F)
    (hValid : ∀ k code, MemPair M G k code → CodeValid M C n Forests code)
    (hRun : TowerReconstruction.Run M C Pairs Plus n Forests CodeSpace G B N Top Hr) (hTopOne : TowerReconstruction.AllOne M C n Top)
    (hT0 : MemPair M Hr C.zero t)
    (hLinear : LinearForest M C.omega n F0) (hP0 : Selects true M C n F0 t P0) (hLayers : LayerRun M C n L' t P0 H')
    (hCanon : ∀ k, M.mem k B → LayerCanon M C n Forests G Hr k)
    (hSelect : ∀ k, M.mem k B → SelectNext M C n Forests G Hr B k) (hBase : BaseSelect M C n G Hr)
    {k q p c : M.Domain} (hAtom : ExpressionDiagram.ActualAtom M C n L' H' k q p c) :
    CopyDiagram.Atom M C ⟨B,n,Forests,CodeSpace,G⟩ k q p c := by
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨W,Q,hRow,R,J,r,U,F,hRows,hRowR,hParent,hRoot⟩ := hAtom
  have hkω : M.mem k C.omega := by
    obtain ⟨_,_,hk,_⟩ := hRow
    exact (hLayers.graph.bounds hM.1 hk).1
  have hrω : M.mem r C.omega := by
    obtain ⟨_,_,hr,_⟩ := hRowR
    exact (hRows.graph.bounds hM.1 hr).1
  classical
  by_cases hk : M.mem k B
  · obtain ⟨hW,code,heights,parents,hAt,hCode,hQ⟩ :=
      tower_layers_d hM hC hBnat hG hValid hRun hT0 hLinear hP0 hLayers hCanon hSelect hBase k hk W Q hRow
    have hY := (hValid k code hAt).read hM.1 hCode
    obtain ⟨k',hk',hkω'⟩ := hC.omega.1.2 k hkω
    have hk'N : M.mem k' N := by
      rcases successor_le_d hM hC hkω hBnat hk' hk with he | hlt
      · exact (hRun.length k').mpr (Or.inr (by rw [he]; exact fun _ => Iff.rfl))
      · exact (hRun.length k').mpr (Or.inl hlt)
    obtain ⟨Vn,_,hVn⟩ := hRun.graph.total k' hk'N
    obtain ⟨R0,P,Run,hRows0,hFrom,_⟩ := hCanon k hk code heights parents W k' Vn hAt hCode hW hk' hVn
    have hPQ := canon_bottom_eq hM hY hRows0 hFrom hQ
    subst P
    have hJJ := hRows.unique_d hM hC hRows0
    subst Run
    have hRR := row_state_space_unique hM.1 hRows.space hRows0.space
    subst R0
    have hF := (hFrom.parents r F).mpr ⟨U,hRowR⟩
    have hFForest := (hRows.at_numeric_d hM hC hRowR).forest
    obtain ⟨_,hCodeMem,_⟩ := hG.total k hk
    exact ⟨hk,r,hrω,code,(hG.bounds hM.1 hAt).2,hAt,heights,parents,hCode,F,(hForests F).mpr hFForest,hF,hParent,hRoot⟩
  · exfalso
    have hBk : B=k ∨ M.mem B k := by
      rcases hw.wellOrder.linear.compare B hBnat k hkω with he | hlt | hgt
      · exact Or.inl (hM.1.eq_of_same_members B k he)
      · exact Or.inr hlt
      · exact False.elim (hk hgt)
    have hRooted := hLayers.at_rooted hM.1 hRow
    have hc : M.mem c n := ((hRows.at_numeric_d hM hC hRowR).forest.bounds hM.1 hParent).1
    obtain ⟨v,_,hV⟩ := hRooted.row.values.total c hc
    obtain ⟨WB,QB,hRowB⟩ := hLayers.at_exists_d hBnat
    have hWB := tower_top_layer_d hM hC hBnat hNonempty hG hValid hRun hT0 hLinear hP0 hLayers hCanon hSelect hBase hRowB
    subst WB
    have hTopC : MemPair M Top c C.one := (hTopOne.2 c C.one).mpr ⟨hc,rfl⟩
    have hRootedB := hLayers.at_rooted hM.1 hRowB
    have hLayerB : LayerValue M L' H' B c C.one :=
      ⟨Top,(hLayers.space.rows.values Top).mpr hRootedB.row.values,QB,(hLayers.space.rows.forests QB).mpr hRootedB.row.forest,hRowB,hTopC⟩
    have hLayerK : LayerValue M L' H' k c v :=
      ⟨W,(hLayers.space.rows.values W).mpr hRooted.row.values,Q,(hLayers.space.rows.forests Q).mpr hRooted.row.forest,hRow,hV⟩
    have hLe := hLayers.value_antitone_d hM hC hBnat hkω hBk hLayerB hLayerK
    have hv1 : v=C.one := by
      rcases hLe with he | hlt
      · exact he
      · rcases (hC.one_succ v).mp hlt with h0 | he
        · exact False.elim (hC.zero_empty v h0)
        · have hv0 := hM.1.eq_of_same_members v C.zero he
          exact False.elim (hC.zero_empty C.zero (hv0 ▸ hRooted.positive c v hV))
    subst v
    have hNone := hRows.no_parent_of_initial_one_d hM hC hV hRowR
    exact hNone p ((hRows.at_numeric_d hM hC hRowR).forest.bounds hM.1 hParent).2 hParent

end KP1Y.OneYFinite.TowerCanon
