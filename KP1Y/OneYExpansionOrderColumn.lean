import KP1Y.OneYMountainReconstruction
import KP1Y.OneYNaturalAdditionFacts

/-! 实际重建网格的单列比较：两列在 [lo,hi] 上的父贡献逐行相同，则 hi 处的差 δ 原样传到 lo。
行号是内部 ω 元素，对行作对象有界反向归纳；不使用宿主 Nat。 -/
namespace KP1Y.OneYFinite.ExpansionOrder
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
open KP1Y.OneYFinite
universe u

private def shiftEnv {M : SetTheory.Structure.{u}} (w f f' lo delta Pairs Plus : M.Domain) : Env M 7 :=
  ((((((oneEnv w).push f).push f').push lo).push delta).push Pairs).push Plus

private def shiftSchema : Project.Delta0UnarySchema 7 where
  body := .imp (Project.Formula.subset (.bound 4) (.bound 0))
    (Project.Formula.forallMem (.bound 7) (Project.Formula.forallMem (.bound 8)
      (.imp (memPairFormula (.bound 8) (.bound 2) (.bound 1))
        (.imp (memPairFormula (.bound 7) (.bound 2) (.bound 0))
          (addAtFormula (.bound 4) (.bound 3) (.bound 0) (.bound 5) (.bound 1))))))
  freeClosed := by
    simp [memPairFormula,addAtFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,
      Project.Formula.subset,Definitional.Formula.FreeClosed]
  delta0 := .imp (.atom _ _ _) (.forallMem _ (.forallMem _ (.imp (memPairFormula_delta0 _ _ _)
    (.imp (memPairFormula_delta0 _ _ _) (addAtFormula_delta0 _ _ _ _ _)))))

private theorem shiftSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (w f f' lo delta Pairs Plus r : M.Domain) :
    Project.Formula.satisfies ((shiftEnv w f f' lo delta Pairs Plus).push r) shiftSchema.body ↔
      (M.MemberSubset lo r → ∀u, M.mem u w → ∀u', M.mem u' w → MemPair M f r u → MemPair M f' r u' →
        AddAt M Pairs Plus u' delta u) := by
  simp only [shiftSchema,shiftEnv,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_subset_iff,
    Project.Formula.satisfies_forallMem_iff,memPairFormula_iff he,addAtFormula_iff he]
  rfl

/-- 两条有限内部数列在 [lo,hi) 的每一步加同一增量，hi 处 f=f'+δ 则 lo 处仍 f=f'+δ。 -/
theorem shifted_columns_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {f f' R R' lo hi delta : M.Domain} (hf : Graph M f R C.omega) (hf' : Graph M f' R' C.omega)
    (hR : M.mem R C.omega) (hR' : M.mem R' C.omega) (hhi : M.mem hi R) (hhi' : M.mem hi R')
    (hlo : lo=hi ∨ M.mem lo hi) (hδ : M.mem delta C.omega)
    (hTop : ∀u u', MemPair M f hi u → MemPair M f' hi u' → AddAt M Pairs Plus u' delta u)
    (hStep : ∀r, M.mem r hi → M.MemberSubset lo r → ∀q, M.SuccessorOf q r → ∃b, M.mem b C.omega ∧
      (∀u v, MemPair M f r u → MemPair M f q v → AddAt M Pairs Plus v b u) ∧
      (∀u v, MemPair M f' r u → MemPair M f' q v → AddAt M Pairs Plus v b u)) :
    ∀u u', MemPair M f lo u → MemPair M f' lo u' → AddAt M Pairs Plus u' delta u := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hhiω := hw.transitive R hR hi hhi
  have hInside {S q : M.Domain} (hS : M.mem S C.omega) (hiS : M.mem hi S) (hq : M.mem q C.omega)
      (hqSub : M.MemberSubset q hi) : M.mem q S := by
    rcases ordinal_subset_cases_d hM (hw.mem hq) (hw.mem hhiω) hqSub with he | hlt
    · exact he ▸ hiS
    · exact (hw.mem hS).transitive hi hiS q hlt
  let env := shiftEnv C.omega f f' lo delta Pairs Plus
  have hAll := bounded_backward_induction_d hM shiftSchema env hC.omega hhiω
    ((shiftSchema_iff hM.1 C.omega f f' lo delta Pairs Plus hi).mpr (fun _ u _ u' _ hU hU' => hTop u u' hU hU'))
    (fun p hp q hq hs hqSub ih => (shiftSchema_iff hM.1 C.omega f f' lo delta Pairs Plus p).mpr (by
      intro hlop u hu u' hu' hU hU'
      have hloq : M.MemberSubset lo q := fun x hx => (hs x).mpr (.inl (hlop x hx))
      obtain ⟨v,hv,hV⟩ := hf.total q (hInside hR hhi hq hqSub)
      obtain ⟨v',hv',hV'⟩ := hf'.total q (hInside hR' hhi' hq hqSub)
      have hIH := (shiftSchema_iff hM.1 C.omega f f' lo delta Pairs Plus q).mp ih hloq v hv v' hv' hV hV'
      obtain ⟨b,hb,hSt,hSt'⟩ := hStep p hp hlop q hs
      have hS1 := (hPlus.add_iff_sum hM hv' hδ).mp hIH
      have hS2 := (hPlus.add_iff_sum hM hv hb).mp (hSt u v hU hV)
      have hS3 := (hPlus.add_iff_sum hM hv' hb).mp (hSt' u' v' hU' hV')
      obtain ⟨y,_,hY⟩ := natural_sum_exists_d hM hC.omega hu' hδ
      have huy := natural_sum_shuffle_d hM hC hδ hb hS1 hS2 hS3 hY
      exact (hPlus.add_iff_sum hM hu' hδ).mpr (huy ▸ hY)))
  intro u u' hU hU'
  exact (shiftSchema_iff hM.1 C.omega f f' lo delta Pairs Plus lo).mp (hAll lo hlo) (fun _ h => h)
    u (hf.bounds hM.1 hU).2 u' (hf'.bounds hM.1 hU').2 hU hU'

/-- Rebuilds 内部的唯一有限网格证书。 -/
structure Grid (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (Pairs Plus : M.Domain)
    (X : CopiedMountain.Data M.Domain) (Top B Parents H : M.Domain) : Prop where
  bound : SequenceBound M C X.width X.heights B
  parents : Prefix M Parents X.parents B X.forests
  reconstructs : Reconstruction.Reconstructs M (MountainReconstruction.grid C X Top Pairs Plus B Parents) H

abbrev GCell (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (Pairs Plus : M.Domain)
    (X : CopiedMountain.Data M.Domain) (Top B Parents H c r v : M.Domain) : Prop :=
  Reconstruction.ValidCell M (MountainReconstruction.grid C X Top Pairs Plus B Parents) H c r v

theorem rebuilds_grid {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {Pairs Plus : M.Domain}
    {X : CopiedMountain.Data M.Domain} {Top F : M.Domain} (h : MountainReconstruction.Rebuilds M C Pairs Plus X Top F) :
    ∃B Parents H, Grid M C Pairs Plus X Top B Parents H ∧ ∀c v, MemPair M F c v ↔ GCell M C Pairs Plus X Top B Parents H c C.zero v := by
  obtain ⟨B,Parents,H,hB,hP,hH,hF⟩ := h
  exact ⟨B,Parents,H,⟨hB,hP,hH⟩,hF.rows⟩

theorem Grid.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C) {Top B Parents H B' Parents' H' : M.Domain}
    (hTop : Graph M Top X.width C.omega)
    (g : Grid M C Pairs Plus X Top B Parents H) (g' : Grid M C Pairs Plus X Top B' Parents' H') :
    B=B' ∧ Parents=Parents' ∧ H=H' := by
  have hBB := g.bound.unique_d hM hC g'.bound
  subst B'
  have hPP := g.parents.graph.ext hM.1 g'.parents.graph (fun r hr F =>
    (g.parents.all_rows hM.1 hX.parents r hr F).trans (g'.parents.all_rows hM.1 hX.parents r hr F).symm)
  subst Parents'
  exact ⟨rfl,rfl,Reconstruction.reconstruction_unique_d hM
    (MountainReconstruction.grid_valid_d hM hC hX hTop hPlus g.bound g.parents) g.reconstructs g'.reconstructs⟩

theorem Grid.column {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {Pairs Plus : M.Domain} {X : CopiedMountain.Data M.Domain} {Top B Parents H c : M.Domain}
    (g : Grid M C Pairs Plus X Top B Parents H) (hc : M.mem c X.width) :
    ∃f, Graph M f B C.omega ∧ ∀r v, GCell M C Pairs Plus X Top B Parents H c r v ↔ MemPair M f r v := by
  obtain ⟨f,_,hCf⟩ := g.reconstructs.graph.total c hc
  exact ⟨f,(g.reconstructs.column he hCf).graph,fun r v => g.reconstructs.valid_cell_iff he hCf⟩

theorem Grid.cell_unique {M : SetTheory.Structure.{u}}
    {C : ExpressionData M.Domain} {Pairs Plus : M.Domain} {X : CopiedMountain.Data M.Domain} {Top B Parents H c r v v' : M.Domain}
    (g : Grid M C Pairs Plus X Top B Parents H) (h : GCell M C Pairs Plus X Top B Parents H c r v)
    (h' : GCell M C Pairs Plus X Top B Parents H c r v') : v=v' :=
  h.unique g.reconstructs.graph h'

theorem Grid.height_bound {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {Pairs Plus : M.Domain} {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C)
    {Top B Parents H c h : M.Domain} (g : Grid M C Pairs Plus X Top B Parents H) (hHeight : MemPair M X.heights c h) :
    M.mem h B :=
  g.bound.1.2.2 c (hX.heights.bounds he hHeight).1 h (hX.heights.bounds he hHeight).2 hHeight

theorem Grid.cell_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus : M.Domain} {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C)
    {Top B Parents H c h r : M.Domain} (g : Grid M C Pairs Plus X Top B Parents H)
    (hHeight : MemPair M X.heights c h) (hr : r=h ∨ M.mem r h) :
    ∃v, M.mem v C.omega ∧ GCell M C Pairs Plus X Top B Parents H c r v := by
  obtain ⟨f,hf,hCell⟩ := g.column hM.1 (hX.heights.bounds hM.1 hHeight).1
  have hhB := g.height_bound hM.1 hX hHeight
  have hrB : M.mem r B := by
    rcases hr with he | hrh
    · exact he ▸ hhB
    · exact ((omega_isOrdinal_d hM hC.omega).mem g.bound.1.1).transitive h hhB r hrh
  obtain ⟨v,hv,hV⟩ := hf.total r hrB
  exact ⟨v,hv,(hCell r v).mpr hV⟩

theorem Grid.cell_top {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {Pairs Plus : M.Domain} {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C)
    {Top B Parents H c h t : M.Domain} (g : Grid M C Pairs Plus X Top B Parents H) (hTop : Graph M Top X.width C.omega)
    (hHeight : MemPair M X.heights c h) (hT : MemPair M Top c t) : GCell M C Pairs Plus X Top B Parents H c h t := by
  have hc := (hX.heights.bounds he hHeight).1
  obtain ⟨f,_,hCf⟩ := g.reconstructs.graph.total c hc
  have hCol := g.reconstructs.column he hCf
  exact (g.reconstructs.valid_cell_iff he hCf).mpr
    (hCol.top h (g.height_bound he hX hHeight) t (hTop.bounds he hT).2 hHeight hT)

theorem Grid.parent_equation_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C) {Top B Parents H c p r s h u v b : M.Domain}
    (g : Grid M C Pairs Plus X Top B Parents H) (hTop : Graph M Top X.width C.omega)
    (hHeight : MemPair M X.heights c h) (hParent : CopiedMountain.ParentAt M X r c p) (hs : M.SuccessorOf s r)
    (hU : GCell M C Pairs Plus X Top B Parents H c r u) (hV : GCell M C Pairs Plus X Top B Parents H c s v)
    (hB : GCell M C Pairs Plus X Top B Parents H p r b) : AddAt M Pairs Plus v b u := by
  have hD := MountainReconstruction.grid_valid_d hM hC hX hTop hPlus g.bound g.parents
  have hc := (hX.heights.bounds hM.1 hHeight).1
  obtain ⟨f,_,hCf⟩ := g.reconstructs.graph.total c hc
  exact g.reconstructs.parent_equation_d hM hD hCf hHeight
    ((MountainReconstruction.grid_parent_iff_d hM hC hX g.bound g.parents).mpr hParent) hs
    ((g.reconstructs.valid_cell_iff hM.1 hCf).mp hU) ((g.reconstructs.valid_cell_iff hM.1 hCf).mp hV) hB

/-- 网格层的单列比较。父列格值由调用者给出逐行对应。 -/
theorem Grid.shift_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {X X' : CopiedMountain.Data M.Domain} (hX : X.Valid M C) (hX' : X'.Valid M C)
    {Top B Parents H Top' B' Parents' H' : M.Domain}
    (g : Grid M C Pairs Plus X Top B Parents H) (g' : Grid M C Pairs Plus X' Top' B' Parents' H')
    (hTop : Graph M Top X.width C.omega) (hTop' : Graph M Top' X'.width C.omega)
    {c c' h h' lo hi delta : M.Domain} (hHeight : MemPair M X.heights c h) (hHeight' : MemPair M X'.heights c' h')
    (hhi : hi=h ∨ M.mem hi h) (hhi' : hi=h' ∨ M.mem hi h') (hlo : lo=hi ∨ M.mem lo hi) (hδ : M.mem delta C.omega)
    (hStart : ∀u u', GCell M C Pairs Plus X Top B Parents H c hi u → GCell M C Pairs Plus X' Top' B' Parents' H' c' hi u' →
      AddAt M Pairs Plus u' delta u)
    (hParents : ∀r, M.mem r hi → M.MemberSubset lo r → ∃p p', CopiedMountain.ParentAt M X r c p ∧
      CopiedMountain.ParentAt M X' r c' p' ∧ ∀b, GCell M C Pairs Plus X Top B Parents H p r b →
        GCell M C Pairs Plus X' Top' B' Parents' H' p' r b) :
    ∀u u', GCell M C Pairs Plus X Top B Parents H c lo u → GCell M C Pairs Plus X' Top' B' Parents' H' c' lo u' →
      AddAt M Pairs Plus u' delta u := by
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨f,hf,hCell⟩ := g.column hM.1 (hX.heights.bounds hM.1 hHeight).1
  obtain ⟨f',hf',hCell'⟩ := g'.column hM.1 (hX'.heights.bounds hM.1 hHeight').1
  have hhB := g.height_bound hM.1 hX hHeight
  have hhB' := g'.height_bound hM.1 hX' hHeight'
  have hle {S a b : M.Domain} (hS : M.mem S C.omega) (hb : M.mem b S) (hab : a=b ∨ M.mem a b) : M.mem a S := by
    rcases hab with he | hlt
    · exact he ▸ hb
    · exact (hw.mem hS).transitive b hb a hlt
  have hAll := shifted_columns_d hM hC hPlus hf hf' g.bound.1.1 g'.bound.1.1 (hle g.bound.1.1 hhB hhi)
    (hle g'.bound.1.1 hhB' hhi') hlo hδ
    (fun u u' hU hU' => hStart u u' ((hCell hi u).mpr hU) ((hCell' hi u').mpr hU'))
    (by
      intro r hr hlor q hs
      obtain ⟨p,p',hP,hP',hCells⟩ := hParents r hr hlor
      obtain ⟨hp,_,hHp⟩ := hX.heights.total p (hP.bounds hM.1 hX).2.2.1
      obtain ⟨b,hb,hBcell⟩ := g.cell_exists_d hM hC hX hHp (hX.endpoint r c p hp hP hHp)
      have hBcell' := hCells b hBcell
      refine ⟨b,hb,?_,?_⟩
      · intro u v hU hV
        exact g.parent_equation_d hM hC hPlus hX hTop hHeight hP hs ((hCell r u).mpr hU) ((hCell q v).mpr hV) hBcell
      · intro u v hU hV
        exact g'.parent_equation_d hM hC hPlus hX' hTop' hHeight' hP' hs ((hCell' r u).mpr hU) ((hCell' q v).mpr hV) hBcell')
  intro u u' hU hU'
  exact hAll u u' ((hCell lo u).mp hU) ((hCell' lo u').mp hU')

/-- 前缀列的高度、父图和顶部一致时，两网格在前缀列的活行格值逐一相同（行界可不同）。 -/
theorem Grid.prefix_cells_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {X X' : CopiedMountain.Data M.Domain} (hX : X.Valid M C) (hX' : X'.Valid M C)
    {Top B Parents H Top' B' Parents' H' : M.Domain}
    (g : Grid M C Pairs Plus X Top B Parents H) (g' : Grid M C Pairs Plus X' Top' B' Parents' H')
    (hTop : Graph M Top X.width C.omega) (hTop' : Graph M Top' X'.width C.omega)
    {cut : M.Domain} (hcut : M.mem cut C.omega) (hLeft : M.MemberSubset cut X.width) (hRight : M.MemberSubset cut X'.width)
    (hHeights : RowsAgreeOn M X.heights X'.heights cut) (hTops : RowsAgreeOn M Top Top' cut)
    (hParents : ∀c, M.mem c cut → ∀r, M.mem r C.omega → ∀p, CopiedMountain.ParentAt M X r c p ↔ CopiedMountain.ParentAt M X' r c p)
    {c r h v : M.Domain} (hc : M.mem c cut) (hHeight : MemPair M X.heights c h) (hr : r=h ∨ M.mem r h) :
    GCell M C Pairs Plus X Top B Parents H c r v ↔ GCell M C Pairs Plus X' Top' B' Parents' H' c r v := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hD := MountainReconstruction.grid_valid_d hM hC hX hTop hPlus g.bound g.parents
  have hD' := MountainReconstruction.grid_valid_d hM hC hX' hTop' hPlus g'.bound g'.parents
  have hPrefix : Reconstruction.PrefixData M (MountainReconstruction.grid C X Top Pairs Plus B Parents)
      (MountainReconstruction.grid C X' Top' Pairs Plus B' Parents') cut :=
    ⟨rfl,hcut,hLeft,hRight,hHeights,hTops,fun c hc r hr p => (MountainReconstruction.grid_parent_iff_d hM hC hX g.bound g.parents).trans
      ((hParents c hc r hr p).trans (MountainReconstruction.grid_parent_iff_d hM hC hX' g'.bound g'.parents).symm)⟩
  have hValues := Reconstruction.reconstruction_prefix_values_d hM hD hD' hPrefix g.reconstructs g'.reconstructs
  have hHeight' := (hHeights c hc h).mp hHeight
  have hhω := (hX.heights.bounds hM.1 hHeight).2
  have hrω : M.mem r C.omega := by
    rcases hr with he | hlt
    · exact he ▸ hhω
    · exact hw.transitive h hhω r hlt
  obtain ⟨a,_,hA⟩ := g.cell_exists_d hM hC hX hHeight hr
  obtain ⟨a',_,hA'⟩ := g'.cell_exists_d hM hC hX' hHeight' hr
  constructor
  · intro hCell
    have hv := (hCell.bounds hM.1).2
    rcases (hValues c hc r hrω v hv).mp (Or.inl hCell) with hNew | ⟨_,hNo⟩
    · exact hNew
    · exact False.elim (hNo a' (hA'.bounds hM.1).2 hA')
  · intro hCell
    have hv := (hCell.bounds hM.1).2
    rcases (hValues c hc r hrω v hv).mpr (Or.inl hCell) with hOld | ⟨_,hNo⟩
    · exact hOld
    · exact False.elim (hNo a (hA.bounds hM.1).2 hA)

end KP1Y.OneYFinite.ExpansionOrder
