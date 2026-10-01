import KP1Y.OneYReconstructionGrid
import KP1Y.OneYCopiedMountainSyntax
import KP1Y.OneYExtractionBounds
import KP1Y.OneYMountainPrefix
import KP1Y.OneYNaturalDifferenceAddition

/-! 将实际ω父行家族限制为有限重建网格，读取真实底行；不假设数值选择恢复。 -/
namespace KP1Y.OneYFinite.MountainReconstruction
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite
universe u

def grid {α : Type u} (C : ExpressionData α) (X : CopiedMountain.Data α) (Top Pairs Plus B Parents : α) : Reconstruction.GridData α :=
  ⟨C,X.width,B,X.heights,X.forests,Parents,Top,Pairs,Plus⟩

theorem grid_parent_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C)
    {Top Pairs Plus B Parents r c p : M.Domain} (hB : SequenceBound M C X.width X.heights B)
    (hP : Prefix M Parents X.parents B X.forests) :
    Reconstruction.ParentAt M (grid C X Top Pairs Plus B Parents) r c p ↔ CopiedMountain.ParentAt M X r c p := by
  constructor
  · rintro ⟨F,hF,hAt,hParent⟩
    exact ⟨F,hF,(hP.rows r (hP.graph.bounds hM.1 hAt).1 F hF).mp hAt,hParent⟩
  · intro hParent
    have hBounds := hParent.bounds hM.1 hX
    obtain ⟨height,hh,hHeight⟩ := hX.heights.total c hBounds.2.1
    have hrh := (hX.source r c height hHeight).mp ⟨p,hParent⟩
    have hhB := hB.1.2.2 c hBounds.2.1 height hh hHeight
    have hrB := ((omega_isOrdinal_d hM hC.omega).mem hB.1.1).transitive height hhB r hrh
    obtain ⟨F,hF,hAt,hParent⟩ := hParent
    exact ⟨F,hF,(hP.rows r hrB F hF).mpr hAt,hParent⟩

theorem grid_valid_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C)
    {Top Pairs Plus B Parents : M.Domain} (hTop : Graph M Top X.width C.omega) (hPlus : AdditionTable M C Pairs Plus)
    (hB : SequenceBound M C X.width X.heights B) (hP : Prefix M Parents X.parents B X.forests) :
    (grid C X Top Pairs Plus B Parents).Valid M := by
  refine ⟨hC,hX.width,hB.1.1,KP1Y.Assignments.graph_tighten_values hX.heights (fun c height hAt =>
    hB.1.2.2 c (hX.heights.bounds hM.1 hAt).1 height (hX.heights.bounds hM.1 hAt).2 hAt),hTop,hP.graph,?_,?_,?_,hPlus⟩
  · intro r F hAt
    exact hX.forest r F ((hP.rows r (hP.graph.bounds hM.1 hAt).1 F (hP.graph.bounds hM.1 hAt).2).mp hAt)
  · intro r _ c _ height hHeight
    exact (⟨fun ⟨p,hp⟩ => ⟨p,(grid_parent_iff_d hM hC hX hB hP).mp hp⟩,
      fun ⟨p,hp⟩ => ⟨p,(grid_parent_iff_d hM hC hX hB hP).mpr hp⟩⟩ :
      (∃p,Reconstruction.ParentAt M (grid C X Top Pairs Plus B Parents) r c p) ↔ ∃p,CopiedMountain.ParentAt M X r c p).trans (hX.source r c height hHeight)
  · intro r c p hParent height hHeight
    exact hX.endpoint r c p height ((grid_parent_iff_d hM hC hX hB hP).mp hParent) hHeight

structure BottomGraph (M : SetTheory.Structure.{u}) (D : Reconstruction.GridData M.Domain) (H F : M.Domain) : Prop where
  graph : Graph M F D.width D.naturals.omega
  rows : ∀c v, MemPair M F c v ↔ Reconstruction.ValidCell M D H c D.naturals.zero v

private def bottomSchema : Project.Delta0BinarySchema 16 where
  body := Reconstruction.validCellFormula
    ⟨⟨.bound 17,.bound 16,.bound 15,.bound 14,.bound 13⟩,.bound 12,.bound 11,.bound 10,.bound 9,.bound 8,.bound 7,.bound 6,.bound 5⟩
    (.bound 4) (.bound 1) (.bound 16) (.bound 0)
  freeClosed := Reconstruction.validCellFormula_freeClosed ⟨⟨rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ _ _ _ _ rfl rfl rfl rfl
  delta0 := Reconstruction.validCellFormula_delta0 _ _ _ _ _

private def bottomEnv {M : SetTheory.Structure.{u}} (D : Reconstruction.GridData M.Domain) (H : M.Domain) : Env M 16 :=
  ((((((((((((((((oneEnv D.naturals.omega).push D.naturals.zero).push D.naturals.one).push D.naturals.sequences).push D.naturals.expressions).push D.width).push D.rows).push D.heights).push D.forests).push D.parents).push D.tops).push D.pairs).push D.plus).push H).push H).push H)

private theorem bottomSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (D : Reconstruction.GridData M.Domain) (H c v : M.Domain) :
    Project.Formula.satisfies (((bottomEnv D H).push c).push v) bottomSchema.body ↔ Reconstruction.ValidCell M D H c D.naturals.zero v :=
  Reconstruction.validCellFormula_iff he _ _ _ _ _ _

theorem bottom_graph_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : Reconstruction.GridData M.Domain} {H : M.Domain} (hH : Reconstruction.Reconstructs M D H)
    (hZero : M.mem D.naturals.zero D.rows) : ∃F, BottomGraph M D H F := by
  obtain ⟨F,hSupport,hRaw⟩ := relation_comprehension_d hM bottomSchema (bottomEnv D H) D.width D.naturals.omega
  have hRows (c v : M.Domain) : MemPair M F c v ↔ Reconstruction.ValidCell M D H c D.naturals.zero v := by
    rw [hRaw c v,bottomSchema_iff hM.1]
    refine ⟨fun h => h.2.2,fun hCell => ?_⟩
    have hv := hCell.bounds hM.1
    have hSaved := hCell
    obtain ⟨f,_,hCf,_,_⟩ := hCell
    exact ⟨(hH.graph.bounds hM.1 hCf).1,hv.2,hSaved⟩
  refine ⟨F,⟨hSupport,?_,?_⟩,hRows⟩
  · intro c hc
    obtain ⟨f,_,hCf⟩ := hH.graph.total c hc
    obtain ⟨v,hv,hV⟩ := (hH.column hM.1 hCf).graph.total D.naturals.zero hZero
    exact ⟨v,hv,(hRows c v).mpr ((hH.valid_cell_iff hM.1 hCf).mpr hV)⟩
  · intro c v v' hV hV'
    exact ((hRows c v).mp hV).unique hH.graph ((hRows c v').mp hV')

def Rebuilds (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (Pairs Plus : M.Domain)
    (X : CopiedMountain.Data M.Domain) (Top F : M.Domain) : Prop :=
  ∃B Parents H, SequenceBound M C X.width X.heights B ∧ Prefix M Parents X.parents B X.forests ∧
    Reconstruction.Reconstructs M (grid C X Top Pairs Plus B Parents) H ∧ BottomGraph M (grid C X Top Pairs Plus B Parents) H F

theorem rebuild_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C) {Top : M.Domain} (hTop : Graph M Top X.width C.omega) :
    ∃F, Rebuilds M C Pairs Plus X Top F := by
  obtain ⟨B,hB⟩ := sequence_bound_exists_d hM hC hX.width hX.heights
  obtain ⟨Parents,hParents⟩ := restrict_prefix_d hM hX.parents ((omega_isOrdinal_d hM hC.omega).transitive B hB.1.1)
  obtain ⟨H,hH⟩ := Reconstruction.reconstruction_exists_d hM (grid_valid_d hM hC hX hTop hPlus hB hParents)
  obtain ⟨F,hF⟩ := bottom_graph_exists_d hM hH hB.1.2.1
  exact ⟨F,B,Parents,H,hB,hParents,hH,hF⟩

theorem Rebuilds.graph {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {Pairs Plus : M.Domain}
    {X : CopiedMountain.Data M.Domain} {Top F : M.Domain} (h : Rebuilds M C Pairs Plus X Top F) : Graph M F X.width C.omega := by
  obtain ⟨_,_,_,_,_,_,hF⟩ := h
  exact hF.graph

theorem Rebuilds.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C) {Top F G : M.Domain} (hTop : Graph M Top X.width C.omega)
    (hF : Rebuilds M C Pairs Plus X Top F) (hG : Rebuilds M C Pairs Plus X Top G) : F=G := by
  obtain ⟨B,Parents,H,hB,hP,hH,hF⟩ := hF
  obtain ⟨B',Parents',H',hB',hP',hH',hG⟩ := hG
  have hBB := hB.unique_d hM hC hB'
  subst B'
  have hPP := hP.graph.ext hM.1 hP'.graph (fun r hr F => (hP.all_rows hM.1 hX.parents r hr F).trans (hP'.all_rows hM.1 hX.parents r hr F).symm)
  subst Parents'
  have hHH := Reconstruction.reconstruction_unique_d hM (grid_valid_d hM hC hX hTop hPlus hB hP) hH hH'
  subst H'
  exact hF.graph.ext hM.1 hG.graph (fun c _ v => (hF.rows c v).trans (hG.rows c v).symm)

theorem Rebuilds.positive_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C) {Top F c v : M.Domain} (hTop : Graph M Top X.width C.omega)
    (hPositive : ∀c v, MemPair M Top c v → M.mem C.zero v) (h : Rebuilds M C Pairs Plus X Top F) (hAt : MemPair M F c v) : M.mem C.zero v := by
  obtain ⟨B,Parents,H,hB,hP,hH,hF⟩ := h
  have hD := grid_valid_d hM hC hX hTop hPlus hB hP
  have hc := (hF.graph.bounds hM.1 hAt).1
  obtain ⟨f,_,hCf⟩ := hH.graph.total c hc
  obtain ⟨height,hh,hHeight⟩ := hX.heights.total c hc
  obtain ⟨top,_,hTopAt⟩ := hTop.total c hc
  obtain ⟨K,hK⟩ := Reconstruction.contribution_graph_exists_d hM hD hH.graph c
  have hFilled := (hH.column hM.1 hCf).to_filled_column hM hD hK hHeight hTopAt
  have hZero : C.zero=height ∨ M.mem C.zero height := by
    by_cases he : height=C.zero
    · exact .inl he.symm
    · exact .inr ((hC.zero_mem_iff hM hh).mpr he)
  exact hFilled.live_positive_d hM hC hK.graph hPlus (hPositive c top hTopAt) hZero
    ((hH.valid_cell_iff hM.1 hCf).mp ((hF.rows c v).mp hAt))

theorem height_zero_column_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C)
    {height : M.Domain} (hHeight : MemPair M X.heights C.zero height) : height=C.zero := by
  apply Classical.byContradiction
  intro he
  have hPos := (hC.zero_mem_iff hM (hX.heights.bounds hM.1 hHeight).2).mpr he
  obtain ⟨p,hP⟩ := (hX.source C.zero C.zero height hHeight).mpr hPos
  exact hC.zero_empty p (hP.bounds hM.1 hX).2.2.2

theorem Rebuilds.first_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus : M.Domain}
    {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C) {Top F v : M.Domain} (hTop : Graph M Top X.width C.omega)
    (h : Rebuilds M C Pairs Plus X Top F) : MemPair M F C.zero v ↔ MemPair M Top C.zero v := by
  obtain ⟨B,Parents,H,hB,_,hH,hF⟩ := h
  have hFirst (hc : M.mem C.zero X.width) : ∃f, MemPair M H C.zero f ∧ ∀v, MemPair M Top C.zero v → MemPair M f C.zero v := by
    obtain ⟨height,_,hHeight⟩ := hX.heights.total C.zero hc
    have hh := height_zero_column_d hM hC hX hHeight
    subst height
    obtain ⟨f,_,hCf⟩ := hH.graph.total C.zero hc
    exact ⟨f,hCf,fun v hTopAt => (hH.column hM.1 hCf).top C.zero hB.1.2.1 v (hTop.bounds hM.1 hTopAt).2 hHeight hTopAt⟩
  constructor
  · intro hAt
    have hc := (hF.graph.bounds hM.1 hAt).1
    obtain ⟨f,hCf,hTopRow⟩ := hFirst hc
    obtain ⟨top,_,hTopAt⟩ := hTop.total C.zero hc
    have he := (hH.column hM.1 hCf).graph.unique C.zero top v (hTopRow top hTopAt)
      ((hH.valid_cell_iff hM.1 hCf).mp ((hF.rows C.zero v).mp hAt))
    exact he ▸ hTopAt
  · intro hTopAt
    obtain ⟨f,hCf,hTopRow⟩ := hFirst (hTop.bounds hM.1 hTopAt).1
    exact (hF.rows C.zero v).mpr ((hH.valid_cell_iff hM.1 hCf).mpr (hTopRow v hTopAt))

theorem BottomGraph.previous_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    {D : Reconstruction.GridData M.Domain} {H F c v : M.Domain} (hH : Reconstruction.Reconstructs M D H)
    (hF : BottomGraph M D H F) (hZero : M.mem D.naturals.zero D.rows) (hc : M.mem c D.width) :
    Reconstruction.PreviousValue M D H c D.naturals.zero v ↔ MemPair M F c v := by
  obtain ⟨f,_,hCf⟩ := hH.graph.total c hc
  have hPrevious := hH.previous_value_iff (r := D.naturals.zero) (x := v) he hCf
  have hValue : Reconstruction.PreviousValue M D H c D.naturals.zero v ↔ MemPair M f D.naturals.zero v :=
    hPrevious.trans ⟨fun h => h.elim id (fun h => False.elim (h.1 hZero)),Or.inl⟩
  exact hValue.trans ((hH.valid_cell_iff he hCf).symm.trans (hF.rows c v).symm)

theorem Rebuilds.prefix_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {X Y : CopiedMountain.Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C) {Top Top' F G cut : M.Domain}
    (hTop : Graph M Top X.width C.omega) (hTop' : Graph M Top' Y.width C.omega)
    (hCut : M.mem cut C.omega) (hLeft : M.MemberSubset cut X.width) (hRight : M.MemberSubset cut Y.width)
    (hHeights : RowsAgreeOn M X.heights Y.heights cut) (hTops : RowsAgreeOn M Top Top' cut)
    (hParents : ∀c, M.mem c cut → ∀r, M.mem r C.omega → ∀p, CopiedMountain.ParentAt M X r c p ↔ CopiedMountain.ParentAt M Y r c p)
    (hF : Rebuilds M C Pairs Plus X Top F) (hG : Rebuilds M C Pairs Plus Y Top' G) : RowsAgreeOn M F G cut := by
  obtain ⟨B,Parents,H,hB,hP,hH,hF⟩ := hF
  obtain ⟨B',Parents',H',hB',hP',hH',hG⟩ := hG
  have hD := grid_valid_d hM hC hX hTop hPlus hB hP
  have hD' := grid_valid_d hM hC hY hTop' hPlus hB' hP'
  have hPrefix : Reconstruction.PrefixData M (grid C X Top Pairs Plus B Parents) (grid C Y Top' Pairs Plus B' Parents') cut :=
    ⟨rfl,hCut,hLeft,hRight,hHeights,hTops,fun c hc r hr p => (grid_parent_iff_d hM hC hX hB hP).trans
      ((hParents c hc r hr p).trans (grid_parent_iff_d hM hC hY hB' hP').symm)⟩
  have hValues := Reconstruction.reconstruction_prefix_values_d hM hD hD' hPrefix hH hH'
  intro c hc v
  by_cases hv : M.mem v C.omega
  · exact (hF.previous_iff hM.1 hH hB.1.2.1 (hLeft c hc)).symm.trans
      ((hValues c hc C.zero hC.zero_nat v hv).trans (hG.previous_iff hM.1 hH' hB'.1.2.1 (hRight c hc)))
  · exact iff_of_false (fun h => hv (hF.graph.bounds hM.1 h).2) (fun h => hv (hG.graph.bounds hM.1 h).2)

structure Spaces (α : Type u) where
  forestLists : α
  grids : α

structure Spaces.Valid (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (Forests : M.Domain) (S : Spaces M.Domain) : Prop where
  forestLists : ∀P, M.mem P S.forestLists ↔ ∃B, M.mem B C.omega ∧ Graph M P B Forests
  grids : ∀H, M.mem H S.grids ↔ ∃n, M.mem n C.omega ∧ Graph M H n C.sequences

theorem spaces_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) (Forests : M.Domain) : ∃S : Spaces M.Domain, S.Valid M C Forests := by
  obtain ⟨Parents,hParents⟩ := KP1Y.Sequences.finite_sequences_exist_d hM hC.omega Forests
  obtain ⟨Grids,hGrids⟩ := KP1Y.Sequences.finite_sequences_exist_d hM hC.omega C.sequences
  exact ⟨⟨Parents,Grids⟩,hParents,hGrids⟩

def bottomGraphFormula {n : Nat} (D : Reconstruction.GridData (Project.Term n)) (H F : Project.Term n) : Project.Formula 1 n :=
  .conj (graphFormula F D.width D.naturals.omega) (Project.Formula.forallMem D.width (Project.Formula.forallMem D.naturals.omega.weaken
    (.iff (memPairFormula F.weaken.weaken (.bound 1) (.bound 0))
      (Reconstruction.validCellFormula D.weaken.weaken H.weaken.weaken (.bound 1) D.naturals.zero.weaken.weaken (.bound 0)))))

theorem bottomGraphFormula_delta0 {n : Nat} (D : Reconstruction.GridData (Project.Term n)) (H F : Project.Term n) :
    (bottomGraphFormula D H F).IsDelta0 := .conj (graphFormula_delta0 _ _ _) (.forallMem _ (.forallMem _
      (.iff (memPairFormula_delta0 _ _ _) (Reconstruction.validCellFormula_delta0 _ _ _ _ _))))

theorem bottomGraphFormula_freeClosed {n : Nat} {D : Reconstruction.GridData (Project.Term n)} (hD : D.Closed)
    (H F : Project.Term n) (hH : H.freeSupport=[]) (hF : F.freeSupport=[]) : (bottomGraphFormula D H F).FreeClosed := by
  have hCell := Reconstruction.validCellFormula_freeClosed hD.weaken.weaken H.weaken.weaken (.bound 1) D.naturals.zero.weaken.weaken (.bound 0)
    (by simpa using hH) rfl (by simpa using hD.naturals.zero) rfl
  simp [bottomGraphFormula,graphFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,
    Definitional.Formula.FreeClosed,hD.width,hD.naturals.omega,hF,hCell]

theorem bottomGraphFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (D : Reconstruction.GridData (Project.Term n)) (H F : Project.Term n)
    (hH : Reconstruction.Reconstructs M (D.eval e) (H.eval e)) :
    Project.Formula.satisfies e (bottomGraphFormula D H F) ↔ BottomGraph M (D.eval e) (H.eval e) (F.eval e) := by
  simp only [bottomGraphFormula,Project.Formula.satisfies_conj_iff,graphFormula_iff he,Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_iff_iff,memPairFormula_iff he,Reconstruction.validCellFormula_iff he,Reconstruction.GridData.eval_weaken,Term.eval_weaken]
  constructor
  · rintro ⟨hF,hRows⟩
    refine ⟨hF,fun c v => ?_⟩
    constructor
    · intro hAt
      exact (hRows c (hF.bounds he hAt).1 v (hF.bounds he hAt).2).mp hAt
    · intro hCell
      have hv := (hCell.bounds he).2
      have hSaved := hCell
      obtain ⟨f,_,hCf,_,_⟩ := hCell
      exact (hRows c (hH.graph.bounds he hCf).1 v hv).mpr hSaved
  · exact fun h => ⟨h.graph,fun c _ v _ => h.rows c v⟩

theorem grid_eval {M : SetTheory.Structure.{u}} {n : Nat} (e : Env M n) (C : ExpressionData (Project.Term n))
    (X : CopiedMountain.Data (Project.Term n)) (Top Pairs Plus B Parents : Project.Term n) :
    (grid C X Top Pairs Plus B Parents).eval e = grid (C.eval e) (X.eval e) (Top.eval e) (Pairs.eval e) (Plus.eval e) (B.eval e) (Parents.eval e) := rfl

def rebuildCertificateFormula {n : Nat} (C : ExpressionData (Project.Term n)) (Pairs Plus : Project.Term n)
    (X : CopiedMountain.Data (Project.Term n)) (Top B Parents H F : Project.Term n) : Project.Formula 1 n :=
  .conj (sequenceBoundFormula C.omega C.zero X.width X.heights B) (.conj (prefixFormula Parents X.parents B X.forests)
    (.conj (Reconstruction.reconstructsFormula (grid C X Top Pairs Plus B Parents) H) (bottomGraphFormula (grid C X Top Pairs Plus B Parents) H F)))

theorem rebuildCertificateFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (Pairs Plus : Project.Term n)
    (X : CopiedMountain.Data (Project.Term n)) (Top B Parents H F : Project.Term n) :
    (rebuildCertificateFormula C Pairs Plus X Top B Parents H F).IsDelta0 :=
  .conj (sequenceBoundFormula_delta0 _ _ _ _ _) (.conj (prefixFormula_delta0 _ _ _ _)
    (.conj (Reconstruction.reconstructsFormula_delta0 _ _) (bottomGraphFormula_delta0 _ _ _)))

theorem rebuildCertificateFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {X : CopiedMountain.Data (Project.Term n)} (hX : X.Closed) (Pairs Plus Top B Parents H F : Project.Term n)
    (hPairs : Pairs.freeSupport=[]) (hPlus : Plus.freeSupport=[]) (hTop : Top.freeSupport=[]) (hB : B.freeSupport=[])
    (hParents : Parents.freeSupport=[]) (hH : H.freeSupport=[]) (hF : F.freeSupport=[]) :
    (rebuildCertificateFormula C Pairs Plus X Top B Parents H F).FreeClosed := by
  have hGrid : (grid C X Top Pairs Plus B Parents).Closed := ⟨hC,hX.width,hB,hX.heights,hX.forests,hParents,hTop,hPairs,hPlus⟩
  have hBound := sequenceBoundFormula_freeClosed C.omega C.zero X.width X.heights B hC.omega hC.zero hX.width hX.heights hB
  have hRebuild := Reconstruction.reconstructsFormula_freeClosed hGrid H hH
  have hBottom := bottomGraphFormula_freeClosed hGrid H F hH hF
  simp [rebuildCertificateFormula,prefixFormula,graphFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,
    Project.Formula.existsMem,Definitional.Formula.FreeClosed,hParents,hX.parents,hX.forests,hB,hBound,hRebuild,hBottom]

theorem rebuildCertificateFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (Pairs Plus : Project.Term n) (X : CopiedMountain.Data (Project.Term n))
    (Top B Parents H F : Project.Term n) : Project.Formula.satisfies e (rebuildCertificateFormula C Pairs Plus X Top B Parents H F) ↔
      SequenceBound M (C.eval e) (X.eval e).width (X.eval e).heights (B.eval e) ∧
      Prefix M (Parents.eval e) (X.eval e).parents (B.eval e) (X.eval e).forests ∧
      Reconstruction.Reconstructs M (grid (C.eval e) (X.eval e) (Top.eval e) (Pairs.eval e) (Plus.eval e) (B.eval e) (Parents.eval e)) (H.eval e) ∧
      BottomGraph M (grid (C.eval e) (X.eval e) (Top.eval e) (Pairs.eval e) (Plus.eval e) (B.eval e) (Parents.eval e)) (H.eval e) (F.eval e) := by
  rw [rebuildCertificateFormula,Project.Formula.satisfies_conj_iff,sequenceBoundFormula_iff he e C,
    Project.Formula.satisfies_conj_iff,prefixFormula_iff he,Project.Formula.satisfies_conj_iff,Reconstruction.reconstructsFormula_iff he]
  constructor
  · rintro ⟨hB,hP,hH,hF⟩
    exact ⟨hB,hP,hH,(bottomGraphFormula_iff he e (grid C X Top Pairs Plus B Parents) H F hH).mp hF⟩
  · rintro ⟨hB,hP,hH,hF⟩
    exact ⟨hB,hP,hH,(bottomGraphFormula_iff he e (grid C X Top Pairs Plus B Parents) H F hH).mpr hF⟩

def rebuildsFormula {n : Nat} (C : ExpressionData (Project.Term n)) (Pairs Plus : Project.Term n)
    (X : CopiedMountain.Data (Project.Term n)) (Top F ForestLists Grids : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem C.omega (Project.Formula.existsMem ForestLists.weaken (Project.Formula.existsMem Grids.weaken.weaken
    (rebuildCertificateFormula C.weaken.weaken.weaken Pairs.weaken.weaken.weaken Plus.weaken.weaken.weaken X.weaken.weaken.weaken
      Top.weaken.weaken.weaken (.bound 2) (.bound 1) (.bound 0) F.weaken.weaken.weaken)))

theorem rebuildsFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (Pairs Plus : Project.Term n)
    (X : CopiedMountain.Data (Project.Term n)) (Top F ForestLists Grids : Project.Term n) :
    (rebuildsFormula C Pairs Plus X Top F ForestLists Grids).IsDelta0 := .existsMem _ (.existsMem _ (.existsMem _ (rebuildCertificateFormula_delta0 _ _ _ _ _ _ _ _ _)))

theorem rebuildsFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {X : CopiedMountain.Data (Project.Term n)} (hX : X.Closed) (Pairs Plus Top F ForestLists Grids : Project.Term n)
    (hPairs : Pairs.freeSupport=[]) (hPlus : Plus.freeSupport=[]) (hTop : Top.freeSupport=[]) (hF : F.freeSupport=[])
    (hParents : ForestLists.freeSupport=[]) (hGrids : Grids.freeSupport=[]) : (rebuildsFormula C Pairs Plus X Top F ForestLists Grids).FreeClosed := by
  have hCert := rebuildCertificateFormula_freeClosed hC.weaken.weaken.weaken hX.weaken.weaken.weaken
    Pairs.weaken.weaken.weaken Plus.weaken.weaken.weaken Top.weaken.weaken.weaken (.bound 2) (.bound 1) (.bound 0) F.weaken.weaken.weaken
    (by simpa using hPairs) (by simpa using hPlus) (by simpa using hTop) rfl rfl rfl (by simpa using hF)
  simp [rebuildsFormula,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hC.omega,hParents,hGrids,hCert]

theorem rebuildsFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (Pairs Plus : Project.Term n) (X : CopiedMountain.Data (Project.Term n))
    (Top F ForestLists Grids : Project.Term n)
    (hSpaces : Spaces.Valid M (C.eval e) (X.eval e).forests ⟨ForestLists.eval e,Grids.eval e⟩)
    (hWidth : M.mem (X.eval e).width (C.eval e).omega) :
    Project.Formula.satisfies e (rebuildsFormula C Pairs Plus X Top F ForestLists Grids) ↔
      Rebuilds M (C.eval e) (Pairs.eval e) (Plus.eval e) (X.eval e) (Top.eval e) (F.eval e) := by
  simp only [rebuildsFormula,Project.Formula.satisfies_existsMem_iff,rebuildCertificateFormula_iff he,
    ExpressionData.eval_weaken,CopiedMountain.Data.eval_weaken,Term.eval_weaken]
  constructor
  · rintro ⟨B,_,Parents,_,H,_,hB,hP,hH,hF⟩
    exact ⟨B,Parents,H,hB,hP,hH,hF⟩
  · rintro ⟨B,Parents,H,hB,hP,hH,hF⟩
    exact ⟨B,hB.1.1,Parents,(hSpaces.forestLists Parents).mpr ⟨B,hB.1.1,hP.graph⟩,
      H,(hSpaces.grids H).mpr ⟨(X.eval e).width,hWidth,hH.graph⟩,hB,hP,hH,hF⟩

structure OriginalColumn (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (R : RowStateSpace M.Domain)
    (H B c f : M.Domain) : Prop where
  graph : Graph M f B C.omega
  rows : ∀r v, MemPair M f r v ↔ M.mem r B ∧ RowValue M R.states R.values R.forests H r c v

private def originalCellSchema : Project.Delta0BinarySchema 5 where
  body := rowValueFormula (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 1) (.bound 2) (.bound 0)
  freeClosed := rowValueFormula_freeClosed _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl
  delta0 := rowValueFormula_delta0 _ _ _ _ _ _ _

theorem original_column_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H B c : M.Domain}
    (hRun : RowRun M C m R V P H) (hB : M.mem B C.omega) (hc : M.mem c m) : ∃f, OriginalColumn M C R H B c f := by
  let e := ((((oneEnv R.states).push R.values).push R.forests).push H).push c
  have hφ (r v : M.Domain) : Project.Formula.satisfies ((e.push r).push v) originalCellSchema.body ↔
      RowValue M R.states R.values R.forests H r c v := rowValueFormula_iff hM.1 _ _ _ _ _ _ _ _
  obtain ⟨f,hSupport,hRaw⟩ := relation_comprehension_d hM originalCellSchema e B C.omega
  have hRows (r v : M.Domain) : MemPair M f r v ↔ M.mem r B ∧ RowValue M R.states R.values R.forests H r c v := by
    rw [hRaw r v,hφ]
    exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,(h.2.bounds hM.1 hRun.space).2,h.2⟩⟩
  refine ⟨f,⟨hSupport,?_,?_⟩,hRows⟩
  · intro r hr
    obtain ⟨v,hv,hV⟩ := hRun.value_exists_d hM hC ((omega_isOrdinal_d hM hC.omega).transitive B hB r hr) hc
    exact ⟨v,hv,(hRows r v).mpr ⟨hr,hV⟩⟩
  · intro r v v' hV hV'
    exact hRun.value_unique hM.1 ((hRows r v).mp hV).2 ((hRows r v').mp hV').2

private def originalColumnFormula {n : Nat} (w S Vs Fs H B c f : Project.Term n) : Project.Formula 1 n :=
  .conj (graphFormula f B w) (Project.Formula.forallMem B (Project.Formula.forallMem w.weaken
    (.iff (memPairFormula f.weaken.weaken (.bound 1) (.bound 0))
      (rowValueFormula S.weaken.weaken Vs.weaken.weaken Fs.weaken.weaken H.weaken.weaken (.bound 1) c.weaken.weaken (.bound 0)))))

private theorem originalColumnFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData M.Domain) (R : RowStateSpace M.Domain) (w S Vs Fs H B c f : Project.Term n)
    (hw : w.eval e=C.omega) (hS : S.eval e=R.states) (hVs : Vs.eval e=R.values) (hFs : Fs.eval e=R.forests)
    {m : M.Domain} (hR : R.Valid M C m) :
    Project.Formula.satisfies e (originalColumnFormula w S Vs Fs H B c f) ↔ OriginalColumn M C R (H.eval e) (B.eval e) (c.eval e) (f.eval e) := by
  simp only [originalColumnFormula,Project.Formula.satisfies_conj_iff,graphFormula_iff he,Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_iff_iff,memPairFormula_iff he,rowValueFormula_iff he,Term.eval_weaken,hw,hS,hVs,hFs]
  constructor
  · rintro ⟨hF,hRows⟩
    refine ⟨hF,fun r v => ?_⟩
    exact ⟨fun hAt => ⟨(hF.bounds he hAt).1,(hRows r (hF.bounds he hAt).1 v (hF.bounds he hAt).2).mp hAt⟩,
      fun h => (hRows r h.1 v (h.2.bounds he hR).2).mpr h.2⟩
  · exact fun h => ⟨h.graph,fun r hr v _ => (h.rows r v).trans ⟨And.right,fun h => ⟨hr,h⟩⟩⟩

private def originalColumnSchema : Project.Delta0BinarySchema 6 where
  body := originalColumnFormula (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := by
    simp [originalColumnFormula,rowValueFormula,rowAtFormula,graphFormula,memPairFormula,codeFormula,pairFormula,
      Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := .conj (graphFormula_delta0 _ _ _) (.forallMem _ (.forallMem _ (.iff (memPairFormula_delta0 _ _ _) (rowValueFormula_delta0 _ _ _ _ _ _ _))))

theorem original_columns_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H B : M.Domain}
    (hRun : RowRun M C m R V P H) (hB : M.mem B C.omega) :
    ∃G, Graph M G m C.sequences ∧ ∀c f, MemPair M G c f ↔ M.mem c m ∧ OriginalColumn M C R H B c f := by
  let e := (((((oneEnv C.omega).push R.states).push R.values).push R.forests).push H).push B
  have hφ (c f : M.Domain) : Project.Formula.satisfies ((e.push c).push f) originalColumnSchema.body ↔ OriginalColumn M C R H B c f :=
    originalColumnFormula_iff hM.1 _ C R _ _ _ _ _ _ _ _ rfl rfl rfl rfl hRun.space
  obtain ⟨G,hSupport,hRaw⟩ := relation_comprehension_d hM originalColumnSchema e m C.sequences
  have hRows (c f : M.Domain) : MemPair M G c f ↔ M.mem c m ∧ OriginalColumn M C R H B c f := by
    rw [hRaw c f,hφ]
    exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,(hC.sequences f).mpr ⟨B,hB,h.2.graph⟩,h.2⟩⟩
  refine ⟨G,⟨hSupport,?_,?_⟩,hRows⟩
  · intro c hc
    obtain ⟨f,hf⟩ := original_column_exists_d hM hC hRun hB hc
    exact ⟨f,(hC.sequences f).mpr ⟨B,hB,hf.graph⟩,(hRows c f).mpr ⟨hc,hf⟩⟩
  · intro c f g hCf hCg
    have hf := ((hRows c f).mp hCf).2
    have hg := ((hRows c g).mp hCg).2
    exact hf.graph.ext hM.1 hg.graph (fun r _ v => (hf.rows r v).trans (hg.rows r v).symm)

theorem original_grid_cell_iff {M : SetTheory.Structure.{u}} (_he : Extensional M)
    {C : ExpressionData M.Domain} {m : M.Domain} {R : RowStateSpace M.Domain} {Run B G : M.Domain}
    {X : CopiedMountain.Data M.Domain} {Top Pairs Plus Parents c r v : M.Domain} (hG : Graph M G m C.sequences)
    (hRows : ∀c f, MemPair M G c f ↔ M.mem c m ∧ OriginalColumn M C R Run B c f) :
    Reconstruction.ValidCell M (grid C X Top Pairs Plus B Parents) G c r v ↔
      M.mem c m ∧ M.mem r B ∧ RowValue M R.states R.values R.forests Run r c v := by
  constructor
  · rintro ⟨f,_,hCf,_,hValue⟩
    have hCol := (hRows c f).mp hCf
    exact ⟨hCol.1,((hCol.2.rows r v).mp hValue)⟩
  · rintro ⟨hc,hr,hValue⟩
    obtain ⟨f,hf,hCf⟩ := hG.total c hc
    have hCol := ((hRows c f).mp hCf).2
    exact ⟨f,hf,hCf,hCol.graph,(hCol.rows r v).mpr ⟨hr,hValue⟩⟩

private theorem value_in_row {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain}
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P Run r W Q c v : M.Domain}
    (hRun : RowRun M C m R V P Run) (hAt : RowAt M R.states Run r W Q)
    (h : RowValue M R.states R.values R.forests Run r c v) : MemPair M W c v := by
  obtain ⟨W',_,Q',_,hAt',hV⟩ := h
  have hWW := (hRun.at_unique he hAt' hAt).1
  exact hWW ▸ hV

theorem row_parent_sum_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P Run r s W Q c p u v b : M.Domain}
    (hRun : RowRun M C m R V P Run) (hAt : RowAt M R.states Run r W Q) (hParent : MemPair M Q c p)
    (hSucc : M.SuccessorOf s r) (hU : RowValue M R.states R.values R.forests Run r c u)
    (hV : RowValue M R.states R.values R.forests Run s c v) (hB : RowValue M R.states R.values R.forests Run r p b) :
    AddAt M Pairs Plus v b u := by
  have hUAt := value_in_row hM.1 hRun hAt hU
  have hBAt := value_in_row hM.1 hRun hAt hB
  have hN := hRun.at_numeric_d hM hC hAt
  have hb := (hB.bounds hM.1 hRun.space).2
  have hv := (hV.bounds hM.1 hRun.space).2
  obtain ⟨W',_,Q',_,hAt',hVAt⟩ := hV
  have hNext := hRun.at_next hM.1 hSucc hAt hAt'
  rcases ((hNext.difference.rows c v).mp hVAt).2 with ⟨hNo,_⟩ | ⟨p',_,x,_,y,_,hP',hX,hY,hDiff⟩
  · exact False.elim (hNo p (hN.forest.bounds hM.1 hParent).2 hParent)
  · have hpp := hN.forest.unique c p' p hP' hParent
    subst p'
    have hxu := hN.values.unique c x u hX hUAt
    have hyb := hN.values.unique p y b hY hBAt
    subst x
    subst y
    have hSum := truncated_difference_add_inverse_d hM hC hDiff (.inr (hN.parentValues c p b u hParent hBAt hUAt).2)
    exact (hPlus.add_iff_sum hM hv hb).mpr (natural_sum_comm_d hM hC hb hv hSum)

theorem original_reconstructs_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P Run Top B Parents G : M.Domain}
    (hRun : RowRun M C m R V P Run) (hPositive : ∀c v, MemPair M V c v → M.mem C.zero v)
    {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C) (hFrom : CopiedMountain.FromRun M C m R V Run X)
    (hTop : TopValueGraph M C m R Run X.heights Top) (hB : SequenceBound M C X.width X.heights B)
    (hParents : Prefix M Parents X.parents B X.forests) (hG : Graph M G m C.sequences)
    (hColumns : ∀c f, MemPair M G c f ↔ M.mem c m ∧ OriginalColumn M C R Run B c f) :
    Reconstruction.Reconstructs M (grid C X Top Pairs Plus B Parents) G := by
  have hTopGraph : Graph M Top X.width C.omega := hFrom.width.symm ▸ hTop.graph
  have hD := grid_valid_d hM hC hX hTopGraph hPlus hB hParents
  have hCell (c r v : M.Domain) := original_grid_cell_iff (Top := Top) (Pairs := Pairs) (Plus := Plus) (X := X) (Parents := Parents) hM.1 hG hColumns (c := c) (r := r) (v := v)
  refine ⟨(show Graph M G X.width C.sequences from hFrom.width.symm ▸ hG),?_⟩
  intro c hc f _ hCf
  have hCol := ((hColumns c f).mp hCf).2
  have hcm := ((hColumns c f).mp hCf).1
  refine ⟨hCol.graph,?_,?_,?_⟩
  · intro height hh top _ hHeight hTopAt
    obtain ⟨height',_,hHeight',hValue⟩ := (hTop.rows c top).mp hTopAt
    have he := hFrom.heights.graph.unique c height' height hHeight' hHeight
    subst height'
    exact (hCol.rows height top).mpr ⟨hh,hValue⟩
  · intro height _ hHeight r hr v hv hRv hhr
    apply Classical.byContradiction
    intro hv0
    have hPos := (hC.zero_mem_iff hM hv).mpr hv0
    have hValue := ((hCol.rows r v).mp hRv).2
    obtain ⟨a,_,hA⟩ := hRun.base.values.total c hcm
    have hHeightAt := ((hFrom.heights.rows c height).mp hHeight).2
    have hLe := (hRun.live_iff_le_height_d hM hC hA (hPositive c a hA) hHeightAt
      ((omega_isOrdinal_d hM hC.omega).transitive B hB.1.1 r hr)).mp ⟨v,hv,hValue,hPos⟩
    rcases hLe with he | hrh
    · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) height (he ▸ hhr)
    · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) height
        (((omega_isOrdinal_d hM hC.omega).mem (hX.heights.bounds hM.1 hHeight).2).transitive r hrh height hhr)
  · intro height hh hHeight r hr s hs u _ v _ b _ hSucc hU hV hContrib
    have hrB := ((omega_isOrdinal_d hM hC.omega).mem hB.1.1).transitive height hh r hr
    have hrω := (omega_isOrdinal_d hM hC.omega).transitive B hB.1.1 r hrB
    have hUValue := ((hCol.rows r u).mp hU).2
    have hVValue := ((hCol.rows s v).mp hV).2
    have hParentValue : ∃p, Reconstruction.ParentAt M (grid C X Top Pairs Plus B Parents) r c p ∧ RowValue M R.states R.values R.forests Run r p b := by
      rcases hContrib with ⟨p,_,hP,hPrevious⟩ | ⟨_,hNone⟩
      · refine ⟨p,hP,?_⟩
        rcases hPrevious with hValue | ⟨_,hNoValue⟩
        · exact ((hCell p r b).mp hValue).2.2
        · have hp := (hP.bounds hM.1 hD).2.2.1
          have hpm : M.mem p m := hFrom.width ▸ hp
          obtain ⟨x,hx,hXValue⟩ := hRun.value_exists_d hM hC hrω hpm
          exact False.elim (hNoValue x hx ((hCell p r x).mpr ⟨hpm,hrB,hXValue⟩))
      · obtain ⟨p,hP⟩ := (hD.live r hrB c hc height hHeight).mpr hr
        exact False.elim (hNone p (hP.bounds hM.1 hD).2.2.2 hP)
    obtain ⟨p,hP,hBValue⟩ := hParentValue
    have hPX := (grid_parent_iff_d hM hC hX hB hParents).mp hP
    obtain ⟨W,Q,hAt,hParent⟩ := (hFrom.parent_iff hM.1 hX r c p).mp hPX
    exact row_parent_sum_d hM hC hPlus hRun hAt hParent hSucc hUValue hVValue hBValue

/-- 真实数值行以其实际TopValue作顶部时，重建底行恰好恢复原V。 -/
theorem rebuild_original_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P Run Top : M.Domain}
    (hRun : RowRun M C m R V P Run) (hPositive : ∀c v, MemPair M V c v → M.mem C.zero v)
    {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C) (hFrom : CopiedMountain.FromRun M C m R V Run X)
    (hTop : TopValueGraph M C m R Run X.heights Top) : Rebuilds M C Pairs Plus X Top V := by
  obtain ⟨B,hB⟩ := sequence_bound_exists_d hM hC hX.width hX.heights
  obtain ⟨Parents,hParents⟩ := restrict_prefix_d hM hX.parents ((omega_isOrdinal_d hM hC.omega).transitive B hB.1.1)
  obtain ⟨G,hG,hColumns⟩ := original_columns_exists_d hM hC hRun hB.1.1
  have hReconstruct := original_reconstructs_d hM hC hPlus hRun hPositive hX hFrom hTop hB hParents hG hColumns
  refine ⟨B,Parents,G,hB,hParents,hReconstruct,⟨(show Graph M V X.width C.omega from hFrom.width.symm ▸ hRun.base.values),?_⟩⟩
  intro c v
  rw [original_grid_cell_iff hM.1 hG hColumns]
  change MemPair M V c v ↔ M.mem c m ∧ M.mem C.zero B ∧ RowValue M R.states R.values R.forests Run C.zero c v
  rw [hRun.value_initial_iff_d hM]
  exact ⟨fun hAt => ⟨(hRun.base.values.bounds hM.1 hAt).1,hB.1.2.1,hAt⟩,fun h => h.2.2⟩

/-- 高度全零的山形重建严格保持输入顶部图，包含空宽度。 -/
theorem Rebuilds.height_zero_identity_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {Pairs Plus : M.Domain} {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C)
    {Top F : M.Domain} (hTop : Graph M Top X.width C.omega)
    (hZero : ∀c height, MemPair M X.heights c height → height=C.zero)
    (h : Rebuilds M C Pairs Plus X Top F) : F=Top := by
  obtain ⟨B,Parents,H,hB,_,hH,hF⟩ := h
  apply hF.graph.ext hM.1 hTop
  intro c hc v
  obtain ⟨height,_,hHeight⟩ := hX.heights.total c hc
  have hh := hZero c height hHeight
  subst height
  obtain ⟨f,_,hCf⟩ := hH.graph.total c hc
  have hTopRead (v : M.Domain) (hTopAt : MemPair M Top c v) : MemPair M f C.zero v :=
    (hH.column hM.1 hCf).top C.zero hB.1.2.1 v (hTop.bounds hM.1 hTopAt).2 hHeight hTopAt
  constructor
  · intro hAt
    obtain ⟨top,_,hTopAt⟩ := hTop.total c hc
    have he := (hH.column hM.1 hCf).graph.unique C.zero top v (hTopRead top hTopAt)
      ((hH.valid_cell_iff hM.1 hCf).mp ((hF.rows c v).mp hAt))
    exact he ▸ hTopAt
  · intro hAt
    exact (hF.rows c v).mpr ((hH.valid_cell_iff hM.1 hCf).mpr (hTopRead v hAt))

theorem rebuild_height_zero_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C) {Top : M.Domain} (hTop : Graph M Top X.width C.omega)
    (hZero : ∀c height, MemPair M X.heights c height → height=C.zero) : Rebuilds M C Pairs Plus X Top Top := by
  obtain ⟨F,hF⟩ := rebuild_exists_d hM hC hPlus hX hTop
  exact hF.height_zero_identity_d hM hX hTop hZero ▸ hF

end KP1Y.OneYFinite.MountainReconstruction
