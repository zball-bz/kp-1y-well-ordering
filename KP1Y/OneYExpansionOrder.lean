import KP1Y.OneYExpansion
import KP1Y.OneYVirtualNeeds
import KP1Y.OneYLexOrder
import KP1Y.OneYReachability

/-! 实际EN的复制参数前缀单调：i≤j时E_i(s)是E_j(s)的前缀。
两侧取同一坏根与同一复制坐标，复制塔在公共宽度上逐层一致，重建只读公共前缀。 -/
namespace KP1Y.OneYFinite.ExpansionOrder
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite KP1Y.OneYFinite.Expansion
universe u

theorem le_subset_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {i j : M.Domain} (hj : M.mem j C.omega)
    (hij : i=j ∨ M.mem i j) : M.MemberSubset i j := by
  rcases hij with he | hij
  · exact he ▸ fun _ h => h
  · exact fun x hx => ((omega_isOrdinal_d hM hC.omega).mem hj).transitive i hij x hx

/-- 宽度last+N*(last-root)对内部N单调。 -/
theorem width_mono_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) {i j n n' : M.Domain}
    (hW : CopyCoordinates.Width M C T A i n) (hW' : CopyCoordinates.Width M C T A j n')
    (hij : M.MemberSubset i j) : M.MemberSubset n n' := by
  obtain ⟨hl,hi,off,hOff,hTimes,hAdd⟩ := hW
  obtain ⟨_,hj,off',hOff',hTimes',hAdd'⟩ := hW'
  have hP := (hT.mul.mul_iff_product hM hi (hA.length_nat hM.1)).mp hTimes
  have hP' := (hT.mul.mul_iff_product hM hj (hA.length_nat hM.1)).mp hTimes'
  have hOffSub := natural_product_mono_left_d hM hC hi hj (hA.length_nat hM.1) hP hP' hij
  exact KP1Y.Arithmetic.sum_mono_right_d hM ((omega_isOrdinal_d hM hC.omega).mem hl)
    ((hT.add.add_iff_sum hM hl hOff).mp hAdd) ((hT.add.add_iff_sum hM hl hOff').mp hAdd') hOffSub

/-- 两次成功展开共用全部原始层数据与坐标；较小宽度的塔与重建是较大者的前缀。 -/
theorem Successful.nested_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {s m last i j t u : M.Domain} {W W' : SuccessData M.Domain}
    (h : Successful M C T s m last i t W) (h' : Successful M C T s m last j u W')
    (hij : M.MemberSubset i j) :
    M.MemberSubset W.width W'.width ∧ RowsAgreeOn M t u W.width := by
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
  have hBB := hB.unique_d hM hC hB'
  subst B'
  have hAA := CopyTower.coordinates_unique_d hM hC hA hA' (hAx.trans hAx'.symm) hCoordinateRoots
  subst A'
  have hSub := width_mono_d hM hC hT hA hWidth hWidth' hij
  have hK := (CopyTower.bad_indices_d hM hC hRun hBad).1
  have hPrefix := CopyNeeds.tower_family_prefix_d hM hC hRun hK hTower hTower' hTower.width (fun _ h => h) hSub
  have hTops : RowsAgreeOn M Top Top' n := by
    intro c hc v
    rw [hTop.2 c v,hTop'.2 c v]
    exact ⟨fun h => ⟨hSub c hc,h.2⟩,fun h => ⟨hc,h.2⟩⟩
  exact ⟨hSub,hRebuild.prefix_d hM hC hT.add hTower.width hTower'.width hTower.bound hTower.graph hTower'.graph
    (fun _ _ => hTower.code_valid) (fun _ _ => hTower'.code_valid) hPrefix hTops hRebuild'⟩

/-- (a) 对全部内部 i≤j：实际E_i(s)是E_j(s)的前缀，长度亦单调。 -/
theorem Expands.nested_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {s i j t u : M.Domain} (h : Expands M C T s i t) (h' : Expands M C T s j u) (hij : i=j ∨ M.mem i j) :
    ∃n p, LegalAt M C.omega C.zero C.one t n ∧ LegalAt M C.omega C.zero C.one u p ∧
      M.MemberSubset n p ∧ Prefix M t u n C.omega := by
  obtain ⟨_,m,hm,hLegal,hCases⟩ := h
  obtain ⟨hj,m',_,hLegal',hCases'⟩ := h'
  have hmm := legal_length_unique hM.1 hLegal' hLegal
  subst m'
  have hSub := le_subset_d hM hC hj hij
  rcases hCases with ⟨hm0,ht⟩ | ⟨last,hl,hSucc,hDrop | ⟨W,hSuccess⟩⟩ <;>
    rcases hCases' with ⟨hm0',hu⟩ | ⟨last',hl',hSucc',hDrop' | ⟨W',hSuccess'⟩⟩
  · subst t
    subst u
    exact ⟨m,m,hLegal,hLegal,fun _ h => h,hLegal.1.2,fun _ _ _ _ => Iff.rfl⟩
  · exact False.elim (hC.zero_empty last' (hm0 ▸ hSucc'.predecessor_mem))
  · exact False.elim (hC.zero_empty last' (hm0 ▸ hSucc'.predecessor_mem))
  · exact False.elim (hC.zero_empty last (hm0' ▸ hSucc.predecessor_mem))
  · have hll := Structure.SuccessorOf.predecessor_eq hM.1 ((omega_isOrdinal_d hM hC.omega).mem hl) hSucc hSucc'
    subst last'
    have hLastSub : M.MemberSubset last m := fun c hc => (hSucc c).mpr (.inl hc)
    have hT' := prefix_legal_d hM hC hLegal hl hLastSub hDrop.2
    have hU' := prefix_legal_d hM hC hLegal hl hLastSub hDrop'.2
    refine ⟨last,last,hT',hU',fun _ h => h,hDrop.2.graph,fun c hc y _ => ?_⟩
    exact (hDrop.2.all_rows hM.1 hLegal.1.2 c hc y).trans (hDrop'.2.all_rows hM.1 hLegal.1.2 c hc y).symm
  · have hll := Structure.SuccessorOf.predecessor_eq hM.1 ((omega_isOrdinal_d hM hC.omega).mem hl) hSucc hSucc'
    subst last'
    exact False.elim (hSuccess'.not_last_one_d hM hC hDrop.1)
  · exact False.elim (hC.zero_empty last (hm0' ▸ hSucc.predecessor_mem))
  · have hll := Structure.SuccessorOf.predecessor_eq hM.1 ((omega_isOrdinal_d hM hC.omega).mem hl) hSucc hSucc'
    subst last'
    exact False.elim (hSuccess.not_last_one_d hM hC hDrop'.1)
  · have hll := Structure.SuccessorOf.predecessor_eq hM.1 ((omega_isOrdinal_d hM hC.omega).mem hl) hSucc hSucc'
    subst last'
    obtain ⟨hWidthSub,hAgree⟩ := Successful.nested_d hM hC hT hSuccess hSuccess' hSub
    refine ⟨W.width,W'.width,hSuccess.legal_d hM hC hT,hSuccess'.legal_d hM hC hT,hWidthSub,
      hSuccess.reconstruction.graph,fun c hc y _ => hAgree c hc y⟩

private def prefixReachEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (Reach : M.Domain) : Env M 5 :=
  ((((oneEnv C.omega).push C.zero).push C.one).push C.expressions).push Reach

private def prefixReachSchema : Project.Delta0UnarySchema 5 where
  body := Project.Formula.forallMem (.bound 2) (Project.Formula.forallMem (.bound 6) (Project.Formula.forallMem (.bound 4)
    (.imp (legalAtFormula (.bound 8) (.bound 7) (.bound 6) (.bound 2) (.bound 3))
      (.imp (Project.Formula.subset (.bound 1) (.bound 3))
        (.imp (prefixFormula (.bound 0) (.bound 2) (.bound 1) (.bound 8)) (memPairFormula (.bound 4) (.bound 0) (.bound 2)))))))
  freeClosed := by
    have hL := legalAtFormula_freeClosed (n := 9) (.bound 8) (.bound 7) (.bound 6) (.bound 2) (.bound 3) rfl rfl rfl rfl rfl
    simp [prefixFormula,graphFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,
      Project.Formula.existsMem,Project.Formula.subset,Definitional.Formula.FreeClosed,hL]
  delta0 := .forallMem _ (.forallMem _ (.forallMem _ (.imp (legalAtFormula_delta0 _ _ _ _ _)
    (.imp (.atom _ _ _) (.imp (prefixFormula_delta0 _ _ _ _) (memPairFormula_delta0 _ _ _))))))

private theorem prefixReachSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (Reach m : M.Domain) :
    Project.Formula.satisfies ((prefixReachEnv C Reach).push m) prefixReachSchema.body ↔
      ∀s, M.mem s C.expressions → ∀n, M.mem n C.omega → ∀t, M.mem t C.expressions →
        LegalAt M C.omega C.zero C.one s m → M.MemberSubset n m → Prefix M t s n C.omega → MemPair M Reach t s := by
  simp only [prefixReachSchema,prefixReachEnv,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    legalAtFormula_iff he,Project.Formula.satisfies_subset_iff,prefixFormula_iff he,memPairFormula_iff he]
  rfl

/-- 全长前缀就是原序列。 -/
theorem prefix_full_eq {M : SetTheory.Structure.{u}} (he : Extensional M) {w s t m : M.Domain}
    (hS : Graph M s m w) (hP : Prefix M t s m w) : t=s :=
  hP.graph.ext he hS (fun c hc y => hP.all_rows he hS c hc y)

/-- (b) 任意前缀经有限次实际E₀步可达；对内部长度作对象自然数归纳。 -/
theorem prefix_reachable_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {Keys EN Reach : M.Domain} (hEN : Expansion.Graph M C T Keys EN) (hR : Reachability.Relation M C Keys EN Reach)
    {s m n t : M.Domain} (hLegal : LegalAt M C.omega C.zero C.one s m) (hn : M.mem n C.omega)
    (hnm : M.MemberSubset n m) (hPrefix : Prefix M t s n C.omega) : MemPair M Reach t s := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hAll := natural_induction_d hM prefixReachSchema.toUnarySchema (prefixReachEnv C Reach) hC.omega
    (fun e hEmpty => (prefixReachSchema_iff hM.1 C Reach e).mpr (by
      intro s hs n _ t _ hL hne hP
      have hn0 : n=e := hM.1.eq_of_same_members n e (fun x => iff_of_false (fun h => hEmpty x (hne x h)) (hEmpty x))
      subst n
      have hts := prefix_full_eq hM.1 hL.1.2 hP
      subst t
      exact hR.reflexive_d hM hC hs))
    (fun p hp ih q hq => (prefixReachSchema_iff hM.1 C Reach q).mpr (by
      intro s hs n hn t ht hL hnq hP
      have hqω := hL.1.1
      rcases ordinal_subset_cases_d hM (hw.mem hn) (hw.mem hqω) hnq with he | hnIn
      · subst n
        have hts := prefix_full_eq hM.1 hL.1.2 hP
        subst t
        exact hR.reflexive_d hM hC hs
      · have hnp : M.MemberSubset n p := by
          rcases (hq n).mp hnIn with hnp | hSame
          · exact fun x hx => (hw.mem hp).transitive n hnp x hx
          · exact fun x hx => (hSame x).mp hx
        obtain ⟨s0,hDrop,hs0,_⟩ := legal_drop_last_d hM hC hL
        obtain ⟨p',hp',hPre⟩ := hDrop
        have hpp : p'=p := previous_length_unique_d hM hC hp' ⟨hp,.inr hq⟩
        subst p'
        have hpq : M.MemberSubset p q := fun x hx => (hq x).mpr (.inl hx)
        have hL0 := prefix_legal_d hM hC hL hp hpq hPre
        have hP0 : Prefix M t s0 n C.omega := ⟨hP.graph,fun c hc y _ =>
          (hP.all_rows hM.1 hL.1.2 c hc y).trans (hPre.all_rows hM.1 hL.1.2 c (hnp c hc) y).symm⟩
        have hReach0 := (prefixReachSchema_iff hM.1 C Reach p).mp ih s0 hs0 n hn t ht hL0 hnp hP0
        have hExpand := (expands_zero_iff_drop_d hM hC hT hL).mpr ⟨p,hp',hPre⟩
        have hStep := hR.actual_expansion_reachable_d hM hC hEN hExpand
        exact hR.transitive_d hM hC hReach0 hStep))
  have hs := (hC.expressions s).mpr ⟨m,hLegal.1.1,hLegal⟩
  have hLt := prefix_legal_d hM hC hLegal hn hnm hPrefix
  exact (prefixReachSchema_iff hM.1 C Reach m).mp (hAll m hLegal.1.1) s hs n hn t
    ((hC.expressions t).mpr ⟨n,hn,hLt⟩) hLegal hnm hPrefix

/-- O02.index_mono：i≤j时实际E_i(s)从E_j(s)经E₀步可达。 -/
theorem index_mono_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {Keys EN Reach : M.Domain} (hEN : Expansion.Graph M C T Keys EN) (hR : Reachability.Relation M C Keys EN Reach)
    {s i j t u : M.Domain} (hij : i=j ∨ M.mem i j)
    (ht : KP1Y.Dynamics.Expansion M Keys EN s i t) (hu : KP1Y.Dynamics.Expansion M Keys EN s j u) : MemPair M Reach t u := by
  have hT' := (Reachability.expansion_step_iff_d hM hC hEN).mp ht
  have hU' := (Reachability.expansion_step_iff_d hM hC hEN).mp hu
  obtain ⟨n,p,hLt,hLu,hnp,hPrefix⟩ := Expands.nested_d hM hC hT hT' hU' hij
  exact prefix_reachable_d hM hC hT hEN hR hLu hLt.1.1 hnp hPrefix

end KP1Y.OneYFinite.ExpansionOrder
