import KP1Y.OneYCopyPathTransport

/-! 复制路径允许把一条源父边替换为目标实际有限祖先路径。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
universe u

private def mappedAncestrySchema : Project.UnarySchema 13 where
  body := Project.Formula.forallMem (.bound 6)
    (.imp (.conj (ancestorFormula ⟨.bound 14,.bound 13,.bound 12,.bound 11,.bound 10⟩ (.bound 9) (.bound 8) (.bound 4) (.bound 1))
      (.conj (.disj (Project.Formula.extensionalEq (.bound 1) (.bound 2))
        (ancestorFormula ⟨.bound 14,.bound 13,.bound 12,.bound 11,.bound 10⟩ (.bound 9) (.bound 8) (.bound 1) (.bound 2)))
        (memPairFormula (.bound 5) (.bound 1) (.bound 0))))
      (ancestorFormula ⟨.bound 14,.bound 13,.bound 12,.bound 11,.bound 10⟩ (.bound 7) (.bound 6) (.bound 3) (.bound 0)))
  freeClosed := by
    have hC : (⟨.bound 14,.bound 13,.bound 12,.bound 11,.bound 10⟩ : ExpressionData (Project.Term 15)).Closed := ⟨rfl,rfl,rfl,rfl,rfl⟩
    have hA := ancestorFormula_freeClosed hC (.bound 9) (.bound 8) (.bound 4) (.bound 1) rfl rfl rfl rfl
    have hD := ancestorFormula_freeClosed hC (.bound 9) (.bound 8) (.bound 1) (.bound 2) rfl rfl rfl rfl
    have hOut := ancestorFormula_freeClosed hC (.bound 7) (.bound 6) (.bound 3) (.bound 0) rfl rfl rfl rfl
    simp [Project.Formula.forallMem,Definitional.Formula.FreeClosed,memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,hA,hD,hOut]

private def mappedAncestryEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (m P n Q J a x last : M.Domain) : Env M 13 :=
  ((((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push m).push P).push n).push Q).push J).push a).push x).push last

private theorem mappedAncestrySchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (m P n Q J a x last c : M.Domain) :
    Project.Formula.satisfies ((mappedAncestryEnv C m P n Q J a x last).push c) mappedAncestrySchema.body ↔
      ∀y, M.mem y n → Ancestor M C m P a c ∧ (c=last ∨ Ancestor M C m P c last) ∧ MemPair M J c y →
        Ancestor M C n Q x y := by
  simp only [mappedAncestrySchema,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,
    ancestorFormula_iff he,memPairFormula_iff he]
  rfl

/-- 仅源起止点之间的父边需要给出目标路径；无需声称全部全ω像落入目标宽度。 -/
theorem ancestor_map_refines_global_bounded_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m n P Q J a c x y : M.Domain}
    (hP : Forest M C.omega m P) (hQ : Forest M C.omega n Q) (hJ : ColumnEmbedding M C.omega C.omega J)
    (hAnc : Ancestor M C m P a c) (hAX : MemPair M J a x) (hCY : MemPair M J c y) (hy : M.mem y n)
    (hEdges : ∀d p u v, (d=c ∨ Ancestor M C m P d c) → (a=p ∨ M.mem a p) → MemPair M P d p →
      MemPair M J d u → MemPair M J p v → M.mem u n → Ancestor M C n Q v u) : Ancestor M C n Q x y := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hAll := KP1Y.ordinal_induction_d hM mappedAncestrySchema (mappedAncestryEnv C m P n Q J a x c) (by
    intro d _ ih
    apply (mappedAncestrySchema_iff hM.1 C m P n Q J a x c d).mpr
    rintro u hu ⟨hAD,hDC,hDU⟩
    obtain ⟨p,hParent,hTail⟩ := ancestor_parent_cases_d hM hC hP hAD
    have hpNat := hw.transitive m hP.width p (hP.bounds hM.1 hParent).2
    obtain ⟨v,_,hPV⟩ := hJ.graph.total p hpNat
    have hv : M.mem v n := (hw.mem hQ.width).transitive u hu v
      (hJ.strict p hpNat d (hJ.graph.bounds hM.1 hDU).1 (hP.left d p hParent) v u hPV hDU)
    have hAPLe : a=p ∨ M.mem a p := hTail.imp_right And.left
    have hStep := hEdges d p u v hDC hAPLe hParent hDU hPV hu
    rcases hTail with he | hAP
    · have hXV := hJ.graph.unique p x v (he ▸ hAX) hPV
      exact hXV.symm ▸ hStep
    · have hPC : Ancestor M C m P p c := by
        have hPD := ancestor_direct_d hM hC hP hParent
        rcases hDC with he | hDC
        · exact he ▸ hPD
        · exact ancestor_trans_d hM hC hP hPD hDC
      have hAV := (mappedAncestrySchema_iff hM.1 C m P n Q J a x c p).mp
        (ih p (hP.left d p hParent)) v hv ⟨hAP,Or.inr hPC,hPV⟩
      exact ancestor_trans_d hM hC hQ hAV hStep)
  have hcNat := hw.transitive m hP.width c (hAnc.bounds hM.1).2
  exact (mappedAncestrySchema_iff hM.1 C m P n Q J a x c c).mp (hAll c (hw.mem hcNat)) y hy ⟨hAnc,Or.inl rfl,hCY⟩

end KP1Y.OneYFinite
