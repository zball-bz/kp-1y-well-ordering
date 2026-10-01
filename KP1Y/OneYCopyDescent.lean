import KP1Y.OneYCopySeamsInduction
import KP1Y.OneYRankDescentStatement

/-! Y06：文稿Lemma 3（有限复制下降）的对象形式。删除/无坏根分支由规范图前缀局部性直接限制；
坏根分支由Y04b的复制图表示，加上Y05b的规范重新提取边包含（唯一命名接口`CanonicalCopyBound`）。 -/
namespace KP1Y.OneYFinite.CopyDescent
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Reflection
open KP1Y.OneYFinite.CopyCoordinates KP1Y.OneYFinite.ExpressionDiagram KP1Y.OneYRank
universe u

/-- Y05b接口（单个模型内）：坏根分支实际输出t的规范根图A(t)的每条边，都是`Successful`中
同一座实际塔在Width(N)处枚举的复制图的边。宽度相等`n=W.width`不在接口内，由合法长度唯一性直接导出。`m=last+1`由调用方的坏根分支提供（Terminal 复制需要）。
本文件不证明此命题；它是Y06唯一未解除的命名前提。 -/
def CanonicalCopyBoundIn (M : SetTheory.Structure.{u}) : Prop :=
  ∀ (E : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (D : Reflection.Data M.Domain),
    E.Valid M → T.Valid M E → D.Valid M → D.omega=E.omega →
    ∀ s m last N t (W : Expansion.SuccessData M.Domain), Expansion.Successful M E T s m last N t W →
    M.SuccessorOf m last →
    ∀ Old, CopyDiagram.Enumerated M E T D ⟨W.horizon,W.width,W.forests,W.codes,W.tower⟩ Old →
    ∀ n B, ExpressionGraph M E T D t n B → ∀ k q p c, EdgeAt M D B k q p c → EdgeAt M D Old k q p c

/-- 对所有KP1Y模型成立的Y05b接口。 -/
def CanonicalCopyBound : Prop :=
  ∀ (M : SetTheory.Structure.{u}), M.Models KP1Y.theory → CanonicalCopyBoundIn M

/-- 同宽度、边包含的子图继承表示。 -/
theorem representation_of_edges_subset {M : SetTheory.Structure.{u}} {D : Reflection.Data M.Domain} {Tab n A B g : M.Domain}
    (h : Representation M D Tab n A g) (hB : Diagram M D n B)
    (hSub : ∀ k q p c, EdgeAt M D B k q p c → EdgeAt M D A k q p c) : Representation M D Tab n B g :=
  ⟨hB,h.labeling,fun k hk q hq p hp c hc hEdge => h.edges k hk q hq p hp c hc (hSub k q p c hEdge)⟩

/-- 非空宽度的末标签存在；若全部标签<beta，则末标签<beta。 -/
theorem last_value_below_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : Reflection.Data M.Domain} (hD : D.Valid M) {zero n g beta : M.Domain} (hZero : ∀ x, ¬M.mem x zero)
    (hg : Labeling M D n g) (hn : n≠zero) (hBelow : Below M D n g beta) :
    ∃ b, M.mem b beta ∧ LastValue M zero n g b := by
  rcases natural_cases hM hD.omega hg.length with hEmpty | ⟨l,_,hSucc⟩
  · exact False.elim (hn (hM.1.eq_of_same_members n zero (fun x => iff_of_false (hEmpty x) (hZero x))))
  · obtain ⟨b,hb,hAt⟩ := hg.graph.total l hSucc.predecessor_mem
    exact ⟨b,hBelow l hSucc.predecessor_mem b hb hAt,Or.inr ⟨l,hSucc.predecessor_mem,hSucc,hAt⟩⟩

/-- 删除末项/无坏根分支：A(t)是A(s)在last以下的实际限制，限制表示的末标签严格小于beta。 -/
theorem drop_branch_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {E : ExpressionData M.Domain} (hE : E.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M E)
    {D : Reflection.Data M.Domain} (hD : D.Valid M) (hOmega : D.omega=E.omega)
    {Tab s m last t A n B f beta : M.Domain} (hA : ExpressionGraph M E T D s m A) (hSucc : M.SuccessorOf m last)
    (hPrefix : Prefix M t s last E.omega) (hRep : Representation M D Tab m A f) (hLast : MemPair M f last beta)
    (hB : ExpressionGraph M E T D t n B) (ht : t≠E.zero) :
    ∃ g b, Representation M D Tab n B g ∧ LastValue M E.zero n g b ∧ M.mem b beta := by
  have he := hM.1
  have hw := omega_isOrdinal_d hM hE.omega
  have hm : M.mem m E.omega := hA.1.1.1
  have hl : M.mem last E.omega := hw.transitive m hm last hSucc.predecessor_mem
  have hLastSub : M.MemberSubset last m := fun i hi => (hSucc i).mpr (Or.inl hi)
  have hLegalT := prefix_legal_d hM hE hA.1 hl hLastSub hPrefix
  have hnl := legal_length_unique he hB.1 hLegalT
  subst n
  have hValues : RowsAgreeOn M s t last := fun c hc v => (hPrefix.all_rows he hA.1.1.2 c hc v).symm
  have hRestrict := hA.prefix_restriction_d hM hE hT hD hOmega hB hLastSub hValues
  obtain ⟨g,hg,hRepB⟩ := hRestrict.representation_exists_d hM hD (hB.diagram_d hM hE hT hD hOmega) hRep
  have hn0 : last≠E.zero := fun h => ht ((legal_zero_length_iff_d hM hE hB.1).mp h)
  have hBelow : Below M D last g beta := by
    intro i hi x hx hix
    exact hRep.labeling.increasing i (hLastSub i hi) last hSucc.predecessor_mem hi x hx beta
      (hRep.labeling.graph.bounds he hLast).2 ((hg.rows i hi x hx).mp hix) hLast
  obtain ⟨b,hb,hLastB⟩ := last_value_below_d hM hD hE.zero_empty hRepB.labeling hn0 hBelow
  exact ⟨g,b,hRepB,hLastB,hb⟩

/-- 坏根分支：Y04b在Width(N)给出全部标签<beta的复制图表示，再由Y05b边包含限制到A(t)。 -/
theorem bad_branch_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (hCanonical : CanonicalCopyBoundIn M)
    {E : ExpressionData M.Domain} (hE : E.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M E)
    {D : Reflection.Data M.Domain} (hD : D.Valid M) (hOmega : D.omega=E.omega) {Tab : M.Domain} (hTable : Table M D Tab)
    {s m last N t A n B f beta : M.Domain} {W : Expansion.SuccessData M.Domain} (hN : M.mem N E.omega)
    (hSuccess : Expansion.Successful M E T s m last N t W) (hSucc : M.SuccessorOf m last) (hA : ExpressionGraph M E T D s m A)
    (hRep : Representation M D Tab m A f) (hLast : MemPair M f last beta)
    (hB : ExpressionGraph M E T D t n B) (ht : t≠E.zero) :
    ∃ g b, Representation M D Tab n B g ∧ LastValue M E.zero n g b ∧ M.mem b beta := by
  have he := hM.1
  obtain ⟨_,F,P,L,H,hF,hP,hH,hEnum⟩ := hA
  have hFF := linear_forest_unique he hF hSuccess.linear
  subst F
  have hPP := hP.unique he hSuccess.selected
  subst P
  have hLL := Expansion.layer_space_unique he hH.space hSuccess.run.space
  subst L
  have hHH := hH.unique_d hM hE hSuccess.run
  subst H
  have hBad : BadAt M E m W.space W.layers W.K W.level W.coordinates.last W.coordinates.root := by
    rw [hSuccess.last,hSuccess.root]
    exact hSuccess.bad
  have hLastC : MemPair M f W.coordinates.last beta := hSuccess.last ▸ hLast
  obtain ⟨Old,hOld,_,_⟩ := CopyDiagram.tower_diagram_exists_d hM hE hT hD hOmega hSuccess.tower
  obtain ⟨g,_,hRepOld,hBelow⟩ := CopySeams.copy_representation_d hM hE hT hD hOmega hTable hSuccess.coordinates
    hSuccess.run hEnum hBad (hSuccess.horizon.natural_d hM hE) hRep hLastC hN hSuccess.width hSuccess.tower hOld
  have hSub := hCanonical E T D hE hT hD hOmega s m last N t W hSuccess hSucc Old hOld n B hB
  have hnW := legal_length_unique he hB.1 (hSuccess.legal_d hM hE hT)
  subst n
  have hRepB := representation_of_edges_subset hRepOld (hB.diagram_d hM hE hT hD hOmega) hSub
  have hn0 : W.width≠E.zero := fun h => ht ((legal_zero_length_iff_d hM hE hB.1).mp h)
  obtain ⟨b,hb,hLastB⟩ := last_value_below_d hM hD hE.zero_empty hRepB.labeling hn0 hBelow
  exact ⟨g,b,hRepB,hLastB,hb⟩

/-- Lemma 3（对象形式，任意实际R表）：非空s的A(s)有末标签beta的表示，任意内部N的非空展开t
的A(t)有末标签<beta的表示。覆盖空输入（矛盾）、末值1删除、坏根复制三支。 -/
theorem expand_last_representation_lower_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (hCanonical : CanonicalCopyBoundIn M)
    {E : ExpressionData M.Domain} (hE : E.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M E)
    {D : Reflection.Data M.Domain} (hD : D.Valid M) (hOmega : D.omega=E.omega) {Tab : M.Domain} (hTable : Table M D Tab)
    {s m A f beta N t n B : M.Domain} (hA : ExpressionGraph M E T D s m A) (hs : s≠E.zero)
    (hRep : Representation M D Tab m A f) (hLastValue : LastValue M E.zero m f beta)
    (hExpand : Expansion.Expands M E T s N t) (ht : t≠E.zero) (hB : ExpressionGraph M E T D t n B) :
    ∃ g b, Representation M D Tab n B g ∧ LastValue M E.zero n g b ∧ M.mem b beta := by
  have he := hM.1
  have hw := omega_isOrdinal_d hM hE.omega
  obtain ⟨hN,m₀,_,hLegal₀,hCases⟩ := hExpand
  have hmm := legal_length_unique he hLegal₀ hA.1
  subst m₀
  have hm0 : m≠E.zero := fun h => hs ((legal_zero_length_iff_d hM hE hA.1).mp h)
  rcases hLastValue with ⟨hm,_⟩ | ⟨last,_,hSucc,hLast⟩
  · exact False.elim (hm0 hm)
  rcases hCases with ⟨hm,_⟩ | ⟨last₀,hl₀,hSucc₀,hDrop | ⟨W,hSuccess⟩⟩
  · exact False.elim (hm0 hm)
  · have hll := Structure.SuccessorOf.predecessor_eq he (hw.mem hl₀) hSucc₀ hSucc
    subst last₀
    exact drop_branch_d hM hE hT hD hOmega hA hSucc hDrop.2 hRep hLast hB ht
  · have hll := Structure.SuccessorOf.predecessor_eq he (hw.mem hl₀) hSucc₀ hSucc
    subst last₀
    exact bad_branch_d hM hCanonical hE hT hD hOmega hTable hN hSuccess hSucc hA hRep hLast hB ht

/-- 交付Lane D所需的精确语句`CopyDescentStatement`；唯一未解除前提是Y05b的`CanonicalCopyBound`。 -/
theorem copy_descent_of_canonical (hCanonical : CanonicalCopyBound.{u}) : KP1Y.OneYRank.CopyDescentStatement.{u} := by
  intro M hM C E T hC _ hE hOmega hT s m A β _ hs hA _ hReal N _ t hExpand ht m' A' hA'
  have hD := hC.reflection
  have hOmega' : C.reflection.omega=E.omega := hOmega.symm
  have hZero := KP1Y.OneYRank.expression_article_zero_eq hM.1 hE hC
  obtain ⟨f,_,hRep,hLast⟩ := hReal
  rw [← hZero] at hLast
  obtain ⟨g,b,hRepB,hLastB,hb⟩ := expand_last_representation_lower_d hM (hCanonical M hM) hE hT hD hOmega' hC.table
    hA hs hRep hLast hExpand ht hA'
  rw [hZero] at hLastB
  exact ⟨b,hb,g,hRepB.labeling.sequence hD,hRepB,hLastB⟩

end KP1Y.OneYFinite.CopyDescent
