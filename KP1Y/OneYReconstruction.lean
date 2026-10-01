import KP1Y.OneYForestSelection
import KP1Y.OneYNaturalAdditionTable

/-! 通用有限数值重建。先按顶部高度构造列内逆向累计和，再供按列递归使用。
父图是否为某次数值山形的重新提取结果不是此模块的输入。
-/
namespace KP1Y.OneYFinite.Reconstruction
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite
universe u

private theorem successor_nat {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {w a b : M.Domain} (hw : M.IsOmega w) (ha : M.mem a w) (hs : M.SuccessorOf b a) : M.mem b w := by
  obtain ⟨b',hs',hb'⟩ := hw.1.2 a ha
  exact Structure.SuccessorOf.eq hM.1 hs hs' ▸ hb'

private theorem successor_inside {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {w h n r s : M.Domain} (hw : M.IsOmega w) (hh : M.mem h w)
    (hn : M.SuccessorOf n h) (hr : M.mem r h) (hs : M.SuccessorOf s r) : M.mem s n := by
  have hwOrd := omega_isOrdinal_d hM hw
  have hrw := hwOrd.transitive h hh r hr
  have hsw := successor_nat hM hw hrw hs
  have hSub : M.MemberSubset s h := by
    intro x hx
    rcases (hs x).mp hx with hxr | hxr
    · exact (hwOrd.mem hh).transitive r hr x hxr
    · exact hM.1.eq_of_same_members x r hxr ▸ hr
  rcases ordinal_subset_cases_d hM (hwOrd.mem hsw) (hwOrd.mem hh) hSub with he | hsh
  · exact he.symm ▸ hn.predecessor_mem
  · exact (hn s).mpr (Or.inl hsh)

/-- 贡献图 K 已给出每一行的父项贡献；列顶高度为 h，长度为 h+1。 -/
structure ColumnSum (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain)
    (Pairs Plus K h top len f : M.Domain) : Prop where
  height : M.mem h C.omega
  length : M.SuccessorOf len h
  graph : Graph M f len C.omega
  top : MemPair M f h top
  step : ∀ r, M.mem r h → ∀ s, M.mem s len → ∀ u, M.mem u C.omega →
    ∀ v, M.mem v C.omega → ∀ b, M.mem b C.omega → M.SuccessorOf s r →
      MemPair M f r u → MemPair M f s v → MemPair M K r b → AddAt M Pairs Plus v b u

def columnSumFormula {n : Nat} (C : ExpressionData (Project.Term n))
    (Pairs Plus K h top len f : Project.Term n) : Project.Formula 1 n :=
  .conj (.mem h C.omega) (.conj (successorFormula len h) (.conj (graphFormula f len C.omega)
    (.conj (memPairFormula f h top)
      (Project.Formula.forallMem h (Project.Formula.forallMem len.weaken
        (Project.Formula.forallMem C.omega.weaken.weaken (Project.Formula.forallMem C.omega.weaken.weaken.weaken
          (Project.Formula.forallMem C.omega.weaken.weaken.weaken.weaken
            (.imp (successorFormula (.bound 3) (.bound 4))
              (.imp (memPairFormula f.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 2))
                (.imp (memPairFormula f.weaken.weaken.weaken.weaken.weaken (.bound 3) (.bound 1))
                  (.imp (memPairFormula K.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 0))
                    (addAtFormula Pairs.weaken.weaken.weaken.weaken.weaken Plus.weaken.weaken.weaken.weaken.weaken
                      (.bound 1) (.bound 0) (.bound 2))))))))))))))

theorem columnSumFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n))
    (Pairs Plus K h top len f : Project.Term n) : (columnSumFormula C Pairs Plus K h top len f).IsDelta0 :=
  .conj (.mem _ _) (.conj (successorFormula_delta0 _ _) (.conj (graphFormula_delta0 _ _ _)
    (.conj (memPairFormula_delta0 _ _ _) (.forallMem _ (.forallMem _ (.forallMem _ (.forallMem _ (.forallMem _
      (.imp (successorFormula_delta0 _ _) (.imp (memPairFormula_delta0 _ _ _) (.imp (memPairFormula_delta0 _ _ _)
        (.imp (memPairFormula_delta0 _ _ _) (addAtFormula_delta0 _ _ _ _ _)))))))))))))

theorem columnSumFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    (Pairs Plus K h top len f : Project.Term n) (hPairs : Pairs.freeSupport=[]) (hPlus : Plus.freeSupport=[])
    (hK : K.freeSupport=[]) (hh : h.freeSupport=[]) (hTop : top.freeSupport=[])
    (hLen : len.freeSupport=[]) (hf : f.freeSupport=[]) : (columnSumFormula C Pairs Plus K h top len f).FreeClosed := by
  simp [columnSumFormula,graphFormula,successorFormula,memPairFormula,codeFormula,pairFormula,addAtFormula,
    Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,
    hC.omega,hPairs,hPlus,hK,hh,hTop,hLen,hf]

theorem columnSumFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (C : ExpressionData (Project.Term n)) (Pairs Plus K h top len f : Project.Term n) :
    Project.Formula.satisfies e (columnSumFormula C Pairs Plus K h top len f) ↔
      ColumnSum M (C.eval e) (Pairs.eval e) (Plus.eval e) (K.eval e) (h.eval e) (top.eval e) (len.eval e) (f.eval e) := by
  simp only [columnSumFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    successorFormula_iff he,graphFormula_iff he,memPairFormula_iff he,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,addAtFormula_iff he,Term.eval_weaken]
  exact ⟨fun h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩,
    fun h => ⟨h.height,h.length,h.graph,h.top,h.step⟩⟩

theorem ColumnSum.length_nat_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus K h top len f : M.Domain}
    (hCol : ColumnSum M C Pairs Plus K h top len f) : M.mem len C.omega :=
  successor_nat hM hC.omega hCol.height hCol.length

theorem ColumnSum.extend_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus K h h' top bottom b len f : M.Domain}
    (hK : Graph M K C.omega C.omega) (hCol : ColumnSum M C Pairs Plus K h bottom len f)
    (hs : M.SuccessorOf h' h) (ht : M.mem top C.omega) (hAt : MemPair M K h b)
    (hAdd : AddAt M Pairs Plus top b bottom) :
    ∃ len' g, ColumnSum M C Pairs Plus K h' top len' g := by
  have hLen := Structure.SuccessorOf.eq hM.1 hCol.length hs
  subst len
  have hh' := successor_nat hM hC.omega hCol.height hs
  obtain ⟨len',hLen',_⟩ := hC.omega.1.2 h' hh'
  obtain ⟨g,hG,hRows⟩ := append_graph_d hM hCol.graph hLen' (fun _ h => h) ht
  have hOld (r : M.Domain) (hr : M.mem r h') (u : M.Domain) : MemPair M g r u ↔ MemPair M f r u := by
    rw [hRows r u]
    exact ⟨fun h => h.elim id (fun he => False.elim
      (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) h' (he.1 ▸ hr))),Or.inl⟩
  have hNewTop : MemPair M g h' top := (hRows h' top).mpr (Or.inr ⟨rfl,rfl⟩)
  refine ⟨len',g,hh',hLen',hG,hNewTop,?_⟩
  intro r hr s _ u hu v hv b' hb' hSucc hru hsv hRb
  rcases (hs r).mp hr with hrh | hrEq
  · have hsOld := successor_inside hM hC.omega hCol.height hs hrh hSucc
    exact hCol.step r hrh s hsOld u hu v hv b' hb' hSucc ((hOld r hr u).mp hru) ((hOld s hsOld v).mp hsv) hRb
  · have hrh := hM.1.eq_of_same_members r h hrEq
    subst r
    have hsh' := Structure.SuccessorOf.eq hM.1 hSucc hs
    subst s
    have huBottom := hG.unique h u bottom hru ((hOld h hs.predecessor_mem bottom).mpr hCol.top)
    have hvTop := hG.unique h' v top hsv hNewTop
    have hb'b := hK.unique h b' b hRb hAt
    subst u
    subst v
    subst b'
    exact hAdd

private def columnEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (K Pairs Plus : M.Domain) : Env M 8 :=
  (((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push K).push Pairs).push Plus

private def columnExistenceSchema : Project.UnarySchema 8 where
  body := Project.Formula.forallMem (.bound 8) (Project.Formula.existsMem (.bound 9)
    (Project.Formula.existsMem (.bound 7)
      (columnSumFormula ⟨.bound 11,.bound 10,.bound 9,.bound 8,.bound 7⟩
        (.bound 5) (.bound 4) (.bound 6) (.bound 3) (.bound 2) (.bound 1) (.bound 0))))
  freeClosed := by
    have hCol := columnSumFormula_freeClosed
      (show (⟨.bound 11,.bound 10,.bound 9,.bound 8,.bound 7⟩ : ExpressionData (Project.Term 12)).Closed from ⟨rfl,rfl,rfl,rfl,rfl⟩)
      (.bound 5) (.bound 4) (.bound 6) (.bound 3) (.bound 2) (.bound 1) (.bound 0) rfl rfl rfl rfl rfl rfl rfl
    simp [Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hCol]

private theorem columnExistenceSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (K Pairs Plus h : M.Domain) :
    Project.Formula.satisfies ((columnEnv C K Pairs Plus).push h) columnExistenceSchema.body ↔
      ∀ top, M.mem top C.omega → ∃ len, M.mem len C.omega ∧ ∃ f, M.mem f C.sequences ∧
        ColumnSum M C Pairs Plus K h top len f := by
  simp only [columnExistenceSchema,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_existsMem_iff,columnSumFormula_iff he]
  rfl

/-- 对内部高度归纳；新顶部 t 通过 t+K(h) 传给较低的列，再实际追加 t。 -/
theorem column_sum_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {K Pairs Plus h top : M.Domain}
    (hK : Graph M K C.omega C.omega) (hPlus : AdditionTable M C Pairs Plus)
    (hh : M.mem h C.omega) (ht : M.mem top C.omega) :
    ∃ len, M.mem len C.omega ∧ ∃ f, M.mem f C.sequences ∧ ColumnSum M C Pairs Plus K h top len f := by
  have hAll := natural_induction_d hM columnExistenceSchema (columnEnv C K Pairs Plus) hC.omega
    (fun z hz => (columnExistenceSchema_iff hM.1 C K Pairs Plus z).mpr (by
      intro top ht
      have hzz := hM.1.eq_of_same_members z C.zero (fun x => iff_of_false (hz x) (hC.zero_empty x))
      subst z
      obtain ⟨f,hF,hRows⟩ := append_graph_d hM (empty_graph (V := C.omega) hC.zero_empty) hC.one_succ (fun _ h => h) ht
      refine ⟨C.one,hC.one_nat,f,(hC.sequences f).mpr ⟨C.one,hC.one_nat,hF⟩,
        hC.zero_nat,hC.one_succ,hF,(hRows C.zero top).mpr (Or.inr ⟨rfl,rfl⟩),?_⟩
      intro r hr
      exact False.elim (hC.zero_empty r hr)))
    (fun h hh ih next hs => (columnExistenceSchema_iff hM.1 C K Pairs Plus next).mpr (by
      intro top ht
      obtain ⟨b,hb,hAt⟩ := hK.total h hh
      obtain ⟨bottom,hBottom,hAdd⟩ := hPlus.add_exists_d hM hC ht hb
      obtain ⟨len,_,f,_,hCol⟩ := (columnExistenceSchema_iff hM.1 C K Pairs Plus h).mp ih bottom hBottom
      obtain ⟨len',g,hG⟩ := hCol.extend_d hM hC hK hs ht hAt hAdd
      have hLen := hG.length_nat_d hM hC
      exact ⟨len',hLen,g,(hC.sequences g).mpr ⟨len',hLen,hG.graph⟩,hG⟩))
  exact (columnExistenceSchema_iff hM.1 C K Pairs Plus h).mp (hAll h hh) top ht

private def agreementSchema : Project.Delta0UnarySchema 3 where
  body := Project.Formula.forallMem (.bound 3) (Project.Formula.forallMem (.bound 4)
    (.imp (.conj (memPairFormula (.bound 4) (.bound 2) (.bound 1)) (memPairFormula (.bound 3) (.bound 2) (.bound 0)))
      (Project.Formula.extensionalEq (.bound 1) (.bound 0))))
  freeClosed := by
    simp [memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := .forallMem _ (.forallMem _ (.imp (.conj (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _)) (.atom _ _ _)))

private theorem agreementSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (w f g r : M.Domain) :
    Project.Formula.satisfies ((((oneEnv w).push f).push g).push r) agreementSchema.body ↔
      ∀ u, M.mem u w → ∀ v, M.mem v w → MemPair M f r u → MemPair M g r v → u=v := by
  simp only [agreementSchema,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,memPairFormula_iff he,Project.Formula.satisfies_extensionalEq_iff_eq he]
  exact ⟨fun h u hu v hv hfu hgv => h u hu v hv ⟨hfu,hgv⟩,fun h u hu v hv hs => h u hu v hv hs.1 hs.2⟩

theorem ColumnSum.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus K h top len len' f g : M.Domain}
    (hK : Graph M K C.omega C.omega) (hPlus : AdditionTable M C Pairs Plus)
    (hF : ColumnSum M C Pairs Plus K h top len f) (hG : ColumnSum M C Pairs Plus K h top len' g) : f=g := by
  have hLengths := Structure.SuccessorOf.eq hM.1 hF.length hG.length
  subst len'
  let env := ((oneEnv C.omega).push f).push g
  have hAll := bounded_backward_induction_d hM agreementSchema env hC.omega hF.height
    ((agreementSchema_iff hM.1 C.omega f g h).mpr (by
      intro u _ v _ hfu hgv
      exact (hF.graph.unique h u top hfu hF.top).trans (hG.graph.unique h v top hgv hG.top).symm))
    (fun r hr s _ hs _ ih => (agreementSchema_iff hM.1 C.omega f g r).mpr (by
      intro u hu v hv hru hrv
      have hsLen := successor_inside hM hC.omega hF.height hF.length hr hs
      obtain ⟨x,hx,hsx⟩ := hF.graph.total s hsLen
      obtain ⟨y,hy,hsy⟩ := hG.graph.total s hsLen
      have hxy := (agreementSchema_iff hM.1 C.omega f g s).mp ih x hx y hy hsx hsy
      subst y
      have hrw := (omega_isOrdinal_d hM hC.omega).transitive h hF.height r hr
      obtain ⟨b,hb,hrb⟩ := hK.total r hrw
      exact hPlus.add_unique hM.1 (hF.step r hr s hsLen u hu x hx b hb hs hru hsx hrb)
        (hG.step r hr s hsLen v hv x hy b hb hs hrv hsy hrb)))
  apply hF.graph.ext hM.1 hG.graph
  intro r hr u
  have hrLe : r=h ∨ M.mem r h := by
    rcases (hF.length r).mp hr with hr | he
    · exact Or.inr hr
    · exact Or.inl (hM.1.eq_of_same_members r h he)
  have hAgree := (agreementSchema_iff hM.1 C.omega f g r).mp (hAll r hrLe)
  constructor
  · intro hru
    obtain ⟨v,hv,hrv⟩ := hG.graph.total r hr
    have huv := hAgree u (hF.graph.bounds hM.1 hru).2 v hv hru hrv
    exact huv.symm ▸ hrv
  · intro hru
    obtain ⟨v,hv,hrv⟩ := hF.graph.total r hr
    exact hAgree v hv u (hG.graph.bounds hM.1 hru).2 hrv hru ▸ hrv

theorem ColumnSum.contributions_congr {M : SetTheory.Structure.{u}}
    {C : ExpressionData M.Domain} {Pairs Plus K J h top len f : M.Domain}
    (hF : ColumnSum M C Pairs Plus K h top len f) (hRows : RowsAgreeOn M K J h) :
    ColumnSum M C Pairs Plus J h top len f := by
  refine ⟨hF.height,hF.length,hF.graph,hF.top,?_⟩
  intro r hr s hs u hu v hv b hb hSucc hru hsv hrb
  exact hF.step r hr s hs u hu v hv b hb hSucc hru hsv ((hRows r hr b).mpr hrb)

theorem ColumnSum.unique_of_contributions_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus K J h top len len' f g : M.Domain}
    (hK : Graph M K C.omega C.omega) (hPlus : AdditionTable M C Pairs Plus) (hRows : RowsAgreeOn M K J h)
    (hF : ColumnSum M C Pairs Plus K h top len f) (hG : ColumnSum M C Pairs Plus J h top len' g) : f=g :=
  hF.unique_d hM hC hK hPlus (hG.contributions_congr (fun r hr b => (hRows r hr b).symm))

private def paddingSchema : Project.Delta0BinarySchema 3 where
  body := .disj (memPairFormula (.bound 4) (.bound 1) (.bound 0))
    (.conj (.neg (.mem (.bound 1) (.bound 3))) (Project.Formula.extensionalEq (.bound 0) (.bound 2)))
  freeClosed := by
    simp [memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := .disj (memPairFormula_delta0 _ _ _) (.conj (.neg (.mem _ _)) (.atom _ _ _))

private theorem paddingSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (f len zero r u : M.Domain) :
    Project.Formula.satisfies (((((oneEnv f).push len).push zero).push r).push u) paddingSchema.body ↔
      MemPair M f r u ∨ (¬M.mem r len ∧ u=zero) := by
  simp only [paddingSchema,Project.Formula.satisfies_disj_iff,memPairFormula_iff he,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_extensionalEq_iff_eq he]
  rfl

theorem pad_zero_graph_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {f len B : M.Domain}
    (hF : Graph M f len C.omega) :
    ∃ g, Graph M g B C.omega ∧ ∀ r u, MemPair M g r u ↔
      M.mem r B ∧ (MemPair M f r u ∨ (¬M.mem r len ∧ u=C.zero)) := by
  obtain ⟨g,hSupport,hG⟩ := relation_comprehension_d hM paddingSchema (((oneEnv f).push len).push C.zero) B C.omega
  have hRows : ∀ r u, MemPair M g r u ↔ M.mem r B ∧ (MemPair M f r u ∨ (¬M.mem r len ∧ u=C.zero)) := by
    intro r u
    rw [hG r u,paddingSchema_iff hM.1]
    refine ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,?_,h.2⟩⟩
    rcases h.2 with hru | ⟨_,he⟩
    · exact (hF.bounds hM.1 hru).2
    · exact he ▸ hC.zero_nat
  refine ⟨g,⟨hSupport,?_,?_⟩,hRows⟩
  · intro r hr
    by_cases hrLen : M.mem r len
    · obtain ⟨u,hu,hru⟩ := hF.total r hrLen
      exact ⟨u,hu,(hRows r u).mpr ⟨hr,Or.inl hru⟩⟩
    · exact ⟨C.zero,hC.zero_nat,(hRows r C.zero).mpr ⟨hr,Or.inr ⟨hrLen,rfl⟩⟩⟩
  · intro r u v hru hrv
    rcases ((hRows r u).mp hru).2 with hru | ⟨hNot,hu⟩ <;>
      rcases ((hRows r v).mp hrv).2 with hrv | ⟨hNot',hv⟩
    · exact hF.unique r u v hru hrv
    · exact False.elim (hNot' (hF.bounds hM.1 hru).1)
    · exact False.elim (hNot (hF.bounds hM.1 hrv).1)
    · exact hu.trans hv.symm

structure FilledColumn (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain)
    (Pairs Plus K B h top f : M.Domain) : Prop where
  rows : M.mem B C.omega
  height : M.mem h B
  graph : Graph M f B C.omega
  top : MemPair M f h top
  absent : ∀ r, M.mem r B → ∀ u, MemPair M f r u → M.mem h r → u=C.zero
  step : ∀ r, M.mem r h → ∀ s, M.mem s B → ∀ u, M.mem u C.omega →
    ∀ v, M.mem v C.omega → ∀ b, M.mem b C.omega → M.SuccessorOf s r →
      MemPair M f r u → MemPair M f s v → MemPair M K r b → AddAt M Pairs Plus v b u

def filledColumnFormula {n : Nat} (C : ExpressionData (Project.Term n))
    (Pairs Plus K B h top f : Project.Term n) : Project.Formula 1 n :=
  .conj (.mem B C.omega) (.conj (.mem h B) (.conj (graphFormula f B C.omega)
    (.conj (memPairFormula f h top)
      (.conj (Project.Formula.forallMem B (Project.Formula.forallMem C.omega.weaken
        (.imp (memPairFormula f.weaken.weaken (.bound 1) (.bound 0))
          (.imp (.mem h.weaken.weaken (.bound 1)) (Project.Formula.extensionalEq (.bound 0) C.zero.weaken.weaken)))))
        (Project.Formula.forallMem h (Project.Formula.forallMem B.weaken
          (Project.Formula.forallMem C.omega.weaken.weaken (Project.Formula.forallMem C.omega.weaken.weaken.weaken
            (Project.Formula.forallMem C.omega.weaken.weaken.weaken.weaken
              (.imp (successorFormula (.bound 3) (.bound 4))
                (.imp (memPairFormula f.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 2))
                  (.imp (memPairFormula f.weaken.weaken.weaken.weaken.weaken (.bound 3) (.bound 1))
                    (.imp (memPairFormula K.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 0))
                      (addAtFormula Pairs.weaken.weaken.weaken.weaken.weaken Plus.weaken.weaken.weaken.weaken.weaken
                        (.bound 1) (.bound 0) (.bound 2)))))))))))))))

theorem filledColumnFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n))
    (Pairs Plus K B h top f : Project.Term n) : (filledColumnFormula C Pairs Plus K B h top f).IsDelta0 :=
  .conj (.mem _ _) (.conj (.mem _ _) (.conj (graphFormula_delta0 _ _ _) (.conj (memPairFormula_delta0 _ _ _)
    (.conj (.forallMem _ (.forallMem _ (.imp (memPairFormula_delta0 _ _ _) (.imp (.mem _ _) (.atom _ _ _)))))
      (.forallMem _ (.forallMem _ (.forallMem _ (.forallMem _ (.forallMem _
        (.imp (successorFormula_delta0 _ _) (.imp (memPairFormula_delta0 _ _ _) (.imp (memPairFormula_delta0 _ _ _)
          (.imp (memPairFormula_delta0 _ _ _) (addAtFormula_delta0 _ _ _ _ _))))))))))))))

theorem filledColumnFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    (Pairs Plus K B h top f : Project.Term n) (hPairs : Pairs.freeSupport=[]) (hPlus : Plus.freeSupport=[])
    (hK : K.freeSupport=[]) (hB : B.freeSupport=[]) (hh : h.freeSupport=[])
    (hTop : top.freeSupport=[]) (hf : f.freeSupport=[]) : (filledColumnFormula C Pairs Plus K B h top f).FreeClosed := by
  simp [filledColumnFormula,graphFormula,successorFormula,memPairFormula,codeFormula,pairFormula,addAtFormula,
    Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,
    hC.omega,hC.zero,hPairs,hPlus,hK,hB,hh,hTop,hf]

theorem filledColumnFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (C : ExpressionData (Project.Term n)) (Pairs Plus K B h top f : Project.Term n) :
    Project.Formula.satisfies e (filledColumnFormula C Pairs Plus K B h top f) ↔
      FilledColumn M (C.eval e) (Pairs.eval e) (Plus.eval e) (K.eval e) (B.eval e) (h.eval e) (top.eval e) (f.eval e) := by
  simp only [filledColumnFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    graphFormula_iff he,memPairFormula_iff he,Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,
    successorFormula_iff he,addAtFormula_iff he,Term.eval_weaken]
  constructor
  · rintro ⟨hRows,hHeight,hGraph,hTop,hAbsent,hStep⟩
    exact ⟨hRows,hHeight,hGraph,hTop,
      fun r hr u hru hhr => hAbsent r hr u (hGraph.bounds he hru).2 hru hhr,hStep⟩
  · intro hF
    exact ⟨hF.rows,hF.height,hF.graph,hF.top,fun r hr u _ hru hhr => hF.absent r hr u hru hhr,hF.step⟩

theorem filled_column_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus K B h top : M.Domain}
    (hK : Graph M K C.omega C.omega) (hPlus : AdditionTable M C Pairs Plus)
    (hB : M.mem B C.omega) (hh : M.mem h B) (ht : M.mem top C.omega) :
    ∃ f, FilledColumn M C Pairs Plus K B h top f := by
  have hwOrd := omega_isOrdinal_d hM hC.omega
  have hhw := hwOrd.transitive B hB h hh
  obtain ⟨len,_,f,_,hCol⟩ := column_sum_exists_d hM hC hK hPlus hhw ht
  have hSub : M.MemberSubset len B := by
    intro r hr
    rcases (hCol.length r).mp hr with hr | he
    · exact (hwOrd.mem hB).transitive h hh r hr
    · exact hM.1.eq_of_same_members r h he ▸ hh
  obtain ⟨g,hG,hRows⟩ := pad_zero_graph_d (B := B) hM hC hCol.graph
  have hOld (r : M.Domain) (hr : M.mem r len) (u : M.Domain) : MemPair M g r u ↔ MemPair M f r u := by
    rw [hRows r u]
    exact ⟨fun h => h.2.elim id (fun h' => False.elim (h'.1 hr)),fun h => ⟨hSub r hr,Or.inl h⟩⟩
  refine ⟨g,hB,hh,hG,(hOld h hCol.length.predecessor_mem top).mpr hCol.top,?_,?_⟩
  · intro r _ u hru hhr
    have hrNot : ¬M.mem r len := by
      intro hr
      rcases (hCol.length r).mp hr with hrh | hrh
      · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) h ((hwOrd.mem hhw).transitive r hrh h hhr)
      · have he := hM.1.eq_of_same_members r h hrh
        exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) h (he ▸ hhr)
    rcases ((hRows r u).mp hru).2 with hfu | ⟨_,hu⟩
    · exact False.elim (hrNot (hCol.graph.bounds hM.1 hfu).1)
    · exact hu
  · intro r hr s _ u hu v hv b hb hs hru hsv hrb
    have hrLen := (hCol.length r).mpr (Or.inl hr)
    have hsLen := successor_inside hM hC.omega hCol.height hCol.length hr hs
    exact hCol.step r hr s hsLen u hu v hv b hb hs ((hOld r hrLen u).mp hru) ((hOld s hsLen v).mp hsv) hrb

theorem FilledColumn.lower_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus K B h top f : M.Domain}
    (hF : FilledColumn M C Pairs Plus K B h top f) :
    ∃ len g, ColumnSum M C Pairs Plus K h top len g ∧ Prefix M g f len C.omega := by
  have hwOrd := omega_isOrdinal_d hM hC.omega
  have hhw := hwOrd.transitive B hF.rows h hF.height
  obtain ⟨len,hLen,_⟩ := hC.omega.1.2 h hhw
  have hSub : M.MemberSubset len B := by
    intro r hr
    rcases (hLen r).mp hr with hrh | hrh
    · exact (hwOrd.mem hF.rows).transitive h hF.height r hrh
    · exact hM.1.eq_of_same_members r h hrh ▸ hF.height
  obtain ⟨g,hG⟩ := restrict_prefix_d hM hF.graph hSub
  refine ⟨len,g,⟨hhw,hLen,hG.graph,
    (hG.all_rows hM.1 hF.graph h hLen.predecessor_mem top).mpr hF.top,?_⟩,hG⟩
  intro r hr s hs u hu v hv b hb hSucc hru hsv hrb
  exact hF.step r hr s (hSub s hs) u hu v hv b hb hSucc
    ((hG.all_rows hM.1 hF.graph r ((hLen r).mpr (Or.inl hr)) u).mp hru)
    ((hG.all_rows hM.1 hF.graph s hs v).mp hsv) hrb

theorem FilledColumn.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus K B h top f g : M.Domain}
    (hK : Graph M K C.omega C.omega) (hPlus : AdditionTable M C Pairs Plus)
    (hF : FilledColumn M C Pairs Plus K B h top f) (hG : FilledColumn M C Pairs Plus K B h top g) : f=g := by
  obtain ⟨len,f',hF',hPrefF⟩ := hF.lower_d hM hC
  obtain ⟨len',g',hG',hPrefG⟩ := hG.lower_d hM hC
  have hLen := Structure.SuccessorOf.eq hM.1 hF'.length hG'.length
  subst len'
  have hfg := hF'.unique_d hM hC hK hPlus hG'
  subst g'
  apply hF.graph.ext hM.1 hG.graph
  intro r hr u
  rcases ((omega_isOrdinal_d hM hC.omega).mem hF.rows).wellOrder.linear.compare r hr h hF.height with he | hrh | hhr
  · have hrEq := hM.1.eq_of_same_members r h he
    subst r
    constructor
    · intro hru
      exact (hF.graph.unique h u top hru hF.top).symm ▸ hG.top
    · intro hru
      exact (hG.graph.unique h u top hru hG.top).symm ▸ hF.top
  · have hrLen := (hF'.length r).mpr (Or.inl hrh)
    exact (hPrefF.all_rows hM.1 hF.graph r hrLen u).symm.trans (hPrefG.all_rows hM.1 hG.graph r hrLen u)
  · constructor
    · intro hru
      obtain ⟨v,_,hrv⟩ := hG.graph.total r hr
      have hu := hF.absent r hr u hru hhr
      have hv := hG.absent r hr v hrv hhr
      exact (hu.trans hv.symm).symm ▸ hrv
    · intro hru
      obtain ⟨v,_,hrv⟩ := hF.graph.total r hr
      have hu := hG.absent r hr u hru hhr
      have hv := hF.absent r hr v hrv hhr
      exact (hu.trans hv.symm).symm ▸ hrv

private def lowerBoundSchema : Project.Delta0UnarySchema 3 where
  body := Project.Formula.forallMem (.bound 3)
    (.imp (memPairFormula (.bound 3) (.bound 1) (.bound 0)) (Project.Formula.subset (.bound 2) (.bound 0)))
  freeClosed := by
    simp [memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := .forallMem _ (.imp (memPairFormula_delta0 _ _ _) (.atom _ _ _))

private theorem lowerBoundSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (w f top r : M.Domain) :
    Project.Formula.satisfies ((((oneEnv w).push f).push top).push r) lowerBoundSchema.body ↔
      ∀ u, M.mem u w → MemPair M f r u → M.MemberSubset top u := by
  simp only [lowerBoundSchema,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    memPairFormula_iff he,Project.Formula.satisfies_subset_iff]
  rfl

theorem ColumnSum.top_subset_value_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus K h top len f r u : M.Domain}
    (hK : Graph M K C.omega C.omega) (hPlus : AdditionTable M C Pairs Plus)
    (hF : ColumnSum M C Pairs Plus K h top len f) (hru : MemPair M f r u) : M.MemberSubset top u := by
  let env := ((oneEnv C.omega).push f).push top
  have hAll := bounded_backward_induction_d hM lowerBoundSchema env hC.omega hF.height
    ((lowerBoundSchema_iff hM.1 C.omega f top h).mpr (by
      intro u _ hhu
      have he := hF.graph.unique h u top hhu hF.top
      subst u
      exact fun _ h => h))
    (fun r hr s _ hs _ ih => (lowerBoundSchema_iff hM.1 C.omega f top r).mpr (by
      intro u hu hru
      have hsLen := successor_inside hM hC.omega hF.height hF.length hr hs
      obtain ⟨v,hv,hsv⟩ := hF.graph.total s hsLen
      obtain ⟨b,hb,hrb⟩ := hK.total r ((omega_isOrdinal_d hM hC.omega).transitive h hF.height r hr)
      have hSub := (lowerBoundSchema_iff hM.1 C.omega f top s).mp ih v hv hsv
      have hAdd := hF.step r hr s hsLen u hu v hv b hb hs hru hsv hrb
      have hSum := (hPlus.add_iff_sum hM hv hb).mp hAdd
      have hvu := KP1Y.Arithmetic.sum_base_subset_d hM ((omega_isOrdinal_d hM hC.omega).mem hv) hSum
      exact fun x hx => hvu x (hSub x hx)))
  have hrLe : r=h ∨ M.mem r h := by
    rcases (hF.length r).mp (hF.graph.bounds hM.1 hru).1 with hr | he
    · exact Or.inr hr
    · exact Or.inl (hM.1.eq_of_same_members r h he)
  exact (lowerBoundSchema_iff hM.1 C.omega f top r).mp (hAll r hrLe) u (hF.graph.bounds hM.1 hru).2 hru

theorem FilledColumn.top_subset_live_value_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus K B h top f r u : M.Domain}
    (hK : Graph M K C.omega C.omega) (hPlus : AdditionTable M C Pairs Plus)
    (hF : FilledColumn M C Pairs Plus K B h top f) (hr : r=h ∨ M.mem r h)
    (hru : MemPair M f r u) : M.MemberSubset top u := by
  obtain ⟨len,g,hG,hPref⟩ := hF.lower_d hM hC
  have hrLen : M.mem r len := by
    rcases hr with he | hr
    · exact he.symm ▸ hG.length.predecessor_mem
    · exact (hG.length r).mpr (Or.inl hr)
  exact hG.top_subset_value_d hM hC hK hPlus ((hPref.all_rows hM.1 hF.graph r hrLen u).mpr hru)

theorem FilledColumn.live_positive_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus K B h top f r u : M.Domain}
    (hK : Graph M K C.omega C.omega) (hPlus : AdditionTable M C Pairs Plus)
    (hF : FilledColumn M C Pairs Plus K B h top f) (hTop : M.mem C.zero top)
    (hr : r=h ∨ M.mem r h) (hru : MemPair M f r u) : M.mem C.zero u :=
  hF.top_subset_live_value_d hM hC hK hPlus hr hru C.zero hTop

end KP1Y.OneYFinite.Reconstruction
