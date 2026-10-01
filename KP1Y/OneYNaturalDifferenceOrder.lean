import KP1Y.OneYNaturalDifferenceFacts
import KP1Y.AssignmentFamilyPatch

/-! 截断差的内部序关系；以实际前驱迭代器及对象自然数归纳证明。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments KP1Y.Naturals
universe u

theorem natural_successor_mem_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a a' : M.Domain}
    (ha : M.mem a C.omega) (hs : M.SuccessorOf a' a) : M.mem a' C.omega := by
  obtain ⟨b,hb,hbω⟩ := hC.omega.1.2 a ha
  exact (Structure.SuccessorOf.eq hM.1 hs hb) ▸ hbω

theorem natural_successor_lt_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b a' b' : M.Domain}
    (ha : M.mem a C.omega) (hb : M.mem b C.omega) (hA : M.SuccessorOf a' a) (hB : M.SuccessorOf b' b) :
    M.mem b' a' ↔ M.mem b a := by
  have hOrd := omega_isOrdinal_d hM hC.omega
  have hOA := hOrd.mem ha
  constructor
  · intro h
    rcases (hA b').mp h with hba | hEq
    · exact hOA.transitive b' hba b hB.predecessor_mem
    · exact (hM.1.eq_of_same_members b' a hEq) ▸ hB.predecessor_mem
  · intro hba
    have hSub : M.MemberSubset b' a := by
      intro x hx
      rcases (hB x).mp hx with hxb | hEq
      · exact hOA.transitive b hba x hxb
      · exact (hM.1.eq_of_same_members x b hEq) ▸ hba
    rcases ordinal_subset_cases_d hM (hOrd.mem (natural_successor_mem_d hM hC hb hB)) hOA hSub with hEq | hb'a
    · subst b'
      exact hA.predecessor_mem
    · exact (hA b').mpr (Or.inl hb'a)

theorem truncated_difference_natural {M : SetTheory.Structure.{u}} (he : Extensional M)
    {w z a b d : M.Domain} (h : TruncatedDifference M w z a b d) : M.mem d w := by
  obtain ⟨_,_,H,hH,hAt⟩ := h
  exact (hH.1.bounds he hAt).2

theorem predecessor_iterator_tail_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a a' H : M.Domain}
    (ha : M.mem a C.omega) (hA : M.SuccessorOf a' a) (hH : PredecessorIterator M C.omega C.zero a' H) :
    ∃ T, PredecessorIterator M C.omega C.zero a T ∧
      ∀ b, M.mem b C.omega → ∀ b', M.mem b' C.omega → M.SuccessorOf b' b →
        ∀ d, M.mem d C.omega → (MemPair M T b d ↔ MemPair M H b' d) := by
  obtain ⟨S,hS,hSRows⟩ := successor_graph_d hM hC.omega
  obtain ⟨T,hT⟩ := tuple_value_exists_d hM hS hH.1
  have hRows (b : M.Domain) (hb : M.mem b C.omega) (b' : M.Domain) (hb' : M.mem b' C.omega)
      (hs : M.SuccessorOf b' b) (d : M.Domain) (hd : M.mem d C.omega) :
      MemPair M T b d ↔ MemPair M H b' d := hT.rows b hb b' hb' d hd ((hSRows b b').mpr ⟨hb,hb',hs⟩)
  refine ⟨T,⟨hT.values,?_,?_⟩,hRows⟩
  · obtain ⟨d,hd,hOne⟩ := hH.1.total C.one hC.one_nat
    have hPred := hH.2.2 C.zero hC.zero_nat C.one hC.one_nat a' (hH.1.bounds hM.1 hH.2.1).2 d hd
      hC.one_succ hH.2.1 hOne
    have hda := previous_length_unique_d hM hC hPred ⟨ha,Or.inr hA⟩
    subst d
    exact (hRows C.zero hC.zero_nat C.one hC.one_nat hC.one_succ a ha).mpr hOne
  · intro i hi j hj x hx y hy hSucc hIx hJy
    obtain ⟨j',hj',hNext⟩ := hS.total j hj
    have hNextSucc := ((hSRows j j').mp hNext).2.2
    exact hH.2.2 j hj j' hj' x hx y hy hNextSucc
      ((hRows i hi j hj hSucc x hx).mp hIx) ((hRows j hj j' hj' hNextSucc y hy).mp hJy)

theorem truncated_difference_cancel_successors_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a a' b b' d e : M.Domain}
    (hA : M.SuccessorOf a' a) (hB : M.SuccessorOf b' b)
    (hUp : TruncatedDifference M C.omega C.zero a' b' d)
    (hDown : TruncatedDifference M C.omega C.zero a b e) : d=e := by
  obtain ⟨_,hb',H,hH,hHd⟩ := hUp
  obtain ⟨ha,hb,J,hJ,hJe⟩ := hDown
  obtain ⟨T,hT,hRows⟩ := predecessor_iterator_tail_d hM hC ha hA hH
  have hTJ := predecessor_iterator_unique_d hM hC hT hJ
  subst T
  exact hJ.1.unique b d e ((hRows b hb b' hb' hB d (hH.1.bounds hM.1 hHd).2).mpr hHd) hJe

theorem truncated_difference_left_zero_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {b d : M.Domain}
    (h : TruncatedDifference M C.omega C.zero C.zero b d) : d=C.zero := by
  obtain ⟨T,hT,hRows⟩ := constant_assignment_d hM C.omega C.omega hC.zero_nat
  have hPred : PredecessorIterator M C.omega C.zero C.zero T := by
    refine ⟨hT,hRows C.zero hC.zero_nat,?_⟩
    intro i hi j hj x _ y _ _ hIx hJy
    have hx := hT.unique i x C.zero hIx (hRows i hi)
    have hy := hT.unique j y C.zero hJy (hRows j hj)
    subst x
    subst y
    exact ⟨hC.zero_nat,Or.inl ⟨rfl,rfl⟩⟩
  obtain ⟨_,hb,H,hH,hHd⟩ := h
  have hHT := predecessor_iterator_unique_d hM hC hH hPred
  subst H
  exact hT.unique b d C.zero hHd (hRows b hb)

private def differenceOrderSchema : Project.UnarySchema 2 where
  body := Project.Formula.forallMem (.bound 2) (Project.Formula.forallMem (.bound 3)
    (.imp (differenceFormula (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0))
      (.conj (.disj (Project.Formula.extensionalEq (.bound 0) (.bound 2)) (.mem (.bound 0) (.bound 2)))
        (.conj (.iff (.mem (.bound 3) (.bound 0)) (.mem (.bound 1) (.bound 2)))
          (.disj (Project.Formula.extensionalEq (.bound 1) (.bound 3))
            (.disj (Project.Formula.extensionalEq (.bound 2) (.bound 3)) (.mem (.bound 0) (.bound 2))))))))
  freeClosed := by
    have hDiff := differenceFormula_freeClosed (n := 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0) rfl rfl rfl rfl rfl
    simp [Project.Formula.forallMem,Definitional.Formula.FreeClosed,hDiff]

private theorem differenceOrderSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (w z a : M.Domain) :
    Project.Formula.satisfies ((((oneEnv w).push z).push a)) differenceOrderSchema.body ↔
      ∀ b, M.mem b w → ∀ d, M.mem d w → TruncatedDifference M w z a b d →
        (d=a ∨ M.mem d a) ∧ (M.mem z d ↔ M.mem b a) ∧ (b=z ∨ a=z ∨ M.mem d a) := by
  simp only [differenceOrderSchema,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    differenceFormula_iff he,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_iff_iff]
  rfl

theorem truncated_difference_order_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b d : M.Domain}
    (hDiff : TruncatedDifference M C.omega C.zero a b d) :
    (d=a ∨ M.mem d a) ∧ (M.mem C.zero d ↔ M.mem b a) ∧ (b=C.zero ∨ a=C.zero ∨ M.mem d a) := by
  have hAll := natural_induction_d hM differenceOrderSchema ((oneEnv C.omega).push C.zero) hC.omega
    (by
      intro z hz
      have hzz := hM.1.eq_of_same_members z C.zero (fun x => iff_of_false (hz x) (hC.zero_empty x))
      subst z
      apply (differenceOrderSchema_iff hM.1 C.omega C.zero C.zero).mpr
      intro b _ d _ hD
      have hd := truncated_difference_left_zero_d hM hC hD
      subst d
      exact ⟨Or.inl rfl,iff_of_false (hC.zero_empty C.zero) (hC.zero_empty b),Or.inr (Or.inl rfl)⟩)
    (by
      intro a ha ih a' hA
      apply (differenceOrderSchema_iff hM.1 C.omega C.zero a').mpr
      intro b hb d hd hD
      rcases natural_cases hM hC.omega hb with hEmpty | ⟨p,hp,hB⟩
      · have hb0 := hM.1.eq_of_same_members b C.zero (fun x => iff_of_false (hEmpty x) (hC.zero_empty x))
        subst b
        have hda := truncated_difference_unique_d hM hC hD
          (truncated_difference_zero_d hM hC (natural_successor_mem_d hM hC ha hA))
        subst d
        exact ⟨Or.inl rfl,Iff.rfl,Or.inl rfl⟩
      · obtain ⟨e,he,hE⟩ := truncated_difference_exists_d hM hC ha hp
        have hde := truncated_difference_cancel_successors_d hM hC hA hB hD hE
        subst e
        obtain ⟨hBound,hPos,_⟩ := (differenceOrderSchema_iff hM.1 C.omega C.zero a).mp ih p hp d hd hE
        have hda' : M.mem d a' := by
          rcases hBound with hEq | hda
          · exact hEq ▸ hA.predecessor_mem
          · exact (hA d).mpr (Or.inl hda)
        exact ⟨Or.inr hda',hPos.trans (natural_successor_lt_iff hM hC ha hp hA hB).symm,Or.inr (Or.inr hda')⟩)
  exact (differenceOrderSchema_iff hM.1 C.omega C.zero a).mp (hAll a hDiff.1) b hDiff.2.1 d
    (truncated_difference_natural hM.1 hDiff) hDiff

theorem truncated_difference_le_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b d : M.Domain}
    (h : TruncatedDifference M C.omega C.zero a b d) : d=a ∨ M.mem d a := (truncated_difference_order_d hM hC h).1

theorem truncated_difference_positive_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b d : M.Domain}
    (h : TruncatedDifference M C.omega C.zero a b d) : M.mem C.zero d ↔ M.mem b a := (truncated_difference_order_d hM hC h).2.1

theorem truncated_difference_strict_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b d : M.Domain}
    (h : TruncatedDifference M C.omega C.zero a b d) (hPos : M.mem C.zero b) (hba : M.mem b a) :
    M.mem C.zero d ∧ M.mem d a := by
  obtain ⟨_,hPositive,hStrict⟩ := truncated_difference_order_d hM hC h
  refine ⟨hPositive.mpr hba,?_⟩
  rcases hStrict with hb | ha | hd
  · exact False.elim (hC.zero_empty C.zero (hb ▸ hPos))
  · exact False.elim (hC.zero_empty b (ha ▸ hba))
  · exact hd

theorem truncated_difference_eq_zero_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b d : M.Domain}
    (h : TruncatedDifference M C.omega C.zero a b d) : d=C.zero ↔ ¬M.mem b a := by
  have hPos := truncated_difference_positive_iff_d hM hC h
  constructor
  · intro hd hba
    exact hC.zero_empty C.zero (hd ▸ hPos.mpr hba)
  · intro hba
    classical
    apply Classical.byContradiction
    intro hd
    exact hba (hPos.mp ((hC.zero_mem_iff hM (truncated_difference_natural hM.1 h)).mpr hd))

theorem truncated_difference_diagonal_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a d : M.Domain}
    (h : TruncatedDifference M C.omega C.zero a a d) : d=C.zero :=
  (truncated_difference_eq_zero_iff_d hM hC h).mpr (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) a)

theorem truncated_difference_successor_of_lt_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b b' d d' : M.Domain}
    (hs : M.SuccessorOf b' b) (hba : M.mem b a)
    (hD : TruncatedDifference M C.omega C.zero a b d) (hD' : TruncatedDifference M C.omega C.zero a b' d') :
    M.SuccessorOf d d' := by
  have hPos := (truncated_difference_positive_iff_d hM hC hD).mpr hba
  rcases (truncated_difference_successor_d hM hC hs hD hD').2 with ⟨hd,_⟩ | hSucc
  · exact False.elim (hC.zero_empty C.zero (hd ▸ hPos))
  · exact hSucc

end KP1Y.OneYFinite
