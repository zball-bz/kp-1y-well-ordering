import KP1Y.OneYCopyNeeds

namespace KP1Y.OneYFinite.CopyNeeds
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite.CopiedMountain
universe u

def needHeightsFormula {n : Nat} (C : ExpressionData (Project.Term n)) (D : Data (Project.Term n))
    (G : Project.Term n) : Project.Formula 1 n :=
  .conj (graphFormula G D.horizon C.omega)
    (Project.Formula.forallMem D.horizon (Project.Formula.forallMem C.omega.weaken
      (.iff (memPairFormula G.weaken.weaken (.bound 1) (.bound 0))
        (Project.Formula.existsMem C.omega.weaken.weaken
          (.conj (boundaryHeightFormula D.weaken.weaken.weaken (.bound 2) (.bound 0))
            (needHeightFormula C.omega.weaken.weaken.weaken D.active.weaken.weaken.weaken
              D.level.weaken.weaken.weaken (.bound 2) (.bound 0) (.bound 1)))))))

theorem needHeightsFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (D : Data (Project.Term n))
    (G : Project.Term n) : (needHeightsFormula C D G).IsDelta0 :=
  .conj (graphFormula_delta0 _ _ _) (.forallMem _ (.forallMem _ (.iff (memPairFormula_delta0 _ _ _)
    (.existsMem _ (.conj (boundaryHeightFormula_delta0 _ _ _) (needHeightFormula_delta0 _ _ _ _ _ _))))))

theorem needHeightsFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {D : Data (Project.Term n)} (hD : D.Closed) (G : Project.Term n) (hG : G.freeSupport=[]) :
    (needHeightsFormula C D G).FreeClosed := by
  have hBoundary := boundaryHeightFormula_freeClosed hD.weaken.weaken.weaken
    (Project.Term.bound 2) (Project.Term.bound 0) rfl rfl
  have hNeed := needHeightFormula_freeClosed C.omega.weaken.weaken.weaken D.active.weaken.weaken.weaken
    D.level.weaken.weaken.weaken (Project.Term.bound 2) (Project.Term.bound 0) (Project.Term.bound 1)
    (by simp [hC.omega]) (by simp [hD.active]) (by simp [hD.level]) rfl rfl rfl
  simpa [needHeightsFormula,Project.Formula.forallMem,Project.Formula.existsMem,
    Definitional.Formula.FreeClosed,graphFormula,memPairFormula,codeFormula,pairFormula,hG,hD.horizon,hC.omega]
    using And.intro hBoundary hNeed

theorem needHeightsFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (D : Data (Project.Term n)) (G : Project.Term n)
    (hD : (D.eval e).Valid M (C.eval e)) :
    Project.Formula.satisfies e (needHeightsFormula C D G) ↔ NeedHeights M (C.eval e) (D.eval e) (G.eval e) := by
  have hBody (k need h : M.Domain) : Project.Formula.satisfies (((e.push k).push need).push h)
      (needHeightFormula C.omega.weaken.weaken.weaken D.active.weaken.weaken.weaken D.level.weaken.weaken.weaken
        (.bound 2) (.bound 0) (.bound 1)) ↔ NeedHeight M (C.eval e) (D.eval e).active (D.eval e).level k h need := by
    simpa only [ExpressionData.eval_weaken,Term.eval_weaken,Project.Term.eval_bound_two_push,
      Project.Term.eval_bound_one_push,Project.Term.eval_bound_zero_push,ExpressionData.weaken,ExpressionData.map,ExpressionData.eval,Data.eval,Data.map] using
      (needHeightFormula_iff he (((e.push k).push need).push h) C.weaken.weaken.weaken
        D.active.weaken.weaken.weaken D.level.weaken.weaken.weaken (.bound 2) (.bound 0) (.bound 1))
  simp only [needHeightsFormula,Project.Formula.satisfies_conj_iff,graphFormula_iff he,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_iff_iff,memPairFormula_iff he,
    Project.Formula.satisfies_existsMem_iff,boundaryHeightFormula_iff he,Data.eval_weaken,Term.eval_weaken,hBody]
  change (Graph M (G.eval e) (D.eval e).horizon (C.eval e).omega ∧
    ∀ k, M.mem k (D.eval e).horizon → ∀ need, M.mem need (C.eval e).omega →
      (MemPair M (G.eval e) k need ↔ ∃ h, M.mem h (C.eval e).omega ∧ BoundaryHeight M (D.eval e) k h ∧
        NeedHeight M (C.eval e) (D.eval e).active (D.eval e).level k h need)) ↔ _
  constructor
  · rintro ⟨hG,hRows⟩
    refine ⟨hG,fun k need => ⟨?_,?_⟩⟩
    · intro hAt
      obtain ⟨hk,hn⟩ := hG.bounds he hAt
      obtain ⟨h,_,hHeight,hNeed⟩ := (hRows k hk need hn).mp hAt
      exact ⟨hk,h,hHeight,hNeed⟩
    · rintro ⟨hk,h,hHeight,hNeed⟩
      exact (hRows k hk need hNeed.1).mpr ⟨h,hHeight.natural he hD,hHeight,hNeed⟩
  · intro hG
    refine ⟨hG.graph,fun k hk need _ => ⟨?_,?_⟩⟩
    · intro hAt
      obtain ⟨_,h,hHeight,hNeed⟩ := (hG.rows k need).mp hAt
      exact ⟨h,hHeight.natural he hD,hHeight,hNeed⟩
    · rintro ⟨h,_,hHeight,hNeed⟩
      exact (hG.rows k need).mpr ⟨hk,h,hHeight,hNeed⟩

def needMapFormula {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (R : KP1Y.Reflection.Data (Project.Term n)) (D : Data (Project.Term n))
    (rowBound size P : Project.Term n) : Project.Formula 1 n :=
  .conj (Filter.partialGraphFormula P size R.needCodes)
    (Project.Formula.forallMem size (Project.Formula.forallMem R.needCodes.weaken
      (.iff (memPairFormula P.weaken.weaken (.bound 1) (.bound 0))
        (indexedNeedFormula C.weaken.weaken T.weaken.weaken D.weaken.weaken rowBound.weaken.weaken (.bound 1) (.bound 0)))))

theorem needMapFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (R : KP1Y.Reflection.Data (Project.Term n)) (D : Data (Project.Term n)) (rowBound size P : Project.Term n) :
    (needMapFormula C T R D rowBound size P).IsDelta0 :=
  .conj (Filter.partialGraphFormula_delta0 _ _ _) (.forallMem _ (.forallMem _
    (.iff (memPairFormula_delta0 _ _ _) (indexedNeedFormula_delta0 _ _ _ _ _ _))))

theorem needMapFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {T : MatrixArithmetic (Project.Term n)} (hT : CopyCoordinates.ArithmeticClosed T) {R : KP1Y.Reflection.Data (Project.Term n)} (hR : R.Closed)
    {D : Data (Project.Term n)} (hD : D.Closed) (rowBound size P : Project.Term n)
    (hBound : rowBound.freeSupport=[]) (hSize : size.freeSupport=[]) (hP : P.freeSupport=[]) :
    (needMapFormula C T R D rowBound size P).FreeClosed := by
  have hPartial := Filter.partialGraphFormula_freeClosed P size R.needCodes hP hSize hR.needCodes
  have hBody := indexedNeedFormula_freeClosed hC.weaken.weaken hT.weaken.weaken hD.weaken.weaken
    rowBound.weaken.weaken (Project.Term.bound 1) (Project.Term.bound 0) (by simp [hBound]) rfl rfl
  simpa [needMapFormula,Project.Formula.forallMem,Definitional.Formula.FreeClosed,memPairFormula,codeFormula,pairFormula,
    Project.Formula.existsMem,hP,hSize,hR.needCodes] using And.intro hPartial hBody

theorem needMapFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (R : KP1Y.Reflection.Data (Project.Term n)) (D : Data (Project.Term n)) (rowBound size P : Project.Term n) :
    Project.Formula.satisfies e (needMapFormula C T R D rowBound size P) ↔
      NeedMap M (C.eval e) (T.eval e) (R.eval e) (D.eval e) (rowBound.eval e) (size.eval e) (P.eval e) := by
  simp only [needMapFormula,Project.Formula.satisfies_conj_iff,Filter.partialGraphFormula_iff he,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_iff_iff,memPairFormula_iff he,
    indexedNeedFormula_iff he,ExpressionData.eval_weaken,MatrixArithmetic.eval_weaken,Data.eval_weaken,Term.eval_weaken]
  constructor
  · rintro ⟨hP,hRows⟩
    refine ⟨hP,fun i packet => ⟨?_,?_⟩⟩
    · intro hAt
      obtain ⟨hi,hPacket⟩ := hP.bounds he hAt
      exact ⟨hi,hPacket,(hRows i hi packet hPacket).mp hAt⟩
    · rintro ⟨hi,hPacket,hIndexed⟩
      exact (hRows i hi packet hPacket).mpr hIndexed
  · intro hP
    exact ⟨hP.graph,fun i hi packet hPacket => (hP.rows i packet).trans
      ⟨fun h => h.2.2,fun h => ⟨hi,hPacket,h⟩⟩⟩

/-- 所有辅助集合显式作为参数；这个固定证书是字面Δ₀。 -/
def certificateFormula {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (R : KP1Y.Reflection.Data (Project.Term n)) (D : Data (Project.Term n))
    (Heights rowBound size P len N I : Project.Term n) : Project.Formula 1 n :=
  .conj (needHeightsFormula C D Heights)
    (.conj (sequenceBoundFormula C.omega C.zero D.horizon Heights rowBound)
      (.conj (mulAtFormula T.mulPairs T.times D.horizon rowBound size)
        (.conj (needMapFormula C T R D rowBound size P)
          (Filter.filteredFormula C.omega P size R.needCodes len N I))))

theorem certificateFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (R : KP1Y.Reflection.Data (Project.Term n)) (D : Data (Project.Term n))
    (Heights rowBound size P len N I : Project.Term n) : (certificateFormula C T R D Heights rowBound size P len N I).IsDelta0 :=
  .conj (needHeightsFormula_delta0 _ _ _) (.conj (sequenceBoundFormula_delta0 _ _ _ _ _)
    (.conj (mulAtFormula_delta0 _ _ _ _ _) (.conj (needMapFormula_delta0 _ _ _ _ _ _ _)
      (Filter.filteredFormula_delta0 _ _ _ _ _ _ _))))

theorem certificateFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {T : MatrixArithmetic (Project.Term n)} (hT : CopyCoordinates.ArithmeticClosed T)
    {R : KP1Y.Reflection.Data (Project.Term n)} (hR : R.Closed) {D : Data (Project.Term n)} (hD : D.Closed)
    (Heights rowBound size P len N I : Project.Term n) (hH : Heights.freeSupport=[]) (hB : rowBound.freeSupport=[])
    (hSize : size.freeSupport=[]) (hP : P.freeSupport=[]) (hLen : len.freeSupport=[]) (hN : N.freeSupport=[]) (hI : I.freeSupport=[]) :
    (certificateFormula C T R D Heights rowBound size P len N I).FreeClosed := by
  have hHeights := needHeightsFormula_freeClosed hC hD Heights hH
  have hBound := sequenceBoundFormula_freeClosed C.omega C.zero D.horizon Heights rowBound hC.omega hC.zero hD.horizon hH hB
  have hProduct := mulAtFormula_freeClosed T.mulPairs T.times D.horizon rowBound size hT.mulPairs hT.times hD.horizon hB hSize
  have hMap := needMapFormula_freeClosed hC hT hR hD rowBound size P hB hSize hP
  have hFilter := Filter.filteredFormula_freeClosed C.omega P size R.needCodes len N I hC.omega hP hSize hR.needCodes hLen hN hI
  simp only [certificateFormula,Definitional.Formula.FreeClosed] at hHeights hBound hProduct hMap hFilter ⊢
  simp [hHeights,hBound,hProduct,hMap,hFilter]

theorem certificateFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (R : KP1Y.Reflection.Data (Project.Term n)) (D : Data (Project.Term n))
    (Heights rowBound size P len N I : Project.Term n)
    (hT : (T.eval e).Valid M (C.eval e)) (hD : (D.eval e).Valid M (C.eval e)) :
    Project.Formula.satisfies e (certificateFormula C T R D Heights rowBound size P len N I) ↔
      NeedHeights M (C.eval e) (D.eval e) (Heights.eval e) ∧
      SequenceBound M (C.eval e) (D.eval e).horizon (Heights.eval e) (rowBound.eval e) ∧
      KP1Y.Arithmetic.Product M (D.eval e).horizon (rowBound.eval e) (size.eval e) ∧
      NeedMap M (C.eval e) (T.eval e) (R.eval e) (D.eval e) (rowBound.eval e) (size.eval e) (P.eval e) ∧
      Filter.Filtered M (C.eval e).omega (P.eval e) (size.eval e) (R.eval e).needCodes (len.eval e) (N.eval e) (I.eval e) := by
  simp only [certificateFormula,Project.Formula.satisfies_conj_iff,needHeightsFormula_iff hM.1 e C D Heights hD,
    sequenceBoundFormula_iff hM.1 e C, mulAtFormula_iff hM.1,needMapFormula_iff hM.1,Filter.filteredFormula_iff hM.1]
  constructor
  · rintro ⟨hH,hBound,hSize,hP,hF⟩
    exact ⟨hH,hBound,(hT.mul.mul_iff_product hM hD.horizon hBound.1.1).mp hSize,hP,hF⟩
  · rintro ⟨hH,hBound,hSize,hP,hF⟩
    exact ⟨hH,hBound,(hT.mul.mul_iff_product hM hD.horizon hBound.1.1).mpr hSize,hP,hF⟩

/-- 真实有界证书盒；消去Box的存在量词是Σ₁，不能误称为Δ₀。 -/
def CertificateIn (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (R : KP1Y.Reflection.Data M.Domain) (D : Data M.Domain) (N Box : M.Domain) : Prop :=
  ∃ Heights, M.mem Heights Box ∧ ∃ rowBound, M.mem rowBound Box ∧ ∃ size, M.mem size Box ∧
    ∃ P, M.mem P Box ∧ ∃ len, M.mem len Box ∧ ∃ I, M.mem I Box ∧
      NeedHeights M C D Heights ∧ SequenceBound M C D.horizon Heights rowBound ∧
      KP1Y.Arithmetic.Product M D.horizon rowBound size ∧ NeedMap M C T R D rowBound size P ∧
      Filter.Filtered M C.omega P size R.needCodes len N I

theorem certificate_in_exists_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} {R : KP1Y.Reflection.Data M.Domain}
    {D : Data M.Domain} {N : M.Domain} : (∃Box, CertificateIn M C T R D N Box) ↔ Lists M C T R D N := by
  constructor
  · rintro ⟨Box,H,_,B,_,size,_,P,_,len,_,I,_,hH,hB,hSize,hP,hF⟩
    exact ⟨H,B,size,P,len,I,hH,hB,hSize,hP,hF⟩
  · rintro ⟨H,B,size,P,len,I,hH,hB,hSize,hP,hF⟩
    obtain ⟨Box,hBox⟩ := KP1Y.Ranking.finite_list_container_d hM [H,B,size,P,len,I]
    exact ⟨Box,H,hBox _ (by simp),B,hBox _ (by simp),size,hBox _ (by simp),P,hBox _ (by simp),
      len,hBox _ (by simp),I,hBox _ (by simp),hH,hB,hSize,hP,hF⟩


def certificateInFormula {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (R : KP1Y.Reflection.Data (Project.Term n)) (D : Data (Project.Term n)) (N Box : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem Box (Project.Formula.existsMem Box.weaken (Project.Formula.existsMem Box.weaken.weaken (Project.Formula.existsMem Box.weaken.weaken.weaken (Project.Formula.existsMem Box.weaken.weaken.weaken.weaken (Project.Formula.existsMem Box.weaken.weaken.weaken.weaken.weaken (certificateFormula C.weaken.weaken.weaken.weaken.weaken.weaken T.weaken.weaken.weaken.weaken.weaken.weaken R.weaken.weaken.weaken.weaken.weaken.weaken D.weaken.weaken.weaken.weaken.weaken.weaken (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) N.weaken.weaken.weaken.weaken.weaken.weaken (.bound 0)))))))

theorem certificateInFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (R : KP1Y.Reflection.Data (Project.Term n)) (D : Data (Project.Term n)) (N Box : Project.Term n) :
    (certificateInFormula C T R D N Box).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (certificateFormula_delta0 _ _ _ _ _ _ _ _ _ _ _))))))

theorem certificateInFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {T : MatrixArithmetic (Project.Term n)} (hT : CopyCoordinates.ArithmeticClosed T)
    {R : KP1Y.Reflection.Data (Project.Term n)} (hR : R.Closed) {D : Data (Project.Term n)} (hD : D.Closed)
    (N Box : Project.Term n) (hN : N.freeSupport=[]) (hBox : Box.freeSupport=[]) :
    (certificateInFormula C T R D N Box).FreeClosed := by
  have hBody := certificateFormula_freeClosed hC.weaken.weaken.weaken.weaken.weaken.weaken hT.weaken.weaken.weaken.weaken.weaken.weaken hR.weaken.weaken.weaken.weaken.weaken.weaken hD.weaken.weaken.weaken.weaken.weaken.weaken
    (Project.Term.bound 5) (Project.Term.bound 4) (Project.Term.bound 3) (Project.Term.bound 2)
    (Project.Term.bound 1) N.weaken.weaken.weaken.weaken.weaken.weaken (Project.Term.bound 0) rfl rfl rfl rfl rfl (by simp [hN]) rfl
  simpa [certificateInFormula,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hBox] using hBody

theorem certificateInFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (R : KP1Y.Reflection.Data (Project.Term n)) (D : Data (Project.Term n)) (N Box : Project.Term n)
    (hT : (T.eval e).Valid M (C.eval e)) (hD : (D.eval e).Valid M (C.eval e)) :
    Project.Formula.satisfies e (certificateInFormula C T R D N Box) ↔
      CertificateIn M (C.eval e) (T.eval e) (R.eval e) (D.eval e) (N.eval e) (Box.eval e) := by
  have hBody (Heights rowBound size P len I : M.Domain) := certificateFormula_iff hM
    ((((((e.push Heights).push rowBound).push size).push P).push len).push I)
    C.weaken.weaken.weaken.weaken.weaken.weaken T.weaken.weaken.weaken.weaken.weaken.weaken R.weaken.weaken.weaken.weaken.weaken.weaken D.weaken.weaken.weaken.weaken.weaken.weaken
    (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) N.weaken.weaken.weaken.weaken.weaken.weaken (.bound 0)
    (by simpa only [ExpressionData.eval_weaken,MatrixArithmetic.eval_weaken] using hT)
    (by simpa only [ExpressionData.eval_weaken,Data.eval_weaken] using hD)
  simp only [ExpressionData.eval_weaken,MatrixArithmetic.eval_weaken,KP1Y.Reflection.Data.eval_weaken,
    Data.eval_weaken,Term.eval_weaken] at hBody
  simp only [certificateInFormula,CertificateIn,Project.Formula.satisfies_existsMem_iff,Term.eval_weaken,hBody]
  rfl

/-- 由实际已构造列表得到真实有限证书盒；盒内全部量化都是有界量化。 -/
theorem lists_certificate_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    (R : KP1Y.Reflection.Data M.Domain) {D : Data M.Domain} (hD : D.Valid M C) :
    ∃N Box, CertificateIn M C T R D N Box := by
  obtain ⟨N,hN⟩ := lists_exists_d hM hC hT R hD
  obtain ⟨Box,hBox⟩ := (certificate_in_exists_iff_d hM).mpr hN
  exact ⟨N,Box,hBox⟩

end KP1Y.OneYFinite.CopyNeeds
