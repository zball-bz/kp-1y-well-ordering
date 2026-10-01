import KP1Y.OrdinalRectangleGraph
import KP1Y.OrdinalArithmeticTerms
import KP1Y.SigmaGraphCertificate

/-! 两个给定排名的乘积编码点：全部辅助序数计算均有实际有界证书。 -/
namespace KP1Y.Ranking
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Arithmetic
universe u

def rectangleCertificateFormula {n : Nat} (I κ q r B : Project.Term n) : Project.Formula 1 n :=
  witnessInstanceFormula rectangleMatrix (Fin.cases I (fun _ => κ)) q r B

theorem rectangleCertificateFormula_delta0 {n : Nat} (I κ q r B : Project.Term n) :
    (rectangleCertificateFormula I κ q r B).IsDelta0 := witnessInstanceFormula_delta0 _ _ _ _ _

theorem rectangleCertificateFormula_freeClosed {n : Nat} (I κ q r B : Project.Term n)
    (hI : I.freeSupport=[]) (hκ : κ.freeSupport=[]) (hq : q.freeSupport=[])
    (hr : r.freeSupport=[]) (hB : B.freeSupport=[]) : (rectangleCertificateFormula I κ q r B).FreeClosed :=
  witnessInstanceFormula_freeClosed _ _ _ _ _ (Fin.cases hI (fun _ => hκ)) hq hr hB

theorem rectangleCertificateFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (e : Env M n) (I κ q r B : Project.Term n) :
    Project.Formula.satisfies e (rectangleCertificateFormula I κ q r B) ↔
      RectangleCertificate M (I.eval e) (κ.eval e) (q.eval e) (r.eval e) (B.eval e) := by
  rw [rectangleCertificateFormula,witnessInstanceFormula,Project.Formula.satisfies_bind]
  apply (KP1Y.formula_bound_congr rectangleMatrix.body rectangleMatrix.freeClosed _
    (((((oneEnv (κ.eval e)).push (I.eval e)).push (q.eval e)).push (r.eval e)).push (B.eval e)) ?_).trans
      (rectangleMatrix_iff hM ((oneEnv (κ.eval e)).push (I.eval e)) _ _ _)
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · refine Fin.cases ?_ (fun i => ?_) i
        · rfl
        · exact Fin.cases rfl (fun i => Fin.elim0 i) i

def ProductRankPoint (M : SetTheory.Structure.{u}) (F G X Y α β p r W : M.Domain) : Prop :=
  ∃ x, M.mem x X ∧ ∃ y, M.mem y Y ∧ ∃ a, M.mem a α ∧ ∃ b, M.mem b β ∧
    ∃ q, M.mem q W ∧ ∃ B, M.mem B W ∧ Codes M p x y ∧ MemPair M F x a ∧ MemPair M G y b ∧
      Codes M q a b ∧ RectangleCertificate M α β q r B

private def pointBody : Project.Formula 1 15 :=
  .conj (codeFormula (.bound 8) (.bound 5) (.bound 4))
    (.conj (memPairFormula (.bound 13) (.bound 5) (.bound 3))
      (.conj (memPairFormula (.bound 14) (.bound 4) (.bound 2))
        (.conj (codeFormula (.bound 1) (.bound 3) (.bound 2))
          (rectangleCertificateFormula (.bound 9) (.bound 10) (.bound 1) (.bound 7) (.bound 0)))))

private theorem pointBody_freeClosed : pointBody.FreeClosed := by
  unfold pointBody
  simp only [Definitional.Formula.FreeClosed]
  refine ⟨?_,?_,?_,?_,rectangleCertificateFormula_freeClosed _ _ _ _ _ rfl rfl rfl rfl rfl⟩ <;>
    simp [codeFormula,pairFormula,memPairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]

def productRankPointMatrix : KP1Y.WitnessMatrix 6 where
  body := Project.Formula.existsMem (.bound 5) (Project.Formula.existsMem (.bound 7)
    (Project.Formula.existsMem (.bound 5) (Project.Formula.existsMem (.bound 7)
      (Project.Formula.existsMem (.bound 4) (Project.Formula.existsMem (.bound 5) pointBody)))))
  freeClosed := by simp [Project.Formula.existsMem,Definitional.Formula.FreeClosed,pointBody_freeClosed]
  delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (codeFormula_delta0 _ _ _) (.conj (memPairFormula_delta0 _ _ _)
      (.conj (memPairFormula_delta0 _ _ _) (.conj (codeFormula_delta0 _ _ _) (rectangleCertificateFormula_delta0 _ _ _ _ _))))))))))

def productRankEnv {M : SetTheory.Structure.{u}} (F G X Y α β : M.Domain) : Env M 6 :=
  (((((oneEnv G).push F).push Y).push X).push β).push α

theorem productRankPointMatrix_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (e : Env M 6) (p r W : M.Domain) :
    Project.Formula.satisfies (((e.push p).push r).push W) productRankPointMatrix.body ↔
      ProductRankPoint M (e.bound 4) (e.bound 5) (e.bound 2) (e.bound 3) (e.bound 0) (e.bound 1) p r W := by
  simp only [productRankPointMatrix,pointBody,Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff,codeFormula_iff hM.1,memPairFormula_iff hM.1,rectangleCertificateFormula_iff hM]
  rfl

theorem ProductRankPoint.meaning_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {F G X Y α β p r W : M.Domain} (h : ProductRankPoint M F G X Y α β p r W) :
    ∃ x, M.mem x X ∧ ∃ y, M.mem y Y ∧ ∃ a, M.mem a α ∧ ∃ b, M.mem b β ∧
      Codes M p x y ∧ MemPair M F x a ∧ MemPair M G y b ∧ RectangleCode M β a b r := by
  obtain ⟨x,hx,y,hy,a,ha,b,hb,q,_,B,_,hp,hF,hG,hq,hRect⟩ := h
  obtain ⟨a',_,b',_,d,_,P,_,S,_,hq',hP,hS⟩ := hRect
  obtain ⟨haa',hbb'⟩ := codes_injective hM.1 hq hq'
  subst a'
  subst b'
  exact ⟨x,hx,y,hy,a,ha,b,hb,hp,hF,hG,d,hP.meaning,⟨S,hS⟩⟩

theorem product_rank_point_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {F G X Y α β P p : M.Domain} (hF : OrdinalRank M F X α) (hG : OrdinalRank M G Y β)
    (hP : IsProduct M P X Y) (hp : M.mem p P) : ∃ r W, ProductRankPoint M F G X Y α β p r W := by
  obtain ⟨x,hx,y,hy,hpCode⟩ := (hP p).mp hp
  obtain ⟨a,ha,hFa⟩ := hF.graph.total x hx
  obtain ⟨b,hb,hGb⟩ := hG.graph.total y hy
  obtain ⟨q,hq⟩ := codes_total hM a b
  obtain ⟨r,hr⟩ := rectangle_exists_d hM hG.ordinal (hF.ordinal.mem ha) (hG.ordinal.mem hb)
  obtain ⟨B,hB⟩ := (rectangle_sigmaOne_iff_d hM ((oneEnv β).push α) q r).mp ⟨a,ha,b,hb,hq,hr⟩
  obtain ⟨W,hW⟩ := SetTheory.KP.exists_pair (KP1Y.models_weakKP hM) q B
  exact ⟨r,W,x,hx,y,hy,a,ha,b,hb,q,(hW q).mpr (Or.inl rfl),B,(hW B).mpr (Or.inr rfl),hpCode,hFa,hGb,hq,
    (rectangleMatrix_iff hM ((oneEnv β).push α) q r B).mp hB⟩

theorem ProductRankPoint.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {F G X Y α β p r r' W W' : M.Domain} (hF : Graph M F X α) (hG : Graph M G Y β)
    (h : ProductRankPoint M F G X Y α β p r W) (h' : ProductRankPoint M F G X Y α β p r' W') : r=r' := by
  obtain ⟨x,_,y,_,a,_,b,_,hp,hFa,hGb,hr⟩ := h.meaning_d hM
  obtain ⟨x',_,y',_,a',_,b',_,hp',hFa',hGb',hr'⟩ := h'.meaning_d hM
  obtain ⟨hxx',hyy'⟩ := codes_injective hM.1 hp hp'
  subst x'
  subst y'
  have haa' := hF.unique x a a' hFa hFa'
  have hbb' := hG.unique y b b' hGb hGb'
  subst a'
  subst b'
  exact rectangle_unique_d hM hr hr'

theorem ProductRankPoint.injective_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {F G X Y α β p p' r W W' : M.Domain} (hF : OrdinalRank M F X α) (hG : OrdinalRank M G Y β)
    (h : ProductRankPoint M F G X Y α β p r W) (h' : ProductRankPoint M F G X Y α β p' r W') : p=p' := by
  obtain ⟨x,_,y,_,a,_,b,hb,hp,hFa,hGb,hr⟩ := h.meaning_d hM
  obtain ⟨x',_,y',_,a',_,b',hb',hp',hFa',hGb',hr'⟩ := h'.meaning_d hM
  obtain ⟨haa',hbb'⟩ := rectangle_injective_d hM hr hr' hb hb' rfl
  subst a'
  subst b'
  have hxx' := hF.injective x x' a hFa hFa'
  have hyy' := hG.injective y y' b hGb hGb'
  subst x'
  subst y'
  exact codes_unique hM.1 hp hp'

end KP1Y.Ranking
