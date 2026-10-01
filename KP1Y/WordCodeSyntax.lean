import KP1Y.WordFoldInjective
import KP1Y.OrdinalRectangleGraph

/-! 最终字词码包含长度和折叠码，排除不同长度（如前导零）的碰撞。 -/
namespace KP1Y.WordRank
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Arithmetic
universe u

def Code (M : SetTheory.Structure.{u}) (ω κ C s r : M.Domain) : Prop :=
  ∃ n, M.mem n ω ∧ ∃ c, M.mem c C ∧ Graph M s n κ ∧ Fold M ω κ s c ∧ RectangleCode M C n c r

def CodeCertificate (M : SetTheory.Structure.{u}) (ω κ C s r W : M.Domain) : Prop :=
  ∃ n, M.mem n ω ∧ ∃ c, M.mem c C ∧ ∃ A, M.mem A W ∧ ∃ q, M.mem q W ∧ ∃ B, M.mem B W ∧
    Graph M s n κ ∧ Codes M q n c ∧ FoldCertificate M ω κ s c A ∧ RectangleCertificate M ω C q r B

private def foldSlots : Fin 5 → Fin 11 := Fin.cases 2 (Fin.cases 3 (Fin.cases 7 (Fin.cases 8 (fun _ => 9))))
private def rectangleSlots : Fin 5 → Fin 11 := Fin.cases 0 (Fin.cases 6 (Fin.cases 1 (Fin.cases 8 (fun _ => 10))))

def codeMatrix : KP1Y.WitnessMatrix 3 where
  body := Project.Formula.existsMem (.bound 3) (Project.Formula.existsMem (.bound 6)
    (Project.Formula.existsMem (.bound 2) (Project.Formula.existsMem (.bound 3) (Project.Formula.existsMem (.bound 4)
      (.conj (graphFormula (.bound 7) (.bound 4) (.bound 9))
        (.conj (codeFormula (.bound 1) (.bound 4) (.bound 3))
          (.conj (foldCertificateMatrix.body.rename foldSlots) (rectangleMatrix.body.rename rectangleSlots))))))))
  freeClosed := by
    simp [graphFormula,codeFormula,pairFormula,memPairFormula,Project.Formula.existsMem,Project.Formula.forallMem,
      Definitional.Formula.FreeClosed,foldCertificateMatrix.freeClosed,rectangleMatrix.freeClosed]
  delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (graphFormula_delta0 _ _ _) (.conj (codeFormula_delta0 _ _ _)
      (.conj (KP1Y.delta0_rename foldCertificateMatrix.delta0 _) (KP1Y.delta0_rename rectangleMatrix.delta0 _))))))))

private theorem foldSlots_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (e : Env M 3) (s r W n c A q B : M.Domain) :
    Project.Formula.satisfies ((((((((e.push s).push r).push W).push n).push c).push A).push q).push B)
      (foldCertificateMatrix.body.rename foldSlots) ↔ FoldCertificate M (e.bound 0) (e.bound 1) s c A := by
  rw [Project.Formula.satisfies_rename]
  apply (KP1Y.formula_bound_congr foldCertificateMatrix.body foldCertificateMatrix.freeClosed _
    (((((oneEnv (e.bound 1)).push (e.bound 0)).push s).push c).push A) ?_).trans
      (foldCertificateMatrix_iff hM ((oneEnv (e.bound 1)).push (e.bound 0)) s c A)
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

private theorem rectangleSlots_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (e : Env M 3) (s r W n c A q B : M.Domain) :
    Project.Formula.satisfies ((((((((e.push s).push r).push W).push n).push c).push A).push q).push B)
      (rectangleMatrix.body.rename rectangleSlots) ↔ RectangleCertificate M (e.bound 0) (e.bound 2) q r B := by
  rw [Project.Formula.satisfies_rename]
  apply (KP1Y.formula_bound_congr rectangleMatrix.body rectangleMatrix.freeClosed _
    (((((oneEnv (e.bound 2)).push (e.bound 0)).push q).push r).push B) ?_).trans
      (rectangleMatrix_iff hM ((oneEnv (e.bound 2)).push (e.bound 0)) q r B)
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

theorem codeMatrix_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (e : Env M 3) (s r W : M.Domain) :
    Project.Formula.satisfies (((e.push s).push r).push W) codeMatrix.body ↔ CodeCertificate M (e.bound 0) (e.bound 1) (e.bound 2) s r W := by
  simp only [codeMatrix,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    graphFormula_iff hM.1,codeFormula_iff hM.1,foldSlots_iff hM,rectangleSlots_iff hM]
  rfl

theorem code_sigmaOne_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (e : Env M 3) (s r : M.Domain) :
    Code M (e.bound 0) (e.bound 1) (e.bound 2) s r ↔ ∃ W, Project.Formula.satisfies (((e.push s).push r).push W) codeMatrix.body := by
  constructor
  · rintro ⟨n,hn,c,hc,hS,⟨A,hFold⟩,hCode⟩
    obtain ⟨q,hq⟩ := codes_total hM n c
    obtain ⟨B,hB⟩ := (rectangle_sigmaOne_iff_d hM ((oneEnv (e.bound 2)).push (e.bound 0)) q r).mp ⟨n,hn,c,hc,hq,hCode⟩
    obtain ⟨W0,hW0⟩ := SetTheory.KP.exists_pair (KP1Y.models_weakKP hM) A q
    obtain ⟨W,hW⟩ := SetTheory.KP.exists_insert (KP1Y.models_weakKP hM) W0 B
    exact ⟨W,(codeMatrix_iff hM e s r W).mpr ⟨n,hn,c,hc,
      A,(hW A).mpr (Or.inl ((hW0 A).mpr (Or.inl rfl))),q,(hW q).mpr (Or.inl ((hW0 q).mpr (Or.inr rfl))),
      B,(hW B).mpr (Or.inr rfl),hS,hq,hFold,(rectangleMatrix_iff hM ((oneEnv (e.bound 2)).push (e.bound 0)) q r B).mp hB⟩⟩
  · rintro ⟨W,hW⟩
    obtain ⟨n,hn,c,hc,A,_,q,_,B,_,hS,hq,hFold,hRect⟩ := (codeMatrix_iff hM e s r W).mp hW
    obtain ⟨n',_,c',_,hq',hCode⟩ := (rectangle_sigmaOne_iff_d hM ((oneEnv (e.bound 2)).push (e.bound 0)) q r).mpr
      ⟨B,(rectangleMatrix_iff hM ((oneEnv (e.bound 2)).push (e.bound 0)) q r B).mpr hRect⟩
    obtain ⟨hnn',hcc'⟩ := codes_injective hM.1 hq hq'
    subst n'
    subst c'
    exact ⟨n,hn,c,hc,hS,⟨A,hFold⟩,hCode⟩

end KP1Y.WordRank
