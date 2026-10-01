import KP1Y.OrdinalRectangle
import KP1Y.SigmaFunctionGraph
import KP1Y.OrdinalRank

/-! 将κ·i+a的Σ₁证书组装成实际有界单射图I×κ→κ·I。 -/
namespace KP1Y.Arithmetic
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

def RectangleCertificate (M : SetTheory.Structure.{u}) (I κ q c W : M.Domain) : Prop :=
  ∃ i, M.mem i I ∧ ∃ a, M.mem a κ ∧ ∃ b, M.mem b W ∧ ∃ P, M.mem P W ∧ ∃ S, M.mem S W ∧
    Codes M q i a ∧ ProductCertificate M κ i b P ∧ KP1Y.OrdinalIteration.ValueCertificate successorMatrix (oneEnv b) a c S

private def productSlots : Fin 4 → Fin 10 := Fin.cases 1 (Fin.cases 2 (Fin.cases 4 (fun _ => 9)))
private def sumSlots : Fin 4 → Fin 10 := Fin.cases 0 (Fin.cases 6 (Fin.cases 3 (fun _ => 2)))

def rectangleMatrix : KP1Y.WitnessMatrix 2 where
  body := Project.Formula.existsMem (.bound 3) (Project.Formula.existsMem (.bound 5)
    (Project.Formula.existsMem (.bound 2) (Project.Formula.existsMem (.bound 3) (Project.Formula.existsMem (.bound 4)
      (.conj (codeFormula (.bound 7) (.bound 4) (.bound 3))
        (.conj (productMatrix.body.rename productSlots) (sumMatrix.body.rename sumSlots)))))))
  freeClosed := by
    simp [codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed,
      productMatrix.freeClosed,sumMatrix.freeClosed]
  delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (codeFormula_delta0 _ _ _) (.conj (KP1Y.delta0_rename productMatrix.delta0 _) (KP1Y.delta0_rename sumMatrix.delta0 _)))))))

private theorem productSlots_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (e : Env M 2) (q c W i a b P S : M.Domain) :
    Project.Formula.satisfies ((((((((e.push q).push c).push W).push i).push a).push b).push P).push S)
      (productMatrix.body.rename productSlots) ↔ ProductCertificate M (e.bound 1) i b P := by
  rw [Project.Formula.satisfies_rename]
  apply (KP1Y.formula_bound_congr productMatrix.body productMatrix.freeClosed _
    ((((oneEnv (e.bound 1)).push i).push b).push P) ?_).trans (productMatrix_iff hM (oneEnv (e.bound 1)) i b P)
  intro k
  refine Fin.cases ?_ (fun k => ?_) k
  · rfl
  · refine Fin.cases ?_ (fun k => ?_) k
    · rfl
    · refine Fin.cases ?_ (fun k => ?_) k
      · rfl
      · exact Fin.cases rfl (fun k => Fin.elim0 k) k

private theorem sumSlots_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (e : Env M 2) (q c W i a b P S : M.Domain) :
    Project.Formula.satisfies ((((((((e.push q).push c).push W).push i).push a).push b).push P).push S)
      (sumMatrix.body.rename sumSlots) ↔ KP1Y.OrdinalIteration.ValueCertificate successorMatrix (oneEnv b) a c S := by
  rw [Project.Formula.satisfies_rename]
  apply (KP1Y.formula_bound_congr sumMatrix.body sumMatrix.freeClosed _
    ((((oneEnv b).push a).push c).push S) ?_).trans (sumMatrix_iff hM (oneEnv b) a c S)
  intro k
  refine Fin.cases ?_ (fun k => ?_) k
  · rfl
  · refine Fin.cases ?_ (fun k => ?_) k
    · rfl
    · refine Fin.cases ?_ (fun k => ?_) k
      · rfl
      · exact Fin.cases rfl (fun k => Fin.elim0 k) k

theorem rectangleMatrix_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (e : Env M 2) (q c W : M.Domain) :
    Project.Formula.satisfies (((e.push q).push c).push W) rectangleMatrix.body ↔ RectangleCertificate M (e.bound 0) (e.bound 1) q c W := by
  simp only [rectangleMatrix,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    codeFormula_iff hM.1,productSlots_iff hM,sumSlots_iff hM]
  rfl

theorem rectangle_sigmaOne_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (e : Env M 2) (q c : M.Domain) :
    (∃ i, M.mem i (e.bound 0) ∧ ∃ a, M.mem a (e.bound 1) ∧ Codes M q i a ∧ RectangleCode M (e.bound 1) i a c) ↔
      ∃ W, Project.Formula.satisfies (((e.push q).push c).push W) rectangleMatrix.body := by
  constructor
  · rintro ⟨i,hi,a,ha,hCode,b,hProduct,hSum⟩
    obtain ⟨P,hP⟩ := (product_sigmaOne_iff_d hM (oneEnv (e.bound 1)) i b).mp hProduct
    obtain ⟨S,hS⟩ := hSum
    obtain ⟨W0,hW0⟩ := SetTheory.KP.exists_pair (KP1Y.models_weakKP hM) b P
    obtain ⟨W,hW⟩ := SetTheory.KP.exists_insert (KP1Y.models_weakKP hM) W0 S
    exact ⟨W,(rectangleMatrix_iff hM e q c W).mpr
      ⟨i,hi,a,ha,b,(hW b).mpr (Or.inl ((hW0 b).mpr (Or.inl rfl))),
        P,(hW P).mpr (Or.inl ((hW0 P).mpr (Or.inr rfl))),S,(hW S).mpr (Or.inr rfl),
        hCode,(productMatrix_iff hM (oneEnv (e.bound 1)) i b P).mp hP,hS⟩⟩
  · rintro ⟨W,hW⟩
    obtain ⟨i,hi,a,ha,b,_,P,_,S,_,hCode,hProduct,hSum⟩ := (rectangleMatrix_iff hM e q c W).mp hW
    obtain ⟨hκ,zero,_,C,_,hZero,hC⟩ := hProduct
    exact ⟨i,hi,a,ha,hCode,b,⟨hκ,zero,hZero,C,hC⟩,⟨S,hSum⟩⟩

theorem rectangle_graph_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {I κ P B : M.Domain}
    (hI : M.IsOrdinal I) (hκ : M.IsOrdinal κ) (hP : IsProduct M P I κ) (hBound : Product M κ I B) :
    ∃ F, Graph M F P B ∧
      (∀ q c, MemPair M F q c ↔ M.mem q P ∧ M.mem c B ∧
        ∃ i, M.mem i I ∧ ∃ a, M.mem a κ ∧ Codes M q i a ∧ RectangleCode M κ i a c) ∧
      (∀ q q' c, MemPair M F q c → MemPair M F q' c → q=q') := by
  let e : Env M 2 := (oneEnv κ).push I
  have hTotal : ∀ q, M.mem q P → ∃ c W, Project.Formula.satisfies (((e.push q).push c).push W) rectangleMatrix.body := by
    intro q hq
    obtain ⟨i,hi,a,ha,hCode⟩ := (hP q).mp hq
    obtain ⟨c,hc⟩ := rectangle_exists_d hM hκ (hI.mem hi) (hκ.mem ha)
    exact ⟨c,(rectangle_sigmaOne_iff_d hM e q c).mp ⟨i,hi,a,ha,hCode,hc⟩⟩
  obtain ⟨F,hF,hRaw⟩ := sigma_function_graph_d hM rectangleMatrix e P B hTotal (by
    intro q _ c W hW
    obtain ⟨i,hi,a,ha,_,hc⟩ := (rectangle_sigmaOne_iff_d hM e q c).mpr ⟨W,hW⟩
    exact rectangle_bounded_d hM hBound hc hi ha) (by
    intro q _ c d W W' hW hW'
    obtain ⟨i,_,a,_,hCode,hc⟩ := (rectangle_sigmaOne_iff_d hM e q c).mpr ⟨W,hW⟩
    obtain ⟨j,_,b,_,hCode',hd⟩ := (rectangle_sigmaOne_iff_d hM e q d).mpr ⟨W',hW'⟩
    obtain ⟨hij,hab⟩ := codes_injective hM.1 hCode hCode'
    subst j
    subst b
    exact rectangle_unique_d hM hc hd)
  have hRows (q c : M.Domain) : MemPair M F q c ↔ M.mem q P ∧ M.mem c B ∧
      ∃ i, M.mem i I ∧ ∃ a, M.mem a κ ∧ Codes M q i a ∧ RectangleCode M κ i a c :=
    (hRaw q c).trans (and_congr Iff.rfl (and_congr Iff.rfl (rectangle_sigmaOne_iff_d hM e q c).symm))
  refine ⟨F,hF,hRows,?_⟩
  intro q q' c hqc hq'c
  obtain ⟨_,_,i,_,a,ha,hCode,hc⟩ := (hRows q c).mp hqc
  obtain ⟨_,_,j,_,b,hb,hCode',hc'⟩ := (hRows q' c).mp hq'c
  obtain ⟨hij,hab⟩ := rectangle_injective_d hM hc hc' ha hb rfl
  subst j
  subst b
  exact codes_unique hM.1 hCode hCode'

theorem rectangle_ordinal_rank_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {I κ P B : M.Domain}
    (hI : M.IsOrdinal I) (hκ : M.IsOrdinal κ) (hP : IsProduct M P I κ) (hBound : Product M κ I B) :
    ∃ F, KP1Y.Ranking.OrdinalRank M F P B := by
  obtain ⟨F,hF,_,hInjective⟩ := rectangle_graph_d hM hI hκ hP hBound
  exact ⟨F,hBound.isOrdinal_d hM,hF,hInjective⟩

end KP1Y.Arithmetic
