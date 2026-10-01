import KP1Y.RankedPackets

/-! 指定packet三个分量的字面Δ₀关系，供默认空排名和递归方程使用。 -/
namespace KP1Y.Ranking
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski
universe u

def packetFormula {n : Nat} (p A Γ F : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem p (Project.Formula.existsMem (.bound 0)
    (.conj (codeFormula p.weaken.weaken A.weaken.weaken (.bound 0))
      (codeFormula (.bound 0) Γ.weaken.weaken F.weaken.weaken)))

theorem packetFormula_delta0 {n : Nat} (p A Γ F : Project.Term n) : (packetFormula p A Γ F).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (codeFormula_delta0 _ _ _) (codeFormula_delta0 _ _ _)))

theorem packetFormula_freeClosed {n : Nat} (p A Γ F : Project.Term n)
    (hp : p.freeSupport=[]) (hA : A.freeSupport=[]) (hΓ : Γ.freeSupport=[]) (hF : F.freeSupport=[]) :
    (packetFormula p A Γ F).FreeClosed := by
  simp [packetFormula,codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem,
    Definitional.Formula.FreeClosed,hp,hA,hΓ,hF]

theorem packetFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (p A Γ F : Project.Term n) : Project.Formula.satisfies e (packetFormula p A Γ F) ↔
      Packet M (p.eval e) (A.eval e) (Γ.eval e) (F.eval e) := by
  simp only [packetFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    codeFormula_iff he,Term.eval_weaken]
  constructor
  · rintro ⟨_,_,q,_,hp,hq⟩
    exact ⟨q,hp,hq⟩
  · rintro ⟨q,hp,hq⟩
    obtain ⟨b,hbp,_,hqb⟩ := codes_components_bounded hp
    exact ⟨b,hbp,q,hqb,hp,hq⟩

end KP1Y.Ranking
