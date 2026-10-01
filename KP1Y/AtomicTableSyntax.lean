import KP1Y.RelationTables
import KP1Y.RelationalAtoms
import KP1Y.ScopedAtoms

/-! 全部原子真值表的字面Δ₀证书，包括支持集约束和精确行。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski
universe u

def atomicTableFormula {n : Nat} (D : RelationalData (Project.Term n)) (Atom : Project.Term n) : Project.Formula 1 n :=
  .conj (relationSupportFormula Atom D.codes D.values)
    (Project.Formula.forallMem D.codes (Project.Formula.forallMem D.values.weaken
      (.iff (memPairFormula Atom.weaken.weaken (.bound 1) (.bound 0))
        (atomValueFormula D.weaken.weaken (.bound 1) (.bound 0)))))

theorem atomicTableFormula_delta0 {n : Nat} (D : RelationalData (Project.Term n)) (Atom : Project.Term n) :
    (atomicTableFormula D Atom).IsDelta0 :=
  .conj (relationSupportFormula_delta0 _ _ _) (.forallMem _ (.forallMem _
    (.iff (memPairFormula_delta0 _ _ _) (atomValueFormula_delta0 _ _ _))))

theorem atomicTableFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (D : RelationalData (Project.Term n)) (Atom : Project.Term n) :
    Project.Formula.satisfies env (atomicTableFormula D Atom) ↔ AtomicTable M (D.eval env) (Atom.eval env) := by
  simp only [atomicTableFormula,Project.Formula.satisfies_conj_iff,relationSupportFormula_iff he,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_iff_iff,
    memPairFormula_iff he,atomValueFormula_iff he,RelationalData.eval_weaken,Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨hSupport,hRows⟩
    refine ⟨hSupport,?_⟩
    intro a s
    constructor
    · intro hAt
      have hBounds := hSupport.bounds he hAt
      exact ⟨hBounds.1,hBounds.2,(hRows a hBounds.1 s hBounds.2).mp hAt⟩
    · rintro ⟨ha,hs,hAt⟩
      exact (hRows a ha s hs).mpr hAt
  · intro h
    exact ⟨h.support,fun a ha s hs => (h.rows a s).trans ⟨fun h => h.2.2,fun h => ⟨ha,hs,h⟩⟩⟩

theorem AtomicTable.unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {D : RelationalData M.Domain} {Atom Atom' : M.Domain} (h : AtomicTable M D Atom) (h' : AtomicTable M D Atom') : Atom=Atom' :=
  relation_ext he h.support h'.support (fun a s => (h.rows a s).trans (h'.rows a s).symm)

end KP1Y.Satisfaction
