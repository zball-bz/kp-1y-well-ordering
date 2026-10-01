import KP1Y.NaturalInduction
import KP1Y.FunctionGraphs

/-! 对内部函数序列追加一项的 Δ₀ 定义、唯一性及去掉末项的逆构造。 -/
namespace KP1Y.Sequences
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Bounded
universe u

def Inserted (M : SetTheory.Structure.{u}) (G F q : M.Domain) : Prop :=
  ∀ x, M.mem x G ↔ M.mem x F ∨ x=q

def insertFormula {n : Nat} (G F q : Project.Term n) : Project.Formula 1 n :=
  .conj (.mem q G) (.conj (Project.Formula.subset F G)
    (Project.Formula.forallMem G (.disj (.mem (.bound 0) F.weaken)
      (Project.Formula.extensionalEq (.bound 0) q.weaken))))

theorem insertFormula_delta0 {n : Nat} (G F q : Project.Term n) : (insertFormula G F q).IsDelta0 :=
  .conj (.mem _ _) (.conj (.atom _ _ _) (.forallMem _ (.disj (.mem _ _) (.atom _ _ _))))

theorem insertFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (G F q : Project.Term n) :
    Project.Formula.satisfies env (insertFormula G F q) ↔
      Inserted M (G.eval env) (F.eval env) (q.eval env) := by
  simp only [insertFormula, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff, Project.Formula.satisfies_subset_iff,
    Project.Formula.satisfies_forallMem_iff, Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨hq,hFG,hG⟩ x
    exact ⟨hG x,fun h => h.elim (hFG x) (fun heq => heq ▸ hq)⟩
  · intro h
    exact ⟨(h _).mpr (Or.inr rfl),fun x hx => (h x).mpr (Or.inl hx),fun x => (h x).mp⟩

def Append (M : SetTheory.Structure.{u}) (G F i a : M.Domain) : Prop :=
  ∃ q, Codes M q i a ∧ Inserted M G F q

def appendFormula {n : Nat} (G F i a : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem G (.conj (codeFormula (.bound 0) i.weaken a.weaken)
    (insertFormula G.weaken F.weaken (.bound 0)))

theorem appendFormula_delta0 {n : Nat} (G F i a : Project.Term n) : (appendFormula G F i a).IsDelta0 :=
  .existsMem _ (.conj (codeFormula_delta0 _ _ _) (insertFormula_delta0 _ _ _))

theorem appendFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (G F i a : Project.Term n) :
    Project.Formula.satisfies env (appendFormula G F i a) ↔
      Append M (G.eval env) (F.eval env) (i.eval env) (a.eval env) := by
  simp only [appendFormula, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff, codeFormula_iff he,
    insertFormula_iff he, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨q,_,hc,hi⟩ => ⟨q,hc,hi⟩,
    fun ⟨q,hc,hi⟩ => ⟨q,(hi q).mpr (Or.inr rfl),hc,hi⟩⟩

theorem append_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (F i a : M.Domain) : ∃ G, Append M G F i a := by
  obtain ⟨q,hq⟩ := codes_total hM i a
  obtain ⟨G,hG⟩ := SetTheory.KP.exists_insert (KP1Y.models_weakKP hM) F q
  exact ⟨G,q,hq,hG⟩

theorem append_unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {G J F i a : M.Domain} (hG : Append M G F i a) (hJ : Append M J F i a) : G=J := by
  obtain ⟨q,hq,hG⟩ := hG
  obtain ⟨r,hr,hJ⟩ := hJ
  have hqr := codes_unique he hq hr
  subst r
  exact he.eq_of_same_members G J (fun x => (hG x).trans (hJ x).symm)

theorem append_rows {M : SetTheory.Structure.{u}} (he : Extensional M)
    {G F i a : M.Domain} (hG : Append M G F i a) (x y : M.Domain) :
    MemPair M G x y ↔ MemPair M F x y ∨ (x=i ∧ y=a) := by
  obtain ⟨q,hq,hG⟩ := hG
  constructor
  · rintro ⟨r,hr,hcode⟩
    rcases (hG r).mp hr with hrF | heq
    · exact Or.inl ⟨r,hrF,hcode⟩
    · subst r
      exact Or.inr (codes_injective he hcode hq)
  · rintro (⟨r,hr,hcode⟩ | ⟨rfl,rfl⟩)
    · exact ⟨r,(hG r).mpr (Or.inl hr),hcode⟩
    · exact ⟨q,(hG q).mpr (Or.inr rfl),hq⟩

theorem graph_append_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {G F i s A a : M.Domain} (hF : Graph M F i A) (hs : M.SuccessorOf s i)
    (ha : M.mem a A) (hApp : Append M G F i a) : Graph M G s A := by
  obtain ⟨J,hJ,hJRows⟩ := append_graph_d hM hF hs (fun _ h => h) ha
  have hRows : ∀ x y, MemPair M G x y ↔ MemPair M J x y :=
    fun x y => (append_rows hM.1 hApp x y).trans (hJRows x y).symm
  refine ⟨?_,?_,fun x y z hxy hxz => hJ.unique x y z ((hRows x y).mp hxy) ((hRows x z).mp hxz)⟩
  · obtain ⟨q,hq,hG⟩ := hApp
    intro r hr
    rcases (hG r).mp hr with hr | heq
    · obtain ⟨x,hx,y,hy,hcode⟩ := hF.support r hr
      exact ⟨x,(hs x).mpr (Or.inl hx),y,hy,hcode⟩
    · subst r
      exact ⟨i,hs.predecessor_mem,a,ha,hq⟩
  · intro x hx
    obtain ⟨y,hy,hxy⟩ := hJ.total x hx
    exact ⟨y,hy,(hRows x y).mpr hxy⟩

theorem graph_decompose_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {G i s A : M.Domain} (hG : Graph M G s A) (hs : M.SuccessorOf s i) :
    ∃ F a, Graph M F i A ∧ M.mem a A ∧ Append M G F i a := by
  obtain ⟨F,hF,hFRows⟩ := restrict_graph_d hM hG (fun x hx => (hs x).mpr (Or.inl hx))
  obtain ⟨a,ha,hGia⟩ := hG.total i hs.predecessor_mem
  obtain ⟨q,hq⟩ := codes_total hM i a
  refine ⟨F,a,hF,ha,q,hq,?_⟩
  intro r
  constructor
  · intro hr
    obtain ⟨x,hx,y,hy,hcode⟩ := hG.support r hr
    rcases (hs x).mp hx with hxi | hxi
    · obtain ⟨t,ht,hcode'⟩ := (hFRows x y).mpr ⟨hxi,r,hr,hcode⟩
      exact Or.inl ((codes_unique hM.1 hcode hcode') ▸ ht)
    · have hEq := hM.1.eq_of_same_members x i hxi
      subst x
      have hya := hG.unique i y a ⟨r,hr,hcode⟩ hGia
      subst y
      exact Or.inr (codes_unique hM.1 hcode hq)
  · rintro (hr | heq)
    · obtain ⟨x,hx,y,hy,hcode⟩ := hF.support r hr
      obtain ⟨t,ht,hcode'⟩ := ((hFRows x y).mp ⟨r,hr,hcode⟩).2
      exact (codes_unique hM.1 hcode hcode') ▸ ht
    · subst r
      obtain ⟨t,ht,hcode⟩ := hGia
      exact (codes_unique hM.1 hq hcode) ▸ ht

end KP1Y.Sequences
