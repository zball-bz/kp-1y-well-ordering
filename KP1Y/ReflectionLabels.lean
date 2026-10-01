import KP1Y.ReflectionShapes

/-! 所有列（包括孤立列）均取ω以上标签；另行记录上界和保留前缀。 -/
namespace KP1Y.Reflection
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

structure Labeling (M : SetTheory.Structure.{u}) (C : Data M.Domain) (m f : M.Domain) : Prop where
  length : M.mem m C.omega
  graph : Graph M f m C.cap
  above : ∀ i, M.mem i m → ∀ x, M.mem x C.cap → MemPair M f i x → M.mem C.omega x
  increasing : ∀ i, M.mem i m → ∀ j, M.mem j m → M.mem i j → ∀ x, M.mem x C.cap → ∀ y, M.mem y C.cap →
    MemPair M f i x → MemPair M f j y → M.mem x y

def labelingFormula {n : Nat} (C : Data (Project.Term n)) (m f : Project.Term n) : Project.Formula 1 n :=
  .conj (.mem m C.omega) (.conj (graphFormula f m C.cap)
    (.conj (Project.Formula.forallMem m (Project.Formula.forallMem C.cap.weaken
      (.imp (memPairFormula f.weaken.weaken (.bound 1) (.bound 0)) (.mem C.omega.weaken.weaken (.bound 0)))))
      (Project.Formula.forallMem m (Project.Formula.forallMem m.weaken
        (.imp (.mem (.bound 1) (.bound 0)) (Project.Formula.forallMem C.cap.weaken.weaken
          (Project.Formula.forallMem C.cap.weaken.weaken.weaken
            (.imp (.conj (memPairFormula f.weaken.weaken.weaken.weaken (.bound 3) (.bound 1))
                (memPairFormula f.weaken.weaken.weaken.weaken (.bound 2) (.bound 0))) (.mem (.bound 1) (.bound 0))))))))))

theorem labelingFormula_delta0 {n : Nat} (C : Data (Project.Term n)) (m f : Project.Term n) : (labelingFormula C m f).IsDelta0 :=
  .conj (.mem _ _) (.conj (graphFormula_delta0 _ _ _)
    (.conj (.forallMem _ (.forallMem _ (.imp (memPairFormula_delta0 _ _ _) (.mem _ _))))
      (.forallMem _ (.forallMem _ (.imp (.mem _ _) (.forallMem _ (.forallMem _
        (.imp (.conj (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _)) (.mem _ _)))))))))

theorem labelingFormula_freeClosed {n : Nat} {C : Data (Project.Term n)} (hC : C.Closed) (m f : Project.Term n)
    (hm : m.freeSupport=[]) (hf : f.freeSupport=[]) : (labelingFormula C m f).FreeClosed := by
  simp [labelingFormula,graphFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,
    Project.Formula.existsMem,Definitional.Formula.FreeClosed,hC.omega,hC.cap,hm,hf]

theorem labelingFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : Data (Project.Term n)) (m f : Project.Term n) : Project.Formula.satisfies e (labelingFormula C m f) ↔
      Labeling M (C.eval e) (m.eval e) (f.eval e) := by
  simp only [labelingFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,graphFormula_iff he,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,memPairFormula_iff he,Term.eval_weaken]
  exact ⟨fun h => ⟨h.1,h.2.1,h.2.2.1,fun i hi j hj hij x hx y hy hiX hjY => h.2.2.2 i hi j hj hij x hx y hy ⟨hiX,hjY⟩⟩,
    fun h => ⟨h.length,h.graph,h.above,fun i hi j hj hij x hx y hy hRows => h.increasing i hi j hj hij x hx y hy hRows.1 hRows.2⟩⟩

def Below (M : SetTheory.Structure.{u}) (C : Data M.Domain) (m f b : M.Domain) : Prop :=
  ∀ i, M.mem i m → ∀ x, M.mem x C.cap → MemPair M f i x → M.mem x b

def belowFormula {n : Nat} (C : Data (Project.Term n)) (m f b : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.forallMem m (Project.Formula.forallMem C.cap.weaken
    (.imp (memPairFormula f.weaken.weaken (.bound 1) (.bound 0)) (.mem (.bound 0) b.weaken.weaken)))

theorem belowFormula_delta0 {n : Nat} (C : Data (Project.Term n)) (m f b : Project.Term n) : (belowFormula C m f b).IsDelta0 :=
  .forallMem _ (.forallMem _ (.imp (memPairFormula_delta0 _ _ _) (.mem _ _)))

theorem belowFormula_freeClosed {n : Nat} {C : Data (Project.Term n)} (hC : C.Closed) (m f b : Project.Term n)
    (hm : m.freeSupport=[]) (hf : f.freeSupport=[]) (hb : b.freeSupport=[]) : (belowFormula C m f b).FreeClosed := by
  simp [belowFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,
    Definitional.Formula.FreeClosed,hC.cap,hm,hf,hb]

theorem belowFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : Data (Project.Term n)) (m f b : Project.Term n) : Project.Formula.satisfies e (belowFormula C m f b) ↔
      Below M (C.eval e) (m.eval e) (f.eval e) (b.eval e) := by
  simp only [belowFormula,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    memPairFormula_iff he,Project.Formula.satisfies_mem_iff,Term.eval_weaken]
  rfl

def PrefixAgree (M : SetTheory.Structure.{u}) (C : Data M.Domain) (f g c : M.Domain) : Prop :=
  ∀ i, M.mem i c → ∀ x, M.mem x C.cap → (MemPair M f i x ↔ MemPair M g i x)

def prefixAgreeFormula {n : Nat} (C : Data (Project.Term n)) (f g c : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.forallMem c (Project.Formula.forallMem C.cap.weaken
    (.iff (memPairFormula f.weaken.weaken (.bound 1) (.bound 0)) (memPairFormula g.weaken.weaken (.bound 1) (.bound 0))))

theorem prefixAgreeFormula_delta0 {n : Nat} (C : Data (Project.Term n)) (f g c : Project.Term n) : (prefixAgreeFormula C f g c).IsDelta0 :=
  .forallMem _ (.forallMem _ (.iff (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _)))

theorem prefixAgreeFormula_freeClosed {n : Nat} {C : Data (Project.Term n)} (hC : C.Closed) (f g c : Project.Term n)
    (hf : f.freeSupport=[]) (hg : g.freeSupport=[]) (hc : c.freeSupport=[]) : (prefixAgreeFormula C f g c).FreeClosed := by
  simp [prefixAgreeFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,
    Definitional.Formula.FreeClosed,hC.cap,hf,hg,hc]

theorem prefixAgreeFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : Data (Project.Term n)) (f g c : Project.Term n) : Project.Formula.satisfies e (prefixAgreeFormula C f g c) ↔
      PrefixAgree M (C.eval e) (f.eval e) (g.eval e) (c.eval e) := by
  simp only [prefixAgreeFormula,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_iff_iff,
    memPairFormula_iff he,Term.eval_weaken]
  rfl

theorem Labeling.sequence {M : SetTheory.Structure.{u}} {C : Data M.Domain} (hC : C.Valid M) {m f : M.Domain}
    (h : Labeling M C m f) : M.mem f C.labels := (hC.labels f).mpr ⟨m,h.length,h.graph⟩

theorem Below.at {M : SetTheory.Structure.{u}} (he : Extensional M) {C : Data M.Domain} {m f b i x : M.Domain}
    (hF : Graph M f m C.cap) (h : Below M C m f b) (hAt : MemPair M f i x) : M.mem x b :=
  h i (hF.bounds he hAt).1 x (hF.bounds he hAt).2 hAt

theorem Below.trans {M : SetTheory.Structure.{u}} {C : Data M.Domain} {m f a b : M.Domain}
    (h : Below M C m f a) (hb : M.IsOrdinal b) (hab : M.mem a b) : Below M C m f b :=
  fun i hi x hx hAt => hb.transitive a hab x (h i hi x hx hAt)

end KP1Y.Reflection
