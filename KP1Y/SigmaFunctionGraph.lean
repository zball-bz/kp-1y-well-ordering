import KP1Y.JointCollection
import KP1Y.FunctionGraphs

/-! Σ₁函数在给定集合域和值界上的实际函数图：同时收集输出和证书，再有界形成图。 -/
namespace KP1Y.Functions
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski
universe u

private def witnessSlots {n : Nat} : Fin (n+3) → Fin (n+4) :=
  Fin.cases 0 (Fin.cases 1 (Fin.cases 2 (fun i => ⟨i.val+4,by omega⟩)))

def boundedWitnessSchema {n : Nat} (φ : KP1Y.WitnessMatrix n) : Project.Delta0BinarySchema (n+1) where
  body := Project.Formula.existsMem (.bound 2) (φ.body.rename witnessSlots)
  freeClosed := by simp [Project.Formula.existsMem,Definitional.Formula.FreeClosed,φ.freeClosed]
  delta0 := .existsMem _ (KP1Y.delta0_rename φ.delta0 _)

private theorem witnessSlots_env {M : SetTheory.Structure.{u}} {n : Nat} (e : Env M n) (B x y z : M.Domain) :
    ((((e.push B).push x).push y).push z).reindex witnessSlots = ((e.push x).push y).push z := by
  rw [Env.mk.injEq]
  constructor
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
  · rfl

theorem boundedWitnessSchema_iff {M : SetTheory.Structure.{u}} {n : Nat} (φ : KP1Y.WitnessMatrix n)
    (e : Env M n) (B x y : M.Domain) :
    Project.Formula.satisfies (((e.push B).push x).push y) (boundedWitnessSchema φ).body ↔
      ∃ z, M.mem z B ∧ Project.Formula.satisfies (((e.push x).push y).push z) φ.body := by
  simp only [boundedWitnessSchema,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_rename,witnessSlots_env]
  rfl

theorem sigma_function_graph_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (φ : KP1Y.WitnessMatrix n) (e : Env M n) (X Y : M.Domain)
    (hTotal : ∀ x, M.mem x X → ∃ y z, Project.Formula.satisfies (((e.push x).push y).push z) φ.body)
    (hBounds : ∀ x, M.mem x X → ∀ y z, Project.Formula.satisfies (((e.push x).push y).push z) φ.body → M.mem y Y)
    (hFun : ∀ x, M.mem x X → ∀ y y' z z', Project.Formula.satisfies (((e.push x).push y).push z) φ.body →
      Project.Formula.satisfies (((e.push x).push y').push z') φ.body → y=y') :
    ∃ F, Graph M F X Y ∧ ∀ x y, MemPair M F x y ↔ M.mem x X ∧ M.mem y Y ∧
      ∃ z, Project.Formula.satisfies (((e.push x).push y).push z) φ.body := by
  obtain ⟨B,hB⟩ := KP1Y.joint_collection_d hM φ e X hTotal
  obtain ⟨F,hSupport,hRaw⟩ := relation_comprehension_d hM (boundedWitnessSchema φ) (e.push B) X Y
  have hBounded (x y : M.Domain) : MemPair M F x y ↔ M.mem x X ∧ M.mem y Y ∧
      ∃ z, M.mem z B ∧ Project.Formula.satisfies (((e.push x).push y).push z) φ.body := by
    simpa only [boundedWitnessSchema_iff] using hRaw x y
  have hRows (x y : M.Domain) : MemPair M F x y ↔ M.mem x X ∧ M.mem y Y ∧
      ∃ z, Project.Formula.satisfies (((e.push x).push y).push z) φ.body := by
    constructor
    · intro hAt
      obtain ⟨hx,hy,z,_,hφ⟩ := (hBounded x y).mp hAt
      exact ⟨hx,hy,z,hφ⟩
    · rintro ⟨hx,hy,z,hφ⟩
      obtain ⟨y',_,z',hz',hφ'⟩ := hB x hx
      have hyy' := hFun x hx y y' z z' hφ hφ'
      subst y'
      exact (hBounded x y).mpr ⟨hx,hy,z',hz',hφ'⟩
  refine ⟨F,⟨hSupport,?_,?_⟩,hRows⟩
  · intro x hx
    obtain ⟨y,z,hφ⟩ := hTotal x hx
    exact ⟨y,hBounds x hx y z hφ,(hRows x y).mpr ⟨hx,hBounds x hx y z hφ,z,hφ⟩⟩
  · intro x y y' hAt hAt'
    obtain ⟨hx,_,z,hφ⟩ := (hRows x y).mp hAt
    obtain ⟨_,_,z',hφ'⟩ := (hRows x y').mp hAt'
    exact hFun x hx y y' z z' hφ hφ'

end KP1Y.Functions
