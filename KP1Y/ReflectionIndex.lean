import KP1Y.ReflectionStageSyntax
import KP1Y.NaturalNumbers

/-! 阶段编号预先形成实际集合函数，使R查询与下一行公式保持字面Δ₀。 -/
namespace KP1Y.Reflection
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Ranking KP1Y.Arithmetic
universe u v

structure IndexData (α : Type u) where
  omega : α
  cap : α
  middle : α
  keys : α
  block : α
  bound : α
  index : α

def IndexData.map {α : Type u} {β : Type v} (C : IndexData α) (f : α → β) : IndexData β :=
  ⟨f C.omega,f C.cap,f C.middle,f C.keys,f C.block,f C.bound,f C.index⟩

def IndexData.eval {M : SetTheory.Structure.{u}} {n : Nat} (C : IndexData (Project.Term n)) (e : Env M n) : IndexData M.Domain :=
  C.map (fun t => t.eval e)

def IndexData.weaken {n : Nat} (C : IndexData (Project.Term n)) : IndexData (Project.Term (n+1)) := C.map (fun t => t.weaken)

theorem IndexData.eval_weaken {M : SetTheory.Structure.{u}} {n : Nat} (e : Env M n) (x : M.Domain)
    (C : IndexData (Project.Term n)) : C.weaken.eval (e.push x)=C.eval e := by
  cases C
  simp [IndexData.weaken,IndexData.eval,IndexData.map,Term.eval_weaken]

structure IndexData.Valid (M : SetTheory.Structure.{u}) (C : IndexData M.Domain) : Prop where
  omega : M.IsOmega C.omega
  cap : M.IsOrdinal C.cap
  middle : IsProduct M C.middle C.omega C.cap
  keys : IsProduct M C.keys C.cap C.middle
  block : Product M C.cap C.omega C.block
  bound : Product M C.block C.cap C.bound
  graph : Graph M C.index C.keys C.bound
  rows : ∀ key σ, MemPair M C.index key σ ↔ M.mem key C.keys ∧ M.mem σ C.bound ∧ StagePoint M C.omega C.cap C.block key σ

theorem index_keys_iff {M : SetTheory.Structure.{u}} {ω cap Mid Keys : M.Domain}
    (hMid : IsProduct M Mid ω cap) (hKeys : IsProduct M Keys cap Mid) (key : M.Domain) :
    M.mem key Keys ↔ ∃ b, M.mem b cap ∧ ∃ K, M.mem K ω ∧ ∃ θ, M.mem θ cap ∧ Packet M key b K θ := by
  constructor
  · intro hk
    obtain ⟨b,hb,q,hq,hKey⟩ := (hKeys key).mp hk
    obtain ⟨K,hK,θ,hθ,hqCode⟩ := (hMid q).mp hq
    exact ⟨b,hb,K,hK,θ,hθ,q,hKey,hqCode⟩
  · rintro ⟨b,hb,K,hK,θ,hθ,q,hKey,hq⟩
    exact (hKeys key).mpr ⟨b,hb,q,(hMid q).mpr ⟨K,hK,θ,hθ,hq⟩,hKey⟩

theorem index_data_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {ω cap : M.Domain}
    (hω : M.IsOmega ω) (hCap : M.IsOrdinal cap) : ∃ C : IndexData M.Domain, C.omega=ω ∧ C.cap=cap ∧ C.Valid M := by
  obtain ⟨Mid,hMid⟩ := product_exists hM ω cap
  obtain ⟨Keys,hKeys⟩ := product_exists hM cap Mid
  have hOrdω := KP1Y.Naturals.omega_isOrdinal_d hM hω
  obtain ⟨L,hL⟩ := product_exists_d hM hCap hOrdω
  obtain ⟨Γ,hΓ⟩ := product_exists_d hM (hL.isOrdinal_d hM) hCap
  let e := stageEnv ω cap L
  obtain ⟨Index,hIndex,hRows⟩ := sigma_function_graph_d hM stageMatrix e Keys Γ (by
    intro key hk
    obtain ⟨b,hb,K,hK,θ,hθ,hPacket⟩ := (index_keys_iff hMid hKeys key).mp hk
    obtain ⟨σ,hσ⟩ := stage_code_exists_d hM hCap (hL.isOrdinal_d hM) (hCap.mem hb) (hOrdω.mem hK) (hCap.mem hθ)
    exact ⟨σ,(stage_sigmaOne_iff_d hM e hL key σ).mp ⟨b,hb,K,hK,θ,hθ,hPacket,hσ⟩⟩) (by
    intro key _ σ W hW
    obtain ⟨b,hb,K,hK,θ,hθ,_,hσ⟩ := (stage_sigmaOne_iff_d hM e hL key σ).mpr ⟨W,hW⟩
    exact stage_code_bounded_d hM hL hΓ hb hK hθ hσ) (by
    intro key _ σ τ W W' hW hW'
    exact ((stage_sigmaOne_iff_d hM e hL key σ).mpr ⟨W,hW⟩).unique_d hM
      ((stage_sigmaOne_iff_d hM e hL key τ).mpr ⟨W',hW'⟩))
  refine ⟨⟨ω,cap,Mid,Keys,L,Γ,Index⟩,rfl,rfl,hω,hCap,hMid,hKeys,hL,hΓ,hIndex,?_⟩
  intro key σ
  exact (hRows key σ).trans (and_congr Iff.rfl (and_congr Iff.rfl (stage_sigmaOne_iff_d hM e hL key σ).symm))

def Cursor (M : SetTheory.Structure.{u}) (Keys Index b K θ σ : M.Domain) : Prop :=
  ∃ key, M.mem key Keys ∧ Packet M key b K θ ∧ MemPair M Index key σ

def cursorFormula {n : Nat} (Keys Index b K θ σ : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem Keys (.conj (packetFormula (.bound 0) b.weaken K.weaken θ.weaken)
    (memPairFormula Index.weaken (.bound 0) σ.weaken))

theorem cursorFormula_delta0 {n : Nat} (Keys Index b K θ σ : Project.Term n) : (cursorFormula Keys Index b K θ σ).IsDelta0 :=
  .existsMem _ (.conj (packetFormula_delta0 _ _ _ _) (memPairFormula_delta0 _ _ _))

theorem cursorFormula_freeClosed {n : Nat} (Keys Index b K θ σ : Project.Term n)
    (hKeys : Keys.freeSupport=[]) (hIndex : Index.freeSupport=[]) (hb : b.freeSupport=[])
    (hK : K.freeSupport=[]) (hθ : θ.freeSupport=[]) (hσ : σ.freeSupport=[]) : (cursorFormula Keys Index b K θ σ).FreeClosed := by
  simp [cursorFormula,packetFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,
    Project.Formula.forallMem,Definitional.Formula.FreeClosed,hKeys,hIndex,hb,hK,hθ,hσ]

theorem cursorFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (Keys Index b K θ σ : Project.Term n) : Project.Formula.satisfies e (cursorFormula Keys Index b K θ σ) ↔
      Cursor M (Keys.eval e) (Index.eval e) (b.eval e) (K.eval e) (θ.eval e) (σ.eval e) := by
  simp only [cursorFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    packetFormula_iff he,memPairFormula_iff he,Term.eval_weaken]
  rfl

theorem IndexData.Valid.cursor_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : IndexData M.Domain}
    (h : C.Valid M) (b K θ σ : M.Domain) : Cursor M C.keys C.index b K θ σ ↔
      M.mem b C.cap ∧ M.mem K C.omega ∧ M.mem θ C.cap ∧ M.mem σ C.bound ∧ StageCode M C.cap C.block b K θ σ := by
  constructor
  · rintro ⟨key,_,hp,hAt⟩
    obtain ⟨_,hσ,b',hb,K',hK,θ',hθ,hp',hCode⟩ := (h.rows key σ).mp hAt
    obtain ⟨hbb',hKK',hθθ'⟩ := hp.injective hM.1 hp'
    subst b'
    subst K'
    subst θ'
    exact ⟨hb,hK,hθ,hσ,hCode⟩
  · rintro ⟨hb,hK,hθ,hσ,hCode⟩
    obtain ⟨key,hp⟩ := packet_exists_d hM b K θ
    have hk := (index_keys_iff h.middle h.keys key).mpr ⟨b,hb,K,hK,θ,hθ,hp⟩
    exact ⟨key,hk,hp,(h.rows key σ).mpr ⟨hk,hσ,b,hb,K,hK,θ,hθ,hp,hCode⟩⟩

theorem IndexData.Valid.cursor_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : IndexData M.Domain}
    (h : C.Valid M) {b K θ : M.Domain} (hb : M.mem b C.cap) (hK : M.mem K C.omega) (hθ : M.mem θ C.cap) :
    ∃ σ, M.mem σ C.bound ∧ Cursor M C.keys C.index b K θ σ := by
  obtain ⟨key,hp⟩ := packet_exists_d hM b K θ
  have hk := (index_keys_iff h.middle h.keys key).mpr ⟨b,hb,K,hK,θ,hθ,hp⟩
  obtain ⟨σ,hσ,hAt⟩ := h.graph.total key hk
  exact ⟨σ,hσ,key,hk,hp,hAt⟩

theorem IndexData.Valid.cursor_unique {M : SetTheory.Structure.{u}} (he : Extensional M) {C : IndexData M.Domain}
    (h : C.Valid M) {b K θ σ τ : M.Domain}
    (hσ : Cursor M C.keys C.index b K θ σ) (hτ : Cursor M C.keys C.index b K θ τ) : σ=τ := by
  obtain ⟨key,_,hp,hAt⟩ := hσ
  obtain ⟨key',_,hp',hAt'⟩ := hτ
  have hkk' := hp.unique he hp'
  subst key'
  exact h.graph.unique key σ τ hAt hAt'

end KP1Y.Reflection
