import KP1Y.ReflectionInterpretation
import KP1Y.ReflectionBodySemantics
import KP1Y.ReflectionTupleTools

/-! 实际符号表逐项实现=、<、R、P、规范化e和ω；也适用于κ的子载域。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Satisfaction
universe u

theorem ArticleInterpretation.body_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain}
    (hC : C.Valid M) {A : M.Domain} {D : RelationalData M.Domain} (h : ArticleInterpretation M C A D)
    (i : Fin 6) {t : M.Domain} (hG : Graph M t (C.numbers (symbolArity i)) A) :
    MemPair M D.interpretation (C.numbers i.castSucc) t ↔ Body M C i t :=
  (h.kind_iff_d hM hC i t).trans ⟨And.right,fun hBody => ⟨hG,hBody⟩⟩

theorem ArticleInterpretation.equality_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain}
    (hC : C.Valid M) {A : M.Domain} {D : RelationalData M.Domain} (h : ArticleInterpretation M C A D) (hSub : M.MemberSubset A C.top)
    {t x y : M.Domain} (hG : Graph M t (C.numbers 2) A) (h0 : MemPair M t (C.numbers 0) x) (h1 : MemPair M t (C.numbers 1) y) :
    MemPair M D.interpretation (C.numbers 0) t ↔ x=y :=
  (h.body_iff_d hM hC 0 hG).trans (binary_body_at hM.1 false (hG.mono_values hSub) h0 h1)

theorem ArticleInterpretation.less_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain}
    (hC : C.Valid M) {A : M.Domain} {D : RelationalData M.Domain} (h : ArticleInterpretation M C A D) (hSub : M.MemberSubset A C.top)
    {t x y : M.Domain} (hG : Graph M t (C.numbers 2) A) (h0 : MemPair M t (C.numbers 0) x) (h1 : MemPair M t (C.numbers 1) y) :
    MemPair M D.interpretation (C.numbers 1) t ↔ M.mem x y :=
  (h.body_iff_d hM hC 1 hG).trans (binary_body_at hM.1 true (hG.mono_values hSub) h0 h1)

theorem ArticleInterpretation.relation_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain}
    (hC : C.Valid M) {A : M.Domain} {D : RelationalData M.Domain} (h : ArticleInterpretation M C A D) (hSub : M.MemberSubset A C.top)
    {t k η a b : M.Domain} (hG : Graph M t (C.numbers 4) A)
    (h0 : MemPair M t (C.numbers 0) k) (h1 : MemPair M t (C.numbers 1) η)
    (h2 : MemPair M t (C.numbers 2) a) (h3 : MemPair M t (C.numbers 3) b) :
    MemPair M D.interpretation (C.numbers 2) t ↔ KP1Y.Reflection.Query M C.reflection.toIndexData C.table k η a b :=
  (h.body_iff_d hM hC 2 hG).trans (relation_body_at hM.1 (hG.mono_values hSub) h0 h1 h2 h3)

theorem ArticleInterpretation.top_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain}
    (hC : C.Valid M) {A : M.Domain} {D : RelationalData M.Domain} (h : ArticleInterpretation M C A D) (hSub : M.MemberSubset A C.top)
    {t k η a : M.Domain} (hG : Graph M t (C.numbers 3) A)
    (h0 : MemPair M t (C.numbers 0) k) (h1 : MemPair M t (C.numbers 1) η) (h2 : MemPair M t (C.numbers 2) a) :
    MemPair M D.interpretation (C.numbers 3) t ↔ KP1Y.Reflection.Query M C.reflection.toIndexData C.table k η a C.top :=
  (h.body_iff_d hM hC 3 hG).trans (top_body_at hM.1 (hG.mono_values hSub) h0 h1 h2)

theorem ArticleInterpretation.enumeration_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain}
    (hC : C.Valid M) {A : M.Domain} {D : RelationalData M.Domain} (h : ArticleInterpretation M C A D) (hSub : M.MemberSubset A C.top)
    {t a n x : M.Domain} (hG : Graph M t (C.numbers 3) A)
    (h0 : MemPair M t (C.numbers 0) a) (h1 : MemPair M t (C.numbers 1) n) (h2 : MemPair M t (C.numbers 2) x) :
    MemPair M D.interpretation (C.numbers 4) t ↔ EnumValue M C.reflection.omega C.enumKeys C.enumeration (C.numbers 0) a n x :=
  (h.body_iff_d hM hC 4 hG).trans (enumeration_body_at hM.1 (hG.mono_values hSub) h0 h1 h2)

theorem ArticleInterpretation.omega_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain}
    (hC : C.Valid M) {A : M.Domain} {D : RelationalData M.Domain} (h : ArticleInterpretation M C A D)
    {t x : M.Domain} (hG : Graph M t (C.numbers 1) A) (h0 : MemPair M t (C.numbers 0) x) :
    MemPair M D.interpretation (C.numbers 5) t ↔ x=C.reflection.omega :=
  (h.body_iff_d hM hC 5 hG).trans (constant_body_at hG h0)

theorem ArticleInterpretation.enumeration_total_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain}
    (hC : C.Valid M) {D : RelationalData M.Domain} (h : ArticleInterpretation M C C.top D)
    {a n : M.Domain} (ha : M.mem a C.top) (hn : M.mem n C.top) :
    ∃ x t, M.mem x C.top ∧ Graph M t (C.numbers 3) C.top ∧ MemPair M t (C.numbers 0) a ∧
      MemPair M t (C.numbers 1) n ∧ MemPair M t (C.numbers 2) x ∧ MemPair M D.interpretation (C.numbers 4) t := by
  obtain ⟨x,hx,hValue⟩ := enum_value_total_d hM hC.enumeration (hC.number_top 0) ha
  let vals : Fin 3 → M.Domain := Fin.cases a (Fin.cases n (fun _ => x))
  obtain ⟨t,hT,hRows⟩ := fixed_tuple_exists_d hM hC.numerals ⟨3,by decide⟩ vals (Fin.cases ha (Fin.cases hn (fun _ => hx)))
  have h0 : MemPair M t (C.numbers 0) a := hRows (0 : Fin 3)
  have h1 : MemPair M t (C.numbers 1) n := hRows (1 : Fin 3)
  have h2 : MemPair M t (C.numbers 2) x := hRows (2 : Fin 3)
  exact ⟨x,t,hx,hT,h0,h1,h2,(h.enumeration_d hM hC (fun _ h => h) hT h0 h1 h2).mpr hValue⟩

theorem ArticleInterpretation.enumeration_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain}
    (hC : C.Valid M) {D : RelationalData M.Domain} (h : ArticleInterpretation M C C.top D)
    {t u a n x y : M.Domain} (ht : Graph M t (C.numbers 3) C.top) (hu : Graph M u (C.numbers 3) C.top)
    (ht0 : MemPair M t (C.numbers 0) a) (ht1 : MemPair M t (C.numbers 1) n) (ht2 : MemPair M t (C.numbers 2) x)
    (hu0 : MemPair M u (C.numbers 0) a) (hu1 : MemPair M u (C.numbers 1) n) (hu2 : MemPair M u (C.numbers 2) y)
    (hEt : MemPair M D.interpretation (C.numbers 4) t) (hEu : MemPair M D.interpretation (C.numbers 4) u) : x=y :=
  enum_value_unique hM.1 hC.enumeration
    ((h.enumeration_d hM hC (fun _ h => h) ht ht0 ht1 ht2).mp hEt)
    ((h.enumeration_d hM hC (fun _ h => h) hu hu0 hu1 hu2).mp hEu)

end KP1Y.ReflectionModel
