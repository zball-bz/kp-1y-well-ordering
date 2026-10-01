import KP1Y.ReflectionModelBodies

/-! 在实际元组图上读取六种解释的精确数学含义。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions
universe u

theorem binary_body_at {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ArticleData M.Domain}
    {t n x y : M.Domain} (strict : Bool) (hG : Graph M t n C.top)
    (h0 : MemPair M t (C.numbers 0) x) (h1 : MemPair M t (C.numbers 1) y) :
    BinaryBody strict M C t ↔ (if strict then M.mem x y else x=y) := by
  constructor
  · rintro ⟨x',_,y',_,h0',h1',hPred⟩
    have hxx' := hG.unique (C.numbers 0) x' x h0' h0
    have hyy' := hG.unique (C.numbers 1) y' y h1' h1
    subst x'
    subst y'
    exact hPred
  · intro hPred
    exact ⟨x,(hG.bounds he h0).2,y,(hG.bounds he h1).2,h0,h1,hPred⟩

theorem relation_body_at {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ArticleData M.Domain}
    {t n k η a b : M.Domain} (hG : Graph M t n C.top)
    (h0 : MemPair M t (C.numbers 0) k) (h1 : MemPair M t (C.numbers 1) η)
    (h2 : MemPair M t (C.numbers 2) a) (h3 : MemPair M t (C.numbers 3) b) :
    RelationBody false M C t ↔ KP1Y.Reflection.Query M C.reflection.toIndexData C.table k η a b := by
  constructor
  · rintro ⟨k',_,η',_,a',_,h0',h1',h2',b',_,h3',hQuery⟩
    have hkk' := hG.unique (C.numbers 0) k' k h0' h0
    have hηη' := hG.unique (C.numbers 1) η' η h1' h1
    have haa' := hG.unique (C.numbers 2) a' a h2' h2
    have hbb' := hG.unique (C.numbers 3) b' b h3' h3
    subst k'
    subst η'
    subst a'
    subst b'
    exact hQuery
  · intro hQuery
    exact ⟨k,(hG.bounds he h0).2,η,(hG.bounds he h1).2,a,(hG.bounds he h2).2,h0,h1,h2,
      b,(hG.bounds he h3).2,h3,hQuery⟩

theorem top_body_at {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ArticleData M.Domain}
    {t n k η a : M.Domain} (hG : Graph M t n C.top)
    (h0 : MemPair M t (C.numbers 0) k) (h1 : MemPair M t (C.numbers 1) η) (h2 : MemPair M t (C.numbers 2) a) :
    RelationBody true M C t ↔ KP1Y.Reflection.Query M C.reflection.toIndexData C.table k η a C.top := by
  constructor
  · rintro ⟨k',_,η',_,a',_,h0',h1',h2',hQuery⟩
    have hkk' := hG.unique (C.numbers 0) k' k h0' h0
    have hηη' := hG.unique (C.numbers 1) η' η h1' h1
    have haa' := hG.unique (C.numbers 2) a' a h2' h2
    subst k'
    subst η'
    subst a'
    exact hQuery
  · intro hQuery
    exact ⟨k,(hG.bounds he h0).2,η,(hG.bounds he h1).2,a,(hG.bounds he h2).2,h0,h1,h2,hQuery⟩

theorem enumeration_body_at {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ArticleData M.Domain}
    {t length a n x : M.Domain} (hG : Graph M t length C.top)
    (h0 : MemPair M t (C.numbers 0) a) (h1 : MemPair M t (C.numbers 1) n) (h2 : MemPair M t (C.numbers 2) x) :
    EnumerationBody M C t ↔ EnumValue M C.reflection.omega C.enumKeys C.enumeration (C.numbers 0) a n x := by
  constructor
  · rintro ⟨a',_,n',_,x',_,h0',h1',h2',hValue⟩
    have haa' := hG.unique (C.numbers 0) a' a h0' h0
    have hnn' := hG.unique (C.numbers 1) n' n h1' h1
    have hxx' := hG.unique (C.numbers 2) x' x h2' h2
    subst a'
    subst n'
    subst x'
    exact hValue
  · intro hValue
    exact ⟨a,(hG.bounds he h0).2,n,(hG.bounds he h1).2,x,(hG.bounds he h2).2,h0,h1,h2,hValue⟩

theorem constant_body_at {M : SetTheory.Structure.{u}} {C : ArticleData M.Domain} {t length A x : M.Domain}
    (hG : Graph M t length A) (h0 : MemPair M t (C.numbers 0) x) : ConstantBody M C t ↔ x=C.reflection.omega := by
  constructor
  · exact fun h => hG.unique (C.numbers 0) x C.reflection.omega h0 h
  · intro he
    change MemPair M t (C.numbers 0) C.reflection.omega
    exact he ▸ h0

end KP1Y.ReflectionModel
