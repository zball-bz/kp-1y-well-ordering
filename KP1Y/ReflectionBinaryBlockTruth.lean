import KP1Y.ReflectionBinaryBlock
import KP1Y.ReflectionBinarySemantics

/-! 二元代码块的全部原子真值等价于实际赋值上逐行比较；大小结构使用同一代码表。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments KP1Y.Satisfaction
universe u

def CompareSelectors (strict : Bool) (M : SetTheory.Structure.{u}) (X Y n scope A s : M.Domain) : Prop :=
  ∀ i, M.mem i n → ∀ u, M.mem u scope → ∀ v, M.mem v scope → MemPair M X i u → MemPair M Y i v →
    ∀ x, M.mem x A → ∀ y, M.mem y A → MemPair M s u x → MemPair M s v y → if strict then M.mem x y else x=y

private theorem block_truth_iff {M : SetTheory.Structure.{u}} {C : ArticleData M.Domain} {D : RelationalData M.Domain}
    {PC : Context M.Domain} {strict : Bool} {scope n X Y B A s : M.Domain} (hB : BinaryBlock M C D strict scope n X Y B)
    (hS : Graph M s scope A)
    (hEval : ∀ u v a x y, BinaryCode strict M (C.numbers 0) (C.numbers 1) (C.numbers 2) D.variables scope u v a →
      MemPair M s u x → MemPair M s v y → (MemPair M PC.atomic a s ↔ (if strict then M.mem x y else x=y))) :
    AllAtoms M PC D B n s ↔ CompareSelectors strict M X Y n scope A s := by
  constructor
  · intro hAll i hi u hu v hv hXu hYv x _ y _ hsx hsy
    obtain ⟨a,_,hBa,hTrue⟩ := hAll i hi
    have hCode := (hB.rows i hi u hu v hv hXu hYv a).mp hBa
    exact (hEval u v a x y hCode hsx hsy).mp hTrue
  · intro hCompare i hi
    obtain ⟨u,hu,hXu⟩ := hB.left.total i hi
    obtain ⟨v,hv,hYv⟩ := hB.right.total i hi
    obtain ⟨x,hx,hsx⟩ := hS.total u hu
    obtain ⟨y,hy,hsy⟩ := hS.total v hv
    obtain ⟨a,ha,hBa⟩ := hB.graph.total i hi
    have hCode := (hB.rows i hi u hu v hv hXu hYv a).mp hBa
    exact ⟨a,ha,hBa,(hEval u v a x y hCode hsx hsy).mpr (hCompare i hi u hu v hv hXu hYv x hx y hy hsx hsy)⟩

theorem BinaryBlock.all_atoms_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {A : M.Domain} {D : RelationalData M.Domain} (hD : ArticleInterpretation M C A D) {PC : Context M.Domain}
    (hAtom : AtomicTable M D PC.atomic) {strict : Bool} {scope n X Y B s : M.Domain}
    (hSub : M.MemberSubset A C.top) (hb : M.mem scope D.omega) (hB : BinaryBlock M C D strict scope n X Y B) (hS : Graph M s scope A) :
    AllAtoms M PC D B n s ↔ CompareSelectors strict M X Y n scope A s :=
  block_truth_iff hB hS (fun _ _ _ _ _ hCode hu hv => hCode.value_iff_d hM hC hD hAtom hSub hb hS hu hv)

theorem Height.binary_block_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {S : ArticleStructure M.Domain} (hS : S.Valid M C) {δ : M.Domain} {small : EvaluationData M.Domain} (h : Height M C S δ small)
    {strict : Bool} {scope n X Y B s : M.Domain} (hb : M.mem scope S.context.omega)
    (hB : BinaryBlock M C S.relations strict scope n X Y B) (hAssign : Graph M s scope small.carrier) :
    AllAtoms M (small.context S.context) S.relations B n s ↔ CompareSelectors strict M X Y n scope small.carrier s :=
  block_truth_iff hB hAssign (fun _ _ _ _ _ hCode hu hv => h.binary_value_iff_d hM hC hS hb hCode hAssign hu hv)

theorem compare_fixed_left_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {strict : Bool} {X Y n scope A s f u z : M.Domain}
    (hX : Graph M X n scope) (hConst : ∀ i, M.mem i n → MemPair M X i u) (hY : Graph M Y n scope)
    (hS : Graph M s scope A) (hu : M.mem u scope) (hz : MemPair M s u z) (hF : TupleValue M f Y s n scope A) :
    CompareSelectors strict M X Y n scope A s ↔ ∀ i, M.mem i n → ∀ x, M.mem x A → MemPair M f i x → if strict then M.mem z x else z=x := by
  constructor
  · intro h i hi x hx hAt
    obtain ⟨v,hv,hYv⟩ := hY.total i hi
    exact h i hi u hu v hv (hConst i hi) hYv z (hS.bounds he hz).2 x hx hz ((hF.rows i hi v hv x hx hYv).mp hAt)
  · intro h i hi u' _ v hv hXu hYv x _ y hy hsx hsy
    have huu' := hX.unique i u' u hXu (hConst i hi)
    subst u'
    have hxz := hS.unique u x z hsx hz
    subst x
    exact h i hi y hy ((hF.rows i hi v hv y hy hYv).mpr hsy)

theorem compare_fixed_right_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {strict : Bool} {X Y n scope A s f v z : M.Domain}
    (hX : Graph M X n scope) (hY : Graph M Y n scope) (hConst : ∀ i, M.mem i n → MemPair M Y i v)
    (hS : Graph M s scope A) (hv : M.mem v scope) (hz : MemPair M s v z) (hF : TupleValue M f X s n scope A) :
    CompareSelectors strict M X Y n scope A s ↔ ∀ i, M.mem i n → ∀ x, M.mem x A → MemPair M f i x → if strict then M.mem x z else x=z := by
  constructor
  · intro h i hi x hx hAt
    obtain ⟨u,hu,hXu⟩ := hX.total i hi
    exact h i hi u hu v hv hXu (hConst i hi) x hx z (hS.bounds he hz).2 ((hF.rows i hi u hu x hx hXu).mp hAt) hz
  · intro h i hi u hu v' _ hXu hYv x hx y _ hsx hsy
    have hvv' := hY.unique i v' v hYv (hConst i hi)
    subst v'
    have hyz := hS.unique v y z hsy hz
    subst y
    exact h i hi x hx ((hF.rows i hi u hu x hx hXu).mpr hsx)

end KP1Y.ReflectionModel
