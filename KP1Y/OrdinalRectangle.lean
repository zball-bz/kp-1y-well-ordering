import KP1Y.OrdinalArithmeticLimits

/-! 序数矩形坐标(i,a)的显式编码κ·i+a：严格块界与单射性，不使用一般良序坍缩。 -/
namespace KP1Y.Arithmetic
open YesMetaZFC YesMetaZFC.SetTheory
universe u

def RectangleCode (M : SetTheory.Structure.{u}) (κ i a c : M.Domain) : Prop :=
  ∃ b, Product M κ i b ∧ Sum M b a c

theorem rectangle_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {κ i a : M.Domain}
    (hκ : M.IsOrdinal κ) (hi : M.IsOrdinal i) (ha : M.IsOrdinal a) : ∃ c, RectangleCode M κ i a c := by
  obtain ⟨b,hb⟩ := product_exists_d hM hκ hi
  obtain ⟨c,hc⟩ := sum_exists_d hM b ha
  exact ⟨c,b,hb,hc⟩

theorem rectangle_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {κ i a c c' : M.Domain}
    (h : RectangleCode M κ i a c) (h' : RectangleCode M κ i a c') : c=c' := by
  obtain ⟨b,hb,hc⟩ := h
  obtain ⟨b',hb',hc'⟩ := h'
  have hbb' := product_unique_d hM hb hb'
  subst b'
  exact sum_unique_d hM hc hc'

theorem RectangleCode.isOrdinal_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {κ i a c : M.Domain}
    (h : RectangleCode M κ i a c) : M.IsOrdinal c := by
  obtain ⟨b,hb,hc⟩ := h
  exact hc.isOrdinal_d hM (hb.isOrdinal_d hM)

theorem rectangle_bounded_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {κ I B i a c : M.Domain}
    (hBound : Product M κ I B) (h : RectangleCode M κ i a c) (hiI : M.mem i I) (ha : M.mem a κ) : M.mem c B := by
  obtain ⟨b,hb,hc⟩ := h
  obtain ⟨j,hs⟩ := SetTheory.KP.exists_successor (KP1Y.models_weakKP hM) i
  have hj := SetTheory.KP.successor_isOrdinal (KP1Y.models_weakKP hM) hb.right_ordinal hs
  obtain ⟨b',hb'⟩ := product_exists_d hM hb.left_ordinal hj
  have hSumNext := product_successor_d hM hs hb hb'
  have hcb' := sum_strict_right_d hM (hb.isOrdinal_d hM) hc hSumNext ha
  have hjI : M.MemberSubset j I := by
    intro x hx
    rcases (hs x).mp hx with hx | hSame
    · exact hBound.right_ordinal.transitive i hiI x hx
    · exact (hM.1.eq_of_same_members x i hSame) ▸ hiI
  exact product_mono_right_d hM ⟨a,ha⟩ hb' hBound hjI c hcb'

theorem rectangle_strict_first_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {κ i j a b c d : M.Domain}
    (h : RectangleCode M κ i a c) (h' : RectangleCode M κ j b d) (hij : M.mem i j) (ha : M.mem a κ) : M.mem c d := by
  obtain ⟨x,hx,hd⟩ := h'
  have hcx := rectangle_bounded_d hM hx h hij ha
  exact sum_base_subset_d hM (hx.isOrdinal_d hM) hd c hcx

theorem rectangle_strict_second_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {κ i a b c d : M.Domain}
    (h : RectangleCode M κ i a c) (h' : RectangleCode M κ i b d) (hab : M.mem a b) : M.mem c d := by
  obtain ⟨x,hx,hc⟩ := h
  obtain ⟨y,hy,hd⟩ := h'
  have hxy := product_unique_d hM hx hy
  subst y
  exact sum_strict_right_d hM (hx.isOrdinal_d hM) hc hd hab

theorem rectangle_injective_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {κ i j a b c d : M.Domain}
    (h : RectangleCode M κ i a c) (h' : RectangleCode M κ j b d)
    (ha : M.mem a κ) (hb : M.mem b κ) (hcd : c=d) : i=j ∧ a=b := by
  have hCopy := h
  have hCopy' := h'
  obtain ⟨x,hx,_⟩ := hCopy
  obtain ⟨y,hy,_⟩ := hCopy'
  have hi := hx.right_ordinal
  have hj := hy.right_ordinal
  have hκ := hx.left_ordinal
  have hw := KP1Y.models_weakKP hM
  rcases Structure.IsOrdinal.trichotomy hM.1 hi hj (SetTheory.KP.difference_exists_d hw)
    (SetTheory.KP.intersection_exists_d hw i j) with hSame | hij | hji
  · have hij := hM.1.eq_of_same_members i j hSame
    subst j
    refine ⟨rfl,?_⟩
    rcases hκ.wellOrder.linear.compare a ha b hb with hSame | hab | hba
    · exact hM.1.eq_of_same_members a b hSame
    · have hLess := rectangle_strict_second_d hM h h' hab
      rw [hcd] at hLess
      exact False.elim (SetTheory.KP.mem_irrefl_d hw d hLess)
    · have hLess := rectangle_strict_second_d hM h' h hba
      rw [hcd] at hLess
      exact False.elim (SetTheory.KP.mem_irrefl_d hw d hLess)
  · have hLess := rectangle_strict_first_d hM h h' hij ha
    rw [hcd] at hLess
    exact False.elim (SetTheory.KP.mem_irrefl_d hw d hLess)
  · have hLess := rectangle_strict_first_d hM h' h hji hb
    rw [hcd] at hLess
    exact False.elim (SetTheory.KP.mem_irrefl_d hw d hLess)

end KP1Y.Arithmetic
