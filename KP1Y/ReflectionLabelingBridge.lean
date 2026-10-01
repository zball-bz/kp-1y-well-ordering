import KP1Y.ReflectionIncreasingBlock
import KP1Y.ReflectionPrefixBlock

/-! 将当前赋值载域中的标签条件恢复为文稿 cap 载域上的字面条件。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Reflection
universe u

def PositiveLabels (M : SetTheory.Structure.{u}) (C : Data M.Domain) (f m A : M.Domain) : Prop :=
  ∀ i, M.mem i m → ∀ x, M.mem x A → MemPair M f i x → M.mem C.omega x

theorem labeling_iff_positive_increasing {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : Data M.Domain} {f m A : M.Domain} (hm : M.mem m C.omega)
    (hF : Graph M f m A) (hSub : M.MemberSubset A C.cap) :
    Labeling M C m f ↔ PositiveLabels M C f m A ∧ Increasing M f m A := by
  constructor
  · intro h
    exact ⟨fun i hi x hx hAt => h.above i hi x (hSub x hx) hAt,
      fun i hi j hj hij x hx y hy hIx hJy => h.increasing i hi j hj hij x (hSub x hx) y (hSub y hy) hIx hJy⟩
  · rintro ⟨hPos,hInc⟩
    exact ⟨hm,hF.mono_values hSub,fun i hi x _ hAt => hPos i hi x (hF.bounds he hAt).2 hAt,
      increasing_enlarge he hF hInc⟩

theorem below_iff_on_carrier {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : Data M.Domain} {f m A b : M.Domain} (hF : Graph M f m A) (hSub : M.MemberSubset A C.cap) :
    Below M C m f b ↔ ∀ i, M.mem i m → ∀ x, M.mem x A → MemPair M f i x → M.mem x b :=
  ⟨fun h i hi x hx hAt => h i hi x (hSub x hx) hAt,
    fun h i hi x _ hAt => h i hi x (hF.bounds he hAt).2 hAt⟩

theorem prefix_iff_on_carrier {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : Data M.Domain} {f g m c A : M.Domain} (hF : Graph M f m A) (hG : Graph M g m A)
    (hSub : M.MemberSubset A C.cap) : PrefixAgree M C f g c ↔ PrefixValues M f g c A :=
  ⟨fun h i hi x hx => h i hi x (hSub x hx),prefix_values_enlarge he hF hG⟩

end KP1Y.ReflectionModel
