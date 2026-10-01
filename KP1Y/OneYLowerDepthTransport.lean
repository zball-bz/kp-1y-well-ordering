import KP1Y.OneYLowerValueTransport
import KP1Y.OneYForestDecoratedOrder
import KP1Y.OneYSparseDepth
import KP1Y.OneYSelectionDepth

/-! 源数值山形的真实深度正规性，以及Lower的低/填充/抬升深度运输。 -/
namespace KP1Y.OneYFinite.CopiedMountain.Lower
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
universe u

/-- DepthRegular由真实源RowRun导出，不作为目标重建前提。 -/
theorem source_depth_selection_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) {X : Data M.Domain} (hFrom : FromRun M C m R V H X)
    {r s F Q Depths : M.Domain} (hNext : M.SuccessorOf s r) (hF : MemPair M X.parents r F) (hQ : MemPair M X.parents s Q)
    (hDepths : Graph M Depths X.width C.omega) (hRows : ∀c d, MemPair M Depths c d ↔ Depth M C X.width Q c d) :
    Selects false M C X.width F Depths Q := by
  obtain ⟨U,hAtF⟩ := (hFrom.parents r F).mp hF
  obtain ⟨W,hAtQ⟩ := (hFrom.parents s Q).mp hQ
  exact hFrom.width.symm ▸ hRun.next_depth_selection_d hM hC hNext hAtF hAtQ (hFrom.width ▸ hDepths)
    (fun c d => hFrom.width ▸ hRows c d)

theorem source_parent_rows_of_previous_depth_eq_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) {X : Data M.Domain} (hX : X.Valid M C) (hFrom : FromRun M C m R V H X)
    {r s F Q c z d : M.Domain} (hNext : M.SuccessorOf s r) (hF : MemPair M X.parents r F) (hQ : MemPair M X.parents s Q)
    (hSame : ParentRowsEqual M F c z) (hCDepth : Depth M C X.width Q c d) (hZDepth : Depth M C X.width Q z d) :
    ParentRowsEqual M Q c z := by
  obtain ⟨Depths,hDepths,hRows⟩ := depth_graph_exists_d hM hC (hX.forest s Q hQ)
  have hSelection := source_depth_selection_d hM hC hRun hFrom hNext hF hQ
    (hDepths.mono_values (fun d hd => (omega_isOrdinal_d hM hC.omega).transitive X.width hX.width d hd)) hRows
  exact hSelection.parent_rows_eq_of_common_chain_value_d hM
    (fun p => ancestor_iff_of_parent_rows_eq_d hM hC (hX.forest r F hF) hSame p)
    ((hRows c d).mpr hCDepth) ((hRows z d).mpr hZDepth)

theorem source_ancestor_mono_of_previous_depth_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) {X : Data M.Domain} (hX : X.Valid M C) (hFrom : FromRun M C m R V H X)
    {r s F Q c z a dc dz : M.Domain} (hNext : M.SuccessorOf s r) (hF : MemPair M X.parents r F) (hQ : MemPair M X.parents s Q)
    (hSame : ParentRowsEqual M F c z) (hCDepth : Depth M C X.width Q c dc) (hZDepth : Depth M C X.width Q z dz)
    (hLe : dc=dz ∨ M.mem dc dz) (hAnc : Ancestor M C X.width Q a c) : Ancestor M C X.width Q a z := by
  obtain ⟨Depths,hDepths,hRows⟩ := depth_graph_exists_d hM hC (hX.forest s Q hQ)
  have hSelection := source_depth_selection_d hM hC hRun hFrom hNext hF hQ
    (hDepths.mono_values (fun d hd => (omega_isOrdinal_d hM hC.omega).transitive X.width hX.width d hd)) hRows
  exact hSelection.ancestor_mono_of_common_chain_d hM hC
    (fun p => ancestor_iff_of_parent_rows_eq_d hM hC (hX.forest r F hF) hSame p)
    ((hRows c dc).mpr hCDepth) ((hRows z dz).mpr hZDepth) hLe hAnc

end KP1Y.OneYFinite.CopiedMountain.Lower
