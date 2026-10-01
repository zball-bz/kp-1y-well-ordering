import KP1Y.ProjectNamingAtoms

/-! 每个自由闭合集合公式的命名转换正确；量词新名字避开旧环境，subset展开语义精确。 -/
namespace KP1Y.Named
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Classes
universe u

theorem encode_correct {M : SetTheory.Structure.{u}} (he : Extensional M) {A : M.Domain}
    (hA : M.TransitiveSet A) {hNe : ∃ x, M.mem x A} {n k : Nat}
    (φ : Project.Formula 1 n) (hClosed : φ.FreeClosed) (fallback : Fin k) (ρ : Fin n → Fin k)
    (fresh : Nat) (hBound : fresh+extraDepth φ≤k) (hNames : ∀ i, (ρ i).val<fresh)
    (vals : Fin k → M.Domain) (s : Env (classModel M (fun x => M.mem x A) hNe) n) (hMatch : ValueMatch ρ vals s) :
    Holds M A vals (encode fallback φ ρ fresh hBound) ↔ Project.Formula.satisfies s φ := by
  induction φ generalizing fresh vals with
  | falsum =>
      simp only [encode,Project.Formula.satisfies_falsum_iff]
      exact iff_of_false (not_holds_falsum A vals fallback) id
  | truth =>
      simp only [encode,Project.Formula.satisfies_truth_iff]
      exact ⟨fun _ => True.intro,fun _ => holds_truth A vals fallback⟩
  | mem a b =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      exact encoded_member_iff fallback ρ vals s hMatch a b hClosed.1 hClosed.2
  | atom symbol hs args =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      cases symbol with
      | extensionalEq => exact encoded_equality_iff he hA fallback ρ vals s hMatch args hClosed hs
      | subset =>
          exact encoded_subset_iff fallback ρ vals s hMatch hNames ⟨fresh,by simp only [extraDepth] at hBound; omega⟩ rfl args hClosed hs
  | neg φ ih =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      simp only [encode,Holds,Project.Formula.satisfies_neg_iff]
      exact not_congr (ih hClosed ρ fresh hBound hNames vals s hMatch)
  | conj φ ψ ihφ ihψ =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      simp only [encode,holds_conj_iff,Project.Formula.satisfies_conj_iff]
      exact and_congr
        (ihφ hClosed.1 ρ fresh (by simp only [extraDepth] at hBound; omega) hNames vals s hMatch)
        (ihψ hClosed.2 ρ fresh (by simp only [extraDepth] at hBound; omega) hNames vals s hMatch)
  | disj φ ψ ihφ ihψ =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      simp only [encode,holds_disj_iff,Project.Formula.satisfies_disj_iff]
      exact or_congr
        (ihφ hClosed.1 ρ fresh (by simp only [extraDepth] at hBound; omega) hNames vals s hMatch)
        (ihψ hClosed.2 ρ fresh (by simp only [extraDepth] at hBound; omega) hNames vals s hMatch)
  | imp φ ψ ihφ ihψ =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      simp only [encode,Holds,Project.Formula.satisfies_imp_iff]
      exact imp_congr
        (ihφ hClosed.1 ρ fresh (by simp only [extraDepth] at hBound; omega) hNames vals s hMatch)
        (ihψ hClosed.2 ρ fresh (by simp only [extraDepth] at hBound; omega) hNames vals s hMatch)
  | iff φ ψ ihφ ihψ =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      simp only [encode,holds_iff_iff,Project.Formula.satisfies_iff_iff]
      exact iff_congr
        (ihφ hClosed.1 ρ fresh (by simp only [extraDepth] at hBound; omega) hNames vals s hMatch)
        (ihψ hClosed.2 ρ fresh (by simp only [extraDepth] at hBound; omega) hNames vals s hMatch)
  | forallE φ ih =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      have hv : fresh<k := by simp only [extraDepth] at hBound; omega
      let v : Fin k := ⟨fresh,hv⟩
      have hBound' : fresh+1+extraDepth φ≤k := by simp only [extraDepth] at hBound; omega
      have hNames' := extended_names_bounded hNames v rfl
      have hBody (x : (classModel M (fun x => M.mem x A) hNe).Domain) :=
        ih hClosed (Fin.cases v ρ) (fresh+1) hBound' hNames' (setValue vals v x.val) (s.push x)
          (hMatch.updated v (old_name_ne_fresh hNames v rfl) x)
      simp only [encode,Holds,Project.Formula.satisfies_forall_iff]
      constructor
      · intro h x
        exact (hBody x).mp (h x.val x.property)
      · intro h x hx
        exact (hBody ⟨x,hx⟩).mpr (h ⟨x,hx⟩)
  | existsE φ ih =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      have hv : fresh<k := by simp only [extraDepth] at hBound; omega
      let v : Fin k := ⟨fresh,hv⟩
      have hBound' : fresh+1+extraDepth φ≤k := by simp only [extraDepth] at hBound; omega
      have hNames' := extended_names_bounded hNames v rfl
      have hBody (x : (classModel M (fun x => M.mem x A) hNe).Domain) :=
        ih hClosed (Fin.cases v ρ) (fresh+1) hBound' hNames' (setValue vals v x.val) (s.push x)
          (hMatch.updated v (old_name_ne_fresh hNames v rfl) x)
      simp only [encode,holds_exists_iff,Project.Formula.satisfies_exists_iff]
      constructor
      · rintro ⟨x,hx,h⟩
        exact ⟨⟨x,hx⟩,(hBody ⟨x,hx⟩).mp h⟩
      · rintro ⟨x,h⟩
        exact ⟨x.val,x.property,(hBody x).mpr h⟩

end KP1Y.Named
