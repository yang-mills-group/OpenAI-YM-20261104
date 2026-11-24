import YangMills.WilsonProof.Hierarchy
import YangMills.WilsonProof.TreePowers

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSharpPhysicalTreeGeometry
open YangMills YangMills.Hierarchy Function Finset OPE OPE.Orbits OPE.Orbits.Reader OPE.Nesting Spec Table
open scoped Classical BigOperators
variable {g : YangMills.GaugeGroup} {C : Family g.core} {f : Extraction.Order} {S : Table C.book}
variable (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
theorem grouped_eq {I J : Type} [Fintype I] [Fintype J] (s : Viewers F)
    (a : I → S.Tag) (x : I → E4) (b : J → S.Tag) (y : J → E4) :
    (YangMills.hierarchy F Q).grouped s a x b y =
      whole (spectator F s) x (fun i => (a i).2) y (fun j => (b j).2) := by
  apply congrArg (S.useAt (spectator F s) _)
  funext k
  change (Sum.elim a b) (YM.OPE.runNames (I ⊕ J) k) = _
  generalize YM.OPE.runNames (I ⊕ J) k = e
  cases e <;> rfl

variable {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
theorem coef_permute (e : I ≃ J) (a : J → S.Tag) (x : J → E4) (o : E4) (m : ℕ) (c : Q.channels m) :
    Q.coef m c (x ∘ e) (fun i => (a (e i)).2) o = Q.coef m c x (fun j => (a j).2) o := by
  apply congrArg (fun v : Q.stratum m => (Q.basis m).repr v c)
  apply Subtype.ext
  exact Q.fresh_perm m x o (fun j => (a j).2) e

theorem public_truncation (q : Viewers F) (a : I → S.Tag) (x : I → E4) (o : E4)
    (b : K → S.Tag) (y : K → E4) (h : ℕ) :
    (YangMills.hierarchy F Q).truncatedWithSpectators h q a x o b y =
      trunc (spectator F q) F Q h x o (fun i => (a i).2) y (fun j => (b j).2) := by
  simp only [YangMills.Hierarchy.truncatedWithSpectators, grouped_eq, trunc]; rfl

theorem grouped_permute (e : I ≃ J) (q : Viewers F) (a : J → S.Tag) (x : J → E4)
    (b : K → S.Tag) (y : K → E4) (hx : Injective (beside x y)) :
    (YangMills.hierarchy F Q).grouped q (a ∘ e) (x ∘ e) b y =
      (YangMills.hierarchy F Q).grouped q a x b y := by
  simp only [grouped_eq]
  exact whole_perm (S := S) (d := fun i => (a i).1) (e := fun j => (b j).1)
    (spectator F q) e (Equiv.refl K) (x := x) (v := fun i => (a i).2) (y := y) (w := fun j => (b j).2) (spectate F q) hx

theorem truncated_permute (e : I ≃ J) (q : Viewers F) (a : J → S.Tag) (x : J → E4)
    (o : E4) (b : K → S.Tag) (y : K → E4) (h : ℕ) :
    (YangMills.hierarchy F Q).truncatedWithSpectators h q (a ∘ e) (x ∘ e) o b y =
      (YangMills.hierarchy F Q).truncatedWithSpectators h q a x o b y := by
  unfold YangMills.Hierarchy.truncatedWithSpectators
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro c hc
  exact congrArg (fun z : ℂ => z * _) (coef_permute F Q e a x o m c)

theorem original_injective (e : I ≃ J) {x : J → E4} {y : K → E4}
    (h : Injective (beside (x ∘ e) y)) : Injective (beside x y) := by
  let renameSeats := e.symm.sumCongr (Equiv.refl K)
  have atName (i : J ⊕ K) : beside (x ∘ e) y (renameSeats i) = beside x y i := by
    cases i <;> simp [renameSeats, beside]
  intro i j eq
  exact renameSeats.injective (h ((atName i).trans (eq.trans (atName j).symm)))

end YM.Integration.WilsonSharpPhysicalTreeGeometry
