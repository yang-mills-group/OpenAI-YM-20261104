import YM.Integration.WilsonThermometerPositionFilmPupil

/-! On the original side the copy pupil is the literal finite Wilson material. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerPositionFilmSelf
open Function Filter Finset Lattice Wilson RG Precision Tree
open QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise Marker Laurent AllOrder.Floe
open Further.PhysicalPeriodLimitF933 Macrame Shingle AllOrder.Ker
open Comparison.RG02 FVA1Physical FVA1Physical.TwoReset
open scoped BigOperators Classical

private theorem originalSite {n:Side} (x:Site n) (u:Fin (Pages n n)) :
    (page (dvd_refl n.val) x u).val=x := by
  have h:=(page (dvd_refl n.val) x u).property
  simp only [parcel,Finset.mem_filter,Finset.mem_univ,true_and] at h
  have eqn (y:Site n): splitter (dvd_refl n.val) y=y := by
    simpa only [wrap_lift] using Macrame.branch (dvd_refl n.val) (lift y)
  exact (eqn _).symm.trans h

variable {G:Gauge} {n:Side} {V ι α:Type} [DecidableEq V] {J:Passport n V} {R:Census V}
variable (M:ι→Row J R G α) (w:V→ℕ) (L:Layout G) (T:Finset Age) (q:ι→ℂ)
private theorem one (u:Fin (Pages n n)) (s:Multi.Hot R) :
    (Air.craft (fun j=>TwoReset.copy (dvd_refl n.val) (M j) u) q w L T).mark s =
      (Air.craft M q w L T).mark s := by
  funext t U
  unfold Air.craft QuadraticLocal.Fk.grant Air.sums
  apply tsum_congr
  intro j
  simp only [ScatterR.actor,ScatterR.familyAt,recenter,originalSite]
  rfl

theorem original :
    copyColor (dvd_refl n.val) M w q L T=Air.craft M q w L T := by
  have h:Pages n n=1:=by simp [Pages]
  unfold copyColor
  congr 1
  funext s
  change (∑ u:Fin (Pages n n), (Air.craft (fun j=>TwoReset.copy (dvd_refl n.val) (M j) u) q w L T).mark s)=_
  simp only [one M w L T q,Finset.sum_const,Finset.card_univ,Fintype.card_fin,h,one_nsmul]
  rfl

theorem pupil (x:α) (d:ℕ) (A:Stationary.Link G n) :
    peek (dvd_refl n.val) M w L T x d A=Air.discharge (Air.craft M (fun i=>(M i).paint x) w L T) d
      (Stationary.arm G n 1 A) := by rw [peek,original]

end YM.Integration.WilsonThermometerPositionFilmSelf
