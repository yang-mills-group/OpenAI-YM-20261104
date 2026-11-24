import YM.Integration.WilsonOriginalClockFacePosterior
import YM.Integration.WilsonThermometerUnitFilingFourRank

/-! Read both fields on the same original tiles before taking their difference.
The inverse controls the whole raw finite column in the native paid norm. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWeakTileColumn
open Function Filter Lattice Wilson RG Next.Rank.Spindle RG17 Stationary
open PhysicalNext PhysicalNext.Repeat.Legato
open scoped Classical
variable {G : Gauge} (R : Run G) {d i N per : ℕ}
local notation "H" => R.family.path.levels.clock.hatBeta

def node (D : ClockFace R d i N per) (a : (R.family.labels.level d).Index) :
    Config G (R.family.side i per) :=
  net (R.family.path.rep N per i).p 0 (sizeQ R.family i) (D.tiles a).val

def column (D : ClockFace R d i N per) (Y : Config G (R.family.side i per) → ℂ) :
    R.family.label d :=
  D.coinL.symm (fun a => Y (node R D a))

theorem registered (D : ClockFace R d i N per) (Y : Config G (R.family.side i per) → ℂ)
    (a : (R.family.labels.level d).Index) :
    watchman R d i N per (column R D Y) (D.tiles a) = Y (node R D a) := by
  rw [← D.register]
  exact congrFun (D.coinL.apply_symm_apply _) a

@[simp] theorem column_zero (D : ClockFace R d i N per) :
    column R D (fun _ => 0) = 0 := D.coinL.symm.map_zero

theorem difference (D : ClockFace R d i N per) (Y Z : Config G (R.family.side i per) → ℂ) :
    column R D (fun U => Y U - Z U) = column R D Y - column R D Z :=
  D.coinL.symm.map_sub _ _

theorem trial (D : ClockFace R d i N per) (v : R.family.label d) :
    column R D (awakeFull R.family i N per v) = v := by
  apply D.coinL.injective
  funext a
  rw [D.register, registered, D.register]
  rfl

theorem original (simple : G.Simple)
    (width : ∀ᶠ j in atTop, (R.family.path.levels.params j).columns ≤ H j) (d : ℕ) :
    ∀ᶠ i in atTop, ∀ {N per : ℕ} (_live : i ≤ N) (D : ClockFace R d i N per)
      (Y Z : Config G (R.family.side i per) → ℂ) (e : ℝ),
      (∀ a, ‖Y (node R D a) - Z (node R D a)‖ ≤ e) →
      (∀ a, flags (R.family.path.rep N per i).p.threshold (node R D a) = ∅) ∧
      paid R.family d i N per (column R D Y - column R D Z) ≤
        (H i)^(3+6*d) * (2*(Fintype.card (R.family.labels.level d).Index : ℝ)*e) := by
  filter_upwards [paidThrough R.family d R.makes simple width] with i price
  intro N per live D Y Z e bounds
  have bought := price N per live
  refine ⟨fun a => bought.1 (D.tiles a).val (D.tiles a).property, bought.2 _ _ ?_⟩
  intro x hx
  apply D.modest _ e _ ⟨x,hx⟩
  intro a
  rw [← D.register, map_sub, Pi.sub_apply, D.register, D.register, registered, registered]
  exact bounds a

theorem four (simple : G.Simple)
    (width : ∀ᶠ j in atTop, (R.family.path.levels.params j).columns ≤ H j) :
    ∀ᶠ i in atTop, ∀ {N per : ℕ} (_live : i ≤ N) (D : ClockFace R 4 i N per)
      (Y Z : Config G (R.family.side i per) → ℂ) (e : ℝ),
      (∀ a, ‖Y (node R D a) - Z (node R D a)‖ ≤ e) →
      paid R.family 4 i N per (column R D Y - column R D Z) ≤ 44*(H i)^27*e := by
  filter_upwards [original R simple width 4] with i enrolled N per live D Y Z e bounds
  have h := (enrolled live D Y Z e bounds).2
  rw [WilsonThermometerUnitFilingFourRank.original R.family simple] at h
  exact h.trans_eq (by norm_num; ring)

end YM.Integration.WilsonCapturedPrimaryWeakTileColumn
