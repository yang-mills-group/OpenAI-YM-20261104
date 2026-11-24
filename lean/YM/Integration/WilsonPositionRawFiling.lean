import YM.Integration.WilsonPositionRawMesh
import YM.Integration.WilsonIndependentSchemeTruncation
import YM.FVA2.Coupling.Frames

/-! The retained joint polynomial is the original finite Wilson publication
in its own variable, with the same change on every external field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionRawFiling
open Finset Function Set Filter Maxwell XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open FVA2 FVA2.Register FVA2.Scale MS MS.WilsonBridge.Coupling PowerSeries
open WilsonPositionRawMesh
open scoped BigOperators Classical Polynomial
variable {G : Gauge} (Z : WilsonPrescription G) (m : Mesh)

def key : Key := ⟨Rose.chosen Z.scheme Z.criterion m, Rose.zero_choice ..,
  RealK.sounds (Rose.real_c Z.scheme Z.criterion m)⟩

def published (d : ℕ) : Reports G d :=
  realm ((key Z m).gate (Scale.Measure.adjust Z.scheme Z.criterion d)) (Z.store.opens Z.scheme m d)

theorem recovered (use : Rose.Use Z.scheme Z.criterion m) (d : ℕ) :
    (key Z m).mix (Scale.System.positions Z.scheme Z.criterion d m) = published Z m d := by
  have report : (key Z m).mix (Rose.proposed Z.scheme Z.criterion m d) = Z.store.opens Z.scheme m d := by
    funext e n
    ext φ v
    have inverse : said (Rose.proposed Z.scheme Z.criterion m d) φ v =
        subst (Rose.χ Z.scheme Z.criterion m) (said (Z.store.opens Z.scheme m d) φ v) := by
      apply PowerSeries.ext
      intro j
      rw [said, coeff_mk, Rose.sent]
      exact Rose.turn_coins .. 
    have h := (key Z m).reports_mix (Rose.proposed Z.scheme Z.criterion m d) φ v
    rw [Key.sent,inverse,subst_comp_subst_apply
      (Rose.χday Z.scheme Z.criterion m) (key Z m).has] at h
    change said _ φ v = subst (subst (Rose.chosen Z.scheme Z.criterion m) (Rose.χ Z.scheme Z.criterion m)) _ at h
    rw [Rose.χverts Z.scheme Z.criterion m use, X_subst] at h
    exact (coeff_mk ..).symm.trans ((congrArg (coeff e) h).trans (coeff_mk ..))
  rw [published,← report,Key.compatiblePS]

theorem fieldwise (use : Rose.Use Z.scheme Z.criterion m) (d : ℕ) {n : ℕ} (φ : Test n) (v : Tags G d n) :
    subst (Rose.chosen Z.scheme Z.criterion m) (said (Scale.System.positions Z.scheme Z.criterion d m) φ v) =
      said (published Z m d) φ v := by
  rw [← recovered Z m use, Key.reports_mix, Key.sent]
  rfl

theorem late (hG : G.Simple) : ∀ᶠ i : ℕ in atTop, ∀ d,
    (key Z (Z.run.step i)).mix (Scale.System.positions Z.scheme Z.criterion d (Z.run.step i)) =
      published Z (Z.run.step i) d := by
  filter_upwards [(goesFront (Expense.Stretched.runs Z.run)).eventually (Rose.usable Z.scheme Z.criterion hG)] with i hi
  exact recovered Z _ hi

end YM.Integration.WilsonPositionRawFiling
