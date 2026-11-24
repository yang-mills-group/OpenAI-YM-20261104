import YM.Integration.WilsonCapturedPrimaryWeakTrialRadial
import YM.Integration.WilsonCenteredCommonGerm
import YM.Integration.WilsonOriginalNullCalibrated

set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWeakTrialNonconstant
open Function Filter Finset Lattice RG Wilson Source Labels Extra.Histories RG17
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato WilsonCapturedPrimaryReading WilsonCapturedPrimaryWeakTileColumn
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G)
local notation "Fr" => R.family.labels.level 4
local notation "Sec" => R.family.localSection 4

private theorem other (simple : G.Simple) : ∃ a : (Fr).Index, a ≠ 0 := by
  letI : Nontrivial (Fr).Index := Fintype.one_lt_card_iff_nontrivial.mp (by
    rw [WilsonThermometerUnitFilingFourRank.original R.family simple]
    norm_num)
  exact exists_ne 0

def axis (simple : G.Simple) : (Fr).Index := (other R simple).choose
theorem axis_ne (simple : G.Simple) : axis R simple ≠ 0 := (other R simple).choose_spec

def entered (simple : G.Simple) : R.family.label 4 := (Fr).e0 + Pi.single (axis R simple) 1

theorem coordinates (simple : G.Simple) : entered R simple 0 = 1 ∧ entered R simple (axis R simple) = 1 := by
  simp [entered,Labels.Frame.e0,axis_ne R simple,Ne.symm (axis_ne R simple)]

theorem nodes_injective {i N per : ℕ} (D : ClockFace R 4 i N per) : Injective (node R D) := by
  intro a b eq
  by_contra ne
  let v := D.coinL.symm (Pi.single a 1)
  have same : D.coinL v a = D.coinL v b := by
    rw [D.register,D.register]
    change Next.Rank.Spindle.awakeFull R.family i N per v (node R D a) =
      Next.Rank.Spindle.awakeFull R.family i N per v (node R D b)
    rw [eq]
  simp [v,Pi.single_eq_of_ne (Ne.symm ne)] at same

theorem nonflat_tile (simple : G.Simple) {i N per : ℕ} (D : ClockFace R 4 i N per) :
    ∃ a, node R D a ≠ 1 := by
  by_contra! h
  exact axis_ne R simple ((nodes_injective R D) ((h _).trans (h 0).symm))

theorem physical (simple : G.Simple) {i N per : ℕ} (late : R.t 4 ≤ i) (live : i ≤ N)
    (q : Coefficient (Fr) (R.family.side i per)) (B : ℝ)
    (shape : q.Format 0 R.family.params (R.family.path.rep N per i))
    (charged : q.remBound 0 (R.family.path.rep N per i) (safety R.family i) B)
    (printed : projection (Fr) R.family.params (R.family.path.rep N per i).p.threshold 0 q = entered R simple) :
    ¬ ∃ z : ℂ, ∀ U, reading Sec (R.family.path.rep N per i) 0 q U = z := by
  let W := R.family.path.rep N per i
  have now : W.p = R.family.path.levels.budget i := (R.makes.wilson.represents N per i live).vac
  have read := (WilsonCapturedPrimarySection.original R late W now).1
  rintro ⟨z,every⟩
  let unity := Extra.Histories.primary (0 : Site (R.family.side i per)) (z • (Fr).e0)
  have paid : unity.remBound 0 W (1:ℝ) 0 := primary_rem (z • (Fr).e0) zero_lt_one
  have same (U) : q.density 0 Sec W U = unity.density 0 Sec W U := by
    have nv : (W.eval U : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Multi.AxisShift.chosen_positive R.makes.wilson live U).ne'
    have unit : part Sec 0 W U (Fr).e0 = 1 := by
      apply mul_left_cancel₀ nv
      rw [←primary_density,unit_density,mul_one]
    have h : q.density 0 Sec W U / (W.eval U : ℂ) = z := every U
    rw [show unity.density 0 Sec W U = (W.eval U : ℂ) * part Sec 0 W U (z • (Fr).e0) from
      primary_density ..,map_smul,smul_eq_mul,unit,mul_one]
    exact ((div_eq_iff nv).mp h).trans (mul_comm _ _)
  have equal := WilsonCenteredCommonGerm.original (P:=W) (Q:=W) rfl read shape
    (primary_format (H:=R.family.params) (z • (Fr).e0)) charged paid (fun _ => rfl) same
  change projection (Fr) R.family.params (R.family.path.rep N per i).p.threshold 0 q =
    projection (Fr) R.family.params W.p.threshold 0 (Extra.Histories.primary 0 (z • (Fr).e0)) at equal
  rw [printed,WilsonOriginalNullCalibrated.raw_page (Fr) R.family.params W 0 (z • (Fr).e0) read.order read.power] at equal
  have atAxis := congrFun equal (axis R simple)
  simp [Labels.Frame.e0,axis_ne R simple,(coordinates R simple).2] at atAxis

end YM.Integration.WilsonCapturedPrimaryWeakTrialNonconstant
