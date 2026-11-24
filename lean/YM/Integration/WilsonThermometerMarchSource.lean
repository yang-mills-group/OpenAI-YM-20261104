import YM.Integration.WilsonThermometerMarchRoster
import YM.Integration.WilsonThermometerNominatedSource

/-! The nominated Vane leg in its actual own-site circuit, with the
one-time size and engineering factors kept outside the normalized source. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerMarchSource
open Function Filter Finset MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open RG.Shoot Marker PhysicalNext.Repeat.Legato RG05Readout Native Address Many RG05Readout.Records
open RG17 Trace.Pilot Climb Table Spec WilsonPositionThermometerCapStation
open WilsonPositionThermometerGradedReading WilsonPositionThermometerGradedSource
open WilsonThermometerNominatedSource WilsonThermometerOwnOffsetField
open scoped Classical Topology
variable {G : Gauge}

def charge {C : Family G} {d : ℕ} (y : Palette C d) : ℝ := max 1 (size y)

def reduce {C : Family G} {d : ℕ} (y : Palette C d) : Palette C d := ((charge y:ℝ):ℂ)⁻¹ • y

theorem charged {C : Family G} {d : ℕ} (y : Palette C d) : 0 < charge y :=
  zero_lt_one.trans_le (le_max_left ..)

theorem small {C : Family G} {d : ℕ} (y : Palette C d) : size (reduce y) ≤ 1 := by
  rw [reduce, size_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (charged y), ←div_eq_inv_mul]
  exact (div_le_one (charged y)).mpr (le_max_right ..)

variable (R : Run G) (A : Group R.family 6) {m N p : ℕ}
local notation "d" => (fun i : Fin 3 => (grade i).val)
local notation "w" => vector A (Finset.univ : Finset (Fin 3))

def coordinate (r : (i : Fin 3) → Emblems R.family (d i)) (hm : m ≤ N) (i : Fin 3) :=
  own R.family (per:=p) (r i) hm (A.station.wheel.atCut (N,p) (index A (grade i)) ((w) i))

def weight (r : (i : Fin 3) → Emblems R.family (d i)) (hm : m ≤ N) (i : Fin 3) : ℂ :=
  ((R.family.S.a m:ℂ)^(d i)) * ((charge (coordinate R A (p:=p) r hm i):ℝ):ℂ)⁻¹

theorem leg (r : (i : Fin 3) → Emblems R.family (d i)) (hm : m ≤ N)
    (z : Fin 3 → Site (R.family.side N p)) (i : Fin 3) :
    WilsonThermometerIntrinsicRoster.source R d z (fun j => reduce (coordinate R A (p:=p) r hm j)) r hm i =
      weight R A (p:=p) r hm i • R.family.O N p
        (A.station.wheel.atCut (N,p) (index A (grade i)) ((w) i)) (z i) := by
  let y := coordinate R A (p:=p) r hm i
  let x := A.station.wheel.atCut (N,p) (index A (grade i)) ((w) i)
  have head : (R.family.factory (d i) N p).terminal (finer (r i) hm (reduce y) (primaryLetter (d i))) =
      ((charge y:ℝ):ℂ)⁻¹ • x := by
    rw [reduce,map_smul,Pi.smul_apply]
    exact ((R.family.factory (d i) N p).terminal.map_smul ((charge y:ℝ):ℂ)⁻¹
      (finer (r i) hm y (primaryLetter (d i)))).trans
        (congrArg (((charge y:ℝ):ℂ)⁻¹ • ·) (fired R.family (per:=p) (r i) hm x))
  unfold WilsonThermometerIntrinsicRoster.source WilsonThermometerOwnOffsetNectar.birth
  rw [head]
  change ((R.family.S.a m:ℂ)^(d i)) • (R.family.O N p (((charge y:ℝ):ℂ)⁻¹ • x) (z i)) =
    (((R.family.S.a m:ℂ)^(d i))*((charge y:ℝ):ℂ)⁻¹) • (R.family.O N p x (z i))
  exact (congrArg (((R.family.S.a m:ℂ)^(d i)) • ·)
    ((R.family.linearO N p (d i) (z i)).map_smul ((charge y:ℝ):ℂ)⁻¹ x)).trans (smul_smul ..)

end YM.Integration.WilsonThermometerMarchSource
