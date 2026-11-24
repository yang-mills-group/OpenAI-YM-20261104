import YM.Integration.WilsonThermometerRegisteredAncestralProperTest
import YM.Integration.WilsonThermometerSupportedCells

/-! When the measured compensating coefficients are shared, a complete fixed-stop
model pupil and its source test use the exact same relative cell weights. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredCenteredFold
open Finset Lattice Wilson RG Extraction Cells RG12 XSpace
open PhysicalNext.Repeat.Legato WilsonThermometerAlignedCells
open scoped BigOperators Classical
variable {G:Gauge} (R:Run G) {N per:ℕ} (r:ℝ) (φ:Test 3)
local notation "Z" => ((N,per):UVIndex)
local notation "T" => Site (R.family.side N per)
local notation "χ" => WilsonSeparatedOriginalThermometerCells.positions (R:=R) r Z
local notation "W" x:max => WilsonSeparatedOriginalThermometerCells.weight φ χ x
local notation "μ" u:max => WilsonThermometerAlignedCells.mass (R:=R) r Z φ u
local notation "m₀" u:max => WilsonThermometerRegisteredAbsoluteRoom.mass R r Z φ u
local notation "Fine" => {x:Fin 3→T//W x≠0}
local notation "Grid" => {u:T×T//m₀ u≠0}
local notation "Obs" => WilsonThermometerSupportedCells.Occupied (N:=N) (per:=per) R r φ
local notation "key" x:max => WilsonThermometerRegisteredAncestralProperTest.key (N:=N) (per:=per) R r φ x
open private sum_triples from YM.Integration.WilsonThermometerAlignedCells

def admitted (y:Obs):Grid:=⟨y.val,by
  have real:‖μ y.val‖ ≤ m₀ y.val:=norm_sum_le _ _
  exact ne_of_gt ((norm_pos_iff.mpr y.property).trans_le real)⟩

theorem original (model:Grid→ℂ):
    (∑x:Fine,W x.val*model (key x))=∑y:Obs,μ y.val*model (admitted R r φ y):=by
  let ext (u:T×T):ℂ:=if h:m₀ u≠0 then model ⟨u,h⟩ else 0
  have atFine(x:Fine):ext (offsets x.val)=model (key x):=by
    unfold ext;split
    · rfl
    · rename_i dead;exact False.elim (dead (key x).property)
  have atObs(y:Obs):ext y.val=model (admitted R r φ y):=by
    unfold ext;split
    · rfl
    · rename_i dead;exact False.elim (dead (admitted R r φ y).property)
  calc
    _=∑x:Fine,W x.val*ext (offsets x.val):=Finset.sum_congr rfl fun x _=>by rw [atFine]
    _=∑x:Fin 3→T,W x*ext (offsets x):=WilsonThermometerSupportedCells.restricted (fun x:Fin 3→T=>W x≠0) (fun x=>W x*ext (offsets x)) (fun x off=>by
      rw [show W x=0 from not_ne_iff.mp off,zero_mul])
    _=∑y:T×T,μ y*ext y:=by
      rw [sum_triples];apply sum_congr rfl;intro y _
      rw [WilsonThermometerAlignedCells.mass,sum_mul];apply sum_congr rfl;intro c _
      have same:offsets (placedAt y c)=y:=by cases y;simp [placedAt,offsets,atOrigin]
      rw [same]
    _=∑y:Obs,μ y.val*ext y.val:=(WilsonThermometerSupportedCells.restricted (fun y:T×T=>μ y≠0) (fun y=>μ y*ext y) (fun y off=>by
      rw [show μ y=0 from not_ne_iff.mp off,zero_mul])).symm
    _=_:=Finset.sum_congr rfl fun y _=>by rw [atObs]

end YM.Integration.WilsonThermometerRegisteredCenteredFold
