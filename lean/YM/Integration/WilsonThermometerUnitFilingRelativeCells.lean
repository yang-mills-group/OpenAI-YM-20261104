import YM.Integration.WilsonThermometerUnitFilingRelative
import YM.Integration.WilsonThermometerUnitFilingSignedCells

/-! Signed connected measurement using only the relative cells issued on the ancestral course. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingRelativeCells
open Filter Function Finset MeasureTheory Lattice Wilson Labels RG Marker Source Extraction Table Spec
open Climb Trace.Pilot RG12 RG17 PhysMS PhysicalNext.Repeat.Legato
open MergeProof MergeProof.Accent MergeProof.East FVA1 OriginalForcedAddresses
open XSpace XSpace.Normalize XSpace.Rose Cells Push.GridApprox
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource WilsonPositionThermometerGradedReading
open WilsonThermometerCenteredAlgebra WilsonThermometerCenteredScalar WilsonThermometerAlignedCells
open WilsonThermometerUnitFilingRelative
open private proper from YM.Integration.WilsonThermometerUnitFilingSignedCells
open scoped BigOperators Classical Topology
variable {G:Gauge} (R:Run G) (A:Group R.family 6) (z:UVIndex) (r:ℝ) (φ:Test 3)
local notation "T!" => Site (R.family.side z.1 z.2)
local notation "J!" => Stock.census (Fin 3)
local notation "μ!" => WilsonThermometerAlignedCells.mass (R:=R) r z φ
local notation "χ!" => WilsonSeparatedOriginalThermometerCells.positions (R:=R) r z
abbrev measured (c:Grid R z r φ): Poly J! :=
  WilsonThermometerCenteredCredit.table R A z (WilsonThermometerRegisteredCells.placement (R:=R) z c.val)
variable (Q:Grid R z r φ→Poly (Stock.census (Fin 3)))
def reference : ℂ :=∑c:Grid R z r φ,μ! c.val * WilsonPositionThermometerConnected.value (read (Q c))

private theorem expense (data:(T!×T!)→(Badge→ℂ)→ℂ)
    (ready:∀i,R.family.ref (grade i).val ≤ z.1):
    φ.applyTo (fun x=>data (offsets (χ! x)) (row A z (χ! x)))=
      ∑c:Grid R z r φ,μ! c.val * data c.val (row A z (atOrigin c.val)):=by
  rw [WilsonThermometerAlignedCells.tested A r z ready φ data,
    WilsonThermometerSupportedCells.restricted (fun y:T!×T!=>μ! y≠0)
      (fun y=>μ! y*data y (row A z (atOrigin y))) (by intro y h;simp [not_not.mp h])]

theorem original {f:Extraction.Order} {H:(Bel R.family.book).Hierarchy} (checked:A.station.checked f H A.horizon)
    (unit:∀ t:Fin 7,A.change t ((Bel R.family.book).unit t)=(Bel R.family.book).unit t):
    ∀ᶠ z:UVIndex in f.fuse,(∀i,R.family.ref (grade i).val ≤z.1) → ∀ (r:ℝ) (φ:Test 3)
    (Q:Grid R z r φ→Poly J!), (∀c,(Q c).part (J!).quiet=1) →
    let w:=fun c:Grid R z r φ=>WilsonThermometerAlignedCells.mass (R:=R) r z φ c.val
    let F:=measured R A z r φ
    let E:=fun (c:Grid R z r φ)=>read (total (F c) (Q c))
    ∀ A₂ A₁ A₃:ℝ,0≤A₂→0≤A₁→
    (∀s:Finset (Fin 3),s.card=2→∑c,‖w c‖*‖E c s‖^2≤A₂^2)→
    (∀v:Fin 3,∑c,‖w c‖*‖E c {v}‖^2≤A₁^2)→(∀v:Fin 3,∑c,‖w c‖*‖E c {v}‖^3≤A₃^3)→
    ‖φ.applyTo (WilsonPositionThermometerGradedReading.full r A z) - reference R z r φ Q -
      WilsonThermometerUnitFilingCylinder.tested R A z r φ (table R z r φ Q)‖≤3*(A₂*A₁)+2*A₃^3:=by
  filter_upwards [WilsonThermometerCenteredCredit.unit_table R A checked unit] with z issued
  intro ready r φ Q qu w F E a b c ha hb two one three
  have quiet (v): (F v).part (J!).quiet=1:=
    issued (WilsonThermometerRegisteredCells.placement (R:=R) z v.val)
  have result:=proper w F Q quiet qu a b c ha hb two one three
  have trueVal (v:Grid R z r φ):read (Extra.Trajectories.connected (F v)) univ=
     WilsonPositionThermometerConnected.value (row A z (atOrigin v.val)):=WilsonThermometerCenteredScalar.three _ (quiet v)
  have specVal (v:Grid R z r φ):read (Extra.Trajectories.connected (Q v)) univ=
     WilsonPositionThermometerConnected.value (read (Q v)):=WilsonThermometerCenteredScalar.three _ (qu v)
  simp only [trueVal,specVal,mul_sub,Finset.sum_sub_distrib] at result
  have phys:=expense R A z r φ (fun _ E=>WilsonPositionThermometerConnected.value E) ready
  have mask:=expense R A z r φ
    (fun j Y=>∑s:(J!).Mode,weight (filled R z r φ Q j) s*Y s.val) ready
  change φ.applyTo (WilsonPositionThermometerGradedReading.full r A z)=_ at phys
  change WilsonThermometerUnitFilingCylinder.tested R A z r φ (table R z r φ Q)=_ at mask
  rw [phys,mask];unfold reference
  convert result using 3
  apply Finset.sum_congr rfl;intro v _
  rw [WilsonThermometerCenteredAlgebra.affine]
  simp only [filled,dif_pos v.property]
  rfl

end YM.Integration.WilsonThermometerUnitFilingRelativeCells
