import YM.Integration.WilsonCapturedPrimaryWardAppointment

/-! Complete the inactive legs by the original unit. The funded occupied
palette is identical for the fine density and for every reflected subface. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWardSeats
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open WilsonThermometerOwnOffsetNectar WilsonThermometerOwnOffsetRadii WilsonThermometerOwnOffsetInvoice
open scoped Classical Topology
set_option quotPrecheck false
open WilsonThermometerIntrinsicRoster
open WilsonCapturedPrimaryActiveArms Extra.Trajectories
open scoped BigOperators
open WilsonCapturedPrimaryFaceWallet WilsonCapturedPrimaryNamedReturn WilsonCapturedPrimaryPhysicalArray
open WilsonReflectedPhysicalRate XSpace OPE GridApprox XSpace.Rose
open private supported from YM.Integration.WilsonCapturedPrimaryPhysicalArray
variable {G : Gauge} {R : Run G} {N p k n : ℕ} {d : Fin n → ℕ} {o : Fin n → Site (R.family.side N p)}

def filled (S : Shelf (N:=N) (p:=p) R k d o) (live:k≤N) (y:(i:Fin n)→Palette R.family (d i))
    (s:Finset (Fin n)) (i:Fin n) : Palette R.family (level d s i) :=
  pick (F:=Palette R.family) (decide (i∈s)) (y i)
    (WilsonNeutralOffsetCutoff.input R (p:=p) (S.units i) live (R.family.refUnit 0))

theorem legal (S : Shelf (N:=N) (p:=p) R k d o) (live:k≤N) (x:(i:Fin n)→R.family.label (d i))
    (y:(i:Fin n)→Palette R.family (d i)) (paid:primary R (p:=p) d S.route live x y) (s:Finset (Fin n)) :
    primary R (p:=p) (level d s) (S.paths s) live (label R s x) (filled S live y s) := by
  intro i
  have both (b:Bool) :
      (R.family.factory (branch b (d i)) N p).terminal
        (finer (pick (F:=Emblems R.family) b (S.route i) (S.units i)) live
          (pick (F:=Palette R.family) b (y i) (WilsonNeutralOffsetCutoff.input R (p:=p) (S.units i) live
            (R.family.refUnit 0))) (primaryLetter _)) =
      ((R.family.S.a k:ℂ)^(branch b (d i)))⁻¹ • pick (F:=R.family.label) b (x i) (R.family.refUnit 0) := by
    cases b
    · exact WilsonNeutralOffsetCutoff.launched R (S.units i) live (R.family.refUnit 0)
    · exact paid i
  exact both (decide (i∈s))

theorem occupied_size (S : Shelf (N:=N) (p:=p) R k d o) (live:k≤N) (y:(i:Fin n)→Palette R.family (d i))
    (s:Finset (Fin n)) :
    (∏ i∈s,(1+size (filled S live y s i)))=∏ i∈s,(1+size (y i)) := by
  apply Finset.prod_congr rfl
  intro i hi
  have same (b:Bool) (yes:b=true) : size (pick (F:=Palette R.family) b (y i)
      (WilsonNeutralOffsetCutoff.input R (p:=p) (S.units i) live (R.family.refUnit 0))) = size (y i) := by
    subst b
    rfl
  exact congrArg (1+·) (same (decide (i∈s)) (by simpa using hi))

theorem separation (R:Run G) (simple:G.Simple) (slow:WilsonWindowReportingPace.Slow R.kit)
    (v:ℕ) (wide:4<v) (φ:Test n) : ∀ᶠ r:ℝ in 𝓝[>]0, let k:=launch R simple v r
    ∀ N p (_:k≤N) (o:Fin n→Site (R.family.side N p)), WilsonCenteredCompactBooking.mass R φ r (N,p) o ≠ 0 →
    ∀ ax i j:Fin n, i≠j → (R.family.path.levels.budget k).B^2 <
      Lattice.separation (WilsonThermometerOwnOffsetJoint.origins R (registered o (some ax)) k i)
        (WilsonThermometerOwnOffsetJoint.origins R (registered o (some ax)) k j) := by
  filter_upwards [WilsonCapturedPrimarySeparatedStop.translated R simple slow v wide φ] with r tested
  dsimp only
  intro N p live o used ax i j ne
  obtain ⟨X,hX,rfl⟩:=supported R φ r o used
  let sites:=WilsonCenteredCompactBooking.site R r (N,p) X
  have pair:=tested N p live X hX (sites ax) i j ne
  have placed (l:Fin n) :
      WilsonThermometerOwnOffsetJoint.origins R (registered sites (some ax)) (launch R simple v r) l =
        (R.family.S.toDepth live p).parent (sites l-sites ax) := by
    unfold WilsonThermometerOwnOffsetJoint.origins WilsonThermometerOwnOffsetNectar.location
    rw [dif_pos live]
    rfl
  rw [placed i,placed j]
  exact pair

end YM.Integration.WilsonCapturedPrimaryWardSeats
