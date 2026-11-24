import YM.Integration.WilsonCapturedPrimaryFiledArms
import YM.Integration.WilsonPositionSeparatedProfileFlatReadout
import YM.Integration.WilsonThermometerOffsetPrimary

/-! The sparse physical unit has its original unit size on every admitted
own-site trajectory, including displaced sites and an arbitrary UV top. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryUnitWallet
open Function Filter MeasureTheory Lattice Wilson RG Source Labels
open Extra.Histories Extra.Histories.Relay Extra.Trajectories Extra.Multi Overlay
open PhysicalNext.Repeat.Legato RG05Readout Native Address Many Records Harvest Copper
open MergeProof Accent Cells Push GridApprox
open WilsonThermometerOffsetTrajectory WilsonThermometerOwnOffsetField
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) {k N p : ℕ}
local notation "C" => R.family

theorem quiet (kn : k ≤ N) :
    dyes C k N p kn (1 : Config G ((C).side N p) → ℂ) = liftVac (C).path N p k := by
  unfold dyes
  simp only [Pi.one_apply, mul_one]
  induction kn using Nat.decreasingInduction with
  | self => exact gust_base ..
  | of_succ j hj ih =>
    rw [gust_step (C).path N p N _ hj, ih]
    exact (vac_transfer (C).path N p j R.makes.wilson hj).symm

theorem original {V : Sight C 0 p} {r : Emblems C 0} (z : Site ((C).side N p))
    (entry : Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R)
      k N p 0 (WilsonThermometerOffsetResidue.digits R N p z) V r)
    (kn : k ≤ N) (started : (C).ref 0 ≤ N) (y : Palette C 0)
    (named : ((C).factory 0 N p).terminal (finer r kn y (primaryLetter 0)) = (C).refUnit 0) :
    y = Suede.firstC C := by
  have start (e : ℕ) (he : e ≤ 0) : (C).ref e ≤ N := Nat.eq_zero_of_le_zero he ▸ started
  have trueUnit (site : Site ((C).side N p)) : (C).O N p ((C).refUnit 0) site = 1 :=
    (C).constant R.makes 0 started site
  have point := WilsonThermometerOffsetPrimary.primary R N p k entry le_rfl kn start
    (primaryLetter 0) (by rfl) y
  let here := WilsonThermometerOffsetCylinder.address R N p k
    (WilsonThermometerOffsetResidue.digits R N p z) (N-k) (by omega)
  change pulseOut (V k y) (line (primaryLetter 0)) =
    dyes C k N p kn ((((C).S.a k : ℂ)^0) • (C).O N p
      (((C).factory 0 N p).terminal (finer r kn y (primaryLetter 0))) here) at point
  rw [named, trueUnit, pow_zero, one_smul, quiet R kn, Suede.equal_letter (primaryLetter 0)] at point
  obtain ⟨_,receipt⟩ := (entry.legal k le_rfl kn).capacity0 y
  have flat := WilsonPositionSeparatedProfileFlatField.read R.makes receipt
  have heard : (((C).path.rep N p k).eval 1 : ℂ) * val y (Suede.mother C) =
      (((C).path.rep N p k).eval 1 : ℂ) :=
    flat.symm.trans (congrFun point 1)
  have locked : val y (Suede.mother C) = 1 := by
    have pos : (((C).path.rep N p k).eval (1 : Config G ((C).side k p)) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Multi.AxisShift.chosen_positive R.makes.wilson (p:=p) kn _).ne'
    apply mul_left_cancel₀ pos
    simpa only [mul_one] using heard
  simpa only [locked, one_smul] using (Suede.letter_sum y).symm

theorem sparse {V : Sight C 0 p} {r : Emblems C 0} (z : Site ((C).side N p))
    (entry : Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R)
      k N p 0 (WilsonThermometerOffsetResidue.digits R N p z) V r) (kn : k ≤ N) (start : (C).ref 0 ≤ N) :
    size (WilsonNeutralOffsetCutoff.input R (p:=p) r kn ((C).refUnit 0)) = 1 := by
  have hits := WilsonNeutralOffsetCutoff.launched R (p:=p) r kn ((C).refUnit 0)
  simp only [pow_zero,inv_one,one_smul] at hits
  rw [original R z entry kn start _ hits]
  exact size_ticket _

end YM.Integration.WilsonCapturedPrimaryUnitWallet
