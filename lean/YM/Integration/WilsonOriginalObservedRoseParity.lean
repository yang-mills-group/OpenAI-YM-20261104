import YM.Integration.WilsonOriginalObservedRoseLedger

/-! On the genuine enrolled finite board every first proper response missing
the upper is even. This removes every higher incidence of the connected cubic. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseParity

open Function Filter Finset Set Metric Spec Extraction Table RG Lattice OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress
open Wilson PhysicalNext.Repeat.Legato RG17 PhysMS PhysMS.Frame Precision Cells
open Maxwell XSpace XSpace.Normalize XSpace.Structure1 XSpace.Rose XSpace.Cirrus XSpace.Photo XSpace.Graph3
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonMaxwellThermometerSignedWallet
open WilsonMaxwellThermometerPublicGalop (quotient)
open XSpace.Retirement XSpace.Tornado XSpace.AxesTangent WilsonMaxwellThermometerFirstDetector
open WilsonMaxwellThermometerPublicEvenSlope (entered)
open WilsonMaxwellThermometerPositionCurrency (received)
open WilsonMaxwellThermometerChargedHeads (sector)
open WilsonSeparatedOriginalThermometerCells (weight positions)
open WilsonOriginalObservedRoseJoint (locations lowerSite)
open WilsonOriginalObservedRoseLedger (Visit)
open scoped Classical Topology BigOperators

variable {G:Gauge} (W:Initialize G) {V:Normalize.Store G} (simple:G.Simple)

include simple

theorem missing_upper (x:Sample 3) (stage:V.Meets W x.F 6) (z:Sec G 6) (a b:Sec G 4)
    (s:Finset (Fin 3)) (absent:(0:Fin 3)∉s) :
    quotient W (V:=V) x (entered z a b) 1 s=0 := by
  have same : missing (entered z a b) s=missing (entered (0:Sec G 6) a b) s := by
    funext i
    fin_cases i <;> simp [missing,entered,trip,absent]
  have quiet:=WilsonMaxwellThermometerPublicEvenSlope.face W simple x stage (0:Sec G 6)
    (by simp [hinge]) a b s
  simpa only [quotient,←detail,same] using quiet

theorem proper (x:Sample 3) (stage:V.Meets W x.F 6) (z:Sec G 6) (a b:Sec G 4) (t:ℂ) :
    WilsonOriginalObservedRoseFaces.remainder W (V:=V) x (entered z a b) t=0 := by
  have lo:=missing_upper W simple x stage z a b {(1:Fin 3)} (by decide)
  have hi:=missing_upper W simple x stage z a b {(2:Fin 3)} (by decide)
  have pair:=missing_upper W simple x stage z a b {(1:Fin 3),2} (by decide)
  simp [WilsonOriginalObservedRoseFaces.remainder,WilsonOriginalObservedRoseFaces.higher,lo,hi,pair]

variable (R:Run G)(D:ChartRatio G)(K:Rose.Pick V){f:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family f S)(J:ℝ→tower S)(A:ℝ→Group R.family 6)
local notation "fit" => WilsonPositionCorrectedCap.adjusted F J V A

theorem filed (m:ℝ→Mesh)(v:Visit→∀i,Axes R i)(u:Visit→Sec G 6)(a b:Visit→Sec G 4)
    (axis:Visit→ℝ)(w:Visit)(vote:V.Meets W (board R (fit w.1).station.k w.1 w.2.2) 6) :
    WilsonOriginalObservedRoseLedger.higher R D W K F J A m v u a b axis w=0 := by
  by_cases h:(fit w.1).station.k≤w.2.1
  · rw [WilsonOriginalObservedRoseLedger.higher,dif_pos h]
    apply Finset.sum_eq_zero
    intro o _
    let k:=(fit w.1).station.k
    let x:=lowerSite R k w.1 w.2 h o
    have paid : V.Meets W x.F 6 := vote
    have tags : deposited R k w.1 w.2.2 (v w)=entered
        (received x (R.family.S.a k) (sector _ (v w 0)))
        (received x (R.family.S.a k) (sector _ (v w 1)))
        (received x (R.family.S.a k) (sector _ (v w 2))) := by
      funext i;fin_cases i <;>rfl
    change _*WilsonOriginalObservedRoseFaces.remainder W (V:=V) x (deposited R k w.1 w.2.2 (v w)) (axis w)=0
    rw [tags,proper W simple x paid, mul_zero]
  · simp only [WilsonOriginalObservedRoseLedger.higher,dif_neg h]

variable {Y:Ultrafilter (ℕ×ℕ)} {H:(Bel R.family.book).Hierarchy}
local notation "cut" => trail.curry (Y:Filter (ℕ×ℕ))

theorem original (book:Book (f:=f) (l:=Y) (H:=H) A J)(lead:Leading F J)
    (m:ℝ→Mesh)(v:Visit→∀i,Axes R i)(u:Visit→Sec G 6)(a b:Visit→Sec G 4)(axis:Visit→ℝ) :
    ∀ᶠ w in cut,WilsonOriginalObservedRoseLedger.higher R D W K F J A m v u a b axis w=0 := by
  apply eventually_curry_iff.mpr
  have entitled:=WilsonPositionCorrectedCap.original F J V A book lead
  filter_upwards [WilsonMaxwellThermometerPublicCollege.voted R W (V:=V) fit (WilsonPositionPrescribedFrame.positioned F J V) simple entitled] with r voted
  exact Eventually.of_forall fun z=>filed W simple R D K F J A m v u a b axis (r,z) (voted z.2)

end YM.Integration.WilsonOriginalObservedRoseParity
