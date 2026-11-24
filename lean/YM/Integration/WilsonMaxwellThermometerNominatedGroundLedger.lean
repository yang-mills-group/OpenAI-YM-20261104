import YM.Integration.WilsonMaxwellThermometerNominatedGroundMeasured

/-! The independent credit is submitted on the same true physical cells. In
each cell it uses the full seven-mode pupil and the fixed original filed test,
with the within-cell Maxwell inverse retained under the signed shape. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerNominatedGroundLedger
open Filter MeasureTheory Lattice Wilson Labels RG Source PhysicalNext.Repeat.Legato
open OPE OPE.Orbits Table Spec PhysMS PhysMS.Frame Maxwell Maxwell.Free XSpace XSpace.Rose XSpace.Normalize
open Marker QuadraticLocal Trace Trace.Pilot Extraction Extra.Trajectories
open WilsonPositionCapTransport WilsonPositionThermometerGradedSource WilsonPositionThermometerCapStation
open WilsonCenteredPhysicalPanel WilsonThermometerCenteredAlgebra
open WilsonMaxwellThermometerNominatedGroundCell
open WilsonMaxwellThermometerNominatedGroundProgram (Visit)
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) {f:Extraction.Order} {S:Table R.family.book}
    (F:Final R.family f S) (J:ℝ→tower S) (V:Store G) (A:ℝ→Group R.family 6) (simple:G.Simple) (v:ℕ)
local notation "J₀"=>Stock.census (Fin 3)
local notation "basis"=>WilsonOriginalThermometerPalette.levels
local notation "hot"=>WilsonPositionThermometerSevenFaceRate.temperature (R:=R) simple (B:=v)
local notation "atCell"=>WilsonCenteredCompactBooking.site R
local notation "k₀"=>WilsonReflectedPhysicalRate.launch R simple v
local notation "Z₀"=>WilsonPositionCorrectedCap.adjusted F J V A
local notation "W"=>WilsonMaxwellThermometerNominatedGroundPurse.policy R
local notation "pub"=>WilsonMaxwellThermometerNominatedGroundPanel.actual R F J V A
local notation "payment"=>WilsonMaxwellThermometerNominatedGroundWeights.payment R
variable (caps:Fin 3→ℕ) (room:∀i,basis i<caps i)
    (roster:(w:Visit)→Sites R w.2 3→WilsonCoeffUV.Wheel.Case caps) (q a:ℕ)

def depot (w:Visit) (o:Sites R w.2 3):Poly J₀:=
  WilsonMaxwellThermometerNominatedOrdinary.table R (Z₀ w.1) w.2.1 w.2.2 (k₀ w.1) caps room
    (WilsonThermometerAlignedCells.atOrigin (WilsonThermometerAlignedCells.offsets o))
    (roster w o) (fun _=>0) (hot w.1 w.2) q a (fun _=>1)
local notation "earn"=>depot R F J V A simple v caps room roster q a
local notation "issued!"=>WilsonMaxwellThermometerNominatedGroundProgram.filed
  R F J V A simple v caps room (fun w x=>roster w (atCell w.1 w.2 x)) q a

def payday (w:Visit) (φ:Test 3):ℂ:=
  ∑o:Sites R w.2 3,∑s:Badge,payment φ (atCell w.1 w.2) o (mode s)*(earn w o).part (mode s)
local notation "paid"=>payday R F J V A simple v caps room roster q a

private theorem faces (F Q:Poly J₀):
    (total F Q).part full=∑s:Badge,weight Q (mode s)*F.part (mode s):=by
  rw [affine,←(modes.sum_comp (fun t=>weight Q t*F.part t))]
  rfl

theorem original (w:Visit) (φ:Test 3):
    φ.applyTo (fun x=>(total (issued! w x) (W x)).part full)=paid w φ:=by
  have m:Measurable (atCell w.1 w.2:Points 3→Sites R w.2 3):=WilsonSeparatedOriginalThermometerCells.placed w.1 w.2
  have weighted:=WilsonMaxwellThermometerNominatedGroundCell.taken R φ (atCell w.1 w.2) m
    (fun o s=>(earn w o).part (mode s))
  change φ.applyTo (fun x=>(total (earn w (atCell w.1 w.2 x)) (W x)).part full)=_
  simpa only [faces,payday] using weighted

private theorem finite_cell {T:Type} [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
    (χ:Points 3→T) (m:Measurable χ) (u:Points 3→ℂ) (good:Integrable u) (h:T→ℂ):
    Integrable (fun x=>u x*h (χ x)):=by
  let fee (o:T):Points 3→ℂ:=fun x=>(χ ⁻¹' {o}).indicator u x*h o
  have ih (o:T):Integrable (fee o):=(good.indicator (m (measurableSet_singleton _))).mul_const (h o)
  have split (x:Points 3):u x*h (χ x)=∑o:T,fee o x:=by
    rw [Finset.sum_eq_single (χ x)]
    · exact congrArg (fun a=>a*h (χ x)) (Set.indicator_of_mem (show x∈χ ⁻¹' {χ x} from rfl) u).symm
    · intro o _ ne;unfold fee;rw [Set.indicator_of_notMem (show x∉χ ⁻¹' {o} from fun h=>ne h.symm),zero_mul]
    · intro h;exact (h (Finset.mem_univ _)).elim
  simp_rw [split]
  exact integrable_finsetSum _ (fun o _=>ih o)

private theorem funded {T:Type} [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
    (χ:Points 3→T) (m:Measurable χ) (φ:Test 3) (u:T→Poly J₀):
    Integrable (fun x=>φ x*(total (u (χ x)) (W x)).part full):=by
  have split (x:Points 3):φ x*(total (u (χ x)) (W x)).part full=
      ∑s:Badge,φ x*weight (W x) (mode s)*(u (χ x)).part (mode s):=by
    rw [faces,Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _=>mul_assoc .. |>.symm
  simp_rw [split]
  exact integrable_finsetSum _ (fun s _=>finite_cell χ m _
    (φ.smearing (WilsonMaxwellThermometerNominatedGroundWeights.regular R (mode s))) (fun o=>(u o).part (mode s)))

/-- Signed connected error on the true filed panel, before regulator limits.
The full independent contribution is the literal finite sum in `payday`. -/
theorem signed (w:Visit) (φ:Test 3):
    φ.applyTo (fun x=>(Extra.Trajectories.connected (pub w x)).part full-(Extra.Trajectories.connected (issued! w x)).part full)=
      φ.applyTo (fun x=>WilsonMaxwellThermometerNominatedDelta.discrepancy (pub w x) (issued! w x) (W x))+
      (φ.applyTo (fun x=>(total (pub w x) (W x)).part full)-paid w φ):=by
  let χ:Points 3→Sites R w.2 3:=atCell w.1 w.2
  have m:Measurable (χ:Points 3→Sites R w.2 3):=WilsonSeparatedOriginalThermometerCells.placed w.1 w.2
  let fundedF:Sites R w.2 3→Poly J₀:=fun o=>WilsonMaxwellThermometerNominatedGroundPurse.table
    (WilsonPositionThermometerGradedReading.row (Z₀ w.1) w.2 o)
  let P:Points 3→ℂ:=fun x=>φ x*((Extra.Trajectories.connected (pub w x)).part full-(Extra.Trajectories.connected (issued! w x)).part full)
  let X:Points 3→ℂ:=fun x=>φ x*(total (pub w x) (W x)).part full
  let Y:Points 3→ℂ:=fun x=>φ x*(total (issued! w x) (W x)).part full
  have pi:Integrable P:=finite_cell χ m (fun x=>φ x) (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport)
    (fun o=>(Extra.Trajectories.connected (fundedF o)).part full-(Extra.Trajectories.connected (earn w o)).part full)
  have xi:Integrable X:=funded R χ m φ fundedF
  have yi:Integrable Y:=funded R χ m φ (earn w)
  rw [←original R F J V A simple v caps room roster q a w φ]
  change (∫x,P x)=(∫x,φ x*_)+((∫x,X x)-(∫x,Y x))
  have split (x:Points 3):φ x*WilsonMaxwellThermometerNominatedDelta.discrepancy (pub w x) (issued! w x) (W x)=
      P x-(X x-Y x):=by dsimp only [P,X,Y,WilsonMaxwellThermometerNominatedDelta.discrepancy];ring
  simp_rw [split]
  have closed:=integral_sub pi (xi.sub yi)
  simp only [Pi.sub_apply] at closed
  rw [closed,integral_sub xi yi]
  ring

end YM.Integration.WilsonMaxwellThermometerNominatedGroundLedger
