import YM.Integration.WilsonPositionScaleLawMeasuredOPEContour
import YM.Integration.WilsonPositionScaleLawMeasuredDatum
import YM.Integration.WilsonPositionPrescribedZero
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawMeasuredOPEDates
open WilsonPhysicalRosePositionFace (located predicted)
open WilsonPositionProgramTrialPublicJointPivotRose (Live tested)
open scoped Classical Topology BigOperators
open Function Filter Set Finset PowerSeries MeasureTheory Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Rose PhysicalNext.Repeat.Legato
open MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open FVA2.Scale.Jury (Thin fxt)
open WilsonPositionScaleLawThermometerChart (response)
open WilsonPositionScaleLawIndependent (ψ)
open scoped Topology BigOperators Classical Polynomial


open Position Position.Axes Dframe Level Reg.Point Facets Equator Measure Reg.CoverTest
variable {G : Gauge} (Z : WilsonPrescription G) {hG : G.Simple}
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ : Prescription (Press.portDeck G)} {b : Bool} (H : Main.Match Z hG M σ b) (ν : ℝ)
open WilsonPositionProgramTrialPublicJointPivotForecast (forecast)


open scoped ContDiff
open WilsonPositionProgramTrialPublicJointPivotRestriction (coordinates)
open MS.Theater FVA2.Dframe
open WilsonPositionScaleLawMeasuredBank (fixed)

open WilsonPositionThermometerCapStation WilsonPositionCapTransport
open WilsonPositionScaleLawMeasuredCut (sample)
open WilsonPositionScaleLawMeasuredJoint (full)
variable {R:Run G}{o:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family o S)(J:ℝ→tower S){l:Ultrafilter (ℕ×ℕ)} {Y:(Bel R.family.book).Hierarchy}{B n:ℕ}
local notation "θ" => WilsonPositionHomogeneousFrame.reading F J Z
local notation "P" => WilsonPositionPrescribedFrame.positioned F J Z.store


open WilsonPositionScaleLawMeasuredOPEContour
variable {d h k:ℕ}
def housed (r t:ℝ)(v:Sec G d) : Sec G d :=
  Maxwell.Free.fields R.family.labels d ((P r d).symm (P t d ((Maxwell.Free.fields R.family.labels d).symm v)))
theorem sameExterior (r t:ℝ)(v:Sec G d) :
    P r d ((Maxwell.Free.fields R.family.labels d).symm (housed Z F J r t v))=
      P t d ((Maxwell.Free.fields R.family.labels d).symm v) := by simp [housed]

def legs (r t:ℝ)(v:Fin n→Sec G d)(e:Fin k→Sec G d) : Fin (n+k)→Sec G d :=
  Fin.append v (fun i=>housed Z F J r t (e i))
def marked (below:h≤d)(j:Toon G h)(e:Fin k→Sec G d) : Fin (k+1)→Sec G d :=
  Fin.cons (up below ((Daylight (Press.portDeck G) h) j)) e

def measured (A:Group R.family B)(d:Fin (B+1))(below:h≤d.val){t:ℝ}(tp:0<t)
    (χ:Test (k+1))(e:Fin k→Sec G d)(cut:ℕ×ℕ)(j:Toon G h) : ℂ :=
  sample F J Z A d tp χ (marked below j e) cut
def limit (d:ℕ)(below:h≤d)(t:ℝ)(χ:Test (k+1))(e:Fin k→Sec G d)(j:Toon G h) : ℂ :=
  WilsonPositionPrescribedScreen.hierarchy F P d t (k+1) χ (marked below j e)
def fee (A:ℝ→Group R.family B)(d:Fin (B+1))(high:6≤d.val)(below:h≤d.val)(order q:ℕ)
    (g:ℝ){r t:ℝ}(rp:0<r)(tp:0<t)(φ:Test n)(both:Test (n+k))(χ:Test (k+1))
    (v:Fin n→Sec G d)(e:Fin k→Sec G d)(cut:ℕ×ℕ) : ℂ :=
  let μ:=measured Z F J (A t) d below tp χ e cut
  let cash:=sample F J Z (A r) d rp both (legs Z F J r t v e) cut
  WilsonPositionScaleLawMeasuredContour.contrast (full Z M H ν high order)
    (WilsonPositionScaleLawMeasuredOPE.row Z M ν below q φ v μ)
    (WilsonPositionScaleLawMeasuredClock.chart Z M H ν high order) (0,g)
    (WilsonPositionScaleLawMeasuredDatum.filed F J Z (A r) d (by omega) rp cut) cash

theorem original (lead:Leading F J)(obedient:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)
    (prior:(l:Filter _)≤o.fuse)(A:ℝ→Group R.family B)(paid:Book (f:=o) (l:=l) (H:=Y) A J)
    (d:Fin (B+1))(high:6≤d.val)(order:ℕ)(g:ℝ→ℝ)(cool:Tendsto g trail (𝓝 0)) :
    ∀ᶠu:ℝ×ℝ in trail×ˢtrail,∀rp:0<u.1,∀tp:0<u.2,
    ∀h:Fin (d.val+1),∀q n k:ℕ,∀φ:Test n,∀both:Test (n+k),∀χ:Test (k+1),
    ∀v:Fin n→Sec G d,∀e:Fin k→Sec G d,
      let below:=Nat.le_of_lt_succ h.isLt
      Tendsto (fee Z M H ν F J A d high below order q (g u.1) rp tp φ both χ v e) (l:Filter _)
        (𝓝 (WilsonPositionPrescribedScreen.hierarchy F P d u.1 (n+k) both (legs Z F J u.1 u.2 v e)-
          WilsonPositionScaleLawMeasuredOPE.row Z M ν below q φ v (limit Z F J d below u.2 χ e) (0,θ u.1))) := by
  let D:=full Z M H ν high order
  let rev:=WilsonPositionScaleLawMeasuredClock.chart Z M H ν high order
  have smooth:=WilsonPositionScaleLawMeasuredJoint.smooth Z M H ν high order
  have jac:=WilsonPositionScaleLawMeasuredClock.jacobian Z M H ν high order
  obtain ⟨δ,pos,sale⟩:=WilsonPositionScaleLawMeasuredOPEContour.original Z M H ν d high order
  obtain ⟨δ',pos',regular⟩:=WilsonPositionScaleLawMeasuredContour.radius D smooth 0 jac
  have zero:Tendsto θ trail (𝓝 0):=WilsonPositionPrescribedZero.measured F J Z.store lead obedient hG Z.criterion
  have base:Tendsto (fun r=>((0:MoveSpace G d),g r)) trail (𝓝 0):=tendsto_const_nhds.prodMk_nhds cool
  have seen:Tendsto (fun r=>(fixed Z d,θ r)) trail (𝓝 (D 0)):=by
    rw [show D 0=(fixed Z d,0) from WilsonPositionScaleLawMeasuredJoint.axis Z M H ν high order 0]
    exact tendsto_const_nhds.prodMk_nhds zero
  have six:6≤B:=by omega
  have f:Tendsto (fun u:ℝ×ℝ=>u.1) (trail×ˢtrail) trail:=tendsto_fst
  have s:Tendsto (fun u:ℝ×ℝ=>u.2) (trail×ˢtrail) trail:=tendsto_snd
  have original:=WilsonPositionScaleLawMeasuredCut.receives F J Z prior A paid
  filter_upwards [f.eventually (base.eventually sale),f.eventually (seen.eventually (Metric.ball_mem_nhds _ pos)),
    f.eventually (seen.eventually (Metric.ball_mem_nhds _ pos')),f.eventually (zero.eventually (WilsonPositionScaleLawMeasuredClock.measured Z M H ν high order)),
    f.eventually (WilsonPositionScaleLawMeasuredDatum.original F J Z lead hG prior A paid six),
    f.eventually original,s.eventually original] with u invoice inside atChart fix data front rear rp tp h q n k φ both χ v e
  let below:=Nat.le_of_lt_succ h.isLt
  let w:=WilsonPositionScaleLawMeasuredDatum.filed F J Z (A u.1) d six rp
  let μ:=measured Z F J (A u.2) d below tp χ e
  let m:=limit Z F J d below u.2 χ e
  let y:=sample F J Z (A u.1) d rp both (legs Z F J u.1 u.2 v e)
  have funded:Tendsto w (l:Filter _) (𝓝 (fixed Z d,θ u.1)):=data rp d
  have positioned:Tendsto (fun i=>rev (w i)) (l:Filter _) (𝓝 (0,θ u.1)):=by
    have placed:ContinuousAt rev (fixed Z d,θ u.1):=(regular _ atChart).1.continuousAt
    have done:=placed.tendsto.comp funded
    rw [show rev (fixed Z d,θ u.1)=(0,θ u.1) from fix] at done
    exact done
  have left:=front rp d (n+k) both (legs Z F J u.1 u.2 v e)
  have right (j:Toon G h):Tendsto (fun cut=>μ cut j) (l:Filter _) (𝓝 (m j)):=rear tp d (k+1) χ (marked below j e)
  have live:(WilsonPositionScaleLawMeasuredOutput.field h (coordinates below (0:MoveSpace G d))).IsInvertible:=by
    rw [map_zero,WilsonPositionScaleLawMeasuredOutput.identity]
    exact ContinuousLinearMap.isInvertible_equiv (f:=ContinuousLinearEquiv.refl ℝ _)
  have sums:=WilsonPositionScaleLawMeasuredOPE.moving Z M ν below q φ v (fun i=>rev (w i)) (0,θ u.1) positioned μ m right live
  apply (left.sub sums).congr'
  filter_upwards [funded.eventually (Metric.isOpen_ball.mem_nhds inside)] with cut good
  exact (invoice (w cut) good h q n φ v (μ cut) (y cut)).symm

end YM.Integration.WilsonPositionScaleLawMeasuredOPEDates
