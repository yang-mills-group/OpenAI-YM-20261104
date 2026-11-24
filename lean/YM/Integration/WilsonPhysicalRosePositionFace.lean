import YM.Integration.WilsonPhysicalPositionedHomeRows
import YM.Integration.WilsonPhysicalCommonSignedAperture
import YM.Integration.WilsonPositionThermometerReading
import YM.Integration.WilsonMaxwellThermometerNominatedSecant

/-! The actual three-position public face, with its missing leaves in the unit sector
of the same dimension-six cap and one source change for the whole measurement. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalRosePositionFace
open Filter Function Finset MeasureTheory Lattice RG PhysicalNext.Repeat.Legato
open RG17 FullVolume OPE OPE.Orbits Climb Next.UVStress FVA2 FVA2.Register Trace.Target Spec Table Trace.Pilot Maxwell Maxwell.Free XSpace XSpace.Normalize PhysMS
open WilsonPositionPrescribedScreen (hierarchy correction)
open WilsonPhysicalNormalizedSignedMenu (Row positioned offered docket retag)
open WilsonPhysicalPositionTargetRows (rows)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
variable (F:Final R.family f S)(J:ℝ→PhysMS.tower S)(V:Store G)
abbrev Face:=Finset (Fin 3)
def arm (s:Face)(i:Fin 3):Sec G 6:=Rose.missing (Rose.tag G) s i
def located (r:ℝ)(x:Points 3):Row G 6 3:=
  WilsonPhysicalPositionedHomeRows.pins F J (fun _=>r) (r • x)
def predicted (Q:Prediction G 6)(W:Row G 6 3)(s:Face):ℂ:=
  positioned (V.survey 6) (V.prepared 6) (fun _:Fin 3=>()) (arm s) (fun _:Unit=>Q) W

theorem actual {r:ℝ}(h:Bijective (stand (correction F J V 6 r)))(x:Points 3)(s:Face):
    predicted V (hierarchy F J 6 r) (located F J r x) s=
      WilsonPositionThermometerReading.sample F (WilsonPositionPrescribedFrame.positioned F J V) r x s:=by
  change S.classMoment (spectator F none) _ (r • x) _=S.classMoment (spectator F none) _ (r • x) _
  apply congrArg
  funext i
  exact congrArg (J r 6) (WilsonPositionPrescribedFrame.leg F J V h (arm s i)).symm

def expense (r:ℝ)(x:Points 3)(Q:Prediction G 6)(move:Change G 6)(W:Row G 6 3):ℝ:=
  let D:=V.survey 6
  let raw:=offered (fun _:Fin 3=>()) (fun _:Unit=>move) W
  ‖rows (located F J r x)-rows raw‖+
    ‖docket D (fun _:Unit=>hierarchy F J 6 r)-docket D (retag (fun _:Unit=>move) (fun _:Unit=>Q))‖*
      ‖rows raw‖

theorem original (lead:Leading F J):
    ∃C:Face→ℝ,(∀s,0<C s) ∧ ∀(Q:ℝ→Prediction G 6)(move:ℝ→Change G 6)
      (_:(V.survey 6).Via Q (u:=trail))(_:Tendsto (fun r=>guide G 6 (move r)) trail (𝓝 0)),
      ∀ᶠr in trail,∀(x:Points 3)(W:Row G 6 3)(s:Face),
      ‖WilsonPositionThermometerReading.sample F (WilsonPositionPrescribedFrame.positioned F J V) r x s-
        predicted V (Q r) W s‖≤C s*expense F J V r x (Q r) (move r) W:=by
  choose C pos bound using fun s:Face=>WilsonPhysicalCommonSignedAperture.original (V.survey 6)
    (V.prepared 6) (fun _:Fin 3=>()) (arm (G:=G) s) trail
  refine ⟨C,pos,fun Q move warm loose=>?_⟩
  have each:=Filter.eventually_all.mpr fun s=>bound s (fun (r:ℝ) (_:Unit)=>hierarchy F J 6 r)
    (fun (r:ℝ) (_:Unit)=>Q r) (fun (r:ℝ) (_:Unit)=>move r) (fun _=>WilsonPositionPrescribedScreen.warm F J lead V 6)
    (fun _=>warm) (fun _=>loose)
  filter_upwards [each,(WilsonPositionPrescribedScreen.original F J lead V 6).2] with r fees sure x W s
  rw [←actual F J V sure.2.1]
  exact fees s (located F J r x) W

end YM.Integration.WilsonPhysicalRosePositionFace
