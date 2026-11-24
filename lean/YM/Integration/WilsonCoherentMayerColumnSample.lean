import YM.Integration.WilsonCoherentMayerOnCourse
import YM.Integration.WilsonCoherentMayerPortfolio
import YM.Integration.WilsonCoherentMayerSignedCharge

/-! Signed integral of the original selected Mayer occurrences in one forest sample. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerColumnSample
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt RGLocalTaylor RGLocalTaylor.Insert
open RG01.Survive PhysicalNext.Repeat.Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open AnalyticBridge.LocalGaussianLaws PhysicalNext.Repeat.Legato WilsonCoherentMayerGate WilsonCoherentMayerSubmission
open WilsonCoherentMayerSignedCharge (polynomial residual)
variable {G:Gauge} {c f L:Side}{S:StepData c f}{T:Tube G S}{F:Forest S.ratio}{R:Rep G f}
    {P:Teller G}{Q:ConnectedActivityE6.Target G P}{W s μ C:ℝ}{o:Target.Order G W}
    {H:Cash W s μ L Q o C T R} {j n l k M:ℕ} {χ:Chi} {p:Molecule S}
    {q r a b Y D' v C' A B cost K θ δ ζ α:ℝ}
    (run:Run G) {I:Type} [Fintype I] (entry:Submitted run R I) (old:Team R)
    (fresh:∀m∈old.own,∀i,m.turn≠(row entry i).turn)
local notation "prior" => together entry old fresh
local notation "lw" => team prior (occupied entry)
local notation "rest" => p\Team.signs prior S

def prescribed (taylor:ℕ) (u:Mayer.Decors rest M) (X:Coat T F) (z:momentSpace X):ℝ:=
  Mayer.planned H p u (Laminate.partner lw H) X z*
    polynomial run entry.grade (F:=F) entry.site entry.phase R.p.threshold (Coat.gStep R.beta) entry.label taylor z.2

theorem issued (taylor:ℕ) (u:Mayer.Decors rest M) (N:Captain H j C' D' v Y A b r B q n χ) (law:Awning H N.conduit A b cost a δ ζ k l)
    (room:Q.goal L s≤K) (allow:Mayer.Approved K θ j M) (contract:∀i z,|entry.phase i z|≤‖z‖)
    {mass:ℝ} (receipt:WilsonCoherentMayerOnCourse.At run entry.grade H taylor mass)
    (before:(prior).signs S⊆p) (retained:Mayer.decorOrder u≤M) (cohort:Mayer.Start rest)
    (reserve:(M+4:ℝ)*r≤α) (charge:1≤α) (speed:ζ≤α) (inside:authorized H p)
    (X:Coat T F) (healthy:Healthy (Pressure.temp s) (H.unionP p) X.V)
    (hx:X.x=s) (hk:X.width=o.K) (hχ:X.χ=χ) (hm:X.manifest) (hot:0<R.beta)
    (fixed:X.V=1) (clear:Assembly.Clear S X.x X.seeds F):
    |(∫z,Mayer.planned H p u (Laminate.partner prior H) X z ∂moment X)-
       ∫z:momentSpace X,@prescribed G c f L S T F R P Q W s μ C o H M p run I _ entry old fresh taylor u X z ∂moment X| ≤
    (old.weight*∏i:↥rest,θ*(N.conduit.tag i.val)^((u i).val+1))*
    (WilsonCoherentReportingPivot.mass run entry.grade R.p.threshold entry.label*(mass*(Coat.gStep R.beta)^(taylor+1))):=by
  have due:=receipt N law room allow entry rfl contract old fresh before u retained cohort reserve charge speed inside
    X healthy hx hk hχ hm hot fixed clear
  let trueField:=Mayer.planned H p u (Laminate.partner prior H) X
  let written:=@prescribed G c f L S T F R P Q W s μ C o H M p run I _ entry old fresh taylor u X
  have resident: Integrable trueField (moment X):=Mayer.integrable_planned u Finset.sdiff_subset retained N law
    room allow _ (fun i hi=>(Laminate.partnerFit ((Laminate.compartments prior p before) ▸ hi)).1)
    cohort healthy hx hk hχ hm
  have err:Integrable (fun z=>trueField z-written z) (moment X):=due.1
  have valid: Integrable written (moment X):=by
    convert resident.sub err using 1
    ext z;change written z=trueField z-(trueField z-written z);ring
  change |(∫z,trueField z ∂moment X)-(∫z,written z ∂moment X)|≤_
  rw [←integral_sub resident valid]
  exact abs_integral_le_integral_abs.trans due.2

end YM.Integration.WilsonCoherentMayerColumnSample
