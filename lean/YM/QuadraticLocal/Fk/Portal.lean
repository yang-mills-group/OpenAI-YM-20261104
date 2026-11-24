import YM.AllOrder.Floe.Voyage
import YM.QuadraticLocal.Fk.Action
import YM.AllOrder.Wheel.Roll
/-!
# Concrete Fk binding on one single charged `Income`
The score & hence all thermal calculations use the actual prescribed Fk with
THIS `PathData etc`. Period correspondence required for Render
step: exponentially wrapping corrections in the vertex.Priced output, **not**
 claiming coefficient equality without them. Costs of those supplied already in Rails.Cost.Tick.
For actual `V` history step, can bind using ANY F without assuming orientation of K.
This proof distinguishes determinant scalar conventions.Pure Pt.Relative.Measure.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Floe.Step.PlanV
open Function Filter Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid Planned.JetPort
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration Pace Plateau
open Kinetic.Port Push.PriceCompiler
open Aero Laurent Bloch Further.PhysicalPeriodLimitF933 Shingle Macrame PhysicalNext ThroughLaunch Pane
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge} {X: Metals G}
variable (D : RG.Supply.Rolls X.p)(R:Roots (G:=G) X.p.profile X.K X.p.kernel){x y k N:ℕ}
local notation "B"=> X.K
local notation "A"=> X.p.profile
local notation "p"=> X.p.profile x
local notation "q"=> X.p.profile y
local notation "K"=> X.p.kernel
local notation "O"=> X.O
variable (hx:4≤x)
set_option quotPrecheck false
local notation "P"=> Mural.sheet X.p D hx
local notation "T"=> tape (k+2)
local notation "I"=> Card D R x y hx k
local notation "V₁"=> (p).clip
local notation "V₂"=> (q).clip
local notation "M₁"=> (fun i:I=> i.self.north)
local notation "Λ₀"=> (fun i:I=> i.self.paid)
variable (F: Income D R x y hx k)
local notation "G₀"=> prePhase P K (A x).clip O M₁ Λ₀ F.frame (fun i:I=> i.self.upCost) X.oga F.tools F.efficient (Card.extra) T (audited D R x y hx)
local notation "u₀"=>Grant
open Comparison.RG02
open Marker
variable (i: Card D R x y hx k) {U:Type}[DecidableEq U][Fintype U] {J:Marker.Census U}
variable {c f : Side} (S:StepData c f) (hP:S.patch=Mural.sheet X.p D hx)(hs:S.kernel=X.p.kernel)(hG:Bid.Larger (G:=G) S)
local notation "D'"=> (dock P K c)
local notation "F₀"=> F.tools i c
local notation "L₀"=> (Ad G P K c)
local notation "ℓ"=> (trees P K c)
local notation "Θ"=> tint G (Exterior.Body 1 c)
section
-- Launch on any D' including independent Plan.Chart Fourier/BKt.
variable (C:Bulk.Kernel (dock (Mural.sheet X.p D hx) X.p.kernel c) (X.p.profile x).clip i.self.north X.O)
variable (a: Forest (dock (Mural.sheet X.p D hx) X.p.kernel c).ratio) (t:(dock (Mural.sheet X.p D hx) X.p.kernel c).Choices)
local notation "W"=> F.frame
open QuadraticLocal.Fk
open Dress
variable (L':Bulk.Colors J G (below (Mural.sheet X.p D hx) c)) (hn:Ad G (Mural.sheet X.p D hx) X.p.kernel c)
local notation "C'"=> Dress.gauge -- no
local notation "Ω"=> QuadraticLocal.Fk.grant i.extra T L'
-- typing
include hn in
private lemma stage_imp (hk:N≤ k+2)(z:rule (Coarse G) c): Symmetry.Orbit.ground C a t Ω (k+2) N ((Θ) (exteriorL G c z))= Complex.ofReal (G₀ i N c z) := by -- add N≤ 
    suffices he : (Symmetry.Orbit.ground C a t Ω (k+2) N ((Θ) (exteriorL G c z))).re= G₀ i N c z ∧ Complex.ofReal ((Symmetry.Orbit.ground C a t Ω (k+2) N ((Θ) (exteriorL G c z))).re)= Symmetry.Orbit.ground C a t Ω (k+2) N ((Θ) (exteriorL G c z)) from he.2.symm.trans (congr_arg _ he.1)
    -- canonical Desk t.Clock use Call.Apex.Policy,F.tools.
    let A':= augment ℓ i.extra T (startup ℓ O (label D') i.self.north V₁ (W) hn i.self.upCost (F.efficient i c hn) X.oga) (audited D R x y hx i)
    obtain ⟨r,hr⟩:= F.frame.graph a i.self.upCost hn rfl rfl; -- type. use give Metric.L.A.
    let T':=startup a O t i.self.north V₁ (W) hn i.self.upCost hr C.ratio; let U':= augment a i.extra T T' (audited D R x y hx i); let y':=exteriorL G c z; let p':= Symmetry.Orbit.ground C a t Ω (k+2) N ((Θ) (exteriorL G c z))
    have hh : ratePlan A'=ratePlan U':= Response.exactly A' U' (mul_pos (pow_pos X.oga.scale _) (Real.exp_pos _)) X.oga C.branches (fun z=> Floe.orchestra i.self.north V₁ i.extra T (audited D R x y hx i) z i.self.upCost) (Dress.minted (C:=C) a t ..)
    have he : preview A'=preview U':= by
       have he:ratePlan A' 0 0=preview A':= Dress.zeroBase (C:=C) ℓ (label D') i.extra T (audited D R x y hx i) F₀ W (F.efficient i c hn) hn i.self.upCost
       exact he.symm.trans ((hh ▸ rfl : ratePlan A' 0 0= ratePlan U' 0 0).trans (zeroBase (C:=C) a t i.extra T (audited D R x y hx i) r W hr hn i.self.upCost))
    haveI : Nonempty I:= ⟨i⟩
    have hz:ratePlan A' N y'= _:= precise_top P K V₁ O _ _ F.frame (fun i:I=>i.self.upCost) X.oga F.tools F.efficient (Card.extra) (Step.tape (k+2)) (audited D R x y hx) i _ hn z N
    refine ⟨?_, tangible a t i.extra T (audited D R x y hx i) C r W hr hn i.self.upCost L' y' (k+2) N hk⟩
    exact add_left_cancel (((Dress.forecast a t i.extra T (audited D R x y hx i) C r W hr hn i.self.upCost L' y' (k+2) N hk).symm.trans (congr_fun (congr_fun hh.symm N) y')).trans (hz.trans (by change PositionX.Jet.just (preview A') N+ _=_; rw [he])))
end
variable (L':Bulk.Colors J G f) (L:PathData G) (V:Clip) (We:Floe.Layout G)
variable (C:Bulk.Kernel S V L X.O)
include hP hs hG
omit hP hs hG in
-- dummy
private lemma pactPaid {S S':StepData c f} (h:S'.patch=S.patch)(hk:S'.kernel=S.kernel): S'=S:=by cases S with| mk p1 k1 t=> cases S' with| mk p2 k2 t=>dsimp only at h hk; subst p1 k2; rfl
lemma portal (a:Forest S.ratio)(t:S.Choices)(h:L=i.self.north)(hp:V=(X.p.profile x).clip)(hw:We=i.extra)(hk:N≤ k+2): (fun z=>Symmetry.Orbit.ground C a t (QuadraticLocal.Fk.grant We T L') (k+2) N (tint G (Exterior.Body 1 c) (exteriorL G c z)))= fun z=> Complex.ofReal (G₀ i N c z) :=by
   subst V L We; have hu: f=below P c:= Subtype.ext (by change f.val=(below P c).val; rw [S.sizes,hP]; rfl); subst f; have hT : S=dock P K c:= pactPaid hP hs; subst S; ext1 z; exact stage_imp D R hx F i C a t L' hG hk z
-- C.Fk orientation in Scores, uses exact library Costs n.Pert. Also use marker >0 unaffected.
lemma cover (a:Forest S.ratio)(t:S.Choices)(h:L=i.self.north)(hp:V=(X.p.profile x).clip)(hw:We=i.extra)(hk:N≤ k+2) :
    let x0:= fun z=>Symmetry.Orbit.ground C a t (QuadraticLocal.Fk.grant We T L') (k+2) N (tint G (Exterior.Body 1 c) (exteriorL G c z))
    let p':= vista F.presence i N c
    (∀ z, (x0 z).im=0) ∧ Prices (N+2) (F.revenue.b N i c* dearth F.σ c) ( (Complex.re ∘ x0)-p'):= by
   intro x₁ p'; have he: x₁ = Complex.ofReal ∘ (G₀ i N c):= portal D R hx F i S hP hs hG L' L V We C a t h hp hw hk; rw [he]
   exact ⟨fun _=> rfl,(F.revenue.earns N i hk).2 c (Wheel.Ride.scope_complete S hP hs hG)⟩
end YM.AllOrder.Floe.Step.PlanV
