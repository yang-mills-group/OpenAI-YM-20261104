import YM.AllOrder.Wheel.Stage
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Wheel
open Function Filter Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid Planned.JetPort
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration Catch Catch.Clock Floe StateE Pace Plateau
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G: Gauge}{L n f : Side}{ι:Type*}{T:Clock ι} {K:KernelChoices}{P:Patch}{σ C b a D η κ:ℝ}{k l p j M:ℕ}
open ConnectedActivityE6.Coat Shellac Work.G05
open Aux Aux.Name Push.PriceCompiler Kinetic.Port -- Bench check
namespace Ride
-- ticket Frame j,P for lower Progress.Power independent of upper moment-gauge. If P->canonical.Guess match all forest shifts Scope. Stamp operator compatibility.Coordinates.
lemma scope_complete {n f:Side}(S:StepData n f)(h:S.patch=P)(hp:S.kernel=K)(hs:Larger (G:=G) S): Ad G P K n:= by
 have he: f=below P n:= Subtype.ext (by change f.val = (below P n).val; rw [S.sizes,h]; rfl)
 subst f; have hV:S=dock P K n:= by cases S with | mk x y => dsimp only at h hp; subst P K; rfl;
 subst S; exact  hs
lemma era_price (P:Patch) (K:KernelChoices)(hP:StepData n f)(h:hP.patch=P)(hx:hP.kernel=K)(H:hP.patch.Branches hP.kernel G)
    (O:ChartRatio G)(hO:LocalRatio O) (T:Forest hP.ratio)(ℓ:hP.Choices) {R R':PathData G}{q q':Clip}{X X':Floe.Layout G} (v:Finset Age)
    (V:Desk T O (spend X v (primitive R q)) ℓ) (H':Desk (trees P K n) O (spend X' v (primitive R' q')) (label (dock P K n))) (hh:0<V.paid 0) (hh':0<H'.paid 0)
    (hv: ∀ z,Laplace.Toll f (spend X v (primitive R q) z)) (hR:R=R') (ht:X=X') (he:q=q'): Response.ratePlan V= Response.ratePlan H':= by
 subst X' q' R'; have he: f=below P n:=Subtype.ext (by change f.val=(below P n).val; rw [hP.sizes,h]; rfl); subst f; have hZ:hP=dock P K n:= by cases hP with | mk x y=> dsimp only at h hx; subst P K; rfl
 subst hP; exact Response.exactly _ _ hh hO H hv hh'
open Aero Sienna Further.PhysicalPeriodLimitF933
variable {r p:Stage} (K) {q:ℕ}{w:ℝ→ℝ} (O:ChartRatio G)(hO:LocalRatio O)
local notation "κs"=> Burn.horizon q
-- Actor.Action.AlphaSchedule.Grow α.Bridge uses $P$ from patch.L.A admissible ∀ Actor Booth. Do not require hall α threshold yet. positions.Condition t∈W.Cash.
namespace Pair
open Aero Step Step.PlanV Laurent Bloch Further.PhysicalPeriodLimitF933 Shingle Macrame PhysicalNext ThroughLaunch Pane
variable {X:Metals G} {D':RG.Supply.Rolls X.p}(S:Roots (G:=G) X.p.profile X.K X.p.kernel)(x y:ℕ) (hx:4≤x)
local notation "B"=> X.K
local notation "v"=>X.p.profile x
local notation "u"=>X.p.profile y
local notation "K"=>X.p.kernel
set_option quotPrecheck false
local notation "L"=>Mural.sheet X.p D' hx
local notation "LΩ"=>D'.L x
local notation "Art"=>Plateau.Art (G:=G)
local notation "I"=>Card D' S x y hx κs
local notation "D*"=> Income D' S x y hx κs
variable (D') (U:Uniform.Before G (X.p.profile x).width (X.p.profile x).paths (Mural.sheet X.p D' hx).J X.p.kernel (k+3)) (F: Income D' S x y hx (Burn.horizon q))
local notation "Ic"=> Aux.Name G L K w q v k U
local notation "Θ"=>X.O
abbrev ProbeU := Σ («u»:Card D' S x y hx (Burn.horizon q)), Aux.Name G L K w q v k U -- not needed
-- No flag or projection yet.Call.Sight.Wear uncert. Fee.A.Operator
structure Pact (A:I)(C:Ic): Prop where
    shape : A.extra=C.shape
    top : A.self.north=C.tube.up
    bottom : A.self.south=C.tube.down
    low : C.tube.low= (u).clip
    paid : A.self.paid= Step.PlanV.strengthP (betaF G C.whenP (Mural.sheet X.p D' hx).L)
    tension : Pressure.Stores.till C.whenP ≤ C.c.val
variable (A:Card D' S x y hx (Burn.horizon q)) (C:Aux.Name G (Mural.sheet X.p D' hx) X.p.kernel w q (X.p.profile x) k U) (h:Pact D' S x y hx U A C)
local notation "Θ'"=>X.oga
include F h
lemma dawn : let n:= C.c; let hP:= (scope_complete C.data C.step C.rates C.loom.large); let U':=F.frame; let f:=trees L K n; let ℓ:=label (dock L K n); let p':=(v).clip
      C.tag Θ Θ'=Response.ratePlan (augment f A.extra (tape (κs+2)) (startup f Θ ℓ A.self.north p' U' hP A.self.upCost (F.efficient A n hP) Θ') (audited D' S x y hx A)):= by
 intro n hn W' V₀ ℓ p'; let hX:= C.path.choose_spec; let c:= C.tube; exact Ride.era_price L K C.data C.step C.rates C.loom.large.1 Θ Θ' C.Fs C.choices (tape (κs+2)) (C.tall Θ Θ') _ (mul_pos (pow_pos X.oga.scale _) (Real.exp_pos _)) (mul_pos (pow_pos X.oga.scale _) (Real.exp_pos _)) (fun z=>Floe.orchestra C.tube.up C.tube.high C.shape (Aux.scope q) (C.legal) z hX) h.top.symm h.shape.symm C.high
lemma worth (hk:j ≤ (Burn.horizon q)+2): ∃ r:ℝ, Prices (j+2) (((F.revenue.b j A) C.c)* dearth F.σ C.c) ((C.tag Θ Θ' j ∘ exteriorL G C.c) -(vista F.presence A j C.c) - fun _=> r):= by
 let n:= C.c; 
 let hh:= (scope_complete C.data C.step C.rates C.loom.large); let V:= ((v).clip); let Z:=startup (trees L K n) Θ (label (dock L K n)) (A.self.north) V F.frame hh A.self.upCost (F.efficient A _ hh) Θ'; let Q:= augment (trees L K n) A.extra (Age.scope (κs+2)) Z (audited D' S x y hx A); let p₀:= preview Q
 have hn: Nonempty I:= ⟨A⟩; let f:= prePhase L K V Θ (fun (a:I)=> a.self.north) (fun a=>a.self.paid) F.frame (fun i=>i.self.upCost) Θ' F.tools F.efficient (Card.extra) (Step.tape (κs+2)) (audited D' S x y hx); let he (b:Link G C.c):ratePlan Q j (exteriorL G n b)= just p₀ j+ f A j n b:= precise_top L K V Θ _ _ _ (fun i:I=>i.self.upCost) Θ' F.tools F.efficient (Card.extra) (Step.tape (κs+2)) (audited D' S x y hx) A n hh b j; -- dots
 let z':= (F.presence j A).table n; refine ⟨just p₀ j,?_⟩; have h' : C.tag Θ Θ'=ratePlan Q:= dawn D' S x y hx U F A C h; rw [h']; refine ((?_ : ratePlan Q j ∘ exteriorL G n-z'-(fun _=>just p₀ j)=f A j n-z').symm ▸ (F.revenue.earns j A hk).2 _ hh); ext1 b; simp only [Function.comp_apply,Pi.sub_apply, he]; ring
end Pair
end Ride
end YM.AllOrder.Wheel
