import YM.Qlocal.Skating.Ahora
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Actual
open Function Filter Set Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open Marker MeasureTheory Extra.Trajectories Overlay RG3.Press RG3.Held RG3.Script.Picnic RG3.Forms
open PhysicalNext PhysicalNext.Repeat Progress.DirectedRecipe
open ConnectedActivityE6 AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Metric Height Roof Input Org Supply Pane Slide
open Further.PhysicalPeriodLimitF933 PriceCompiler ThroughLaunch Opera Boulevard Trio Lantern Roost PhysicalNext.Repeat.Legato
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius Classical ContDiff BigOperators YM.Qlocal.Payload
open AllOrder Transit Transit.WheelP Floe.Step.PlanV
open RGComparison01 RGComparison01.Pledge
open Leasing Integration Integration.LocalComparison Integration.RiderTastePresentation
open Program Program.Camp Program.Certificate
variable {Ω V : Type} [DecidableEq V] {B:Marker.Census V} {G:Gauge} {m k p N j k' z n l v : ℕ} {δ r θ u E C ℓ: ℝ}
open Primitives.TwoWave Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open AllOrder Ker Ker.Start Haiku Haiku.Coat Fire Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money
open Work.G05 Kinetic.Port Kinetic Binding
open Comparison.RG02.Bulk
open Org Floe Pace Step.PlanV
-- guard notation all dependent arguments fully (macro locality)
variable (X:Run G)
set_option quotPrecheck false
local notation "W"=> X.metals
local notation "D"=> X.rolls
local notation "A"=> X.alloy
local notation "C"=> X.family
local notation "Y"=> RunFormalChain.fromRun X
local notation "a"=> X.alloy.B.a
local notation "K"=> X.metals.p.kernel
local notation "J"=> X.alloy.B.a.clock.J (m+1)
local notation "J'"=> X.alloy.B.a.clock.J m
local notation "t₀"=> X.alloy.B.a.clock.adm (m+1)
local notation "κ"=> X.metals.p.profile
local notation "P"=> Mural.sheet X.metals.p X.rolls (X.alloy.B.a.clock.adm (m+1))
local notation "S"=> (a).clock.op m p
local notation "c"=> (a).S.side m p
local notation "f"=> (a).S.side (m+1) p
local notation "f₀"=> (κ J).clip
local notation "p₀"=> (κ J').clip
local notation "k₀"=> Burn.horizon k
local notation "Z"=> Age.scope (Burn.horizon k+2)
variable (R: Roots (G:=G) X.metals.p.profile X.metals.K X.metals.p.kernel)(Q:R.Tab X.rolls)
local notation "I"=> Card D R J J' t₀ k₀
open Squall Squall.Lumber Skating Skating.Rune
open Dredge Quipu Quipu.Sonnet Tern Quipu.Eluder Quipu.Eluder.Incline Quipu.Eluder.Incline.Bookworm
namespace Booth
-- Beacon m Ready uses specific Dough.P.ClockExpiry any PTO.H.Canvas.Sensor.Metadata.Shape.Current stencil, rank. no full tensor. permits ψ.Frame.Program.SupportedB \f shade. claim Orbit.Material.Scope only for Estimate. Include Burn Return.C.
variable (η ζ:ℕ→ℝ)(H T:ℕ→ℕ) -- H capacity Rough Epoch extra
variable {w:ℕ→Layout G}{Γ: ℕ→ Pace.Coin}{x:(i:ℕ)→RG.Rep G ((X.alloy).B.a.S.side i p)}
variable (g:G.Simple) (hK:TicketP X.alloy X.kit R Q)
local notation "d♥"=> (A).delay
local notation "F"=> X.kit
structure Fair (X:Run G)(R: Roots (G:=G) X.metals.p.profile X.metals.K X.metals.p.kernel)(Q:R.Tab X.rolls) : Prop where
    resource : TicketP X.alloy X.kit R Q
    breath : YM.Qlocal.Schedule.Breath X.metals X.rolls R
    crew : Account η T ζ X.metals X.rolls X.alloy X.kit R Q
-- Count M.Book pre_ reserve.W.Memory.Public.Player.Beta.a.C.Body.p.SupportAt. All births in one x.Cut Frame.Ensemble.
variable (hF:Fair η ζ T X R Q) (h:Step.PlanV.Path R X.alloy Q (Burn.horizon k) N z w Γ) (hk:z ≤ m) (he:m<N) -- ≤ m lex
local notation "Tq"=> X.family.path
local notation "Hn"=> horizon k
local notation "m₀"=> (A).delay -- not useful remove
structure Art (he:m<N) : Prop where
 action : ∃ (X':Card X.rolls R J J' t₀ k₀) (h0:k₀+2≤ J'), Journey R X.alloy (m:=m) (N:=N) X'∧ w (m+1)=X'.extra ∧ w m=(litP R X.alloy Q h0 X').laid X' ∧ Γ m=(litP R X.alloy Q h0 X').issue X' ∧ ∀ d r₀:ℕ,d≤ J→ r₀ ≤ J → ∃ (M:Runway X.kit m η T d r₀)(hB:Pleased (R:=R) (ζ:=ζ) X.kit M), Demand X R Q he hK M hB X' w Γ (z:=z)
include h hk he g hF
lemma engaged : Art X R Q η ζ T hK (k:=k) (w:=w) (Γ:=Γ) (z:=z) he:= by
 obtain ⟨X',hx,hQ,hB,hC,hΓ⟩:= h.2.2 m hk he; constructor; refine ⟨X',hx,hQ,hB,hC,hΓ,fun d r hd hr=>?_⟩
 obtain ⟨M,hM⟩:=(show Lumber.Plan X.kit.shape η T X.kit.scout R X.alloy.delay ζ from hF.crew).supplies J J' (step_paid (a) m) t₀ d r hd hr; exact ⟨M,hM,Booth.demands X R Q he hK _ hM X' hQ hx g w Γ hk hB⟩ -- order check.
omit h he hk
structure Awake (k z N:ℕ) :Prop where
    heads : ∃ (w:ℕ→Layout G)(Γ:ℕ→Pace.Coin), Step.PlanV.Path R X.alloy Q (Burn.horizon k) N z w Γ ∧ (∀ p:ℕ,∃ x,Metre X.alloy X.kit X.T w Γ z N p k x) ∧ ∀ (m:ℕ), z≤ m →∀ (he:m<N), Art X R Q η ζ T (k:=k) (w:=w) (Γ:=Γ) hK (z:=z) he
-- corridor per size eventual.Start bound no assumption. At each k all wake.B.He.Card.Caption.Reset.Weight.World.T.Price fields from existing manuscript.Frame.Gened. Need carry & Startup separately.
lemma breaking (hk:k₀+2≤ X.family.path.levels.clock.J z)(hN:z≤ N): Awake X R Q η ζ T hK k z N:= by
 obtain ⟨W',Γ,hW,h⟩:= WheelP.obligeK R Q X.alloy X.kit z k N g hk X.T X.tuning.receipts hK hN; exact ⟨W',Γ,hW,h,fun i hi he=> engaged X R Q η ζ T g hK hF hW hi he⟩ -- check order.
omit hF
-- parameter pledge also includes full repeated unmarked station in .resource & enough expenses Camp λ rough if needed. Not alter F.Frame.Path Mea2 estimates.PowerBudget.Motion.Mesh.Tag.
local notation "ϕ"=> Schedule.accompanying (Schedule.berth (Account (G:=G) η T ζ)) (Program.booked η H T)
lemma chosen (d:ℝ) (he:0<d)(hp:∀ i,0 < η i)(hr:∀ i,0<ζ i) :∃ (X:Run G) (R: Roots (G:=G) X.metals.p.profile X.metals.K X.metals.p.kernel) (Q:R.Tab X.rolls) (C':Camp X.kit η H T), X.family.path.levels.clock.kernel.penalty=d ∧ C'.height=(fun i=> H (X.alloy.B.a.clock.J (i+1))) ∧∃ hF:Fair η ζ T X R Q, ∀ (k z N:ℕ), (Burn.horizon k)+2≤X.alloy.B.a.clock.J z → z≤ N → Awake X R Q η ζ T hF.resource k z N:= by
 have hf: Schedule.Obtainable (Schedule.berth (Account (G:=G) η T ζ)):= Lumber.granted η T ζ hp hr g; obtain ⟨Xr,hM,hb,hK⟩:= Run.rampK g (hf.also (Program.sold η H T g hp)) d he; obtain ⟨X',Y',hF,hP,hξ⟩:= hb; let hB:Fair η ζ T Xr X' Y':=⟨hF,hP,hξ⟩;
 obtain ⟨Qw,hQ⟩:= Program.supplier Xr.kit η H T hK (d:=fun m=>H (Xr.alloy.B.a.clock.J (m+1))) (fun i=>le_refl _); exact ⟨Xr,X',Y',Qw,hM,hQ,hB,fun k z N hp h'=> Booth.breaking Xr X' Y' η ζ T g hF hB hp h'⟩
end Booth
end YM.Qlocal.Actual
