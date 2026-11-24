import YM.AllOrder.Wheel.Riot
import Mathlib.Order.Filter.Curry
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
variable (D') (U:Uniform.Before G (X.p.profile x).width (X.p.profile x).paths (Mural.sheet X.p D' hx).J X.p.kernel (k+3+3)) (F: Income D' S x y hx (Burn.horizon q))
local notation "Ic"=> Aux.Name G L K w q v (k+3) U
local notation "Θ"=>X.O
local notation "Θ'"=>X.oga
-- all sensing stamps choose Budget(J,R) physical width.Y.S.A.Green.Atomic.Contact. Actor filter before choosing ζ e for next release Mirror moves.
open PertExtension.Series.Tested
abbrev Film:= ℝ × ℝ
abbrev film:= Filter.curry (𝓝[>] (0:ℝ)) (atTop (α:=ℝ))
lemma time_l : Tendsto Prod.snd film atTop:= tendsto_snd.mono_left Filter.curry_le_prod
def life (G:Gauge)(L':Side) : Clock Film:= ⟨film, fun i=> betaF G i.2 L', (Work.E09.betaF_growth ..).comp time_l⟩
abbrev tunnel (δ:ℝ):= -(1/2:ℝ)+δ
abbrev velocity (G:Gauge)(L':Side)(δ:ℝ)(x:ℝ):= (betaF G x L')^tunnel δ -- prototype
lemma warp_area (G:Gauge)(L':Side): (life G L').Meter (fun i=>velocity G L' i.1 i.2) (-(1/2)):= by
 intro b hb; let P:=life G L'; let s:= b+1/2; have hs:0<s:=(by unfold s; linarith); apply eventually_curry_iff.mpr; have hc:∀ᶠ x:ℝ in (𝓝[>] (0:ℝ)), 0<x∧ x<s:= Tested.eventually_small hs; filter_upwards [hc] with i hi; filter_upwards [(Work.E09.betaF_growth G L'|>.eventually_ge_atTop 1)] with z hz; unfold velocity; let p:=betaF G z L'; change |p^tunnel i|≤ p^b; have hw:1≤p:=hz; rw [abs_of_nonneg (by positivity)]; apply Real.rpow_le_rpow_of_exponent_le hw; unfold tunnel; unfold s at hi; linarith only [hi.2]
abbrev deltaN(V:I)(β:ℝ) := now (F.issue V) (κs+2) β
-- group state.
abbrev localC (A:I)(C:Ic): C.X→ℝ := C.realCost Θ + ((now (F.issue A) (κs+2) C.beta • staff C.tube.low C.tube.down C.c) + Precision.loop C.tube.down ∘ Desk.night (c:=C.c) + spell (κs+2) (F.laid A) (now (F.issue A) (κs+2) C.beta) (radiusB C.whenP) C.c ∘ Desk.night)
local notation "J"=> life G (LΩ)
local notation "H"=> S.pre κs x
structure Keynote (d s:ℝ)(A:I)(C:Ic)(V:C.X) : Prop where
    writes : Pact D' S x y hx U A C
    paid : C.goods Θ d s V ∧ C.goods Θ d s 0
    awake : Aux.Name.Civil C (S.pre (Burn.horizon q) x)
-- Height uniformization
structure Meet (d:ℝ)(C':ℝ→ℝ)(i:Film) where
    W : Card D' S x y hx (Burn.horizon q)
    Y : Ic
    whenP : i.2=Y.whenP
    V : Y.X
    ready : Keynote D' S x y hx U d (C' i.2) W Y V
    due : ‖V‖≤ velocity G (D'.L x) i.1 i.2
variable (G D) (h0:0<D) (C':ℝ→ℝ) (hp:Rate G (D'.L x) 0 C') -- binder
local notation "Ψ"=> Meet D' S x y hx U (w:=w) (q:=q) D C'
local notation "Ω"=> J
local notation "Ts"=> (J).stage Ψ
variable (hw:Lantern.Bolt G (D'.L x) w)
include F hp h0 hw
lemma member (hj:κs+5≤j)(hG:G.Simple)(hl:κs+2≤k)(ht: Aux.Name.StellarP G (LΩ) j k (graded (κs+2+1)) κ)(s:ℝ)(hs:s> graded (κs+3)) :
    ∀ᶠ z in (J).rail,∀ m :Meet D' S x y hx U (w:=w) (q:=q) D C' z, Brush j ((J).cost z^s) (velocity G (LΩ) z.1 z.2)⁻¹ (off (localC D' S x y hx U F m.W m.Y)) m.V := by
 let N:= Ts; let W:= Sigma Ψ; let f (i:W):= i.2.W; let g(i:W):= i.2.Y; let z (i:W):= i.2.V; let V i:=(Sigma.fst (β:=Ψ) i); let q' (i:W):= velocity G (LΩ) (V i).1 (V i).2; have hV: Clock.Fare (J) (U:=N) V:= (J).liftF _; have he: (life G LΩ).cost= (fun i=> betaF G i.2 (D'.L x)):=rfl; have h'(i:W): (V i).2= (g i).whenP:= i.2.whenP;
 have hF: Looks G LΩ N (fun i=>(g i).whenP):= by
    refine ⟨(time_l.comp hV.tends).congr h', hV.same.trans (Eventually.of_forall fun i=>?_)⟩; change betaF G (V i).2 (LΩ)= _; rw [h']; rfl
 have hQ: Proper g N:= ⟨hF,hw, S.pre (Burn.horizon q) x,(S.shape _).pos _,Eventually.of_forall fun i=> i.2.ready.awake⟩; let a i:= C' (V i).2; have ha:N.Meter a 0:= Clock.Meter.eq_mem (Looks.bill hF hp) (Eventually.of_forall fun i=> congr_arg C' (h' i).symm)
 have hh:∀ᶠ i in N.rail,0<q' i ∧ ‖z i‖ ≤ q' i:= N.positive.mono (fun i hi=> ⟨Real.rpow_pos_of_pos hi _,i.2.due⟩)
 have hv:= rounded (z:=z) D D' S x y hx U F f g (T:=N) (Eventually.of_forall fun i=> i.2.ready.writes) hQ q' ((warp_area G LΩ).pays V hV) hh hj hG hl h0 ht a ha (Eventually.of_forall fun i=> i.2.ready.paid); exact (J).everybody (p:=fun i:W=> Brush j (N.cost i^s) ((q' i)⁻¹) (off (localC D' S x y hx U F (f i) (g i))) (z i)).mp (hv s hs)
end Pair
end Ride
end YM.AllOrder.Wheel
