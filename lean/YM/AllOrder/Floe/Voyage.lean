import YM.AllOrder.Floe.Lamps
import YM.AllOrder.Plateau.Stage
import YM.AllOrder.Floe.Topo
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Harmonic
import YM.PhysicalNext.RANK_COVARIANCE_ATLAS.Atlas
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Floe.Step
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration Pace Aero StateE
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge}{ι:Type}[Nonempty ι]{a b C D Z Λ ε σ Ω:ℝ}{k r m n N l:ℕ}{j:Side}
open Rent PriceCompiler
namespace PlanV
open Aero Kinetic.Port Laurent Bloch Further.PhysicalPeriodLimitF933 Shingle Macrame PhysicalNext ThroughLaunch Pane
variable {X:Metals G} {D:RG.Supply.Rolls X.p}(R:Roots (G:=G) X.p.profile X.K X.p.kernel)(x y:ℕ) -- x stage fine from D
local notation "B" => X.K
local notation "A" => X.p.profile
local notation "p" => X.p.profile x
local notation "q" => X.p.profile y
local notation "K" => X.p.kernel
local notation "O"=> X.O
local notation "Ωz" => abs (X.K.Ω x)
local notation "Ωy" => abs (X.K.Ω y)
variable (D) (hx:4≤x)
set_option quotPrecheck false
local notation "P" => Mural.sheet X.p D hx
local notation "C₀" => Pane.cloak D x
local notation "P'" => Plateau.Ticket (P) K O (A x) (A y) (Pane.cloak D x)
local notation "u" => guard (k+2)
local notation "s₁" => R.pre k x
local notation "s₂" => R.pre k y
local notation "T" => tape (k+2)
abbrev level (k:ℕ)(i:Age):ℕ:=gateE (guard (k+2) i) (k+2)
abbrev authority (k:ℕ)(i:Age)(Λ:ℝ) := (1+|Λ|)^(level k i+1)
structure Card (k:ℕ) where
    self : P'
    up : Bed
    down : Bed
    -- use `star`, not self.tower (α hypothesis from Books witness doesn't conclude equal). not allowed in step billing!
    star : Towers (D.L x)
    extra : Layout G
    quote i (h:i∈Age.scope (k+2)) : Quoted (extra i) (R.pre k x i) (authority k i self.paid)
    prior i (h:i∈Age.scope (k+2)) : StateE.Kernel (R.pre k x i) (R.pre k y i) (abs (X.K.Ω x)) (abs (X.K.Ω y)) (D.L x) up down star
    metric1 : up.metric.strip (X.K.α x) Ωz
    metric2 : down.metric.strip (X.K.α y) Ωy
    att1 : Attached up self.north
    att2 : Attached down self.south
    floor1 n' : Floor up (A x).clip n' (X.K.η x) Ωz
    floor2 n' : Floor down (A y).clip n' (X.K.η y) Ωy
    sworn1 n' : Bid.Sworn up n' G
    sworn2 n' : Bid.Sworn down n' G
    traced : ∀ n:Side, Aero.ContinuousLife (fun (l:Side)=> let W:=dock P K l; Ad G P K l ∧ Towers.Diagonal W up down star ∧ ∀ t:Forest W.ratio, ∃ ρ, Critical (S:=W) t (X.p.profile x).clip self.north ρ ∧ Precision.Guessed (S:=W) t (installed W.ratio star.A0) ρ) n
local notation "I"=> Card D R x y hx k
-- audit arg x implicit λ.
local notation "X0" => fun i:I=> Card.extra i
local notation "V₁" => (p).clip
local notation "V₂" => (q).clip
local notation "Q"=>Plateau.Art (G:=G) (N:=k+2) P K (A x)
namespace Card
def north (i:Card D R x y hx k) : PathData G:=i.self.north -- explicit auto includes!
end Card
-- use notation projections via `₁(x)`
local notation "M₁" => (fun i:I=> i.self.north)
local notation "M₂" => (fun i:I=> i.self.south)
local notation "Λ₀" => (fun i:I=> i.self.paid)
local notation "α₀" => (fun i:I=> i.self.alpha)
local notation "hU" => (fun i:I=> i.self.upCost)
local notation "f₀" => (fun (j:Age)(i:I)=> authority k j i.self.paid)
lemma allowance_f : Fleet (Λ₀) (guard (k+2)) (k+2) (X0) (tape (k+2)) f₀ (s₁):=by
 intro i hi; refine ⟨⟨1,zero_le_one, fun j =>⟨pow_nonneg (by positivity) _,by rw [one_mul]⟩⟩,fun j=>j.quote i hi⟩ -- maybe nonempty not needed
lemma audited (i:I):Legal T i.extra:= by have h : Nonempty I:= ⟨i⟩; exact (allowance_f D R x y hx|>.legal X0 T ((R.shape k).pos x) i)
lemma guessed_eq {c f:Side}{S:StepData c f}{t:Forest S.ratio}{ρ χ:Exterior.fieldDir G c 1 → AxisChart G t}{V} (hf:Precision.Guessed (S:=S) t V ρ)(hg:χ =ᶠ[𝓝 0] ρ): Precision.Guessed (S:=S) t V χ:= fun v=>(hf v).congr_of_eventuallyEq ((show Tendsto (fun t:ℝ=>t • v) (𝓝 0) (𝓝 0) from by simpa using! (tendsto_id (x:=𝓝 (0:ℝ))).smul_const v).eventually hg)
variable (Qt: Plateau.Art (G:=G) (N:=k+2) (Mural.sheet X.p D hx) X.p.kernel (X.p.profile x))(F:Card D R x y hx k→candidates (Mural.sheet X.p D hx) X.p.kernel G)(h:proofC (Mural.sheet X.p D hx) X.p.kernel (X.p.profile x).clip (fun i:Card D R x y hx k=> i.self.north) Qt F)
include h
lemma fog (i:I)(n:Side) : Aero.ContinuousLife (fun n=> Ad G P K n ∧ (Towers.Diagonal (dock P K n) i.up i.down i.star) ∧ Precision.Guessed (S:=dock P K n) (trees P K n) (installed ((dock P K n).ratio) i.star.A0) (F i n)) n:= by
 obtain ⟨Y,d,hh,he,hm⟩:=i.traced n; refine ⟨Y,d,hh,he,fun k =>?_⟩; obtain ⟨hx,hh,hξ,hΩ⟩:=hm k; obtain ⟨ρ,hp,hq⟩:=hΩ (trees P K _); exact ⟨hx,hh,hξ,guessed_eq hq ((h i _ hh).is_extension hp |>.symm)⟩
-- license bodies & future local horizon real.Pone.
local notation "G₀"=> prePhase P K (A x).clip O M₁ Λ₀ Qt (fun i:I=> i.self.upCost) X.oga F h (Card.extra) (tape (k+2)) (audited D R x y hx)
local notation "w"=>fun j:Age => R.wage x y k ((D.L x).val:ℝ) j
structure Income (k:ℕ) where -- avoid Q' binder uses k
   frame : Plateau.Art (N:=k+2) (G:=G) P K (A x)
   tools : Card D R x y hx k → candidates P K G
   efficient : proofC P K V₁ (fun i:Card D R x y hx k=> i.self.north) frame tools
   presence : Snap (Card D R x y hx k) G
   laid : Card D R x y hx k → Layout G
   issue : Card D R x y hx k → Coin
   l : ℕ -- placeholder
   σ : ℝ
   revenue : Scores (Ad G P K) (fun i:Card D R x y hx k=> i.self.paid) σ l (k+2) (Function.swap (prePhase P K V₁ O (fun i:Card D R x y hx k=> i.self.north) (fun i=>i.self.paid) frame (fun i=> i.self.upCost) X.oga tools efficient (Card.extra) (tape (k+2)) (audited D R x y hx))) presence
   sustenance : Step.Sustained (fun i:Card D R x y hx k=> i.self.paid) (guard (k+2)) (fun i=>i.self.alpha) (k+2) (R.pre k y) (vista presence) (fun i=>i.self.south) (fun i v=>R.wage x y k ((D.L x).val:ℝ) i * authority k i v.self.paid) k V₂ laid issue
end PlanV
end YM.AllOrder.Floe.Step
