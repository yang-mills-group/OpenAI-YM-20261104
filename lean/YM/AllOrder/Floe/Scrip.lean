import YM.AllOrder.Floe.Crown
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
-- construction inside (*) one step, through k and f.Entrants. Age set ≤. Carry `ψ output price φ*C` + CreditF.Strict.Growth`
abbrev Fees := Age→ℝ
variable (Γ:ι→ℝ)
abbrev tape (N:ℕ):=Age.scope N
def album (Γ:ι→ℝ)(s f:Fees) (e:ι→ Age→ℝ) (X:Finset Age)(V:ι→Layout G): Prop:= ∀ i∈X, ∀ j,StateE.Quoted (V j i) (s i) (e j i) -- no use Γ.F
-- use abstract model.A generation library club.M.Stories connective.
variable (p:Clip) (x:ι→PathData G) (L:ι→ℝ) (h : ∀ i,(x i).Bounds p a C (L i)) (g:G.Simple)
variable (A:Snap ι G) (s:Fees) (w:ι→ Age→ℝ) (H:ι→Scene G) (α:ι→ℝ)
-- root residual of earlier because sign negative. initialization includes no coupling powers from meter until omega2.Establish receipts.
def ask (p:Clip) (x:PathData G)(F:Scene G)(q:Coin)(X:Finset Age)(V:Layout G) : Scene G:= 0-F-grouping q V X p x
-- hF valid; maintain const strict. ignore ω slots ≥ N.Toll.Other flags charged.Pace.
variable {H} {Q:ι→ Coin} {V:ι→Layout G} (hF:∀ i,Pace.Valid (H i) N) (X:Finset Age)
local notation "W" => (fun i:ι=> ask p (x i) (H i) (Q i) X (V i))
variable (he:∀ i,Legal X (V i)) (hS:Haiku.Coat.strict (fun i=> ask p (x i) (H i) (Q i) X (V i)) k)
include h g he hF
-- call q all tape, hS proof strict through k. Mat.Herm calls.
lemma ask_pose (i:ι): Pace.Valid (W i) N := (Valid.void.sub (hF i)).sub (glories _ _ X _ _ (h i) (he i) g)
include hS
lemma pose (i:ι)(hk:k≤N): Admits ((W i) k):= votes (fun _=> (ask_pose p x L h g hF X he i _ hk _).2) (hS i) (fun n=> (ask_pose p x L h g hF X he i|>.rank _ hk n).read) -- remove Γ param
omit hS
-- prices ancestor.B-snapshot.PriceAPI.Op.Trim l
variable (hv:∀ i∈X,0<s i) (ht:∀ i∈X,∃ f:ι→ℝ,CreditF Γ l f ∧ ∀ j,Extra.Iteration.Charged (V j i) (s i) (f j))
variable (hh:∀ i∈X,Sparkle G (s i) b k i.r)(hs:Slanted G p a C b k)(hd:∀ j≤N,Pace.Cost Γ l fun i=> Q i j)(hL:CreditF Γ l L)(hb:0<b)
include ht hh hv hs hd hL hb
lemma timing {l':ℕ}(hM:money Γ (fun i=>H i r) k l' b)(hr:r≤N) : money Γ (fun i=>W i r) k (l'+l*N+l+l) b := by
 let l'' := (l'+l*N+l+l); let M i:= H i r; let Z₀ i:= grouping (Q i) (V i) X p (x i) r; have hp : Pace.money Γ Z₀ k l'' b:= (bless V X s he hv ht hd p x h hL g hs hb hh hr).squeeze le_rfl hb (by unfold l''; omega); have hv:mental Z₀:= fun i n=> (glories _ _ _ _ _ (h i) (he i) g|>.rank r le_rfl n).read.smooth.contDiffAt.analyticAt;
 have hT: Pace.money Γ (0:ι→Ink.Money.Bills (Coarse G)) k l' b:= money.void (fun i n=>?_) hb; swap; · simp
 have hh:= money.zipper hT hM (fun _ _=>analyticAt_const) (fun i n=>(hF i|>.rank r hr n).read.smooth.contDiffAt.analyticAt); exact money.zipper (hh.2.squeeze le_rfl hb (show l'≤l'' by unfold l''; omega)) hp (fun i n=>analyticAt_const.sub (show AnalyticAt ℝ (H i r n) 0 from (hF i|>.rank r hr n).read.smooth.contDiffAt.analyticAt)) hv|>.2

end YM.AllOrder.Floe.Step
