import YM.AllOrder.Floe.Voyage
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
local notation "I"=> Card D R x y hx k
-- audit arg x implicit λ.
local notation "X0" => fun i:I=> Card.extra i
local notation "V₁" => (p).clip
local notation "V₂" => (q).clip
local notation "Q"=>Plateau.Art (G:=G) (N:=k+2) P K (A x)
-- use notation projections via `₁(x)`
local notation "M₁" => (fun i:I=> i.self.north)
local notation "M₂" => (fun i:I=> i.self.south)
local notation "Λ₀" => (fun i:I=> i.self.paid)
local notation "α₀" => (fun i:I=> i.self.alpha)
local notation "hU" => (fun i:I=> i.self.upCost)
local notation "f₀" => (fun (j:Age)(i:I)=> authority k j i.self.paid)
variable (Qt: Plateau.Art (G:=G) (N:=k+2) (Mural.sheet X.p D hx) X.p.kernel (X.p.profile x)) -- binder.Current price.Any Q => choose Walks grants per Bt.Pioneer
namespace Income
lemma earn_round(hκ:Nonempty I) (g:G.Simple) (hxy:StepStages x y): ∃ U:Income D R x y hx k,U.frame=Qt:= by
 let s':=tape (k+2); let br(x':ℕ) := arms A B K G k x'; let ST:= s₁; let D':=baseS (G:=G) B K x; have ha :((P).Branches K G):= X.p.has (P)
 obtain ⟨F,hF⟩:= tens P K V₁ M₁ Λ₀ Qt hU
 obtain ⟨A'⟩:= tracks P K V₁ M₁ Λ₀ Qt ha hU D' Card.up Card.att1 Card.metric1 Card.floor1 Card.sworn1
 have ht:CreditF Λ₀ 1 Λ₀:= givenC (fun i => budget_nonneg i.self.upCost.two)
 let b:= br x; have h0:0<b:= arms_p ..; have hs(v:Age):0<s₁ v:= (R.shape k|>.pos x _)
 obtain ⟨ζ,hζ,H⟩:= sharpen s' (fun i z=> z ≤ leaseF (s₁ i) (k+2)) (fun i _=>⟨_,lease_pos (hs i) _,fun _ _ h=>h⟩)
 let Z:=min b ζ; have hZ:0 < Z:= lt_min h0 hζ
 obtain ⟨U⟩:= decay P K V₁ M₁ (b:=b) A' (show Z≤ b from min_le_left ..); let d := 1+s'.sup (level k ·+1)
 have hv(v:Age)(hi:v∈s') :request Z (Λ₀) d (k+2) (Card.extra) v:= by
    have hp : level k v +1 ≤ d:= (Finset.le_sup (f:=fun i=> level k i +1) hi).trans (Nat.le_add_left ..)
    exact ⟨f₀ v, s₁ v,hs v, ((allowance_f D R x y hx) v hi |>.1).up hp, H Z hZ (min_le_right ..) v hi,fun i=>(i.quote v hi).pay⟩
 obtain ⟨M,⟨hM⟩⟩:= solo P K V₁ O M₁ Λ₀ Qt ha hU X.oga F hF Card.extra s' (audited D R x y hx) Λ₀ U hZ (le_trans (min_le_left ..) (min_le_left ..)) (ht.up (Nat.le_add_right 1 _)) hv
 have hT : Pace.Cost Λ₀ 1 α₀:= CreditF.down ((freeC |C₀| (abs_nonneg _)).up zero_le_one) (fun i=> i.self.bounded.trans (le_abs_self _)) (fun i=>abs_nonneg _)
 have hC (i:I) n':Channels P K V₁ O M₁ F V₂ M₂ α₀ i n':= by
    obtain ⟨v,η,c,hc,H⟩:=i.self.stationary; obtain ⟨ϖ,d,h,h',hx'⟩:=i.traced n'; refine ⟨ϖ,d,(fun i=>(hx' i).1),h',h,v,η,c,hc,fun j=>?_⟩; have he:= (hx' j).2.1; obtain ⟨ρ,hρ,hK,hΦ⟩:= H (ϖ j) (trees P K _) he; let U:= (channel P K V₁ M₁ V₂ M₂ i.self.tower i (ϖ j)); exact ⟨he,Pane.payouts («R»:=U) ((hF i _ he).is_extension hρ) hK hΦ⟩ -- check
 choose u₀ h' using (fun i:Age=> (show ∃ C:ℝ, i∈tape (k+2)→ PriorDue G (q).clip (p).width (q).width (q).paths (R.pre k x) (R.pre k y) b (X.K.α y) (k+2) i (|X.K.Ω y|) C from Classical.byCases («p»:=i∈tape (k+2)) (fun h=> ((R.shape k).crossing i x y hxy h).imp fun i hi _=> hi) (fun h=> ⟨1,(fun hi=> (h hi).elim)⟩))) -- Classical names & alignment h expansion
 obtain ⟨Vy,Qy,H0⟩:=towerbook P K V₁ O M₁ Λ₀ Qt ha hU X.oga F hF Card.extra T (audited D R x y hx) Λ₀ V₂ M₂ Λ₀ (fun i:I=> i.self.downCost) Card.up Card.down Card.star Card.metric2 Card.att2 Card.floor2 Card.sworn2 s₁ s₂ hM A' (fog D R x y hx Qt F hF) (X.K.eta_pos x) Card.floor1 Card.sworn1 (guard (k+2)) α₀ (guard_ok _) (allowance_f D R x y hx) hs (R.shape k|>.pos y) rfl hT ht ht (abs_nonneg _) (abs_nonneg _) (show k+2=k+2 from rfl) h' (fun i hi j=> j.prior i hi) hC g
 exact ⟨⟨Qt,F,hF,M,Vy,Qy, _,_,hM,H0⟩,rfl⟩ -- check revenue subject and l.
end Income
end PlanV
end YM.AllOrder.Floe.Step
