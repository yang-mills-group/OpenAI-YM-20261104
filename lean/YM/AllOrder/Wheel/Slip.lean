import YM.AllOrder.Wheel.Languish
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
abbrev δE (A:I)(β:ℝ):= now (F.issue A) (κs+2) β-β -A.self.alpha
local notation "Λ"=>fun i:I=>i.self.paid
-- Pointwise clock no sizing.∆ prediction and α all phases stands at weather.
structure Note (g:ℝ) where
    token : I
    earns : token.self.paid = strengthP (betaF G g (D'.L x))
    beta : ℝ
    band : beta∈Set.Icc (betaF G g (D'.L x)/2) (2* betaF G g (D'.L x))
local notation "Tc"=>Aux.fare G (LΩ)
local notation "Φ"=> Note D' S x y hx (q:=q)
local notation "τ"=> Tc
local notation "Ω"=> (τ).stage Φ
-- not using roster view.Later supports. zone.Coarse need proximity β goal.A.Light.See.
include F
lemma lesson : Hall Ω (κs+2) (fun i=> i.2.beta) (fun i=> F.issue i.2.token):= by
    let V₀ := Sigma Φ; let P:V₀→ I:=fun i=>i.2.token; let S':= Ω; let H:= (Tc).liftF (Y:=V₀) Sigma.fst; let W i:=Step.PlanV.strengthP (S'.cost i); let t:V₀→ℝ:=Sigma.fst; have h : S'.Meter (Λ∘P) 0:= Meter.eq_mem (Looks.transfer (f:=strengthP) H (Burn.hats_rate (G:=G))) (Eventually.of_forall fun i=> i.2.earns.symm); let f(i:V₀):=i.2.beta
    have hv : ∀ᶠ i in S'.rail, Burn.Near (S'.cost i) (f i) ∧ f i>0:= by filter_upwards [S'.positive] with i hi; obtain ⟨hs,hp⟩:= i.2.band; let Z:= S'.cost i; change Z/2≤ f i at hs; change f i≤2*Z at hp; change 0<Z at hi; exact ⟨⟨by linarith only [hs,hi],by linarith only [hp,hi]⟩,by linarith only [hi,hs]⟩
    have hz:Looks G (LΩ) S' t:= H; have hw:= hz.costs («v»:=f) (hv.mono fun i hi=> hi.1) H -- arg order? v notation
    refine ⟨⟨hv.mono fun i hi=>hi.2,Meter.smaller ((Looks.slow H).lscale 4) (hv.mono fun i hi=>(((abs_of_pos hi.2).le.trans hi.1.2).trans (le_abs_self _))), hw.1,hw.2⟩,fun j hj=> ?_,Eventually.of_forall fun i=> ⟨(F.sustenance.due _).1,(F.sustenance.due _).2.1⟩⟩
    let hs(j:I):=F.sustenance.due j; rcases j with _|j; · exact (Meter.nil S' _).eq_mem (Eventually.of_forall fun j=> (hs _).1.symm)
    rcases j with _|j; · exact (Meter.nil S' _).eq_mem (Eventually.of_forall fun j=> (hs _).2.1.symm)
    rcases j with _|j; · apply Clock.Meter.smaller (Clock.Meter.const S' (cloak D' x)); exact Eventually.of_forall (fun (i:V₀)=> by rw [(hs _).2.2]; exact i.2.token.self.bounded.trans (le_abs_self _))
    have hr:= bill_transfer (F.sustenance.income j (by omega)|>.grade) (show S'.Meter (Λ∘P) 0 from h); exact hr.smaller (Eventually.of_forall fun i=>(abs_abs _ |>.symm.le))
lemma fee_delta (a:ℝ)(hp:a>-(1/2)):∀ᶠ i:ℝ in atTop, ∀ A:I, A.self.paid=strengthP (betaF G i (LΩ))→∀ β, β∈ Set.Icc (betaF G i (LΩ)/2) (2* betaF G i (LΩ)) → |δE D' S x y hx F A β| ≤ betaF G i (LΩ)^a:= by
    let H:=lesson D' S x y hx F; have he:= Hall.fee_d H (by omega); filter_upwards [(Tc).everybody (V:=Φ) _|>.1 (he a hp)] with i hi A hx β hv; let V: Φ i:= ⟨A,hx,β,hv⟩; have ht:= hi V; unfold δE; rw [← (F.sustenance.due A).2.2]; exact ht
-- clamps ratio at TWO levels epoch. does not deliberately force width. Demand `Burn.Near m (βform)`. need sign q.C.N.
lemma prior_d : ∀ᶠ i:ℝ in atTop, ∀ A:I,A.self.paid=strengthP (betaF G i (LΩ))→∀ β,β∈ Set.Icc (betaF G i (LΩ)/2) (2* betaF G i (LΩ))→ Burn.Near i (now (F.issue A) (κs+2) β):= by
 -- soft |∆β| relative; ≤ constant. t ~ cost.T positive.
 let J:= (LΩ); let W i:= betaF G i J; let K':=G.slopeConstant*Real.log J.val; let h:= fee_delta D' S x y hx F (-(1/4)) (by norm_num); let d:= cloak D' x; have ht': ∀ᶠ i:ℝ in atTop, (W i)^(-(1/4):ℝ)≤1:=(((Work.E09.betaF_growth G (LΩ)).eventually_ge_atTop 1).mono fun x hx=> Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num));
 filter_upwards [h,eventually_gt_atTop (32*(|K'|+|d|+1)),ht'] with i hi hp he A ha β hB; have hv:= abs_le.mp ((hi A ha β hB).trans he); have hz₀:β ≤2*W i:=hB.2; have hz₁:W i/2≤β:=hB.1; have hh:W i=i+K':= rfl; let Z:= A.self.alpha; have ht: |Z| ≤ d:= A.self.bounded; unfold δE at hv; constructor <;> linarith [le_abs_self d,(abs_le.mp ht).1,(abs_le.mp ht).2,le_abs_self K', neg_abs_le K']
end Pair
end Ride
end YM.AllOrder.Wheel
