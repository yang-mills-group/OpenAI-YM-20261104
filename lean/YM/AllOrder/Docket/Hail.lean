import YM.AllOrder.Docket.Hair
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Aux
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open PertExtension.Series Laplace Laplace.SigmaP Response Laurent Stationary
open PositionX.Jet Extra.Iteration Floe Floe.Pace Floe.Aero Floe.StateE
open Catch Catch.Clock Sienna 
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge} {L n f: Side}{ι:Type*}{T:Catch.Clock ι} {W b D α a B C Ω κ V:ℝ}{k p M:ℕ}
variable {P:Patch}{K:KernelChoices}{S : StepData n f} {s:Teller G}{η : Stage}
open Metric ConnectedActivityE6.Coat
namespace Name
variable {r:Stage}{j:ℕ}{u:ℝ→ℝ} {t w x:ℕ}{U:Push.Uniform.Before G r.width r.paths P.J K ((k+3)+3)}
variable (A: Aux.Name G P K u x r (k+3) U)
local notation "I"=>Aux.Name G P K u x r (k+3) U
local notation "ξ"=> Aux.scope x
local notation "d"=> A.Θ
local notation "Θ"=> A.price.threshold
open Till Tilt Lantern
local notation "F"=> A.Fs
local notation "X"=> A.X
local notation "Y"=> Body A.Vx
variable {O:ChartRatio G}(hO:LocalRatio O)
variable (W:ι→Aux.Name G P K u x r (k+3) U) (h:Proper W T)
set_option quotPrecheck false
local notation "V'"=>fun i=> (W i|>.Bank O)
local notation "b'"=> (fun i=> (W i).Θ)
local notation "hX"=> T.Meter
set_option quotPrecheck false
local notation "Λ"=> T.rail
local notation "R"=> fun i=> (W i).Qc
local notation "K'"=> fun i=> (W i).Ph
local notation "M₁"=> fun i=> (W i).Mh
local notation "Q'"=> fun i=> (W i).Zc
variable (D) (hD:0<D) {p:ι→ℝ}
local notation "Z"=> fun i=> (W i).aster O hO
-- Point & forecast, interpolation, projection. Actual Taylor Γ still per-Step.Density.All.Clock.Power.
variable {y z:∀ i,(W i).X} (hg:∀ᶠ i in T.rail,(W i).goods O D (p i) (z i))(hp:T.Meter p 0)
local notation "r'"=> fun i=> receipt (W i) O hO
include h hO hD hg hp
lemma reach (hx:T.Meter (fun i=> ‖z i‖) (-(1/2))){h':ℝ}(hl : StellarP G P.L j k a h') : Catch.Cover T j a (fun _=>1) (fun i=> r' i k) z := by
 let K i:= Metric.closedBall (z i) (Name.radium W i); let U:=T.book K; let f:= T.bookF K; let y(i:Σ i:ι,{y:(W i).X//y∈ K i}):= i.2.1; -- y type? dependent inferred `let y` impossible binder infer...
 have he := fatigue (T:=U) D hO (W∘Sigma.fst) (Proper.sail W h _ _ f) hD (z:=fun i=>z i.1) (y:=y) (f.tends.eventually hg) (Name.aux_burden hx ((h.look.bill (belt G P.L)).weak (by norm_num))) (Eventually.of_forall fun i=> mem_closedBall_iff_norm.mp i.2.2) (hp.pays _ f) (j+1); have hv: U.Meter (fun i=>r' i.1 k (y i)) (graded (k+1)):= (Name.corridor D hO W h hD hg hp hx).2.stamps k le_rfl
 let Z' i:= r' i k; let D' i:= (W i).due; intro e hE; filter_upwards [T.booked K (fun i v=> Brush (j+1) (T.cost i^(vigor (j+1)+1)) 1 (Z' i) v)|>.1 (he _ (lt_add_one _)), T.booked K (fun i v=> |Z' i v| ≤ T.cost i ^ h') |>.1 (hv _ hl.ok), h.look.tends.eventually hl.terms, T.pos, h.look.same] with i hi hI ht hz hx -- shadow h' bound vs proof tactic!
 have ht': T.cost i=(W i).due:=hx; apply (ht ((W i).X) (Z' i) (z i) ?_ ?_).climb ?_ le_rfl
 · rw [ht'] at hi; exact hi
 · rw [ht'] at hI; exact hI
 change (D' i)^a ≤ _; rw [ht'] at hz ⊢; exact Real.rpow_le_rpow_of_exponent_le hz hE.le
lemma projected (l:ℕ)(hh: l≤k)(hb:hX (fun i=> ‖z i‖) (-(1/2))) {t':ℝ}(ht:StellarP G P.L j k (graded (l+1)) t') (b:ι→ℝ)(hv:T.Meter b (-(1/2:ℝ)))(hj:∀ᶠ i in Λ,0<b i): Catch.Cover T j (graded (l+1)) (fun i=>(b i)⁻¹) (fun i=> r' i l) z := by
 let h₀:= reach D hO W h hD hg hp hb ht; let G i:= r' i k; let H i:=r' i l; have hz: Catch.Cover T j (graded (l+1)) (fun i=>(b i)⁻¹) G z:= h₀.small le_rfl le_rfl ( ((hv.low (by norm_num) zero_lt_one).and hj).mono fun _ hi=> ((one_le_inv₀ hi.2).2 ((le_abs_self _).trans hi.1.le)) ); let h':= Catch.Cover.add hz (omegaL D hO W h hD j hh hb hg hp b hv hj); have hx i : H i= G i + (Name.call (W i) O hO k-Name.call (W i) O hO l):=(by unfold H G receipt; ext1 x; simp only [Pi.add_apply,Pi.sub_apply]; ring); rw [show (fun i=>r' i l)=_ from funext hx]; exact h'
end Name
end YM.AllOrder.Aux
