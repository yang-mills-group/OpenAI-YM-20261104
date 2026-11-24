import YM.Contacts.Junction.Vest
/-! # Estimate canonical normalization. Clamp as auxiliary optimization. -/
noncomputable section
namespace YM.Contacts.Junction
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Function Filter Set Finset Metric Lattice RG Gauge Pressure Wilson PertExtension.Series MeasureTheory
open Radial Precision Matrix PhysicalNext.Repeat Bid Tree Tested PertExtension.Chart Lapis Milling
open YM.Stationary Milling.Forge Exterior Push.Uniform ConnectedActivityE6 Blaze Shield Poll Next.SectorChange Fare Model.Arbor
open scoped Topology ContDiff Pointwise BigOperators Matrix.Norms.Frobenius Classical NNReal
variable {G:Gauge} {P : ChartRatio G} {σ C e v d t K τ ω' s a:ℝ}{n k j r i:ℕ}
namespace Provision
open Ion House Lintel Lintel.Angle Cove Model Province.Costing Lumen Pulse Spine Steam
open Milling.Garf Loom Loom.Patch Meter Capture Buyer Push Current Milling.Spark
open Sienna Lantern Planned.JetPort Dew Uniform StagePort
open Push.AbsoluteSums SectorMeasure Presented Next.Fluctuations Next.Fluctuations.Sector
variable {U:Teller G} {L:Side} {M:Uniform.ChartPrices}{X:G.ColorIndex} {Φ:ℕ→StagePort G U P X k L σ C M n}
local notation "ι" => StagePort.dew ∘ Φ
local notation "E" => (fun i=> Dew.X (ι i))
local notation "Y" => (fun i=> Dew.Y (ι i))
local notation "μ" => (fun i=>StagePort.μ (Φ i))
local notation "γ" => γC (ι)
local notation "π" => (fun i z x=> StagePort.hint (Φ i) x z)
local notation "wβ" => (fun i z x=> StagePort.warmth (Φ i) x z)
variable {N:Meter}{Q:ℝ→ℝ}
namespace Travel
open Loom.Patch
variable (p:Travel N Q Φ)(hk:2≤k)(hn:k≤n)(hG:G.Simple)(hp:LocalRatio P)(hd:0<d)
local notation "g" => (arcCoast Φ d)
local notation "α" => (fun i z x=> StagePort.crab (Φ i) x z)
include p hd
lemma climbBank : ∀ᶠ i in atTop, let D:= (Φ i).dew; ∀ z∈Frame.Bank (fun i=>(Φ i).dew.X) 1 i, ∀ y∈Metric.closedBall (0:D.Y) (g i), (Φ i).crab z y∈ Metric.ball 0 (N.pow Capture.stashp i):= by
   have he:= Pouch.canon (N:=N) (p:=stashp); have hh:= he.bank (paidCrabs p hd) (by norm_num [fit,stashp]); filter_upwards [hh] with i hi D z hz y hy; exact mem_ball_zero_iff.mpr (hi (⟨z,hz⟩,⟨y,hy⟩))
include hp hk hn hG
lemma heatMeter (q:ℝ) : Narrow N (n+3) q 1 (g) π:= by
   let V:= Frame.Port (fun i=>(Φ i).dew.Q) (N.pow stashp); let D:= StagePort.dew ∘ Φ; let g' i:= Φ i; let U i:= (g' i).bench- (g' i).natal; have hs := (presentFee p hk hG hp hn).2.2 (q-1); have hx: Narrow N (n+3) (q-1) 1 (g) (fun i z x=>U i (α i z x)):= Current.rUse (A:=fun i=>Dew.Q (ι i)) (V:=fun _=>ℝ) (d:=fit) hs (he:=paidCrabs p hd) (hv:=(climbBank p hd).mono (fun i hi v=> hi _ v.1.2 _ v.2.2)) (by norm_num [fit]); exact Arms.weighted hx (volume_count p.dawn p.scale p.plaza p.ferry|>.2.1) (by ring) -- coords geometry.Ix.Pre.Scope.Var
set_option quotPrecheck false
local notation "Z" => Frame.Bank (fun i=>(Φ i).dew.X) (fun _=>1)
lemma warm_cash : ∀ᶠ i in atTop, let v:= Φ i; ∀ z∈ Z i, ∀ y∈ Metric.closedBall (0:v.dew.Y) (g i), 0< v.warmth z y ∧ v.warmth z y≤ Real.exp 1 := by
    let ℓ(i:ℕ):=(Φ i).bench; let D:= fun i=>(Φ i).dew; let f:=fun i (z:(Φ i).dew.Y)=> Capture.pulse ℓ (γ) (α) i z
    have he': Narrow N (n+3) Capture.race 1 (g) f:= by
       refine (Capture.book (presentFee p hk hG hp hn|>.1) Pouch.canon p.parameter (paidCrabs p hd) (n:=k) (by omega) ).plush (codes_omit ..)
    filter_upwards [Capture.Budget.limits he' (by norm_num [race]) _ zero_lt_one] with i hi v z hz y hy; refine ⟨Real.exp_pos _,Real.exp_monotone ( (le_abs_self (f i y z)).trans (hi (⟨z,hz⟩,⟨y,hy⟩)).le)⟩ -- definitional.C
lemma hintMin (he:e<0): ∀ᶠ i in atTop, let v:= Φ i; ∀ z∈ Z i, ∀ y∈ Metric.closedBall (0:v.dew.Y) (g i), ‖v.hint z y‖≤N.pow e i ∧ ‖v.hint z y‖≤1:= by
   have hp':= heatMeter p hk hn hG hp hd (e-1); filter_upwards [Loom.Arms.read hp' (show e-1<e by linarith),Pouch.small Pouch.canon he (N:=N)] with i hi h v z hz y hy; let w:=v.hint z y; have hu:‖w‖ ≤ N.pow e i:= (hi (⟨z,hz⟩,⟨y,hy⟩)).bound; exact ⟨hu,hu.trans h⟩
private lemma sight_toll (x:ℝ)(h:|x|≤1): ‖Real.exp x-1‖ ≤ Real.exp 1*‖x‖:= by
   let S:= Icc (-1:ℝ) 1; simpa only [sub_zero,Real.exp_zero] using ((convex_Icc (𝕜:=ℝ) (-1:ℝ) 1).norm_image_sub_le_of_norm_deriv_le (f:=Real.exp) (fun i _=> Real.differentiableAt_exp) (fun i hi=>by rw [Real.deriv_exp,Real.norm_of_nonneg (Real.exp_pos _).le]; exact Real.exp_monotone hi.2) (show (0:ℝ)∈ S from by unfold S; simp) (abs_le.mp h : x∈S))
lemma warm_precise (he:e<0): ∀ᶠ i in atTop, let v:= Φ i; ∀ z∈ Z i, ∀ y∈ Metric.closedBall (0:v.dew.Y) (g i), let W:= v.warm z y;
     0<W∧ W≤ (Real.exp 1)^2∧ ‖W-v.warmth z y‖ ≤ (Real.exp 1)^2 * N.pow e i:= by
   filter_upwards [warm_cash p hk hn hG hp hd,hintMin p hk hn hG hp hd he] with i hi hf v z hz y hy W; obtain ⟨ht,hu⟩:=hf z hz y hy; obtain ⟨he,hh⟩:=hi z hz y hy; let t:= v.warmth z y; let u:=v.hint z y; have hu: |u| ≤1:=hu;
   refine ⟨mul_pos he (Real.exp_pos _), ((mul_le_mul hh (Real.exp_le_exp.mpr ((le_abs_self u).trans hu)) (Real.exp_pos u).le (Real.exp_pos 1).le).trans_eq (sq _).symm), ?_⟩; rw [show W-t=t*(Real.exp u-1) from (by unfold W StagePort.warm; change t*_ -t=t*_; ring),norm_mul, Real.norm_of_nonneg he.le]; refine (mul_le_mul hh ((sight_toll p hk hn hG hp hd u hu).trans (mul_le_mul_of_nonneg_left ht (Real.exp_pos _).le)) (norm_nonneg _) (Real.exp_pos _).le).trans_eq ?_; ring
-- integrand qualifications.W.Curr
lemma seen : ∀ᶠ i in atTop, let v:= Φ i; let D:= v.dew; ∀ x∈ Z i, ∀ z∈ Metric.closedBall (0:v.dew.Y) (g i), let y:=v.flag • x; let u:= v.shiftV y z; let s:= Fare.windmill D.B u; s∈ Next.SectorChange.mouth P ∧
       D.grad^v.sizes * (Next.SectorChange.pay P s * traceK v y (stainP v y z))= v.dream y* (Shield.lens₀ D.matrix⁻¹ z* shadeV v x z):= by
    filter_upwards [flowFee p hk hG hp hn, Provision.paid P p.dawn p.scale hp,p.climbBank hd,branchInside p.dawn p.scale,p.dawn,p.quake_model hk] with i hi hv hz hr ht hQ v D x hx z hy y u s; let w:= v.crab x z; have hu:w∈ Metric.ball 0 (N.pow stashp i):=hz x hx z hy; obtain ⟨hv,hz⟩:= hv w hu; refine ⟨hv, StagePort.leafV ht hp x z ⟨hv,fun h' => ⟨hQ _ h',?_,hz ⟩⟩ hi.2.2⟩; exact (hr w hu).2
end Travel
end Provision
end YM.Contacts.Junction
