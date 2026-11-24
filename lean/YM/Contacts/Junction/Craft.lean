import YM.Contacts.Junction.Cliff
/-! # analytic transfer to real frame. `Caps..` -/
noncomputable section
namespace YM.Contacts.Junction
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Function Filter Set Finset Metric Lattice RG Gauge Pressure Wilson PertExtension.Series MeasureTheory
open Radial Precision Matrix PhysicalNext.Repeat Bid Tree Tested PertExtension.Chart Lapis Milling
open YM.Stationary Milling.Forge Exterior Push.Uniform ConnectedActivityE6 Blaze Shield Poll Next.SectorChange Fare Model.Arbor
open scoped Topology ContDiff Pointwise BigOperators Matrix.Norms.Frobenius Classical NNReal
variable {G:Gauge} {P : ChartRatio G} {σ C e v d t K τ ω':ℝ}{n k j r i:ℕ}
namespace Provision
open Ion House Lintel Lintel.Angle Cove Model Province.Costing Lumen Pulse Spine Steam
open Milling.Garf Loom Loom.Patch Meter Capture Buyer Push Current Milling.Spark
open Sienna Lantern Planned.JetPort Dew Uniform StagePort
open Push.AbsoluteSums
variable {U:Teller G} {L:Side} {M:Uniform.ChartPrices}{X:G.ColorIndex} {Φ:ℕ→StagePort G U P X k L σ C M n}
local notation "ι" => StagePort.dew ∘ Φ
local notation "E" => (fun i=> Dew.X (ι i))
local notation "Y" => (fun i=> Dew.Y (ι i))
local notation "Xr" => (fun i=> Dew.Q (ι i))
local notation "K₀" => (fun i=> StagePort.bench (Φ i))
local notation "O₀" => (fun i=> StagePort.eternal (Φ i))
local notation "O₁" => (fun i=> StagePort.targetY (Φ i))
local notation "γ" => γC (ι)
variable {N:Meter}{Q:ℝ→ℝ}
local notation "μ" => (fun i=>StagePort.μ (Φ i))
local notation "δ" => (fun i=> StagePort.bare (Φ i))
local notation "π" => (fun i=> StagePort.smooth (Φ i))
local notation "α" => (fun i z x=> StagePort.crab (Φ i) x z)
abbrev arcCoast (Φ:ℕ→StagePort G U P X k L σ C M n) (d:ℝ): ℕ→ℝ:= fun i=>wick G L d (Φ i).pearlRide
namespace Travel
open Loom.Patch
variable (p:Travel N Q Φ) (hG:G.Simple)(hk:2≤k)(hn:k ≤ n)(hp:LocalRatio P)
    (hd:0<d)(hr:Loom.Capture.race < τ)(hτ:τ<0)(hu:τ*((k:ℝ)+1)<K)(hv: K<0)
include p
include hd in
lemma paidCrabs : Narrow N (n+3) fit 1 (arcCoast Φ d) (α) := t_scale p.fC.2 p.fC.1 (p.quarry hd) (Rush.settle 1)
lemma burn : Loom.Patch.Joint N (n+3) fit 1 (α):= t_full p.fC.2 p.fC.1 (Rush.settle 1)
lemma stickV : Direct N (n+3) fit 1 (π) := by
   let V i:= (Φ i).dew; let t(i:ℕ):ℝ:=(Φ i).flag; let L(i:ℕ):=((V i).X); have hx : Direct N (n+3) fit 1 (fun i (x:L i)=> t i • x):= Arms.weighted (Current.meetP (Rush.settle 1) le_rfl) p.fC.2 (zero_add _); have hm(i:ℕ):∀ x, ‖settle (G:=G) (V i).c x‖ ≤ ‖x‖:= fun x=> ((settle (V i).c).le_opNorm x).trans (mul_le_of_le_one_left (norm_nonneg _) (Model.Arbor.due _)); exact Current.polar (Loom.Budget.tally (γ) p.fC.1) (Loom.Budget.natural (k:=n+3) (fun i=> Model.Arbor.settle (G:=G) (V i).c) hx hm)
include hG hk hn hp
lemma windowH : ∀ᶠ i in atTop, Measurable ((Φ i).bench) ∧ ∀ x∈ Frame.Bank E 1 i, Measurable (fun z => α i z x):= (flowFee p hk hG hp hn).mono fun i hi=>⟨hi.1,fun x _=> by unfold StagePort.crab; fun_prop⟩ -- definitional comp
include hd hr hτ
lemma heard : Direct N (n+3) τ 1 (summitK Φ d-1) := by haveI : ∀ i:ℕ,BorelSpace (Φ i).dew.Q:= fun i=> (inferInstance : BorelSpace ((Φ i).dew.Q)); exact Patch.neat (n:=k) (F:=fun i=>(Φ i).dew.Q) (V:=fun i=>(Φ i).dew.Y) («E»:=fun i=>(Φ i).dew.X) (p.heat hd) (presentFee p hk hG hp hn).1 Pouch.canon p.parameter (paidCrabs p hd) p.burn (p.windowH hG hk hn hp) (by omega) hr hτ
include hu hv
lemma nickel : Direct N (n+3) K 1 (logS (summitK Φ d)- logS (meteor (summitK Φ d))- Patch.head (δ) (γ) (π)):=
    by haveI : ∀ i:ℕ,BorelSpace (Φ i).dew.Q:= fun i=> (inferInstance : BorelSpace ((Φ i).dew.Q)); exact Loom.Patch.steer (F:=fun i=>(Φ i).dew.Q) (V:=fun i=>(Φ i).dew.Y) («E»:=fun i=>(Φ i).dew.X) (p.heat hd) (presentFee p hk hG hp hn).1 Pouch.canon p.parameter (paidCrabs p hd) (p.windowH hG hk hn hp) p.burn (Nat.add_le_add_right hn 3) hr hτ hu hv (Eventually.of_forall fun _=>zero_lt_one) (gap_root p.funds) p.stickV (order_slots p hG hk hn hp)
-- expand-skeleton consequence for target in *hat* physical B.Call units yes.
omit hd hr hτ hu hv
lemma refund : ∀ᶠ i in atTop, let v:= (Φ i); ∀ x, -(v.dew.β*v.bare (v.smooth x))= -(v.dew.β * v.dew.℘ (v.flag • x)) + Loom.Patch.head (δ) (γ) (π) i x:= by
    have hs:= volume_count p.dawn p.scale p.plaza p.ferry;
    filter_upwards [pilot p hG hk hn hp,hs.1] with i hi h x y; let p:= Φ i; let D:= p.dew; let β:= D.β; let g:=D.grad; let b:=p.bare; let A:= p.targetY; let J:= D.℘; let q:= settle (G:=G) D.c; obtain ⟨hx,hp⟩:= hi; let v' : D.X:=p.flag • y; let V:= q v'; have hu:J 0=0:= cam_zero D.B D.T D.label D.L
    have hJ(x:D.X)(s:ℝ): J (s • x)=s^2*J x:= by
       let f:= table D.B D.label D.T.up D.T.high; change jet f 2 _=s^2 * jet f 2 _; exact Eq.trans (congr_arg (jet f 2) (show (s • x, D.L (s • x))=s • (x,D.L x) from Prod.ext rfl (D.L.map_smul ..))) (jet_smul f 2 s (x,D.L x))
    have hh: Radial.Stationary b:= registry (swell p.outB (k+3)) (orchestra ..) (spectrum ..)
    have hℓ:0<g ∧ g^2*β=1:= Fare.gS _ (h.1);
    let t:=(g,V); have hz: skel b 3 t= jet b 2 t:= by unfold skel; rw [sum_range_succ,sum_range_succ,sum_range_succ,jet_zero]; simp only [sum_range_zero,hh.base0, hh.base1,zero_add]; -- to profile
    have ht : g⁻¹ ^ 2=β:= by have h:=hℓ.1; rw [inv_pow]; field_simp; linarith [hℓ.2] -- syntax
    let K:cap G D.c→L[ℝ] cap G D.c:=(ContinuousLinearMap.fst ℝ ℝ (Link G D.c)).prod 0; have ha: AnalyticAt ℝ A 0:= orchestra ..; let U':=g⁻¹ • v'; have hg := Radar.base hx U';
    have hk: g⁻¹ ^ 2 * jet b 2 t=g⁻¹ ^2 * J v':= by
       rw [← jet_smul b,← hJ]; rw [show g⁻¹ • t=(1,q U') from Prod.ext (inv_mul_cancel₀ hℓ.1.ne') (q.map_smul ..).symm,show b=A-A ∘ K from rfl, Ion.jet_minus _ _ _ _ ha (starts _ ha _),Garf.woven ha K]; change jet A 2 (1,q U') - jet A 2 ((1:ℝ),0)=_; change J U'-J 0= jet A 2 (1,q U') - jet A 2 (1,0) at hg; rw [← hg,hu,sub_zero]
    rw [ht] at hk; change -(β*b t)= -(β* J v') + ( -(g⁻¹^2)*(b t-skel b 3 t)); rw [ht,hz,mul_left_cancel₀ (h.1.ne' : β≠0) hk]; ring -- RHS J_v' definitional maybe ring fail
include hd hr hτ hu hv
lemma forever : let q i:= Φ i; Direct N (n+3) K (fun _=>1) (fun i x=> logS (summitK Φ d) i x-logS (summitK Φ d) i 0-(q i).dew.β * ((q i).dew.℘ ((q i).flag • x)) + (q i).dew.β * (δ i (π i x))) := by
   intro q; apply Arms.reveal (nickel p hG hk hn hp hd hr hτ hu hv) _ le_rfl le_rfl ; filter_upwards [refund p hG hk hn hp] with i hi j; refine Eventually.of_forall fun x=>?_ ; let b:= Φ i; let a:= summitK Φ d; have h:= hi x; change -(b.dew.β*b.bare (b.smooth x))= -(b.dew.β * b.dew.℘ _) + Loom.Patch.head (δ) (γ) (π) i x at h; change _ = (Real.log (a i x)-Real.log (a i 0))-Loom.Patch.head (δ) (γ) (π) i x; change Real.log (a i x)-Real.log (a i 0) - b.dew.β*b.dew.℘ _ + b.dew.β*b.bare (b.smooth x)=_; linarith only [h]
end Travel
end Provision
end YM.Contacts.Junction
