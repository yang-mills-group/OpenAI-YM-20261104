import YM.AllOrder.Rosary.Sweet
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Rosary
open Function Filter Set Lattice Wilson RG Ovens
open AnalyticBridge VerifiedReset Collection Quotes Residual WilsonStartup UVNext.PricedKernels Averaging Geo Progress.DirectedRecipe Extra.Iteration Push.BetaTransport
open Till Burn
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} {R : PathData G} {c : Clip} {p : BudgetPoint} {σ C Λ H w : ℝ}
    {X : Listing G n} {v : Collection.Source G n} {ι κ : Type}
/-! Pole & Estimate budgets billed after L. Coarse T.cost=up betaHat(s) or down exactly (for simplicity). -/
namespace Repair
open Push PriceCompiler Floe Floe.Step Floe.StateE Floe.Step.PlanV Plateau PhysicalNext.Repeat Pressure
open ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.Blaze Catch Catch.Clock -- maybe remove
open Tilt
-- Cost ratio for nearby betas. Payout via Search lease. Includes weighted difference with all mask.Finance.
local notation "Z"=>Real.exp
namespace PostP
open Guard Lapis Gyro Time
variable (G)(p:Stage) -- stage real
variable (u:ℕ)
/- after real comparison through order 3*u+2. reference XSmall required. E2 only half enhanced Ω allowance. pre contraction computed from `credit` only (restoration). -/
abbrev θ1 (G:Gauge)(S:Stage)(x:ℝ)(u:ℕ):ℝ:=Time.credit G S* young x u
abbrev θ2 (G:Gauge)(S:Stage)(x:ℝ)(u:ℕ):ℝ:=2* θ1 G S x u
abbrev beg (x:ℝ):ℝ:= x^(-(11/10:ℝ))
-- Earnings for compare.DemandAfter reclose. Includes G.Simple outside just numeric.H positions χ.Region. choose soft margin. u.r goal bounds.
abbrev C' (S:BudgetPoint)(G:Gauge)(u:ℕ)(β x:ℝ):ℝ:= Tilt.price S G (Burn.horizon u) S.B (strengthP x) (gStep β) (Age.scope (Burn.horizon u+2))
abbrev taxes (S:BudgetPoint)(G:Gauge)(u:ℕ)(β b x:ℝ):ℝ:= deo G S (gStep β) (gStep b) (Burn.horizon u) (Age.scope (Burn.horizon u+2)) (strengthP x)
abbrev rentsAux (W:Stage)(G:Gauge)(p:BudgetPoint)(x:ℝ)(b a:ℝ)(u:ℕ)(n:Side)(Δ:ℝ):ℝ:= Real.exp p.supportExponent*taxes p G u a b x +(food G n p Δ+regularNeed G p W.clip W.width W.paths 0 (θ2 G W x u))
variable (H H':ℝ)
-- AsProp.Actor.Core. loon β actual out BOTH seed frame. ∆ real projected charge (out−pred). old calibration δold from forecast and error H.Permit.Frame. Ysoft≤ Rent.Seed tune.Un.
structure Actor (G:Gauge)(S:Stage)(u:ℕ)(H:ℝ) (x:ℝ) where
 p : BudgetPoint
 frost : Time.Same S p ∧ p.B=radiusB x ∧ p.threshold=temp x
 n : Side
 loft : Loft p n
 b : ℝ
 c : ℝ -- pred
 W : ℝ -- k
 Δ : ℝ -- u correction to α
 Δ' : ℝ -- TRUE gap: projected(E)−(b−c)
 D : ℝ -- projected ESmall
 H' : ℝ -- cost preEb
 bright : Burn.Near x b ∧ Burn.Near x c ∧ |W| ≤ H ∧ |Δ| ≤ H ∧ 0≤H' ∧ H'≤ x
 struck : Δ'=D-(b-c)
 guess : p.threshold^2* |D| ≤ θ1 G S x u
 thrift : |Δ'| ≤ Gyro.reward n p.threshold*Gyro.vault n p (Guard.totalFee p G S.clip S.width S.paths W Δ (C' p G u c x) (θ1 G S x u)+H')
-- targeted reclosure payment post P. peel y.B. don't rely on `Life.Cap` for it. Ear.Stock: input error bills β'(Actual), alternative p.C.
structure Checks {x:ℝ} (A:Actor G p u H x):Prop where
 reset : A.p.threshold^2* |A.b-A.c| ≤ θ2 G p x u
 economies : rentsAux p G A.p x A.b A.c u A.n A.Δ' ≤ young x u
 worth : Real.exp A.p.supportExponent*C' A.p G u A.b x ≤ Burn.silver x
 funded : Burn.silver x + young x u ≤ beg x /32
 kernel : Lapis.flare G A.n A.p A.Δ' + (x^(-(2/5:ℝ))+softNeed G A.p p.clip p.width p.paths A.W (θ2 G p x u)) ≤ x^(-(1/3:ℝ))
-- aux Y requested x^-2/5= Rate strictly weaker than solver.Y earn. could loosen. x^-1/3 goal from Pair.credit.
set_option quotPrecheck false
local notation "S"=> Sigma (Actor G p u H)
abbrev clockI : Catch.Clock ℝ:=⟨atTop,id,tendsto_id⟩
local notation "T"=>clockI.stage (Actor G p u H)
local notation "P"=> fun i:S=> (Actor.p i.2)
local notation "TV"=> fun i:S=> (P i|>.threshold)
local notation "N"=> fun i:S=>(Actor.n i.2)
local notation "X"=> fun i:S=> (Sigma.fst i)
local notation "a"=> fun i:S=> Actor.b i.2
local notation "b"=> fun i:S=> Actor.c i.2
local notation "Z₀"=> fun i:S=> Actor.D i.2
local notation "Δ"=> fun i:S=> Actor.Δ' i.2
local notation "k"=> fun i:S=> Actor.W i.2
local notation "U"=> fun i:S=> Actor.Δ i.2
local notation "Yξ"=>fun i:S=> C' (P i) G u (b i) (X i)
local notation "Y"=> fun i:S=> Actor.H' i.2
local notation "Q0"=> fun i:S=> θ1 G p (X i) u
local notation "M"=>Catch.Clock.Meter T
local notation "r"=> Catch.Clock.rail T
lemma legal : Frost T p P:= Eventually.of_forall fun i=> i.2.frost
lemma earns (x:ℕ): Burn.credit x ≤ -(7/5:ℝ):= by rw [sale_eq]; have hx:=Nat.cast_nonneg (α:=ℝ) (Burn.horizon x); linarith
local notation "τ"=> Burn.credit u
lemma θ1_meter : M Q0 τ := (Meter.pale T τ).lscale (Time.credit G p)
lemma growth {β:S→ℝ} (h:∀ᶠ i in r,Burn.Near (X i) (β i)): M (fun i=> C' (P i) G u (β i) (X i)) (-(3/2:ℝ)):= by
 intro e he; filter_upwards [legal G p u H,h, (T).drive.eventually (budgets_x (Burn.stop (G:=G) (Age.scope (Burn.horizon u+2)) p 0 (Burn.horizon u)) he)] with i hi hh hx; obtain ⟨h0,hb,hp⟩:=hi; unfold C'; rw [Tilt.sameprice,hp,hb,h0.1,h0.2.1]; exact hx _ hh
local notation "q"=> Time.probe p
local notation "L"=> (Eventually.of_forall (p:=fun i:S=> Loft (P i) (N i)) fun i=> i.2.loft)
set_option quotPrecheck false
lemma power_warp (z:ℝ): M (fun i=> food G (N i) (P i) (Δ i)) z∧M (fun i=> flare G (N i) (P i) (Δ i)) z ∧ M (fun i=>(TV i)^2* |Δ i|) z:= by
 have h := Eventually.of_forall (f:=r) (fun i:S=>i.2.bright); let hp:= legal G p u H; have hw:M k 0:= (Meter.const T H).smaller (Eventually.of_forall fun i=> i.2.bright.2.2.1.trans (le_abs_self _)); have hh: M U 0 := (Meter.const T H).smaller (Eventually.of_forall fun i=> i.2.bright.2.2.2.1.trans (le_abs_self _)); let hv:= growth G p u H (β:=b) (h.mono fun i hi=>hi.2.1); have hf:0≤ -(τ):= by linarith only [earns u]
 refine warp_wrap G hp L (δ:=1) ?_ (Eventually.of_forall fun i:S=>i.2.thrift) z; let he: M (fun i=> totalFee (P i) G p.clip p.width p.paths (k i) (U i) (Yξ i) (Q0 i)) 0 := total_panel G hp hw hh (hv.weak (by norm_num)) ((θ1_meter G p u H).weak (by linarith)); refine Meter.add (he.weak zero_le_one) ((Meter.pale T 1).smaller (Eventually.of_forall fun i:S=>?_)); let hx:Y i ≤ X i:= i.2.bright.2.2.2.2.2; change |Y i|≤ |(X i)^ (1:ℝ)|; rw [abs_of_nonneg (show 0 ≤ Y i from i.2.bright.2.2.2.2.1), Real.rpow_one]; exact hx.trans (le_abs_self _)
end PostP
end Repair
end YM.AllOrder.Rosary
