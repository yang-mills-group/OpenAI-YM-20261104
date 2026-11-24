import YM.LocalLTE.Newborn.Bank
import YM.LocalLTE.Crafts.Bands
/-! Reserve Lens bills. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow
open Filter Function Lattice Wilson Pressure RG RG.Supply Input Precision
open Push.PriceCompiler Push.SectorMeasure Push.AbsoluteSums ConnectedActivityE6 AnalyticBridge VerifiedReset
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open scoped Topology Classical ContDiff BigOperators Matrix.Norms.Frobenius
open LocalLTE.Inset Org
open ThroughLaunch WilsonStartup Extra.Histories Next.Scheduling Next.Foundations UVNext.CouplingReset
open Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.PriceCompiler ThroughLaunch Height Opera Roof Roost
open Progress.DirectedRecipe Time WilsonStartup Extra.Histories Next.Foundations
open ClockB Urns
variable {G:Gauge}(s:Sheet G)(K:MapPrices){u g k:ℕ→ℝ} {r:Bid.Worth} {T': Further.StrongStartup.Tariffs} {Θ: Extra.Multi.Scope} {v:ℕ→ℕ}
    (hG:G.Simple) (τ:ℕ) (η:ℝ) (hη:0<η)
-- χ spacing.F tol choose internal order p at request after. power Δ advance.
open LocalLTE.Fan LocalLTE.Fan.Pastel

open LocalLTE.Cabana Frost
variable {κ v' :ℝ}{c :ℝ}{p :ℕ}(W:Wind p c)
-- request ψ small as needed.Chip releases for all. W.pre
variable (R:Targets s (ThroughLaunch.bearing s K))(E:Expenses R)(z:Return.Wages)
variable (hS :Reliable G κ v')(hN:∀ i j, (R i j).rate < Pastel.mini)
variable {l: ℕ →ℕ}(D:Rolls (ThroughLaunch.raise s l)) (v : Return.Wages) {u':ℕ→ℝ}
variable (R' : Register D E v u') {Q:Protection D} (d:ℕ→ℕ→ℝ)(f:ℕ→ℕ→ℕ→ℕ)(ψ b:ℕ→ℕ→ℝ)
local notation "Z" => ThroughLaunch.currency s K l
local notation "r'"=> Mallow.bsize s K W R
-- Chron visitors.
structure ExtraB (V:Delays Q) (k:ℝ) (M:ℕ→ℕ→ℕ→ℝ→ℝ) : Prop where
    spark (i j:ℕ)(h:StepStages i j)(x:ℝ): x≥V.betaEntry i→∀ w≤τ, Urns.Straps (X:=ThroughLaunch.currency s K l) D R W k (d i j) x i j (r' i j) w (M i j w x)
    receipts (i j:ℕ)(h:StepStages i j)(x:ℝ): x≥V.betaEntry i→∀ n≤τ, Mallow.trophy (G:=G) (R i j|>.halo) (r' i j) n (s.profile j) W (D.L i) x ≤ ψ i j*(betaF G x (D.L i))^(Pastel.chip (n+1))
    canopy (i j:ℕ)(h:StepStages i j)(x:ℝ): x≥V.betaEntry i → Price.Colors G (D.L i) (s.profile j) (Pane.cloak (X:=ThroughLaunch.currency s K l) D i) τ (ψ i j) (b i j) k x (r' i j*radiusB x)
    light (j i:ℕ) : StepStages j i → ∀ x:ℝ,x≥ V.betaEntry j →∀ n:ℕ,n ≤ τ → East.Peers (D.L j) x (Testing.query s (ThroughLaunch.bearing s K) j i) (R j i) (v j i) (R'.o j i) (Pastel.pie n+1) τ (f j i n) W.ℓ k
    dawn (i j:ℕ)(h:StepStages i j)(x:ℝ):x≥V.betaEntry i → ∀ (a:Levels G)(m:ℕ), a.params m=s.profile j→a.clock.hatBeta m=x→(s.profile j).clip.direct ≤1 → ∃ η:ℝ, Frost.Cup G τ η (D.L j) a m k
-- assemble via collecting.Y.
variable {v}
include hS
variable (ha:∀ i j,StepStages i j → 0 < d i j) (hP:W.l< Pastel.chip (τ+1))(hu:∀ i j,Price.Penny τ (ψ i j) (b i j) (s.profile j) G) (V:Delays Q)
include hP ha V hu
lemma verdant : ∃ (M:ℕ→ℕ→ℕ→ℝ→ℝ)(U:Delays Q), DelayLe V U∧∀ T:Delays Q,DelayLe U T→ExtraB s K τ W R E D v R' d f ψ b T κ M := by -- order edit
    have h i j u : ∃ M:ℝ→ℝ,∀ᶠ x in atTop, StepStages i j → Urns.Straps (X:=ThroughLaunch.currency s K l) D R W κ (d i j) x i j (r' i j) u (M x) := by
       by_cases he:StepStages i j
       · obtain ⟨M,h⟩:= Urns.flying (D:=D) (C:=R) (X:= Z) W (i:=i) (j:=j) hS (r' i j) u (ha i j he)
         exact ⟨M,h.mono fun i h _=>h⟩
       exact ⟨0, by simp [he]⟩
    choose M hM using h
    let v₀:= Finset.range (τ+1)
    have he i j (he:StepStages i j):∀ᶠ x in atTop, (∀ n≤τ, Urns.Straps (X:= Z) D R W κ (d i j) x i j (r' i j) n (M i j n x)∧ Mallow.trophy (G:=G) (R i j|>.halo) (r' i j) n (s.profile j) W (D.L i) x ≤ ψ i j*(betaF G x (D.L i))^(Pastel.chip (n+1)) ∧ East.Peers (D.L i) x (Testing.query s (ThroughLaunch.bearing s K) i j) (R i j) (v i j) (R'.o i j) (Pastel.pie n+1) τ (f i j n) W.ℓ κ)∧ Price.Colors G (D.L i) (s.profile j) (Pane.cloak (X:=ThroughLaunch.currency s K l) D i) τ (ψ i j) (b i j) κ x (r' i j*radiusB x) ∧ ∀ a:Levels G,∀ m:ℕ, a.params m = s.profile j →a.clock.hatBeta m=x→(s.profile j).clip.direct ≤1→∃ η:ℝ, Frost.Cup G τ η (D.L j) a m κ:= by
       have hp(l:ℕ)(hl:l∈ v₀): W.l< Pastel.chip (l+1):= hP.trans_le (by have he:l≤τ:= Nat.le_of_lt_succ (Finset.mem_range.mp hl); unfold chip; gcongr)
       obtain ⟨c,hc,hV⟩:= Frost.cashC τ (s.profile j)
       filter_upwards [(eventually_all_finset v₀).mpr (fun l hl=> (hM i j l).and ((Mallow.moment (G:=G) (L':=D.L i) (R i j).halo (r' i j) l (s.profile j) W _ (hu i j).1 (hp _ hl)).and (East.chrome (D.L i) (R i j) (v i j) (R'.o i j) τ W.ℓ (pie l+1) (f i j l) (by omega) hS))), Frost.rentC G τ (s.profile j) c (D.L j) hS hc hV, Price.paid_colors G (D.L i) (s.profile j) _ τ _ _ (r' i j) (hu _ _) hS] with x hx hv hΓ -- order rent
       refine ⟨fun n hn=>?_,hΓ,fun a m h hl h'=>⟨c,hv a m h hl h'⟩⟩; obtain ⟨h,hy⟩:= hx n (Finset.mem_range.mpr (Nat.lt_succ_of_le hn)); exact ⟨h he,hy⟩
    obtain ⟨u,-,hp,h⟩:= collect_upper V.betaEntry _ (fun i=>eventually_transitions i _ _ (he i)); exact ⟨M,{V with betaEntry:=u},⟨hp,le_rfl,le_rfl,le_rfl⟩,fun T ht=>⟨fun i j he x hx n hn=> (h i x ((ht.beta _).trans hx) j he|>.1 _ hn).1,
        fun i j he x hx n hn=> (h i x ((ht.beta _).trans hx) j he|>.1 _ hn).2.1,
        fun i j he x hx=> (h i x ((ht.beta _).trans hx) j he).2.1,
        fun i j he x hx n hn=> (h i x ((ht.beta _).trans hx) j he|>.1 _ hn).2.2,
        fun i j he x hx=> (h i x ((ht.beta _).trans hx) j he).2.2⟩⟩
end YM.PhysicalNext.Repeat.Mallow
