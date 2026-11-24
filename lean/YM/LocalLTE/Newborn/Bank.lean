import YM.LocalLTE.Newborn.Port
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
lemma sail : ∃ p':ℕ,0≤p'∧ Nonempty (ClockB.Wind p' 1)∧ ∀ (W:ClockB.Wind p' 1),W.l< Pastel.chip (τ+1):= by
   obtain ⟨b,hb⟩:=exists_nat_gt (-2*Pastel.chip (τ+1)); exact ⟨b,Nat.zero_le _, ClockB.airborne b zero_lt_one,fun W=>by linarith only [hb,W.hemlock,W.minister]⟩
-- select w before C.T. maintain ε asked using internal Wind param; Funding requires `Balance p0 ℓ` with ε. may choose η=ε/2 instead!
lemma sailing (c:ℝ)(he:0<c) (n:ℕ): ∃ p':ℕ,n ≤ p'∧ Nonempty (ClockB.Wind p' c)∧ ∀ W:ClockB.Wind p' c, W.l< Pastel.chip (τ+1):=by
    obtain ⟨v,h⟩:= exists_nat_gt (-2 * Pastel.chip (τ+1) + c)
    refine ⟨v+n,Nat.le_add_left .., ClockB.airborne (v+n) he,fun W=>?_⟩; have he:= W.minister; push_cast at he; linarith only [he,W.hemlock,h,Nat.cast_nonneg (α:=ℝ) n]

open LocalLTE.Cabana Frost
variable {κ v' :ℝ}{c :ℝ}{p :ℕ}(W:Wind p c)
-- request ψ small as needed.Chip releases for all. W.pre
variable (R:Targets s (ThroughLaunch.bearing s K))(E:Expenses R)(z:Return.Wages)
variable (hS :Reliable G κ v')(hN:∀ i j, (R i j).rate < Pastel.mini)
def bsize (i j:ℕ):ℕ:= Coup.wire W.ℓ (R i j|>.halo)
include hS hN z
lemma ether :
    ∃ (n :ℕ→ℕ) (f:ℕ→ℕ→ℕ→ℕ)(y ψ μ:ℕ→ℕ→ℝ), (∀ i j,0< y i j∧ Price.Penny τ (ψ i j) (μ i j) (s.profile j) G)∧∀ l:ℕ→ℕ,n ≤ l→∀ D : Rolls (ThroughLaunch.raise s l), let _Z:=ThroughLaunch.currency s K l; let b:=Mallow.bsize s K W R
       (∀ i,2*Coup.CeilingExtent b i ≤ (D.L i).val) ∧ (∀ i j,StepStages j i → z j i/(D.L j).val ≤ y j i) ∧ (∀ j i,StepStages j i → Coup.voltage (s.profile i) (b j i) (3*y j i) ≤ ψ j i) ∧ (∀ j i,StepStages j i→(Height.gusts (R j i)).choose≤(D.L j).val) ∧ ∃ g:ℕ→ℕ→ℕ, Coup.Receipt (κ:=κ) (X:=ThroughLaunch.currency s K l) (C:=R) (Z:=E) W b τ f g ∧ ∀ j i,StepStages j i → g j i ≤ (D.L j).val:= by
    let r i j:=Mallow.bsize s K W R i j
    have hc(X:Stage)(N:ℕ):∃ y t u:ℝ, 0<y∧ Price.Penny τ t u X G∧ Coup.voltage X N (3*y) ≤ t:=by
        obtain ⟨t,u,h⟩:= Price.earn G X τ
        let f x:= Coup.voltage X N (3*x); have he:f 0=0:=by simp [f,Coup.voltage]
        have hx:Continuous f:=by unfold f Coup.voltage; fun_prop
        obtain ⟨x,hx',hδ⟩:= Metric.mem_nhds_iff.mp (hx.continuousAt.eventually (gt_mem_nhds (he.trans_lt h.1))); refine ⟨x/2,t,u,half_pos hx',h,?_⟩; refine le_of_lt (hδ (a:=x/2) ?_); simp only [Metric.mem_ball,Real.dist_eq,sub_zero, abs_of_pos (half_pos hx')]; exact half_lt_self hx'
    choose y t u hY hp hD using fun i j => hc (s.profile j) (r i j); let X:=ThroughLaunch.currency s K s.floorL
    obtain ⟨w,k,hK⟩:= Coup.salve (X:=X) (κ:=κ) (K:=v') (C:=R) (Z:=E) W r τ (fun i j _=>hN _ _) (fun i j _=>le_refl _) hS -- order
    have h j i (_:StepStages j i) : ∀ᶠ x:ℕ in atTop, z j i / (x:ℝ) ≤ y j i :=
       (((tendsto_const_nhds (x:=z j i)).div_atTop tendsto_natCast_atTop_atTop).eventually (gt_mem_nhds (hY j i))).mono (fun _ h=>h.le)
    obtain ⟨V,-,-,hV⟩:= collect_upper s.floorL _ (fun j=> eventually_transitions j _ _ (h j))
    let g i j:=(Height.gusts (R i j)).choose; let n i:=2*Coup.CeilingExtent r i
    refine ⟨(n⊔V) ⊔ (fromMax g ⊔ fromMax w),k,y,t,u,fun i j=> ⟨hY _ _,hp _ _⟩,fun l hl D=>?_⟩
    intro C b
    obtain ⟨ha,h⟩:= sup_le_iff.mp hl; obtain ⟨ha,hz⟩:= sup_le_iff.mp ha; obtain ⟨hg,he⟩:= sup_le_iff.mp h
    exact ⟨fun i=> (ha i).trans (D.large i).need,fun i j h=> hV j _ ((hz j).trans (D.large j).need) i h,fun i j _=> hD _ _,fun j i h=>((le_fromMax g h).trans (hg j)).trans (D.large j).need,w,hK,fun i j h=> ((le_fromMax w h).trans (he i)).trans (D.large i).need⟩ -- binders Universe.init
end YM.PhysicalNext.Repeat.Mallow
