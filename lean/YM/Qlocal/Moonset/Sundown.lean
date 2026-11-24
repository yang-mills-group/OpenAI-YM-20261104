import YM.Qlocal.Moonset.Seats
import YM.Qlocal.Calendars.Hymn
/-!
# Buying the one-calendar post-coupling marked reset budget. Retain other purchases from that *same* Print Run.

Global invoice after L and before requesting any cutoff /comparison horizon /period size.
`Tab` available once before Entitle, not repurchasing from ANY nonempty Frame query.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Schedule
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Bid Planned.JetPort PhysicalNext Repeat Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Trio Lantern
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm JointLoad.Clockwork
open AllOrder Burn Carillon Cap
open Transit Transit.Moon Floe.Step.PlanV Floe.StateE Roost
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Roost Cub Circlet Graces
variable {G:Gauge} {P Q : Harbor G}
def tandem (P Q:Harbor G): Harbor G:= fun x y z s f l=> P x y z s f l∧ Q x y z s f l
lemma Prospecting.twin (h : Prospecting P) (ht: Prospecting Q) : Prospecting (tandem P Q):= by
 intro s K B p T E he x; obtain ⟨f,hf⟩:= h s K B p T E he x; obtain ⟨g,hg⟩:= ht s K B p T E he x; refine ⟨f⊔g,fun l hl D w o Z F S hκ p₁ hϑ X₀ Q V G' hp=> ?_⟩;
 obtain ⟨Y,hY,hX⟩:= hf l (le_sup_left.trans hl) D w o Z F S hκ p₁ hϑ X₀ Q V G' hp
 obtain ⟨W,hW,hA⟩:= hg l (le_sup_right.trans hl) D w o Z F S hκ p₁ hϑ X₀ Q Y G' hp
 refine ⟨W,hY.trans hW,fun W' hW' C₀ K I hp' B he ha _ _ _ _ _ _ _ hx_ ht_ hw' hy_ => ?_⟩
 exact ⟨hX W' (hW.trans hW') _ _ _ hp' B he ha _ _ _ _ _ _ _ hx_ ht_ hw' hy_, hA W' hW' _ _ _ hp' B he ha _ _ _ _ _ _ _ hx_ ht_ hw' hy_⟩ -- witness of Roof.F.
end YM.Qlocal.Schedule
namespace YM.Qlocal.Moonset
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Bid Planned.JetPort PhysicalNext Repeat Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Trio Lantern
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open AllOrder Burn Floe
open Transit Transit.WheelP Floe.Step.PlanV Floe.StateE Roost
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open PostDebt
-- fix P to Harbor of Run road.
variable {G:Gauge}{X:Metals G}{D:Rolls X.p}
variable (R:Roots (G:=G) X.p.profile X.K X.p.kernel)(F:R.Tab D)(η:ℕ→ℝ)
set_option quotPrecheck false
local notation "LΩ[x]"=>D.L x
local notation "Tp"=>X.p.profile
abbrev Payday (x y:ℕ)(t:ℝ) := ∀ (he:StepStages x y)(hx:4≤x)(q:ℕ)(h: Burn.horizon q+2 ≤y)(H:Nonempty (Card D R x y hx (Burn.horizon q)))(p k M N i:ℕ), p ≤ Burn.horizon q+1→ k≤x→M≤x→N≤x→ i≤x→PostDebt.Knowledge D R x y hx (F.income x y hx he (Burn.horizon q) h H) (2*Squall.Prior.yard R (Burn.horizon q) i y) N M k p (η x) t
variable {p':Protection D}(V:Delays p')
structure StationFee : Prop where
    rent (x y:ℕ)(hx:StepStages x y)(t:ℝ): V.betaEntry x ≤ t → Payday R F η x y t
open Squall Squall.Lumber
variable (x y:ℕ)(hx:4≤x)(he:StepStages x y)
variable (q:ℕ) (hQ:Burn.horizon q+2≤ y) (H:Nonempty (Card D R x y hx (Burn.horizon q)))
variable (hη:∀ x,0<η x)
local notation "Ω[t]"=> PostDebt.Knowledge D R x y hx (F.income x y hx he (Burn.horizon t) hQ H)
include hη
private lemma each : ∀ᶠ t in atTop, ∀ p ≤ Burn.horizon q+1, ∀ k ≤x,∀ M ≤ x,∀ N ≤x,∀ i≤x, PostDebt.Knowledge D R x y hx (F.income x y hx he (Burn.horizon q) hQ H) (2*Prior.yard R (Burn.horizon q) i y) N M k p (η x) t:= piano _ _ _ (fun i hi=>piano _ _ _ (fun k hk=> piano _ _ _ (fun M hM=> piano _ _ _ (fun N hN=> piano _ _ _ (fun i hi' => PostDebt.acquired D R x y hx _ _ N M k _ (mul_pos zero_lt_two (Prior.yard_p ..)) hi (hη x)))))) -- arguments order
private lemma every (he:StepStages x y) : ∀ᶠ t in atTop, Payday R F η x y t:= by
 by_cases h:4≤x; swap; · exact Eventually.of_forall fun t he hx => (h hx).elim
 let φ (q:ℕ) (t:ℝ):= ∀ (hQ:Burn.horizon q+2≤y)(H:Nonempty (Card D R x y h (Burn.horizon q))), ∀ p ≤ Burn.horizon q+1, ∀ k ≤x,∀ M ≤ x,∀ N ≤x,∀ i≤x, PostDebt.Knowledge D R x y h (F.income x y h he (Burn.horizon q) hQ H) (2*Prior.yard R (Burn.horizon q) i y) N M k p (η x) t
 have hx q: ∀ᶠ t in atTop,φ q t:= by
    by_cases h':Burn.horizon q+2≤y; swap; · exact Eventually.of_forall fun t hx=> (h' hx).elim
    by_cases he': Nonempty (Card D R x y h (Burn.horizon q)); swap; · exact Eventually.of_forall fun t hx hv=> (he' hv).elim
    exact (each R F η x y h he q h' he' hη).mono fun i hi _ _=> hi
 filter_upwards [piano y atTop φ (fun i _=> hx i)] with t ht; exact fun he hx q hb hv p k M N i hp hK hM hN hi=> ht q (by unfold Burn.horizon at hb; omega) hb hv p hp k hK M hM N hN i hi
lemma StationFee.defer : ∃ W: Delays p',DelayLe V W ∧ ∀ Y: Delays p',DelayLe W Y→ StationFee R F η Y := by
 obtain ⟨X,-,hx,hY⟩:= collect_upper V.betaEntry (fun x t=>∀ y,StepStages x y→ Payday R F η x y t) (fun x=>eventually_transitions x _ _ (fun y he=> every R F η x y hη he)); exact ⟨{V with betaEntry:=X},⟨hx,le_rfl,le_rfl,le_rfl⟩,fun Y hY'=> ⟨fun x y he t ht=> hY x t ((hY'.beta x).trans ht) y he⟩⟩
open Schedule
abbrev Spending (η:ℕ→ℝ): Harbor G:= fun _ _ A _ R F' => Moonset.StationFee R F' η A.delay
lemma invoices : Prospecting (Spending (G:=G) η):= by
 intro s K C' z R' E ht x; refine ⟨fun _=>0,fun l hl D w o Z F S hp c hc P Q V Y hY=>?_⟩; obtain ⟨U,hU,hC⟩:= StationFee.defer (X:=ThroughLaunch.currency s K l) x Y η V hη
 exact ⟨U,hU,fun W hw C₀ K I hp B he ha _ _ _ _ _ _ _ hx_ ht_ hw' hy_ => hC W hw⟩
end YM.Qlocal.Moonset
