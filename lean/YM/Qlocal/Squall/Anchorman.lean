import YM.Qlocal.Squall.Plunge
import YM.Qlocal.Spire
import YM.Qlocal.Permit

/-!
 Calendar financing of both unmarked Station and first marked passports.
 These can spend Before-L and ∀ᶠ Entrance requests.Need still apply to
 campaign from Passenger. All actual Ω for any manifested height and geometry.
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

variable {G:Gauge} (h:G.Simple)
abbrev Breath (X:Metals G)(D:Rolls X.p)(R:Roots (G:=G) X.p.profile X.K X.p.kernel):= ∀ x, Squall.Prior.Awning R x (↑(D.L x).val:ℝ)
abbrev Harbor (G:Gauge):= ∀ (M:Metals G) (D:Rolls M.p)(A:Alloy M D)(F_:Factor A)(R:Roots (G:=G) M.p.profile M.K M.p.kernel)(G_ : R.Tab D), Prop
-- Keep Station witness with this contract. Offers AFTER R.SF
variable (H:Harbor G)
def berth (H: Harbor G): Goal G:= fun M D A F=> ∃ (R:Roots (G:=G) M.p.profile M.K M.p.kernel)(G':R.Tab D), WheelP.TicketP A F R G' ∧ Breath M D R ∧ H M D A F R G'
section

-- invoice at time of purchasing Delays. Requires NO p before L except settler C z t
variable (s:Sheet G) (T:MapPrices)(C:Programs s) (l:ℕ→ℕ)
     {R:Targets s (ThroughLaunch.bearing s T)} (z:Return.Wages)(E:Expenses R)
     (D:Rolls (ThroughLaunch.raise s l)) (w:Return.Wages) (u:ℕ→ℝ) (Z:PhysicalNext.Repeat.Register D E w u) (F:ℕ→ℕ→Postage)(S:Time.Scouts (F:=F))
     (p₁:ℕ→ℕ→JointLoad.Heir.Record) {P:Protection D}(V:Delays P)
local notation "M" =>ThroughLaunch.currency s T l
-- regression must check eq casts.
def Lung (Q:ℕ→ℕ→JointLoad.Clockwork.Menu)(d:Roots (G:=G) s.profile (ThroughLaunch.bearing s T) s.kernel) (G' : Roots.Tab (X:=ThroughLaunch.currency s T l) d D) : Prop:= ∀ (C0:PostCost D) (K0:Bar V)(I : Wait K0) (hp:Stock.Priced V) (B0: Directed G I (chart G) (ThroughLaunch.bearing s T) C0),
  Extension.UV.Archive B0 → (∃ f,RankCovariance.ShapePort B0.a B0.M f) →
  let A : Alloy M D:= Alloy.mk C0 P V K0 I hp B0
  ∀ E' η q B bt b J hf hF hW ha,H M D A ⟨E',F,S,η,q,w,B,R,E,u,Z,bt,z,rays s,mile,b,C,Q,p₁,J,hf,hF,hW,ha⟩ d G'

end

def Prospecting (H: Harbor G): Prop:=
  ∀ (s:Sheet G) (T:MapPrices)(C:Programs s)(z:Return.Wages) (R:Targets s (ThroughLaunch.bearing s T)) (E:Expenses R),
    (∀ i k,(R i k).table=chart G ∧ (R i k).halo=500 ∧ (E i k).earn=Roof.rays s i k ∧ (E i k).wanting=-(7/16:ℝ) ∧ (E i k).degrees=0) →
    ∀ x:Roots (G:=G) s.profile (ThroughLaunch.bearing s T) s.kernel, ∃ f:ℕ→ℕ,∀ l:ℕ→ℕ,f ≤ l →∀ (D:Rolls (ThroughLaunch.raise s l)) (w:Return.Wages) (u:ℕ→ℝ) (Z:PhysicalNext.Repeat.Register D E w u) (F:ℕ→ℕ→Postage)(S:Time.Scouts (F:=F)), Pocket Z S →
       ∀ (p₁:ℕ→ℕ→JointLoad.Heir.Record), (∀ j i,StepStages j i → s.first ≤ i → (p₁ j i).ε ≤ 1 / 4) →
       ∀ (P:Protection D)(Q:ℕ→ℕ→JointLoad.Clockwork.Menu)(V:Delays P) (G' : Roots.Tab (X:=ThroughLaunch.currency s T l) x D), Breath (ThroughLaunch.currency s T l) D x →∃ W:Delays P,DelayLe V W ∧ ∀ Y, DelayLe W Y → Lung H s T C l z E D w u Z F S p₁ Y Q x G'

include h
lemma all_chances (hF:Prospecting (G:=G) H) : Obtainable (berth H):= by
 intro s T C z R E ht; obtain ⟨u,hU⟩:=AllOrder.Shop.leased s R E; obtain ⟨Ψ,hΨ⟩:= Transit.must s _ E z; obtain ⟨x⟩:= acquire h s.profile (ThroughLaunch.bearing s T) s.kernel
 obtain ⟨j,hJ⟩:= x.prize; obtain ⟨d,hd⟩:= Squall.Prior.obtain_world x; obtain ⟨e,he⟩:= hF s T C z R E ht x; refine ⟨u⊔(Ψ⊔(j⊔(d⊔e))),fun l hl D w o Z F S hκ p₁ hϑ P Q V=>?_⟩
 let M:=ThroughLaunch.currency s T l; have hx:∀ i,x.Rise i (↑(D.L i).val):= fun i=> hJ i _ (((le_sup_left.trans <| le_sup_right.trans (le_sup_right.trans hl)) i).trans (D.large i).need) -- syntax bad
 obtain ⟨K'⟩:=Roots.options (X:=M) D x h
 have hψ:Transit.Needed M.p M.K E z l := by
     let he:= le_sup_left.trans (le_sup_right.trans hl)
     exact ⟨fun i j L h hL=> hΨ.hair i j L h ((he j).trans hL), fun i j t L ht=> hΨ.acts i j t L ((he i).trans ht)⟩
 have hQ i q : (E i q).wanting=-(7/16:ℝ):=(ht i q).2.2.2.1
 obtain ⟨W',hW,hP⟩:= Transit.predicts (X:=M) (C':=R) Z x K' z C (rays s) mile p₁ S (wind Q) h hψ (fun i j h=> (ht i j).1) (fun i j _=>hQ i j) (fun i j _=> add_nonneg (s.profile j).price_pos.le (by norm_num)) hϑ V
 obtain ⟨V₁,h₁,H₁⟩:= Shop.funding (X:=M) (C:=R) D Z (fun _ i=> Shop.edgeW i) W' (u:=u) hU (fun i=>(le_sup_left.trans hl i).trans (D.large i).need) (fun i j _=> lt_trans (E i j).reach (by rw [hQ]; norm_num)) (fun _ i=> Shop.edge_pp i)
 obtain ⟨V₂,h₂,H₂⟩:= Roots.summit (X:=M) D x hx K' V₁; obtain ⟨V₃,h₃,H₃⟩:= WheelP.demands (X:=M) V₂
 have hx' : Breath M D x:= fun i=> hd i _ ((le_sup_left.trans <| le_sup_right.trans <| le_sup_right.trans <| le_sup_right.trans hl) i |>.trans (D.large i).need)
 obtain ⟨V₀,h₀,hH⟩:= he l (le_sup_right.trans <| le_sup_right.trans <| le_sup_right.trans <| le_sup_right.trans hl) D w o Z F S hκ p₁ hϑ P Q V₃ K' hx'
 refine ⟨V₀,hW.trans (h₁.trans (h₂.trans (h₃.trans h₀))), fun W ht C₀ K I hp B he ha _ _ _ _ _ _ _ hx_ ht_ hw' hy_ => ?_⟩
 refine ⟨x,K',⟨⟨hP _ (h₁.trans (h₂.trans (h₃.trans (h₀.trans ht)))),hx,H₂ _ (h₃.trans (h₀.trans ht)),H₁ _ (h₂.trans (h₃.trans (h₀.trans ht))),he,ha⟩,H₃ _ (h₀.trans ht)⟩,hx',hH W ht _ _ _ hp B he ha _ _ _ _ _ _ _ hx_ ht_ hw' hy_ ⟩ -- Ticket nesting
end YM.Qlocal.Schedule
