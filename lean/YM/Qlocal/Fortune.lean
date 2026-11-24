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
variable {G:Gauge} (h:G.Simple)
def wheel : Goal G:= fun _ _ A F=>Transit.WheelP.Station A F
-- adopt Spectrum Native AllOrder rents epoch.No Optical.Waves context
include h
lemma all_orders : Obtainable (G:=G) wheel:= by
 intro s T C z R E ht; obtain ⟨u,hU⟩:=AllOrder.Shop.leased s R E; obtain ⟨Ψ,hΨ⟩:= Transit.must s _ E z; obtain ⟨x⟩:= acquire h s.profile (ThroughLaunch.bearing s T) s.kernel
 obtain ⟨j,hJ⟩:= x.prize; refine ⟨u⊔(Ψ⊔j),fun l hl D w o Z F S hκ p₁ hϑ P Q V=>?_⟩
 let M:=ThroughLaunch.currency s T l; have hx:∀ i,x.Rise i (↑(D.L i).val):= fun i=> hJ i _ ((le_sup_right.trans (le_sup_right.trans hl) i).trans (D.large i).need) -- syntax bad
 obtain ⟨K'⟩:=Roots.options (X:=M) D x h
 have hψ:Transit.Needed M.p M.K E z l := by
     let he:= le_sup_left.trans (le_sup_right.trans hl)
     exact ⟨fun i j L h hL=> hΨ.hair i j L h ((he j).trans hL), fun i j t L ht=> hΨ.acts i j t L ((he i).trans ht)⟩
 have hQ i q : (E i q).wanting=-(7/16:ℝ):=(ht i q).2.2.2.1
 obtain ⟨W',hW,hP⟩:= Transit.predicts (X:=M) (C':=R) Z x K' z C (rays s) mile p₁ S (wind Q) h hψ (fun i j h=> (ht i j).1) (fun i j _=>hQ i j) (fun i j _=> add_nonneg (s.profile j).price_pos.le (by norm_num)) hϑ V
 obtain ⟨V₁,h₁,H₁⟩:= Shop.funding (X:=M) (C:=R) D Z (fun _ i=> Shop.edgeW i) W' (u:=u) hU (fun i=>(le_sup_left.trans hl i).trans (D.large i).need) (fun i j _=> lt_trans (E i j).reach (by rw [hQ]; norm_num)) (fun _ i=> Shop.edge_pp i)
 obtain ⟨V₂,h₂,H₂⟩:= Roots.summit (X:=M) D x hx K' V₁; obtain ⟨V₃,h₃,H₃⟩:= WheelP.demands (X:=M) V₂
 refine ⟨V₃,hW.trans (h₁.trans (h₂.trans h₃)), fun W ht C₀ K I hp B he ha _ _ _ _ _ _ _ hx_ ht_ hw' hy_ => ?_⟩
 exact ⟨x,K',⟨hP _ (h₁.trans (h₂.trans (h₃.trans ht))),hx,H₂ _ (h₃.trans ht),H₁ _ (h₂.trans (h₃.trans ht)),he,ha⟩,H₃ _ ht⟩ -- Ticket nesting
omit h
/-- Geometry cost testimony. Holds even when X≫ all witnessed periods, spending true
 support exponent. This is needed when moving captions unmasked. -/
def runway (η:ℕ→ℝ)(H:ℕ→ℕ):Goal G:= fun M D A F=> Leasing.Facilities F.expense F.shape F.scout A.delay η H ∧ ∀ i j, StepStages j i→
      (M.p.profile i).supportExponent*(10*Footprint.preCost 0/(↑(D.L j).val:ℝ))≤(M.p.profile j).supportExponent
private lemma rulers (s : Sheet G) : ∃ f:ℕ→ℕ,∀ i j,StepStages j i → ∀ L:Side,f j≤L.val →
   (s.profile i).supportExponent * (10*Footprint.preCost 0/(↑(L.val):ℝ)) ≤ (s.profile j).supportExponent:= by
   let c i j:=(s.profile i).supportExponent*(10*Footprint.preCost 0)/(s.profile j).supportExponent; let m j i:= ⌈c i j⌉₊; refine ⟨fromMax m,fun i j he L hL=>?_⟩
   have hx:c i j≤(L.val:ℝ):= (Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_fromMax m he).trans hL))
   rw [← mul_div_assoc, div_le_iff₀ (by positivity),mul_comm ((s.profile j).supportExponent)]; exact (div_le_iff₀ (s.profile j).price_pos).1 hx
open RGComparison01.Pledge.Holdings
lemma purchased {η:ℕ→ℝ}(H:ℕ→ℕ)(hη:∀ i,0 < η i) : Obtainable (runway (G:=G) η H):= by
 intro s T C z R E ht; obtain ⟨j,hJ⟩:= Leasing.clearance E; obtain ⟨k,hK⟩:= rulers s; refine ⟨j⊔ k, fun l hl D w o Z F S hκ p₁ hϑ P Q V=>?_⟩
 obtain ⟨hj,hk⟩:=sup_le_iff.mp hl; obtain ⟨W,hW,hP⟩:= Leasing.advance (X:=ThroughLaunch.raise s l) E Z S V (fun i j' hp=> hJ i j' hp _ ((hj j').trans (D.large j').need)) η hη hκ H; exact ⟨W,hW,fun Y he C₀ K I hp B hv hm _ _ _ _ _ _ _ hx_ ht_ hw' hy_=> ⟨hP Y he, fun i j' hi=> hK i j' hi _ ((hk j').trans (D.large j').need)⟩⟩
end YM.Qlocal.Schedule
