import YM.Qlocal.Calendars.Podia
/-! # Caption width & ancestor support at beyond-Rental payment. Loom can later use any stakeholder valuations at least under this true-meter appointment. Choose CutAura on the input only when Keeper.Ed.Year Requests.J.Ph; output stencil support included in Room Fresh.Width, AND future input can spend similarly after arrival.-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Calendars
open Filter Function Set Lattice Wilson RG Pressure Tree Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open PhysicalNext PhysicalNext.Repeat AnalyticBridge VerifiedReset Extra.Iteration Song
open Collection Quotes Input Org Supply PriceCompiler Next.Scheduling Progress.DirectedRecipe Time Roost Coat ThroughLaunch Animals
open RGComparison01 RGComparison01.Pledge RGComparison01.Pledge.Holdings BudgetPoint
open Push.Uniform Sienna Gauges
open Parabola Reckoner Scribe
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open AllOrder Floe Step Step.PlanV Catch Squall Squall.Lumber Squall.Skull
variable {G:Gauge}{V:Type}{c f:Side}
namespace Uplink
open Quipu.Sonnet Schedule
-- ancestor.Welfare
private lemma hops (r:Ratio c f)(x y:Site f): r.count.val*separation (r.parent x) (r.parent y) ≤ separation x y+r.count.val:=by
 apply (Corona.below r _ _).trans; have he:=separation_triangle (r.embed (r.parent x)) x (r.embed (r.parent y)); have h:=separation_triangle x y (r.embed (r.parent y)); have hh:= Corona.near r x; have hq:= Corona.near r y; rw [separation_comm _ x] at he; omega
abbrev habitat (c:Side)(t:ℝ)(p:Site c):= Tale.court (radiusB t-Stores.till t) p
-- `till` proportion.M.G Couture margin.We.Weight.Price.Shape`. full support serializing.Payment unaffected Ω. Supports all Σ sizes.
lemma history {S: StepData c f} {O:V→Site f}{o:V→Support f}{X Y:ℝ}(he:∀ i,o i⊆ habitat f X (O i))(hB:radiusB X≤2*radiusB Y)(hp:10 ≤ radiusB Y): ∀ i,StageArt.fly S.ratio (o i) ⊆ habitat c Y (S.ratio.parent (O i)):= by
 intro i j hj; rcases mem_image.mp hj with ⟨k,hk,rfl⟩; let L:= S.ratio.count.val; let b:=radiusB Y; let w := b-Stores.till Y; have hz : L*separation (S.ratio.parent (O i)) (S.ratio.parent k)≤ 2*radiusB Y+L:= (hops S.ratio _ _).trans (add_le_add (le_trans ((neighbors_mem ..).1 (he i hk)) ((Nat.sub_le ..).trans hB)) le_rfl)
 apply (neighbors_mem ..).2; have hy : 3 ≤ L:= S.patch.coarse -- path
 by_contra! hh; have hc:= Nat.mul_le_mul_left L (Nat.succ_le_iff.mpr hh); rw [Nat.mul_succ] at hc; have he: 2*radiusB Y< 3*(radiusB Y-Stores.till Y):=by unfold Stores.till; omega
 have hw:= Nat.mul_le_mul_right (radiusB Y-Stores.till Y) hy; omega -- include hy*w as fact
-- pay next reserve in ALL epochs, even permitting beyond supportExponent.Th mark.
def additional : Goal G := fun M D _ _=>∀ i j,StepStages j i → ((M.p.profile i).supportExponent+1)*(10*Footprint.preCost 0/(↑(D.L j).val:ℝ)) ≤ (M.p.profile j).supportExponent
-- same argument as `Schedule.Runway`. Need still mark Lease invocation.R_Log arithmetic from these.We.Order.Em.Condition.
private lemma rulers (s : Sheet G) : ∃ g:ℕ→ℕ,∀ i j,StepStages j i → ∀ L:Side,g j≤ L.val →
   ((s.profile i).supportExponent+1)*(10*Footprint.preCost 0/(↑(L.val):ℝ)) ≤ (s.profile j).supportExponent:= by
   let c i j:=((s.profile i).supportExponent+1)*(10*Footprint.preCost 0)/(s.profile j).supportExponent; let m j i:= ⌈c i j⌉₊; refine ⟨fromMax m,fun i j he L hL=>?_⟩
   have hx:c i j≤(L.val:ℝ):= (Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_fromMax m he).trans hL))
   rw [←mul_div_assoc,div_le_iff₀ (by positivity),mul_comm ((s.profile j).supportExponent)]; exact (div_le_iff₀ (s.profile j).price_pos).1 hx
lemma preferred : Obtainable (G:=G) additional:=by
 intro s T C z R E ht; obtain ⟨u,h⟩:= rulers s
 exact ⟨u,fun l hl D w o Z F S hp p₁ hϑ P Q V=> ⟨V,⟨le_rfl,le_rfl,le_rfl,le_rfl⟩,fun W hw C₀ K I hp B he ha _ _ _ _ _ _ _ hx_ ht_ hw' hy_ i j hi=> h i j hi _ ((hl j).trans (D.large j).need)⟩⟩
lemma parent {X:Metals G} {D: Rolls X.p}{A:Alloy X D}(F:Factor A)(hf:additional X D A F)(m p:ℕ)(u:ℝ)(he:u ≤ (A.B.a.budget m).supportExponent +1):
 u*Footprint.conversion (A.B.a.clock.op m p).ratio 0 ≤ (A.B.a.budget (m+1)).supportExponent:=by
 unfold Footprint.conversion; rw [show (A.B.a.clock.op m p).ratio.count=D.L (A.B.a.clock.J (m+1)) from PriceCompiler.block_eq A.B.valid m]; apply (mul_le_mul_of_nonneg_right he ?_).trans
 · rw [show (A.B.a.budget m).supportExponent=(X.p.profile _).supportExponent from congr_arg Stage.supportExponent (params_eq A.B.valid m), show (A.B.a.budget (m+1)).supportExponent=(X.p.profile _).supportExponent from congr_arg Stage.supportExponent (params_eq A.B.valid (m+1))]; exact hf _ _ (step_paid A.B.a m)
 unfold Footprint.preCost; positivity
end Uplink
end YM.Qlocal.Calendars
