import YM.AllOrder.Local.Carbon
import YM.AllOrder.High.Extract
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Roof.Honey

/-!
# Uniform auxiliary layout prices for the stepwise high expansion

Work strictly in P-L subwindows. Donate inflated halo parameter for *counting*
windows only, not a different E6 target, so previous roots retained. Buy
prediction and height AND path-tail and room to preserve estimates across same
period thereafter. Use one grade π cap and sum all orders to any k≤a passed,
post β remains physical, not a choice of observation basis. Estimates combined
at arbitrary power η; not presuming given parameters for the proofs. More
(high-field, model packets etc.) can ask stronger gates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Shop
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Bid Planned.JetPort PhysicalNext Repeat Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Trio Lantern High
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {i j:ℕ}

section currency

def parking (π b : ℕ) : ℕ:=10*((π+10)^2)*(b+10)
def cargo (π b B:ℕ):= Meadow.studio (parking π b) B
lemma traffic (π b:ℕ) (k : ℕ) (h : 1 ≤ k) : clusterBound π (Mint.width b k k) π + Mint.width b k k ≤ cargo π b k := by
  -- huge room enlargement :( #cap. Independent of c.
  let D:=Mint.width b k k; let v:=(b+10)*k
  have he:D≤ v:= by unfold D Mint.width v; nlinarith
  have hv:1 ≤ v:= by unfold v; nlinarith
  have hx: (π+1)*π ≤ (π+10)^2:= by nlinarith
  change clusterBound π D π+D ≤ _; unfold clusterBound; calc
   _ ≤ (π+10)^2*(4*v+2)+2*v+v:= by gcongr
   _ ≤ (π+10)^2*10*v:= by nlinarith [Nat.le_mul_of_pos_left v (show 0 < (π+10)^2 from by positivity), Nat.mul_le_mul_left ((π+10)^2) hv]
   _ ≤ _ := by change _ ≤ 18* (parking π b*k+(6*k+3)+k)+8+2*k; rw [show (π+10)^2*10*v=parking π b*k by unfold parking v; ring]; omega
lemma perimeter (π b B:ℕ): B+B≤ cargo π b B:= by unfold cargo Meadow.studio; omega
-- π choose ∝ target high power & jet orders for width; independent of window geometry.
def tall (i:ℕ):=4*(i+2)
end currency

variable {X: Metals G} (D: Rolls X.p) {C : Targets X.p X.K} {Z :Expenses C} {F : ℕ→ℕ→Postage} {S : Time.Scouts (F:=F)} {p:Return.Wages} {v:ℕ→ℝ} (R : Repeat.Register D Z p v)
    {P : Protection D} {u : Delays P}
local notation "J" => (Testing.query X.p X.K j i)

section first
-- Tickets after hearing halls. Orders m use fixed ξ values and finite request list (cap derivative supplied).
abbrev seam_hat (t:ℕ) : ℝ:= -1 - t

-- one price test on geometry. b window for Taylor chosen later; leaves explicit z^eta before actual r=guards.
def MorningP (i j k n : ℕ) (t η : ℝ) : Prop := let Q:= C j i; let L:= D.L j; let I:= parking (tall i) Q.halo; let E:= X.p.profile j; let H:= X.p.profile i; let V:= ConnectedActivityE6.loopBill G L t
    Real.exp 1 ≤ t ∧ ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (F:Forest S.ratio) (X' : Coat T F) (B B' : BudgetPoint) (h : 4≤j), S.patch=(Mural.sheet X.p D h) → S.kernel = X.p.kernel →
    Quilt T F (Trio.paySide G L I t) → T.high=E.clip → T.low=H.clip → T.up.Bounds T.high E.width E.paths V → T.down.Bounds T.low H.width H.paths V →
    ∀ ρ, Critical F T.high T.up ρ → ClassicalMatch F T.high T.low T.up T.down ρ →
    B'.threshold=Pressure.temp t → ∀ (l:S.Choices) (β a r:ℝ), Cash (p j i) t (R.μ j i) L Q (R.o j i) a T (virgin T B β) → X'.x=t → X'.width=(R.o j i).K → X'.manifest → flags (Pressure.temp t) X'.V=∅ →
       ∀ x : Positions (Uniform.Primary c G), X'.V=represent (tint G _ x)→ ‖(gStep β,x)‖ ≤ r → r<eaves G L t → ‖x‖+2*furl G L t< eaves G L t →
         let z:= betaF G t L; 0 < Token.tramp T B β x ∧ Blaze.Brush n (z^η*(z*r^(k+3)+r^(k+1)) + z^(seam_hat i)) (r⁻¹) (Token.pures T B β- Local.Pure.script F T Q.table ρ β l k) x

set_option maxHeartbeats 200000 in
lemma announces {k n:ℕ} (he:StepStages j i) (hk : k+3 ≤ n) {η:ℝ} (ho:0<η) : ∀ᶠ t in atTop, MorningP D R i j k n t η:= by
  by_cases hJ : 4≤ j
  swap; · filter_upwards [eventually_ge_atTop (Real.exp 1)] with t ht; exact ⟨ht,fun _ _ _ _ _ _ _ _ h=> (hJ h).elim⟩
  let G₀:= C j i; let b:=parking (tall i) G₀.halo
  let P:= Mural.sheet X.p D hJ; let E:= X.p.profile j; let H:= X.p.profile i
  obtain ⟨V'⟩:= Uniform.pre_order G E.width E.paths P.J X.p.kernel (n:=(n+1+2)+3) (by omega)
  let w:= Classical.choice (BareRates.offered G H.width H.paths ((n+1+2)+3))
  obtain ⟨A,hA,h'⟩:= Local.Pure.predicted P G₀ (R.o j i) n k V' (Classical.choice (Planned.JetPort.purchase G₀.table G₀.table_exists _)) w E.clip H.clip hk (Trio.circles G P.L b) _ (seam_hat i) (R.consumes _ _ he).2.1
  filter_upwards [h', hA η ho, eventually_ge_atTop (Real.exp 1),Delay.shift_pos G P.L] with t hT hη hL hz
  refine ⟨hL,fun c f S T F X B B' hJ hS hK hv hh he hp hB ρ hρ hm h' l β a r Q hX hF hM hV x he' hr hU hy =>?_⟩
  let W:= Sienna.warm V' hS hK
  obtain ⟨σ,hσ⟩:= W.graph F hp hv.large rfl rfl
  have ht:= Before.Service.is_extension hσ hρ; have hH : ClassicalMatch F T.high T.low T.up T.down σ:=by
    intro i hi v; obtain ⟨hP,hg,hV⟩:= hm i hi v
    have hx:= ht.mono (p:=fun x=> ρ x=σ x) (q:=fun x=>tested F v T.high T.up x (ρ x)=tested F v T.high T.up x (σ x)) (fun x=> congr_arg _)
    have hyg : (fun x=>tested F v T.high T.up x (ρ x))=ᶠ[𝓝 0] fun x=>tested F v T.high T.up x (σ x):=hx
    exact ⟨hP.congr_of_eventuallyEq hyg.symm,hg, ((hyg.iteratedFDeriv ℝ i).eq_of_nhds).symm.trans hV⟩
  obtain ⟨hP,hg⟩:= hT c f S T F hS hK l B B' h' hv hh he (hh ▸ hp) _ (he ▸ hB) σ hσ hH β a Q X hX hF hM hV x he' hy r hr hU
  have hR:0 ≤ r:=(norm_nonneg _).trans hr
  refine ⟨hP,?_⟩; rw [Local.Pure.one_frame F T _ _ _ l ht k β]; exact hg.climb (add_le_add (mul_le_mul_of_nonneg_right ((le_abs_self _).trans hη) (by positivity)) le_rfl) le_rfl
end first
end YM.AllOrder.Shop
