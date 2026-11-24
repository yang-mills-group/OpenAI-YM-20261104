import YM.Qlocal.Frigus
import YM.Qlocal.Discount
import YM.Qlocal.BaubleDesk
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Frigus
open Function Filter Set Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open Marker MeasureTheory Extra.Trajectories Overlay RG3.Press RG3.Held RG3.Script.Picnic RG3.Forms
open Progress.DirectedRecipe -- reorder
open PhysicalNext PhysicalNext.Repeat
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Metric Height Roof Input Org Supply Pane Slide
open PriceCompiler ThroughLaunch Opera Boulevard Trio Lantern Roost
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius Classical ContDiff BigOperators YM.Qlocal.Payload
open AllOrder Transit Transit.WheelP Floe.Step.PlanV
open Merge Switch Spectrum UniformPays Publishing Emissions Payload Provisional Footprint StageArt
open RGComparison01 RGComparison01.Pledge
open Leasing Integration Integration.LocalComparison Integration.RiderTastePresentation
variable {Ω ι V : Type} [DecidableEq V] {B:Marker.Census V} {G:Gauge}{X:Metals G}{D:Rolls X.p}
    {Δ:ℕ→Prop}{A:Alloy X D}(F:Factor A){m k p N j k':ℕ} {δ r τ u v w E C : ℝ}
local notation "a"=> A.B.a
set_option quotPrecheck false
local notation "c"=> (a).S.side m p
local notation "f"=> (a).S.side (m+1) p
local notation "I"=> (a).clock.J m
local notation "J"=> (a).clock.J (m+1)
local notation "W"=> (a).budget (m+1)
local notation "L"=> D.L J
local notation "α"=> A.B.kin.alpha N m
local notation "S"=> (a).clock.op m p
local notation "Hx"=> (a).clock.hatBeta m
-- support.Hall process
variable {P : RG.Rep G (A.B.a.S.side (m+1) p)} {R:RG.Rep G (A.B.a.S.side m p)}
variable (hm:m<N) (hp:Lives A.B.bake N (m+1) p P)(hQ:A.B.Move N m p R P)
    (hβ: P.beta∈ band A.B.a (m+1)) (he:∀ U,R.eval U≠0)
    (η:ℕ→ℝ) {Y₀:Org.Bolt A}
open Scale
variable {H T':ℕ→ℕ}
local notation "p₀"=> (a).budget m
local notation "φ"=> (a).clock.hatBeta (m+1)
local notation "p★"=> (a).clock.forcedAllowance m
-- numeric receipts keep for local price conversions.
lemma reserve_bounds (A':Levels G)(m:ℕ) : 0<A'.clock.forcedAllowance m∧ A'.clock.forcedAllowance m ≤1 :=⟨Real.exp_pos _,Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.rpow_nonneg (Real.exp_pos _).le _))⟩
lemma tiles_cast (h: Descends A F m N p R P)(hq:R.p=A.B.a.budget m):∃ F₀:Guide A.B F.shape N m p P, Opera.Price A.B F.shape N m p P F₀ ∧
    Nonempty (KLink R.p ((Beam.marquee F₀ R.p).read (Song.plusone F₀ (Divides.selfA F₀) Chi.canonical (A.B.kin.alpha N m)))
      (Time.forecastK A.B.a m F.scout P.beta /8) (R.p.supportExponent+1+1) R.p R.activities (Time.quoteHard A.B.a m F.book P.beta) R.p.supportExponent):= by
 obtain ⟨K,hK,h⟩:=h; refine ⟨K,hK,?_⟩; rw [hq]; exact h

-- encode raw presentation as Tt.Native.Bolts.V gauges. Any E inherited.
variable [Nonempty Ω] {o: V→Site (A.B.a.S.side (m+1) p)}{s: V→ Support (A.B.a.S.side (m+1) p)}
    (u:V→ℝ){c':B.Mode→ℝ} {d:Set (ℕ ×ℕ)} (Y:Taste Ω o P B)
    (hv:Peak P o Y (rent u c') P.p.supportExponent 1 1)(hw: RetainsDeclared d Y s) [Fintype V][Nonempty V]
    {U:Holdings.Bauble G (D.L (A.B.a.clock.J (m+1)))}
    (hZ: Lease.Coupon F (η:=η) (T:=T') k k' U) -- use Scale.Namespace
    (hD: Descends A F m N p R P)(hS: Transit.WheelP.Station A F)
    (hY: Schedule.runway η H X D A F)
local notation "t!"=> surf L U (X.p.profile I) Hx
local notation "o'"=> (S).ratio.parent ∘ o
local notation "z"=> StageArt.fly (S).ratio ∘ s
-- Pay property in p0 for local rank;
def hardcap (A:Levels G) (T:ℕ→ℕ)(m:ℕ):= A.clock.forcedAllowance m*A.clock.hatBeta (m+1)^(-((T (A.clock.J (m+1))):ℝ))
lemma hip (A:Levels G) (T:ℕ→ℕ) (m:ℕ): hardcap A T m ≤ A.clock.forcedAllowance m:=by
 unfold hardcap; exact mul_le_of_le_one_right (reserve_bounds A m).1.le (Real.rpow_le_one_of_one_le_of_nonpos ((A.fits.delayed (m+1)).le) (neg_nonpos.mpr (by positivity)))
-- register criterion includes Peak cost bag on outgoing AND all assist e_i residual Help.Act compressed process. Preserve Tt.P.F.
local notation "A'"=>Time.quoteHard (a) m F.book P.beta
include hS hY hp hQ
lemma siteBill : P.p.B≤ 2* R.p.B ∧ R.p.supportExponent * Footprint.conversion (A.B.a.clock.op m p).ratio 0 ≤ P.p.supportExponent:= by
 obtain ⟨V,K,h⟩:= hS; rw [hp.point, hQ.bundle.point]; refine ⟨(zones V K A F (m:=m) h.pledge).2.2.2.2.2.2.1,?_⟩
 have hi := (show _ ∧ _ from hY).2 I J (step_paid A.B.a m)
 unfold Footprint.conversion; rw [show ((S).ratio).count=D.L J from PriceCompiler.block_eq A.B.valid m,
         show (p₀).supportExponent=(X.p.profile I).supportExponent from congr_arg Stage.supportExponent (params_eq A.B.valid m),
         show (W).supportExponent=(X.p.profile J).supportExponent from congr_arg Stage.supportExponent (params_eq A.B.valid (m+1))]; exact hi
include hZ he hβ hm hD hv hw -- remove hκM
-- note leave height cost relation. Pick q lot prior. user's fixed relative powers via .spinal_read .Recovered
variable (hC: Spirit c') (hu:∀ i,0 < u i)
include hC hu
set_option maxHeartbeats 1000000
lemma lands : ∃ K: Taste Ω (o') R B,
      (Peak R (o') K (rent (Emissions.shift (t!^2) u) c') R.p.supportExponent 1 (A')) ∧
       RetainsDeclared (Declared R z B) K z ∧ ∀ x, (S).push P.beta (Y.leaf x).density=(K.leaf x).density:= by
 obtain ⟨F₀,hU,Z0⟩:= tiles_cast F hD hQ.bundle.point
 let r:= t!; obtain ⟨ho,h1,⟨hr,hx,hB⟩,hs,hε⟩:= Lease.actual F η T' U hZ; let d:=Emissions.shift r u
 have hq:0<r:=zero_lt_one.trans_le hr; have hQ':0 ≤ StageArt.cost S R.p.supportExponent:= by unfold StageArt.cost; positivity
 obtain ⟨h₂,hf⟩:= siteBill F hp hQ η hS hY; let x:Ω:= Classical.ofNonempty; obtain ⟨g⟩:= Payload.existF hw hv rfl x (rent_spend hu hC.fresh)
 let Δ:ℕ→Prop:= fun _=> True; let v:= A.B.a.clock.allowance (m+1); have hg : (Tithe.portion P.activities Δ).EBound P.p v:= by unfold Tithe.portion Δ; simp; exact hp.valid.labels.boundE
 have hP : v=incomingE G L Hx:= by unfold incomingE; rw [← PriceCompiler.beta_eq A.B.valid m]; rfl
 have hr' :=shift_pos hq hu; have hτ := Lease.actual F η T' U hZ |>.2.2.2.2 p; rw [← hQ.bundle.point] at hτ
 obtain ⟨he,hK,hℓ,hΩ⟩:= standard F hm hp hQ hβ he η U ho F₀ hU (Classical.choice Z0) Y hv hw g hf h₂ hg hP.le (show r⁻¹*(2*(1+1)) ≤ _ by linarith only [hs]) (inv_pos.mpr hq) (rent_spend hu hC.fresh) (rent_spend hr' hC.fresh) (prepaid r hC hr hu) (τ:=1) zero_le_one (fun i hi=> (voyage r (fun i=>(hC.fresh i).le) hu i hr hi).trans (mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hr) ((rent_spend hu hC.fresh i).le)))
 refine ⟨_,?_,hℓ,hΩ⟩; rw [show t!^2=r*r from sq _,← shift_chain]
 rw [one_mul, one_mul, mul_one, one_mul] at hK
 refine Peak.loosen (Peak.transfer (fun i=>(rent_spend (shift_pos hq hr') hC.fresh i).le) (inv_pos.mpr hq|>.le) hK (fun i hi=> voyage r (fun i=>(hC.fresh i).le) hr' i hr hi)) ?_ ?_
 · exact (mul_le_mul_of_nonneg_left hτ (inv_pos.mpr hq).le).trans (le_of_eq (inv_mul_cancel₀ hq.ne'))
 exact mul_le_of_le_one_left (Real.exp_nonneg _) (inv_le_one_of_one_le₀ hr)
end YM.Qlocal.Frigus
