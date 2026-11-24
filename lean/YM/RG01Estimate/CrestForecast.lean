import YM.RG01Estimate.Scope
import YM.UVNext.COUPLING_RESET.Regular
/-!
 # Specific cost for Bare forecast used in alignment; only pay candidates as extra.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Promise
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree Matrix
open Push Push.Uniform Push.SectorMeasure Presented PhysicalNext.Repeat
open PhysicalNext.Repeat.Lapis PhysicalNext.Repeat.Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Animals PhysicalNext.Repeat.Fare Sienna Conditioning Token Office Courtyard RealTaylor
open Laplace Laplace.Stellar Series Boulevard Blaze.Frond Exterior Abacus
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Geo Footprint
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{c f:Side}{S:StepData c f}(T:Tube G S)(F:Forest S.ratio)(B:BudgetPoint)
   {μ C Λ r a W K Y s:ℝ}{R n:ℕ}
section car
local notation "X" => Positions (Uniform.Primary c G)
variable (V : ℝ × Positions (Uniform.Primary c G)→ℝ)

def columnR (x:X):= mainTerm T.low T.down (actual x)
def floorR (γ:ℝ) (x:X):= draft γ T.down T.low (tint G _ x)
-- raw residual before mask; T kept.
def liftsR (γ:ℝ)(x:ℝ × Positions (Uniform.Primary c G)):=
    columnR T (rho x).2+(x.1^2)*floorR T γ (rho x).2+V x

lemma supplies_forecast (X':ℕ→ Config G c→ℝ) (β γ:ℝ)(h:0<β)
     (hf:∀ i∈ball (0:Positions (Uniform.Primary c G)) Y, actual (gStep β • i)∈ Boulevard.sunny B → Boulevard.throng X' (actual (gStep β • i))=β*V (gStep β,i)) :
      ∀ i∈ball (0:Positions (Uniform.Primary c G)) Y, actual (gStep β • i)∈ Boulevard.sunny B → Promise.forecast T X' β γ (actual (gStep β • i))=β*liftsR T V γ (gStep β,i):= by
  intro x hx ht; let b:=gStep β; have hh:= Fare.gS β h; let Z:=actual (b • x)
  unfold Promise.forecast; rw [hf x hx ht]; unfold liftsR
  change _=β*(columnR T (b • x) + b^2*(γ*secondTerm T.low T.down Z+Precision.loop T.down Z)+V _)
  unfold columnR; unfold Z b; linear_combination -(γ*secondTerm T.low T.down (actual (gStep β • x))+Precision.loop T.down (actual (gStep β • x)))*hh.2

variable (A:BareRates.pre G μ C n) (s:ℝ) (b t M:ℝ) (h : T.down.Bounds T.low μ C Λ) (hm:(Fintype.card (Uniform.Primary c G):ℝ)≤ M)
    (he:1≤M)(hn:1 ≤ n)

def lowerW (J:BareRates.pre G μ C n)(c:Clip)(M:ℝ):= tollS M n (BareRates.bill J c) * (1+1)
def higherW (J:BareRates.pre G μ C n)(c:Clip) (M α Λ :ℝ):= tollS M n ((1+α+Λ)*BareRates.bill J c)*(1+1)
include B in
lemma zeroed : columnR T 0=0 ∧ floorR T t 0=0:= by
    have h':(actual (0:Positions (Uniform.Primary c G)))= (1:Config G c):=by simp [actual]
    have hv:(1:Config G c)∈ sunny B:= Promise.f_one B
    obtain ⟨h₁,h₂,-⟩:= UVNext.CouplingReset.unmasked_precision T.down T.low (smoky hv)
    rw [BetaTransport.kinetic_one] at h₁
    rw [UVNext.CouplingReset.loop_one] at h₂
    change mainTerm _ _ (actual 0)=0 ∧ t*secondTerm T.low T.down (actual 0)+Precision.loop T.down (actual 0)=0; rw [h',← h₁,← h₂, UVNext.CouplingReset.second_one]; simp
include B h hm he hn
lemma base_bill (x:X)(hx:x∈ball 0 1): Brush n (lowerW A T.low M) 1 (columnR T) x ∧ Brush n (higherW A T.low M |t| Λ) 1 (floorR T t) x:= by
   have hp x (hx:x∈ball (0:X) 1):= bareSocket c A h hx t
   obtain ⟨_,_,hr,hH,hF,hK⟩:= hp x hx
   have hv:= hasInheritance h
   have hx' i (hi:i∈ ball (0:X) 1):= hp _ hi
   obtain ⟨hh,hq⟩:=zeroed T B t
   exact ⟨horizon0 he hm hH.le hr zero_lt_one hh hn hx (fun i hi=> ⟨(hx' i hi).2.2.2.2.1,(hx' i hi).1⟩), horizon0 he hm (by positivity) hr zero_lt_one hq hn hx (fun i hi=> ⟨(hx' i hi).2.2.2.2.2,(hx' i hi).2.1⟩)⟩

def price_view (J:BareRates.pre G μ C n)(c:Clip)(M t Λ Υ s:ℝ):= clump n (Courtyard.expense n Υ) (lowerW J c M) + Series.cost n 1 (Series.cost n 1 1 1) (clump n (Courtyard.expense n Υ) (higherW J c M t Λ))+s
lemma crest_view (hY:1≤ Y)(hv:b*Y≤1)(hb:b ≤1)(ht: |t| ≤ W)(hk:Λ ≤ a)(hp : ∀ x∈ corridor b (ball (0:Positions (Uniform.Primary c G)) Y), Brush n s 1 V x) :
     ∀ x∈ corridor b (ball (0:Positions (Uniform.Primary c G)) Y), Brush n (price_view A T.low M W a Y s) 1 (liftsR T V t) x:= by
   intro x hx; have hh := mem_ball_zero_iff.mp hx.1; have hr := mem_ball_zero_iff.mp hx.2
   have hz := (norm_snd_le (rho x)).trans_lt (((rho_mem x hY hr).trans_lt (mul_lt_mul_of_pos_right hh (zero_lt_one.trans_le hY))).trans_le hv)
   obtain ⟨hF,hQ⟩:= base_bill T B A t M h hm he hn (rho x).2 (mem_ball_zero_iff.mpr hz)
   have hc:higherW A T.low M |t| Λ≤ higherW A T.low M W a:= by
     have hp : 0<BareRates.bill A T.low:= (bareSocket _ A h (mem_ball_self (x:=(0:X)) zero_lt_one) t).2.2.2.1; unfold higherW tollS; gcongr
   let f(y:ℝ × X):= y.1
   have he':Brush n 1 1 f x := Brush.linearB (ContinuousLinearMap.fst ℝ ℝ X) (hh.le.trans hb) (by rw [one_mul]; exact ContinuousLinearMap.norm_fst_le ..) zero_le_one
   have h₂: Brush n (Series.cost n 1 1 1) 1 (fun x=> f x^2) x:= by
      simp_rw [sq]; exact tint_cost (ContinuousLinearMap.mul ℝ ℝ) he' he' (ContinuousLinearMap.opNorm_mul_le ..)
   exact ((Stellar.panel x (hh.le.trans hb) hY hr.le hF).gathering (tint_cost (ContinuousLinearMap.mul ℝ ℝ) h₂ (Stellar.panel x (hh.le.trans hb) hY hr.le (hQ.climb hc le_rfl)) (ContinuousLinearMap.opNorm_mul_le ..))).gathering (hp x hx)
end car
lemma view_cost {G:Gauge} {L:Side}{n:ℕ} (M Y t s:ℝ→ℝ)(hM:Cookie G L M)(hY:Cookie G L Y)(ht: Cookie G L t)(hs: Cookie G L s)(c:Clip)(v:BareRates.pre G μ C n): Cookie G L (fun i=> price_view v c (M i) (t i) (ConnectedActivityE6.loopBill G L i) (Y i) (s i)):= by
   have he : Cookie G L (ConnectedActivityE6.loopBill G L):= (Cookie.const 2).pays Cookie.mast
   let hp:= hM.pow n; let hx:=hY.expense n
   let hz : Cookie G L (fun x=> lowerW v c (M x)):= ((hM.pow n).pays (Cookie.const _)).pays (Cookie.const _)
   let hf : Cookie G L (fun x=> higherW v c (M x) (t x) (ConnectedActivityE6.loopBill G L x)):= (hp.pays (((Cookie.const 1|>.joins ht).joins he).pays (Cookie.const _))).pays (Cookie.const _)
   exact ((hx.lump hz n).joins (((Cookie.const _).pays ((Cookie.const _).pays (hx.lump hf n))).pays (Cookie.const _))).joins hs
end YM.RG01Estimate.Promise
