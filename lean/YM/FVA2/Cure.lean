import YM.FVA2.ProfilePower
import YM.FVA2.MarketContrib
import YM.FVA2.InField
/-!
# Limit with positive power after position normalization, canonical scheme
 -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 940000
noncomputable section
namespace YM.FVA2.Elegant
open Function Filter Set MeasureTheory PositionX
open Pert Pert.Position Maxwell Maxwell.Free PositionX.Bare.Shop PositionX.Jet
open PositionX.Ribbon PositionX.Detector PositionX.Bend
open Lattice Topology
open MS MS.Menus MS.Land MS.Theater MS.Book MS.Book.Program MS.Book.Convolve MS.Orbit MS.Tide MS.Rake
open Clock Score Based PairCoords Modes Paper Trans ColorCode Attend BoxOffice Blaze Frost ArchTurn
open PowerSeries WorldJet Counterpart Spring
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} (hg:G.Simple) {B:Booked (wings G)} (V:Warehouse G)(P: Prescription (wings G))(M:MS_Data G B)
variable (H:ExactSpin V P)(HI:Trusted P)(he: MixedStory.AllProfiles M V P)
variable (q:ℕ+)(hq:1<q.val) (μ:ℝ) {d c:ℕ}
local notation "Y"=> V.F
local notation "ℙ"=> BoxOffice.warehouse V
local notation "D"=>nested V.F hg ( BoxOffice.warehouse V )
local notation "𝒮"=>ms V M μ
local notation "Ξ"=>Bank V.F
local notation "κ"=> Buffer V.F
local notation "ℓ"=> lookie V.F
local notation "ψ" x=> (μ-Pond.clock q x)
open Prow Fountain
local notation "τ"=> unglue V P H HI q μ
local notation "Bκ"=> bust hg V P H HI q μ
local notation "F"=>stage hg V P H HI q μ
local notation "η"=> feel q
include hq
lemma fading : Rag atTop ( feel q ):= ⟨ Eventually.of_forall fun j=> cost_pos q j|>.le, Real.tendsto_exp_atBot.comp ( (Pond.forward q hq).const_mul_atTop_of_neg (neg_lt_zero.mpr mild_p) ) ⟩
variable {W:Type*}{l:Filter W} {f:W→ ℕ}(h:Tendsto f l atTop)
include h
lemma fading_t : Rag l (η ∘ f):= ⟨ Eventually.of_forall fun _=> cost_pos _ _ |>.le, ( fading q hq ).vanish.comp h ⟩
include he
-- on-filter hp extracted anyway.
lemma start_power (d:ℕ): Prow.Gold l (η ∘ f) (fun i=>τ (f i) d) (fun _=>𝒮 d) (𝒮 d):= by
    intro ⟨p,v,u⟩ i; refine ⟨?_, tendsto_const_nhds⟩; obtain ⟨C,hC,hP⟩:= limits_power V P M H HI he q hq i μ u v; exact ⟨ C,hC,h.eventually ( hP.mono (fun p hp=> by rw [← dist_eq_norm] at hp; exact hp)) ⟩
lemma report_power (d:ℕ): side l (η ∘ f) (fun i=> Bκ ( f i ) d) (fun _=> turns hg V M μ d) (turns hg V M μ d):= Gold.reports ( fading_t q hq h ) ( start_power V P M H HI he q hq μ h d ) _ ( regular .. ) -- amb Gold
lemma pattern_power (d:ℕ) : Prow.Gold l (η ∘ f) (fun i=> F ( f i ) d) (fun _=> pattern hg V M μ d) (pattern hg V M μ d):= by apply Gold.shop ( fading_t q hq h ) ( start_power V P M H HI he q hq μ h d ) (report_power hg V P M H HI he q hq μ h d)
variable {R:ℝ}(T:Booth R V.F)(K:Knocker hg T q hq ( warehouse V ))
local notation "𝔛"=> ξ hg V M μ T
local notation "χ"=> isell hg V P H HI q μ T
local notation "ℚ"=> Bend.curveF (warehouse V) q hg T
local notation "Ω"=> renormal (warehouse V) q hg T
lemma χpower : side l (η ∘ f) (χ ∘ f) (fun _=>𝔛) 𝔛:= by
    let t:=pattern hg V M μ 6; let U(i:W):=F ( f i ) 6; let b:= Board7 V.F T.r1; obtain hF:= fading_t q hq h; obtain ht:= pattern_power hg V P M H HI he q hq μ h 6; have hu: side l (η ∘ f) (fun i=> b∘ (U i)) (fun _=>b∘t) (b∘t):= by intro k; refine Tandem.every hF (fun i=> ht (menu V.F T.r1 i) k); -- context
    have he:= side.runs hF hu rankT rank_smooth.contDiffAt; intro n; rcases n with _|n; · simp_rw [ comp_apply, show ∀ i, χ i 0=0 from fun i=> metric_zero .., show (ξ hg V M μ T) 0=0 from metric_zero .. ]; exact Tandem.stable hF _
    let c:= T.normalC; have hl(p:Word ( Bank V.F 6 )): metricT T p (n+1)=c⁻¹*(Wanted T.r1 p (n+1)).re:= by simp [metricT,haze, smul_eq_mul,just,c]
    simp_rw [comp_apply,Elegant.ξ,isell,hl]; apply Tandem.smult hF ( Tandem.stable hF c⁻¹ ); exact Tandem.after hF ( he (n+1) ) Complex.reCLM Complex.reCLM.contDiff.contDiffAt -- he is shadow
include K H HI μ
lemma tip_power : Tandem l (η ∘ f) (fun i=> ℚ ( f i ) 1) (fun _=>1) 1:= by
    obtain hp:= χpower hg V P M H HI he q hq μ h T 1; dsimp only [Function.comp_apply] at hp; rw [ show ( Elegant.ξ hg V M μ T ) 1=1 from χone hg V P M H HI he q hq μ T K ] at hp; refine hp.congr ?_; filter_upwards [ h.eventually ( meterBound hg V P M H HI he q hq μ T ) ] with i hi; show χ (f i) 1=_; rw [ hi,Jet.tip ( φzero P q μ (f i) ),φone,one_smul] -- comp.elab
lemma inverse_power : side l (η ∘ f) ( fun i=> Jet.inverse (χ ( f i ))) ( fun _=> Jet.inverse 𝔛 ) (Jet.inverse 𝔛):= side.inverted (fading_t q hq h) ( χpower hg V P M H HI he q hq μ h T ) (χlive hg V P M H HI he q hq μ T K ) ( h.eventually (meterLive hg V P M H HI he q hq μ T K|>.1 ) |>.and ( Eventually.of_forall fun _=> χlive hg V P M H HI he q hq μ T K ) ) -- defeq and?
lemma endpoint_power (d:ℕ) : Prow.Gold l (η ∘ f) ( fun i=> Ω ( f i ) d ) (fun _=> bright hg V M μ T d) ( bright hg V M μ T d ):= by
    let T':=pattern hg V M μ d; obtain hk:= inverse_power hg V P M H HI he q hq μ h T K; obtain ht:= pattern_power hg V P M H HI he q hq μ h d; obtain hL:= Gold.rebuy ( fading_t q hq h ) ht hk;
    intro s n; refine (hL s n).congr ?_; filter_upwards [ h.eventually ( turn_meter hg V P M H HI he q hq μ T K d ), h.eventually ( meterLive hg V P M H HI he q hq μ T K|>.1 ) ] with i hi hx; change (( ℓ s ) ∘ ( ren ( Jet.inverse (χ ( f i )) ) (F ( f i ) d) )) n = _; rw [hi,ren_writes,ren_writes, asc ( lives ( χ ( f i ) )) hx.1,guarded hx,ren_head ];
end YM.FVA2.Elegant
