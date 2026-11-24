import YM.Integration.FVA1Physical.Sources.Round2.FieldPalette
import YM.MSbar.Ballet.Palette

/-! Eliminate the ordinary Ballet data for an arbitrary new analytic receipt on the realized scene. The same forest and chart compute the outgoing vacuum. The stage identifications are those in Ballet.palette. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open YM.MSbar YM.MSbar.Ballet RGComparison.Core16.Spool
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Pressure Matrix
open Precision Gauge Midpoint Rolling Tramp Exterior Tree YM.Wilson Laurent Bloch Wave Parma Tin Bronze Asymptotics Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Alto Mosaic Mosaic.Issue
variable {G:Gauge}
open Supply Input
variable {O:ChartRatio G}{K:MapPrices}{B:Sheet G}{D:Rolls B}{Θ:Protection D}{Y0:Delays Θ}{W:Bar Y0}{I:Wait W}{P:PostCost D}(A:Directed G I O K P)
variable (u:G.ColorIndex)(V:Heath.Voice G) (N M k i p m s:ℕ) -- M is minimum scene level. i period. 
variable (T:Scene A.a i p)
variable (hT:Realized A.kin N i M p (sun G u) T)
set_option quotPrecheck false
local notation "C!"=>A.a.clock.op k i
local notation "b!"=>A.a.clock.hatBeta
local notation "ℓ"=>A.a.S
local notation "Ω!"=>A.kin.path
local notation "U!" j=> A.a.params j
variable (R:Rep G (A.a.S.side (k+1) i))(Q:Rep G (A.a.S.side k i))
open Heath
variable (ht:Stock.Season V (A.a.params k) (A.a.params (k+1)) (A.a.clock.hatBeta k) R Q (A.a.clock.op k i) (Stock.courage G (A.a.clock.op k i).patch.L (A.a.clock.hatBeta k))) (hf: R.path=A.kin.path N (k+1))(hg:Q.path=A.kin.path N k)
    (hy: Wedge (T.Poly (k+1)) Dean (hat A.a (k+1)) (candles A.a (k+1)) s p)
    (hLv: 6 ≤ s) (hJ:4 ≤ m)(hr:p+2 ≤ m)
    (hξ: max s m ≤ A.a.clock.J (k+1)) (hp:m+1 ≤ Q.p.order)(hH: Touch R.eval)(hc: M ≤ k)(hk:k < N)

include hT ht hf hg hy hLv hξ hH hc hk
variable (goal:Mosaic.Issue G→Prop)
variable (hX:G.Simple)(h0 : (A.a.clock.op k i).patch.Branches B.kernel G →
  ∃ (Z:Uniform.Before G (A.a.params (k+1)).width (A.a.params (k+1)).paths
    (A.a.clock.J (k+1)) B.kernel (p+3)),
    let P:=(A.a.clock.op k i).patch
    let x:=A.a.clock.hatBeta k;let a:=A.a.clock.J (k+1);let b:=A.a.clock.J k
    let H:=A.a.params k;let H':=A.a.params (k+1)
    Sent O K p s m a b H H' P B.kernel Z u V x ∧
    ∀ C:Mosaic.Issue G,Issue.Paid C P H H' V x → C.S.kernel=B.kernel → Festival C O p u →
      ClockD C p m s x → Cs C O s p m x u (purse Dean (hatW x) p) (bigF (seats K a b s)) →
      Issue.Receipt C (stamping (QCost O K p s a b H' P B.kernel Z) s) x → goal C)
  (hA:Reports K B O A.a)(hu:Merit A.a A.M)
include hX h0 hA hu
open Aqua Bakery Bakery.Portal
-- derivative at every profile stroll.Stamp Schedule
open YM.Integration.FVA1Physical.Round2.Curvature (chargedIssue)
local notation "q₀"=>Aqua.film Q (T.Poly k) (Stock.cue Q.beta) p
local notation "q₁"=>Aqua.film R (T.Poly (k+1)) (Stock.cue R.beta) p
/-- Expose the measured stage inputs once, so any compatible comparison can consume them. -/
theorem apply_scene_receipt (hC : Ticket (b! (k+1)) (A.a.S.side (k+1) i) q₁ s p m) :
    let F:=(hT.step k hk hc).choose
    let v:=(hT.step k hk hc).choose_spec.choose
    let B' := chargedIssue A N k i p T R Q F v
    T.Poly k = B'.Zpost O ∧ goal B' := by
    let S':=C!; let M':=S'.patch
    let F:=(hT.step k hk hc).choose
    let j:=(hT.step k hk hc).choose_spec.choose
    obtain ⟨hz,hj,hK⟩:=(hT.step k hk hc).choose_spec.choose_spec
    let C:= A.a.clock.hatBeta; let Y:=A.a.S.side k i; let X:=A.a.S.side (k+1) i
    have ht0:R.clip=(A.a.params (k+1)).clip:= ht.case_.clip; have ht1:=ht.hull.clip; have h':countV G (C!).patch.L (b! k)=C (k+1):=by unfold C countV Calendar.hatBeta; rw [Schedule.scale_succ]; change _+_*Real.log (A.a.S.block k).val= _ + _*(_+Real.log (A.a.S.block k).val); unfold Levels.S; ring
    let M₁:=(A.M.towers N k).A0; let ρ:=A.kin.stationary N k i F; let B':Mosaic.Issue G:= ⟨_,_,S',F,j,R,Q,ρ,T.Poly (k+1),M₁,T.action k⟩
    have hB:T.Poly k=B'.Zpost O:=by change T.Poly k= bley _ (colorCut F j R.path R.clip O _ _) (MSbar.Wave.ink Y Q.clip Q.path); rw [hf,hg,ht0,ht1]; exact hK
    have hβ:B'.passage (C k)= C (k+1):=h'
    obtain ⟨qx,hP⟩:=hT.budget (k+1) hk (by omega); obtain ⟨hk',hQ⟩:=hT.budget k hk.le hc
    have he:=hu.towns k i; let j₀:=A.a.clock.J (k+1); let j₁:=A.a.clock.J k; have hz':S'.patch.Branches B.kernel G:= (show (A.a.clock.op k i).kernel=B.kernel from A.valid.kernel) ▸ he.1 -- binder names
    obtain ⟨Z,receipt⟩:=h0 hz'
    have hW:=receipt.1.aim
    obtain ⟨hw,hα,hα',hJ',hκ⟩:=hW.E0; let H:=A.a.params k; let H':=A.a.params (k+1); let D':= QCost O K p s j₀ j₁ H' M' B.kernel Z
    let a:= candles A.a k; let b:=candles A.a (k+1); let W:=hat A.a k; let W':=hat A.a (k+1); rw [h'] at hw hα' hJ'; have htW:0 < W:=zero_lt_one.trans_le hw.wise.1; have htW':0 < W':=htW.trans_le hw.wise.2
    obtain ⟨v,v₀,v₁⟩:= (hA.pulse k i).1; have hψ := ready A k N p i s F hu hk Z u j hLv qx.quiet ((show 5 ≤ s from (by omega)).trans ((le_max_left ..).trans hξ)) (inK A k) hα hκ htW' hJ' hα' v₀ v₁
    have hS : Rolling.Serves S' G:=⟨he.1,(A.a.blocks ..).symmetric,(A.a.blocks ..).gauge,he⟩; have hA_:Matrix.PosDef (Push.Uniform.block (priced F j H'.clip (Ω! N (k+1))) 0):= blueprint F j _ _ he.1 qx.quiet (P.price _) (A.support.gap N k i hk F)
    have hc₀:= newT F j (Ω! N (k+1)) (Ω! N k) H'.clip H.clip ρ O A.ratio (T.Poly (k+1)) (T.film (k+1)) p hS (A.support.critical N k i hk F).1 (A.support.classicalPart N k i hk F) qx hA_
    have hc' :αm (C k) ≤ a:=by
         unfold Mosaic.αm a Alto.candles cWidth; simp_rw [_root_.zpow_neg]; rw [one_div]; apply inv_anti₀ (pow_pos htW 2); exact pow_le_pow_right₀ hw.wise.1 (by omega : 2 ≤ 3)
    have hm₁: Station F j ρ R.path R.clip (installed S'.ratio M₁) s (Alto.cWidth (C k)/(S'.patch.L.val:ℝ)) D'.c1 D'.c2 D'.c3 D'.c4:=by rw [hf,ht0]; exact hψ.seat
    have he':Issue.Receipt B' (stamping D' s) (C k):=⟨hm₁,stance A j₀ j₁ k N i hu hk rfl rfl _ s (show 0 ≤ αm _ from (by unfold αm; exact _root_.zpow_nonneg htW.le _)) (hc'.trans hα) ((show 5 ≤ s from (by omega)).trans ((le_max_left ..).trans hξ))⟩
    have hBi: ∀ t':ℕ,t' ≤ p → ∀ x:ℕ,Tin (Measuring.chart X G) b s x W' (PowerSeries.coeff t' (T.Poly (k+1))) (Alto.purse Dean W' t'):= fun t he x' => Tin.aspires htW' (hy.shares _ he) (qx.plane.profile _ he |>.trans (by omega)) _
    have hok: ClockD B' p m s (C k):=by
        obtain ⟨hg,hg'⟩:=hC
        constructor
        · rw [hβ]; exact hg
        · rw [hβ]; exact hg'
        · rw [hβ]; exact fun t he=> hBi t he m
    have hv':∀ k',k' ≤ p → Tin (Measuring.chart Y G) a s (k'+1) W' (PowerSeries.coeff k' (B'.color O)) (purse Dean W k') ∧ Tin (Measuring.chart Y G) a s (k'+1) W' (PowerSeries.coeff k' (B'.Zpost O)) (purse Dean W k') ∧ |PowerSeries.coeff k' B'.tilt| ≤ purse Dean W k':=by
         intro k' he
         have h':= paths F Dean ranked _ (Ω! N (k+1)) (A.a.params (k+1)).clip _ (Ω! N k) (A.a.params k).clip j _ O (T.Poly (k+1)) (T.film (k+1)) u qx hX hP hw hψ hy hz (show Keeps _ _ _ from hK ▸ hQ) hc₀.plane hc₀.bond k' he
         unfold Issue.Zpost Issue.color; dsimp only [B']; rw [← hf,← ht0,← hg,← ht1] at h' -- hψ not occ station
         exact h'
    have hY₁:B'.color O= colorCut F j (Ω! N (k+1)) H'.clip O (T.Poly (k+1)) ρ:=by unfold Issue.color B'; dsimp only; rw [hf,ht0]
    have hq: Cs B' O s p m (C k) u (purse Dean W p) (bigF (seats K j₀ j₁ s)):=by
        let A0:= bigF (seats K j₀ j₁ s); have he0(r:ℕ)(hq:r ≤ p): purse Dean W r ≤ purse Dean W p:= pow_le_pow_right₀ hw.wise.1 (ranked hq)
        have hX_:Tin _ a s m W (MSbar.Wave.ink Y H.clip (Ω! N k)) _:=garnish A _ _ i s hu hk k hk.le a (inK A k) (hα.trans (le_trans (min_le_right ..) (min_le_right ..))) hk'.quiet m _ htW
        have hZ_:Tin _ b s m W' (MSbar.Wave.ink X H'.clip (Ω! N (k+1))) _:=garnish A _ _ i s hu hk (k+1) hk b (inK A _) hα' qx.quiet m _ htW'
        constructor
        · intro i hi; have hp': Tin (Measuring.chart Y G) a s (i+1) W (PowerSeries.coeff i (B'.color O)) (purse Dean W i):=⟨(hv' _ hi).1.dec,fun p he j=> ((hv' _ hi).1.fan p he j).trans (div_le_div_of_nonneg_left (hv' _ hi|>.1.dec) (pow_pos htW _) (pow_le_pow_left₀ htW.le hw.wise.2 _))⟩
          rw [hY₁] at hp' ⊢; exact ((hp'.aspires htW (hc₀.plane.profile _ hi|>.trans (by omega)) m).it htW (he0 _ hi) le_rfl)
        · intro i hi; exact ((hv' _ hi).2.2).trans (he0 _ hi)
        · change Tin _ a s m W (MSbar.Wave.ink _ Q.clip Q.path) (W^2*A0); rw [hg,ht1]; exact hX_.it htW (mul_le_mul_of_nonneg_left (le_max_left ..) (sq_nonneg ..)) le_rfl
        · rw [hβ]; change Tin _ b s m W' (MSbar.Wave.ink _ R.clip R.path) (W'^2*A0); rw [hf,ht0]; exact hZ_.it htW' (mul_le_mul_of_nonneg_left (le_max_right ..) (sq_nonneg ..)) le_rfl
        change 1 ≤ |caliper _ _ (MSbar.Wave.ink _ Q.clip Q.path)|; rw [ht1,hg]; exact hψ.cand
    have hg₁: Critical F R.clip R.path B'.ρ ∧ ClassicalMatch F R.clip Q.clip R.path Q.path B'.ρ:=by rw [hf,hg,ht0,ht1]; exact ⟨hψ.critical,A.support.classicalPart N k i hk F⟩
    have hK': ∃ f,Trend f (B'.Zpost O) Q.path Q.clip p:=by rw [← hB,hg,ht1]; exact ⟨_,hk'⟩
    have h₁ : ∃ f,Trend f (B'.color O) Q.path Q.clip p:= by rw [hg,ht1,hY₁]; exact ⟨_,hc₀⟩
    have h₂ : ∃ f,Trend f B'.T R.path R.clip p:=by rw [hf,ht0]; exact ⟨_,qx⟩
    have hx:Festival B' O p u:=⟨hg₁.1,hψ.crop,hg₁.2,hz,h₂,h₁,hK',hP,hB ▸ hQ,hH,ht.taskEval ▸ safePush _ hS hH⟩
    refine ⟨hB,?_⟩
    exact receipt.2 B' ⟨rfl,ht⟩ A.valid.kernel hx hok hq he'

end YM.Integration.FVA1Physical.Wilson
