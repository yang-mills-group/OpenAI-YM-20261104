import YM.OPE.Compatible.Kyoto.Mind
import YM.OPE.Compatible.Kyoto.Brawn
import YM.OPE.Compatible.Kyoto.Ploy
import YM.OPE.Compatible.Kyoto.Team
import YM.OPE.Compatible.Kyoto.Cloud
import YM.OPE.Compatible.Kyoto.Gazer
import YM.OPE.Compatible.Kyoto.Opal
import YM.OPE.Compatible.Kyoto.TreeQ
import YM.OPE.Compatible.Ice.Ares
import YM.OPE.Compatible.Nut.Hero
import YM.OPE.Compatible.Silva.Bride
import YM.OPE.Compatible.Kyoto.Room
/-!
# Operator estimates for matched coefficient frames

`TapeWork` applies the single-coefficient comparison to a finite
basis to bound the operator discrepancy. Under the scale and rate
hypotheses of `ΡLift`, the frame transport eventually defines a
complex-linear equivalence. Its norm and its inverse norm share
a bound of upper exponential rate zero.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark Topic StageLight
variable {n c f:Side}{I :Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{C:KernelChoices}{p p':Clip}
variable {v v' b u:ℝ}

variable {H:LocalRatio R}{hs:G.Simple}
open Balsam Nestle Pert.Full GlowPack Yolk Pipes Dial Raucous Zeph Zeph.Dew Borealis Flume.Script 
open Next.Free
section
variable {L:PriceBook H T}{a:Axis}
namespace MatchZ

section
open Lass.Zest Lass PhysicalNext.Repeat.Aroma Pressure ConnectedActivityE6 Shell Channel
variable {Ξ:Medal P' G K.K P'.J} {P₀:Teller G}
variable {E:ConnectedActivityE6.Target G P₀} {Q:Side}{W C κ:ℝ}{o:ConnectedActivityE6.Target.Order G W}
variable (F:I→Mug P' p p' T j R Ξ)
variable (L₁:∀ i,Wall P' E Q o κ C k (F i).hostS){l₀:Filter I} (hq:Chase (Eve L₁) l₀)
local notation "ζ"=>Eve L₁
local notation "X*!"=> fate (Eve L₁)
variable {β ε:I→ℝ}
set_option quotPrecheck false
variable (R1:ℝ)(hV:∀ i,|MatchZ.fare ((F i).row)|≤R1)(hv:Mag P'.J j) (hp:Wage (Eve L₁) l₀ (fun i=> (F i).row.fine.fees) 0)
set_option quotPrecheck false
open Limn
open Spells Labels Source Cameo Yolk Pill Lass.Zest.Torch Ibis
variable (V:Foyer L hs a l (d+6)){he:highStage L hs a V ≤ P'.J} {he':highStage L hs a V ≤ j}
variable (X:BankW L hs a V he p)
variable (Y:BankW L hs a V he' p')
variable (hz: Shear L₁ (fun i=>(F i).pV) l₀ β)
variable {c r' t:ℝ}(H₀:StackP R c r' t)
variable {A:Labels.Frame G l}{U₀:Hol G}{S:SectionData A}
variable {M:∀i,A.Coeff → Coefficient A (F i).f}{N:∀i,A.Coeff → Coefficient A (F i).c} {η γ:I→ℝ}
variable (P₁:∀ i,Torch S U₀ 0 (F i|>.pW) (M i) d (η i))
variable (P₂:∀ i,Torch S U₀ 0 (F i|>.pV) (N i) d (γ i))
variable (hf:Torch.BondS P₁ (βM (Eve L₁)) l₀ (Chase.σW (Eve L₁)))(hc:Torch.BondS P₂ β l₀ ε)
variable (hΔ: Cameo.Quench (fate (Eve L₁)) l₀ (fun i=> (F i).pW.beta) (fun i=> (F i).pV.beta) (fun i=> (F i).row.fare) (Chase.σW (Eve L₁)) ε)
variable (H0: ∀ᶠ i in l₀,(F i).pV.eval=(F i).hostS.Z.push (F i).pW.beta (F i).pW.eval)
local notation "κS"=> Chase.σW ζ
local notation "δh"=> (P'.L.val:ℝ)^l
variable (z:I→A.Coeff)(z':I→A.Coeff)
variable (hM: Receipt (βM (Eve L₁)) l₀ z)(hN:Receipt β l₀ z')
variable (hF:∀ᶠ i in l₀,(N i (z' i)).density 0 S (F i|>.pV)= ((P'.L.val:ℝ)^l) • ((F i|>.hostS.Z).push (F i|>.pW.beta) ((M i (z i)).density 0 S (F i|>.pW))))
variable (R'':Spells.Pad G)(e':ℂ→L[ℝ]ℝ) (hK:  Wage (Eve L₁) l₀ (fun i=> ((↑(F i).c.val:ℝ))⁻¹) v)(hq':-(11/10:ℝ)< v)
local notation "T1*"=>fun i=> tintX V (he:=he) (P₁ i) (F i).row.fine R'' ((Chase.σW (Eve L₁)) i) e' (z i)
local notation "T2*"=>fun i=> tintX V (he:=he') (P₂ i) (F i).row.coarse R'' (ε i) e' (z' i)
local notation "W˘"=>fun i=> Ibis.vintage G V.pay.st.hτ ((F i).row.fare) ((T2*) i)-((P'.L.val:ℝ)^l) • Flail (F i) V ((T1*) i)
local notation "ΖQ"=> V.pay.st
variable {t':ℝ} 
local notation "ZT"=> fun i=> Stint V (F i|>.row) Ξ
local notation "N*"=> fun i=> (F i).row.coarse
local notation "C*"=> fun i=> (F i).row.fine
local notation "Á"=> FaithV
variable (heL:l+6≤d)(hT:v<t')(hW:∀ᶠ i in l₀, RequestZ (P':=P') (j:=j) V (hazard V he') heL v t' hT hq' I (fate (Eve L₁) i) ≤ (F i).c.val)(hC:Wage (Eve L₁) l₀ (fun i=> (F i).row.coarse.fees) 0)(hB:P'.L= V.pay.st.S.L^m)
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
local notation "Z!"=>V.pay.st
section
variable (f:I→ A.Coeff→L[ℂ] A.Coeff)(hZ:Receipt β l₀ f) (fM:∀ᶠ i in l₀,∀ z:A.Coeff,(N i (f i z)).density 0 S (F i|>.pV) = ((P'.L.val:ℝ)^l) • ((F i|>.hostS.Z).push (F i|>.pW.beta) ((M i z).density 0 S (F i|>.pW))))

include hc hZ in
private lemma transformedPrice (x : A.Coeff) : Receipt β l₀ (fun i => f i x) := by
  have operatorNorm : Receipt β l₀ (fun i => ‖f i‖) := by
    obtain ⟨u, price⟩ := hZ
    exact ⟨u, price.norm⟩
  exact (operatorNorm.product (Score.steady ‖x‖ (carth hc.Lamp.Clock))).under
    (Eventually.of_forall fun i => (f i).le_opNorm x)

private abbrev coefficientPrice (x : A.Coeff) (read : ℂ →L[ℝ] ℝ) :=
  LeapYear F L₁ hq R1 hV hv hp V X Y hz H₀ P₁ P₂ hf hc hΔ H0
    (fun _ => x) (fun i => f i x) (Score.steady x hq.tense)
    (transformedPrice (F := F) (P₂ := P₂) (hc := hc) (f := f) (hZ := hZ) (x := x))
    (fM.mono fun _ given => given x) R'' read hK hq' heL hT hW hC hB

include X Y hq hf hc hΔ hW hT hC hB hK hq' hz heL H0 hv H₀ hp hV
include hZ fM
lemma TapeWork : Wage ζ l₀ (fun i=> (ClockVal V Y (F i).row.coarse S R'' (P₂ i) (ε i)).comp (f i) - (Adventure V X Y P'.L (Stint V (F i).row Ξ) (F i).row.fine (F i).row.coarse (Chase.σW ζ i)).comp (ClockVal V X (F i).row.fine S R'' (P₁ i) (Chase.σW ζ i))) t':=by
  refine Wage_obs V X Y R'' P'.L (ZT) (C*) (N*) P₁ P₂ f hq.tense ?_
  intro index read
  with_reducible
    exact coefficientPrice (F := F) (L₁ := L₁) (hq := hq) (R1 := R1) (hV := hV)
      (hv := hv) (hp := hp) (V := V) (X := X) (Y := Y) (hz := hz) (H₀ := H₀)
      (P₁ := P₁) (P₂ := P₂) (hf := hf) (hc := hc) (hΔ := hΔ) (H0 := H0)
      (f := f) (hZ := hZ) (fM := fM) (R'' := R'') (hK := hK) (hq' := hq')
      (heL := heL) (hT := hT) (hW := hW) (hC := hC) (hB := hB) (CastX (X := A) index) read
end
section treaty
variable {L':Filter I}{Kη Bf Bc:I→ℝ}
variable {α:I→ℝ}
variable (hh:∀ᶠ i in L', Bf i-Bc i= Δfare G P'.L)(hP:Tendsto Kη L' atTop)(hx:Tendsto Bf L' atTop)(he1:RateLE L' Kη (fun i=> (F i).row.fine.fees) 0)(hQ:RateLE L' Kη (fun i=>(F i).row.coarse.fees) 0)
       (hΛ: RateLE L' Kη Bf 1)(hE:RateLE L' Kη α (-(1/2)))(hB':∀ᶠ i in L', Bf i * α i^2 ≤ 2)
include hh hP hx he1 hQ hΛ hE hB' hv hB hV X Y
open Lake(Flyer Treaty)
local notation "φ"=>V.pay.st.S
local notation "ζA"=>fun i=>Adventure V X Y P'.L ((ZT) i) ((C*) i) ((N*) i) (α i)
lemma ΡLift :∃ B:I→ℝ, RateLE L' Kη B 0 ∧∀ᶠ i in L', ∃ v: BoxQ (dims V)≃L[ℂ] BoxQ (dims V), v.toContinuousLinearMap=Adventure V X Y P'.L (Stint V (F i).row Ξ) (F i).row.fine (F i).row.coarse (α i) ∧ Treaty (P'.L.val:ℝ) (Reven (κBit V) (Bc i) (Bf i)) (B i) (E:=fun i=> BC (dims V i)) v:=by
        let V':=κBit V; let Q(i):= Reven V' (Bc i) (Bf i); let b:ℝ:=P'.L.val; have he':0<Δfare G P'.L:=mul_pos (Gauge.slopeConstant_pos hs) (Real.log_pos (by exact_mod_cast Nat.lt_of_lt_of_le (by decide:1<3) P'.coarse)); have hr :∀ᶠ i in L',Flyer ((ζA) i) b (Q i):= ΡbFly V X Y (C*) (N*) (ZT) hP he1 hQ (StintCost V Ξ (fun i=>(F i).row) R1 hV hP he1 hv) hE hB P'.coarse (Eventually.of_forall fun i=> StampP (he':=he) V _ _ hB) hx hΛ hB' hh 
        choose! F' hF using fun i hq=>Lake.Flyer.existsB (show Flyer ((ζA) i) b (Q i) from hq);
        have ht:1 ≤ b:=by unfold b;exact_mod_cast P'.L.pos
        let p:=ζA; have hF':RateLE L' Kη p 0:= FortuneW V X Y (C*) (N*) (ZT) hP he1 hQ (StintCost V Ξ (fun i=>(F i).row) R1 hV hP he1 hv) hE
        have he:= (revenueZ V' he' hx hh).mono (fun i hi=>hi.1); have hp : Tendsto Q L' (𝓝 1):=by
             let x(i):= Bc i/Bf i; have hV:Tendsto x L' (𝓝 1):=by
                   have hm:= tendsto_const_nhds.div_atTop (f:=fun _=> Δfare G P'.L) hx; have he: Tendsto (fun i=>1-(Δfare G P'.L)/Bf i) L' (𝓝 1):= by simpa only[sub_zero] using (tendsto_const_nhds (x:=1)).sub hm
                   refine he.congr' ?_; filter_upwards [hx.eventually_gt_atTop 0,hh] with i hi hh; unfold x; field_simp; linarith only [hh]
             have h:= (hV.log one_ne_zero).neg; rw [Real.log_one,neg_zero] at h; have hk: Tendsto (fun i=>Real.exp (V' * -Real.log (x i))) L' (𝓝 1):=by convert! Real.continuous_exp.continuousAt.tendsto.comp (h.const_mul (V':ℝ)) using 1; rw [mul_zero,Real.exp_zero] 
             apply hk.congr'; filter_upwards [hx.eventually_gt_atTop (Δfare G P'.L),hh] with i hi H; unfold Q Reven x; rw[Real.log_div (show Bc i≠0 from ne_of_gt (by linarith only [hi,H])) (he'.trans hi).ne',neg_sub] -- The fixed difference and the lower bound on the fine scale make both scales positive.
        have hz: RateLE L' Kη (fun i=>(F' i).symm.toContinuousLinearMap) 0:= Lake.μTravel (hr.mono (fun i hi=>⟨hF i hi,hi⟩)) hP hF' ht he (RateLE.absBound 2 hP (hp.norm.eventually (ge_mem_nhds (by norm_num : ‖(1:ℝ)‖<2))))
        refine ⟨fun i=>‖p i‖+ ‖(F' i).symm.toContinuousLinearMap‖,hF'.norm.add hz.norm hP,?_ ⟩; filter_upwards [hr,he] with i hi h; let v:=F' i; have hs : v.toContinuousLinearMap=p i:= hF i hi; exact ⟨v,hF i hi,⟨hs.symm ▸ hi.grow, hi.opposes hs, hs.symm ▸ hi.hi,hi.revD hs ht h, le_trans (le_of_eq (congr_arg norm hs)) (le_add_of_nonneg_right (norm_nonneg _)),le_add_of_nonneg_left (norm_nonneg _)⟩⟩
end treaty
end
end MatchZ
end
end YM.OPE.Stroke
