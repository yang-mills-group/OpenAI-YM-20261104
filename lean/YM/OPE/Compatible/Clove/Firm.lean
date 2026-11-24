import YM.OPE.Compatible.Clove.Pan
/-!
# H.Launch supplies.Born.Cumul integrations at Mark. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit.PriceZ
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P:Patch}{R:ChartRatio G}{C:KernelChoices}{p:Clip}
namespace Scape
variable {W:Type}{nρ fρ:W→Side}(U:(x:W)→ Scape K T P (nρ x) (fρ x) i j R) {u m₁ m₂ m₃ w:ℝ}{q:W→ℝ}{s:ℕ}
local notation "Σ(" i ")"=> VC (U i)
local notation "L!"=> solar G d τ

local notation "σ!"=> gDump nρ k
open Pose JetS
local notation "Y!"=> nρ
abbrev calmP (i:W):= (Bor.L ((U i).V) ((U i).E)).hat R
abbrev iBill (i:W)(z:Σ(i)): ℝ:=
    let x:= U i; CostH x.rungS P.odd_side x.tH x.U x.t x.g x.x R (rayS _ x.E G z)
lemma Zap (i:W)(hs:LocalRatio R)(x:Σ(i)):storm' (U i) x= calmP U i x + merry (iBill U i x):=by
     change calmP U i x*flareTok 0 _=_; have h : (calmP U i x).s=1:= Lid.hat_full _ hs x; apply eta
     all_goals simp [h,merry,flareTok,iBill]
     exact add_comm ..
lemma sway (hs:G.Simple)(pW:LocalRatio R)(S:SlopePrice U k u m₁ w): WindZ nρ 0 2 σ! (iBill U):=by
      let f:=max 0 (EonFee k m₁ u w w w (Fintype.card (Slip G P.L))); let a:ℝ:= ↑(Fintype.card (Shade G))*m₁; have hf:0 ≤ f:=le_max_left ..; have ha:0 ≤ a:=mul_nonneg (Nat.cast_nonneg _) S.height; refine ⟨⟨f*a^2,(by positivity),fun i z=>?_⟩,fun i=>?_⟩; swap
      · have ht := sunStorm (U i) pW hs; have hv:= Lid.hat_toll (Bor.L ((U i).V) ((U i).E)) pW; have hq:iBill U i=(fun x=>(storm' (U i) x).seq 2) - fun x=>(calmP U i x).seq 2:= by funext x; rw [Pi.sub_apply,Zap U i pW]; change _=(calmP U i x).h+ iBill U i x-(calmP U i x).h;abel
        rw [hq]; exact (ht 2).sub (hv 2)
      let Y:= U i; let q:= rayS _ ((U i).E) G z; let Z:= Y.power z; obtain ⟨h,h',h''⟩:= S.flight i
      have hp: ((nρ i).val:ℝ)^k * ‖iBill U i z‖ ≤ f * ‖Z‖^2:= by
           apply (feast Y.rungS P.odd_side Y.tH Y.U Y.t Y.ok.1 k m₁ u w w w S.base S.height (S.vent i).dot h' h'' h q).trans; rw [← bounty Y.rungS P.odd_side Y.U Y.t Y.ok.1]; exact mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity)
      unfold care;rw [pow_zero]; convert! gWorry (nρ i) ‖iBill U i z‖ (f*a^2) ((1+‖z‖)^2) 1 k (hp.trans ?_) using 1; · rw [one_mul,one_mul]
      apply le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (le_trans (L_norm U S i z) (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) ha)) 2) hf); unfold a; rw [mul_pow];exact le_of_eq (by ring)
lemma headsOne (ht:LocalRatio R)(i:W)(x:Σ(i)):(storm' (U i) x).s=1:=by
    rw [Zap U i ht]; change (calmP U i x).s+0=1; rw [add_zero]; exact Lid.hat_full _ ht x
lemma FirmCap (pW:LocalRatio R)(hs:G.Simple)(S:SlopePrice U k u m₁ w)(hh: WindT nρ 8 6 1 (calmP U)): WindT nρ 8 6 1 (fun i=> storm' (U i)):=by
    rw [show (fun i=> storm' (U i))= calmP U + fun i x=> merry (iBill U i x) from funext fun i=>funext fun x=>Zap U i pW x]; refine hh.add ?_; intro v; fin_cases v; exact WindZ.zero ..; exact WindZ.zero ..
    exact (sway U hs pW S).gauge (gDuty _ _) (gLow _ _) (by omega) (by omega)
lemma asset_0 (v:W)(x y:Σ(v)→ℝ)(hp:Bond y)(w:ScriptJ (Σ(v)))(hx:w.B)(ht:LocalRatio R) (he:storm' (U v) = fun z=> calmP U v z + merry (y z)) (hw:∀ i,x i= (w i).s):
   let μ:= BootZ (U v); let L:= penon ((Bor.L ((U v).V) ((U v).E))); let A:= L.average μ; let W:= fair μ L
   W (storm' (U v)) w-W (calmP U v) w=merry (A (y*x)-A x*A y):=by
     intro μ L A W; rw [he]; have H:=sparing μ L (calmP U v) w y (fun _=>0) (Lid.hat_toll ((U v).V.L (U v).E) ht) hx hp (Bond.keep 0) (Lid.hat_full _ ht); unfold W; rw [funext hw]; dsimp only at H; rw [singleConst μ L 0,zero_add] at H; rw [show (fun i=> w i+merry 0)= w from funext fun i=> add_zero _] at H; rw [H,add_sub_cancel_left]
end Scape
end YM.OPE.Quit.PriceZ
