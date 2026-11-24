import YM.OPE.Compatible.Clove.Firm
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
structure Rebate (Z C:ℝ) (p:Clip):Prop where
   base : PathL Z (fun i=>(U i).b')
   tops : 0≤C
   mdt (i:W): 0 ≤ (U i).B
   hat(i:W):(U i).B≤ C
   cap(i:W):(U i).y.clip=p
lemma solvent (hs:G.Simple)(hr:LocalRatio R)(hh:Rebate U m₁ m₂ p): WindT nρ 8 6 1 (calmP U):=BootPrice (fun i=> (U i).y) nρ (fun i=> (U i).tH) (fun i=> (U i).E) R hr _ m₂ _ (fun i=> (U i).V) hh.base hh.mdt hh.hat hh.tops hh.cap hs
abbrev iFact (U:Scape K T P n f i j R) := fair U.BootZ (penon ( Bor.L U.V U.E )) U.storm'
lemma WindT.b (p:(i:W)→ScriptJ (Σ(i)))(h:WindT nρ e k q p)(x:W): (p x).B:= ScriptJ.Xbond ((h 0).zon x) ((h 1).zon x) ((h 2).zon x)
lemma ascendW (hs:G.Simple)(hr:LocalRatio R)(S:SlopePrice U k u m₁ w)(X:(i:W)→ScriptJ (Σ(i)))(hX:WindT nρ e s q X)(hp:0 ≤ q)(ht:4 ≤ j):
    let A(i):=iFact (U i) (X i)
    let B(i):= fair (BootZ (U i)) (penon ((U i).V.L ((U i).E))) (calmP U i) (X i)
    Permit nρ (4+(e+8)+4*(s+6)+(4+8+4*6+(4+8+4*6))) (q*σ!) (A-B):=by
       intro A B j'
       let D(i):=(fun v=>(X i v).s)
       let R'(i):=penon ((U i).V.L (U i).E); let μ(i):= BootZ (U i); let f(i):=iBill U i; let L(i):= (R' i).average (μ i); let a(i):= L i (f i); let t(i):= L i (D i); let p'(i):= L i ((f*D) i)
       have hf : WindZ nρ 0 2 σ! f:=sway U hs hr S; have hD: WindZ nρ e s q D:=hX 0; have hv:= gDuty nρ k; have HA(i:W):(A-B) i=merry (p' i-t i*a i):= asset_0 U i _ _ (hf.zon i) _ (WindT.b U X hX i) hr (funext (Zap U i hr)) (fun i=>rfl)
       have hpV: Cash nρ (4+0+4*2) σ! a:= wages _ nρ _ _ (fun i=>(U i).V) _ hf hv ht hs
       have hpT: Cash nρ (4+e+4*s) q t:= wages _ nρ _ _ (fun i=>(U i).V) _ hD hp ht hs
       have hpA:Cash nρ (4+(0+e)+4*(2+s)) (σ!*q) p':= wages _ nρ _ _ (fun i=>(U i).V) _ (hf.mul hD hv) (fun i=>mul_nonneg (hv i) (hp i)) ht hs
       rw [mul_comm σ!] at hpA
       simp_rw [HA]
       fin_cases j'; exact ⟨0,le_refl _,fun i=>le_of_eq (by change ‖(0:ℝ)‖= _; simp)⟩; exact ⟨0,le_rfl, fun i=> le_of_eq (by change ‖(0:ℝ)‖= _; simp)⟩
       have hv:(q*σ!) ≥0:=fun i=> mul_nonneg (hp _) (gDuty nρ k _)
       change Cash _ _ _ (fun i=>p' i- (t*a) i)
       simp_rw[sub_eq_add_neg]; exact gold_plus (costGauge nρ hpA hv le_rfl (by omega)) (costGauge nρ (gold_minus nρ (gold_times hpT hp hpV)) hv le_rfl (by omega))
abbrev Setup (G:Gauge)(d:ℕ):=4+(0+8)+4*((glideZ d+glideZ d)+6)+(4+8+4*6+(4+8+4*6))+(0:ℕ)*Fintype.card G.ColorIndex
lemma SeamBill (hs:G.Simple)(hr:LocalRatio R)(S:SlopePrice U k u m₁ w)(rr:Rebate U m₂ m₃ p)
   (hp':Aware d τ)(h:∀ i,k+44 ≤ τ i)(ht:4 ≤ j)(x y:W→ L!)(a b:(i:W)→Site (nρ i))(Z:ℝ)(hp:∀ i,‖(U i).vault hs hr hp'‖≤ Z)(v:ℝ)(he:2 ≤ v)(hv:∀ i,Settle (a i) (b i) v)
   (Y':∀ i,Bor (even_both (U i).rungS.ratio (U i).tH) (U i).x (U i).b)(V:∀ i,Plot (even_both (U i).rungS.ratio (U i).tH))(W':∀ i,Plot ((U i).tH)):
    let g(i):=let t:=U i; RGram _ (V i) (Y' i) (x i) (y i) (t.rungS.ratio.embed (a i)) (t.rungS.ratio.embed (b i)) R
    let To(p:W→L!)(i):=(U i).upL hs hr hp' (p i)
    let z(i):= let t:= U i; RGram t.tH (W' i) t.V (To x i) (To y i) (a i) (b i) R
    Permit nρ (Setup G d) (passM x*passM y*σ!) (g-z):=by
       intro g To z
       let M(i):=MuseJ U i x y a b
       let N(i):= (isolate (U i).tH (U i).E (To x i).val (To y i).val (a i) (b i))
       let J(i):= iFact (U i) (N i)
       let P:=passM x*passM y; let Q:= P*σ!; let d':=glideZ d; have hy:0≤ passM y:=fun i=>norm_nonneg _; have hx:0≤ passM x:=fun i=> norm_nonneg _; have hP:0≤P:=fun i=> mul_nonneg (hx i) (hy i); have hQ:0≤ Q:=fun i=> mul_nonneg (hP i) (gDuty nρ k i); have hD:WindT nρ 0 (d'+d') Q (M-N):= PaidEcho U S hr hs hp' h x y a b Z hp v he hv; let T:= Setup G d
       have hU: WindT nρ 0 (d'+d') P N:= PriceZ.WindT.prod (Magn U hr hs hp' x a Z hp) (Magn U hr hs hp' y b Z hp) hx
       rw [show g-z=g-J+(J-z) from by abel, Setup,Nat.zero_mul,Nat.add_zero]; apply Permit.add
       · rw [show g-J=fun i=> iFact (U i) ((M-N) i) from ?_]; swap
         · funext i; have hx: g i=iFact (U i) (M i):=chartVal (U i) (x i) (y i) _ _ (Y' i) (V i) hr hs; -- hp supplied??
           simp only [Pi.sub_apply,hx]; rw [show iFact _ (M i)=iFact _ (M i-N i+N i) from congrArg _ (sub_add_cancel ..).symm, show iFact _ _=iFact _ (M i-N i)+iFact (U i) (N i) from Firmly _ _ _ (sunStorm (U i) hr hs) (WindT.b U _ hD i) (WindT.b U _ hU i)]; exact add_sub_cancel_right ..
         exact channelP _ nρ _ _ (fun i=> (U i).V) hD hQ (fun i=>headsOne U hr i) (FirmCap U hr hs S (solvent U hs hr rr)) ht hs
       rw [show z= _ from ?_]
       · exact ascendW U hs hr S N hU hP ht
       let A:= fun i=> fair (BootZ (U i)) (penon ((U i).V.L ((U i).E))) (calmP U i) (N i)
       change z=A; funext i; let V:=(U i); let X:=V.E; unfold z; dsimp only; rw [parade _ _ _ _ _ _ _ X hr]; unfold RGram; exact ((U i).V.L X).cutOut hr _ _ (penon_shape _)
end Scape
end YM.OPE.Quit.PriceZ
