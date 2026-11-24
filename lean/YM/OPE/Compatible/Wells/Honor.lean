import YM.OPE.Compatible.Wells.Prance
/-!
# Marginal plans. True relative density jets, *before* normalization
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.OPE.Owl.HillZ
open Function Filter MeasureTheory Lattice Laurent Wilson Matrix RG Gauge Precision
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ENNReal ContDiff
open Eyrie Push Push.AbsoluteSums Push.Mark Cascade Flume Flume.Page Flume.Script Pilot Finset
open Silt Libra Coin Rill Silt.Float Votive PertExtension Series GaussianScore Radial Next.Foundations
open Merchant Merchant.Aloof Merchant.Sleeve Merchant.SiteL
open Next.Free Next.Scheduling Stroke Spells Lass Lass.Zest Pill CardinalQ
variable {I:Type}{φ:Filter I}{G:Gauge} {K:Sponsor G}{T:Seasons K}
variable {β:I→ℝ}{n:I→Side}{S:Stage}{i j d r k:ℕ}{τ s a B:ℝ}
variable (A:∀ x:I,HillZ (T:=T) S i r d τ (β x) (n x))(U: Scaffold φ (Counters β) n (Mnd i S A) r)
variable (D:I→ Law (Merchant.Chamber G r))(hs:G.Simple)
open Merchant.SiteL
variable (h:Tendsto β φ atTop)(hD: GaugeD A U D)
open Cinders Metric Set Zeph Jargon Crown PertExtension Flock Stranded
variable {N:ChartRatio G} {s c R:ℝ} (H:StackP N s c R)(hN:LocalRatio N)
variable (x:∀ i,Bid.Dir G (n i)) (g:ℂ→L[ℝ]ℝ) (P:Pad G)
open ScriptJ
local notation "TC"=> Merchant.Chamber G r
local notation "X!"=>cEye A U D x
-- deterministic growth: fee combined conditional with unit formal Z
noncomputable abbrev epmt (P:ChartRatio G)(j:I):= propH (ShoreP D) (Tact A U D x P) j
noncomputable abbrev vclay (P:ChartRatio G)(j:I)(y:Merchant.Chamber G r):= (epmt A U D x P j)⁻¹ * Tact A U D x P j y
noncomputable def winterS (N:ChartRatio G)(j:I)(y:Merchant.Chamber G r) := vclay A U D x N j y*ArtY A P g j (liftedM A U D x j y)
section
lemma ep_s (j:I): (epmt A U D x N j).s=1:=by change (∫ _ :TC,(1:ℝ) ∂ShoreP D j)=1; simp
variable {A U D}(hp:Lyd A φ x)
include hp h hs H hN hD
lemma sends : Cinders.Feast (fun i=> (epmt A U D x N i)⁻¹) φ (Counters β):=revD (props (d:=et A) (Kpeak hs h hD H hN x hp) (carth h) ((poleV A h).mono (by norm_num))).1 (carth h) (Eventually.of_forall fun i=> ep_s (N:=N) A U D x i)
local notation "pGA"=> Butte (ShoreP D) φ (Counters β)
lemma GPin : pGA (vclay A U D x N):=by
       let b:= sends hs h hD H hN x hp; let T:(i:I)→TC→Token:=fun i _=>(epmt A U D x N i)⁻¹; have he:pGA T:=by intro i; fin_cases i; exact Grain.const b.1; exact Grain.const b.2.1; exact Grain.const b.2.2
       exact gluing he (Kpeak hs h hD H hN x hp) (carth h)
lemma εPin : pGA (winterS A U D x g P N):= gluing (GPin hs h hD H hN x hp) (noteG hs h hD x g P hp) (carth h)
omit hp h hs H hN hD
variable {E:Type}[MeasurableSpace E]
private lemma ξProm (μ:Measure E)(p:E→Token)(h1:Integrable (fun x=>(p x).s) μ)(h2:Integrable (fun x=>(p x).l) μ)(h3:Integrable (fun x=>(p x).h) μ)(t:Token):
        propH (I:=Unit) (fun _=>μ) (fun _ x=>t*p x) ()= t*propH (I:=Unit) (fun _=>μ) (fun _=>p) () :=by
           unfold propH; simp only [JetS.ml_s,JetS.ml_l,JetS.ml_h]; apply JetS.eta; exact integral_const_mul ..; exact (integral_add (h2.const_mul _) (h1.const_mul _)).trans (congr_arg₂ HAdd.hAdd (integral_const_mul ..) (integral_const_mul ..)); exact (integral_add (show Integrable (fun x=> t.s*(p x).h+t.l*(p x).l) μ from (h3.const_mul _).add (h2.const_mul _)) (h1.const_mul _)).trans (congr_arg₂ HAdd.hAdd ((integral_add (h3.const_mul _) (h2.const_mul _)).trans (congr_arg₂ HAdd.hAdd (integral_const_mul ..) (integral_const_mul ..))) (integral_const_mul ..))
include hp h hs H hN hD
lemma PeakPin : Wax β φ (fun i=> ∫ y, (winterS A U D x g P N i y).atK (et A i) ∂ShoreP D i) Deb:=by
        let p:=winterS A U D x g P N; let W:=Glaco A U D N P x g; let c(i):= (epmt A U D x N i)⁻¹; have he:p=fun i y=> c i * W i y:=funext fun i=>funext fun y=>by unfold p winterS vclay W Glaco c; ring
        let g:=carth h; let e:=poleV A h; have ht:=e.mono (show _ ≤ 0 by norm_num); let a:=ShoreP D; have hY:pGA p:=εPin hs h hD H hN x _ P hp; have h₀:pGA W:=greetK hs h hD H hN x _ P hp; obtain ⟨V,V',V₀⟩:=props hY g ht; obtain ⟨R',hr,hv⟩:=props h₀ g ht; let v:=propH a p; let z:=propH a W; let t:=et A; let rho(i):=(z i).atK (t i); have hh: Wax β φ rho Deb:= (decipher hs h hD H hN x _ P hp).congr hv
        have hx :=sends hs h hD H hN x hp
        apply ((((lampFee hx g ht).mul hh).mono (by simp)).sub ((shiftP hx R' e (by norm_num) g).mono (by unfold Deb;norm_num)) g).congr
        filter_upwards [V₀, (h₀ 0).integral.1,(h₀ 1).integral.1,(h₀ 2).integral.1] with j hj hg hK hW; have hz:v j=c j*z j:=(by unfold v; rw [he]; exact ξProm _ (W j) hg hK hW _); change (c j).atK _* (rho j)- ((c j).atK _*(z j).atK (t j)-(c j*z j).atK (t j))=∫ y, aftD p t j y ∂a j; rw [hj,← hz]; exact sub_sub_cancel ..
end
end YM.OPE.Owl.HillZ
