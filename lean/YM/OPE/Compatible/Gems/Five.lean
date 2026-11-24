import YM.OPE.Compatible.Gems.Mine
/-! # Root and mon nearby assets. Seismic periods. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis.Galea
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type*} {i k m:ℕ}{t C s u z ℓ v a c e r R:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown
variable {K:Sponsor G}{T:Seasons K}
section
variable {L:Host K T} {Y:Studio L} {w: Bid.Dir G L.c}
set_option quotPrecheck false
local notation "Fθ"=> L.ForestQ
local notation "L!"=> majr L
local notation "W!"=> worldA L w
variable (h:L.Rich s c e v u C)(ht:0<s)(hc:0≤c)(he:0<e)(hv:Scale Y t)(hw:‖w‖≤ t)
noncomputable abbrev Tz (v t C:price)(a:ℝ)(k:ℕ) := JumpP (‖a‖ • hikeP (J1+(J1+(v+ t))) k) C
include h ht hc he hv hw
variable (X:Seats L.ForestQ)(hx:(X.card:ℝ)≤ z)(hq:∀ i:Rubric G X, Rebound L Y w ℓ (Sum.inr (shout G X i)))
omit h ht hc he hv in lemma grantW : Scale (worldA L w) t:=⟨hw,norm_zero.trans_le ((norm_nonneg _).trans hw)⟩
omit h ht hc he hv hw
private lemma leap (A V:price)(a:ℝ): JumpP A (a • V) = a • JumpP A V:=by funext i; simp only [JumpP,Pi.smul_apply,smul_eq_mul]; ring
include h ht hc he hv hw
local notation "R!"=>hueCost (FWind G s c u C t) z G
local notation "Z!"=> hueCost (Cσ G s c u C t) z G
local notation "ε_"=>oer u ℓ
include hq hx
lemma Plucked (q:Sender L) (hp:Funded L X q a k)(i: Phase):
        Cane L! ((yQ L Y (fun x=>(q (Vtone L Y x)).seq i.val))-(yQ L W! (fun x=>(q (Vtone L W! x)).seq i.val))) (ε_ • Tz R! R! Z! a k):=by
           obtain ⟨p,hp,hΨ⟩:=hp.net; let f:= Zσ L Y X; let g:= Zσ L W! X; let S(x):=(1:ℝ)+(‖f x‖+‖g x‖); let W(x):=a*(1+S x)^k; let D(x):= ‖f x-g x‖; let Q(x):= (p (f x)).seq i.val-(p (g x)).seq i.val; have he': 0 ≤a:=hp.pos; have hx':Cane L! S (J1+(R!+R!)):= (Cane.constant (μ:=majr L) 1 (show ‖(1:ℝ)‖≤1 by norm_num)).add ((ZBill h ht hc he hv _ hx).add (ZBill h ht hc he (grantW hw) _ hx)); have hw' : Cane L! W (‖a‖ • hikeP (J1+(J1+(R!+R!))) k):= (powerQ ((Cane.constant (μ:=majr L) 1 (show ‖(1:ℝ)‖≤1 by norm_num)).add hx') k).scal a; have hk(x):‖Q x‖≤ W x*D x:=by
                have hvx: 1 ≤ S x:=le_add_of_nonneg_right (add_nonneg (norm_nonneg _) (norm_nonneg _)); exact hp.Ease hvx (f x) (g x) ((le_add_of_nonneg_right (norm_nonneg _)).trans (le_add_of_nonneg_left zero_le_one)) ((le_add_of_nonneg_left (norm_nonneg _)).trans (le_add_of_nonneg_left zero_le_one)) _
           have hZ : Cane L! D (ε_ • Z!):=Zclose h ht hc he hv hw X hx hq; rw [hΨ]; change Cane L! Q _; apply (of_K (hw'.mul hZ) _ (fun i=>(hk i).trans (Real.le_norm_self _))).grow; · intro i hi; rw [leap]
           exact (((hp.spikes i).comp (ύT L Y X)).sub ((hp.spikes i).comp (ύT L W! X))).aestronglyMeasurable
omit hx hq
abbrev Bird (p:RodZ L k)(Y:Studio L):= yQ L Y (Gale L Y p)
lemma Bridge (p:RodZ L k)(hp:∀ i,Rebound L Y w ℓ (p i)): Cane L! (Bird p Y-Bird p W!) (ε_ • reelP (FWind G s c u C t) (Cσ G s c u C t) k) :=by
        have he'(v:Studio L) : Bird p v= ∏ i:Fin k,TagK L v (p i):=by funext i; unfold Bird Gale yQ TagK; simp only[Finset.prod_apply, Function.comp_apply]
        let A:= (Finset.univ : Finset (Fin k)); have hx': A.card=k:=by simp [A]
        have hT(B:Studio L)(i:Fin k)(hz:Scale B t): Cane L! (TagK L B (p i)) (FWind G s c u C t):=y_cost L B (TinV h ht hc he hz _); have hz:= craftP A _ _ (fun i _=>hT Y i hv) (fun i _=>hT W! i (grantW hw)) (fun i _=> PulseR h ht hc he hv hw (p i) (hp i)); rw [hx',re_s] at hz; rw [he',he']; exact hz
end
end YM.OPE.Borealis.Galea
