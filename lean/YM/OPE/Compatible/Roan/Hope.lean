import YM.OPE.Compatible.Roan.Crimp
/-! # Pressures within cluster, uniformly attenuated for exterior registers. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis.Galea
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius ENNReal
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type*} {i k m n:ℕ}{t C s u z ℓ v a c e r R β:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown
variable {K:Sponsor G}{T:Seasons K}
open Lav
section
variable {L:Host K T} {q:Sender L} (p:Site L.f) {Y:Studio L}{w:Bid.Dir G L.c}
set_option quotPrecheck false
local notation "Fθ"=> L.ForestQ
local notation "W!"=> worldA L w
local notation "η!"=> Gov s u
local notation "ζ!"=> burst (Gov s u) ℓ
variable {N:ChartRatio G}(hN:LocalRatio N)(H:StackP N r R β)
variable (h:L.Rich s c e v u C)(ht:0<s)(hc:0≤c)(he:0<e)(hβ:0≤v)(hv: Scale Y t)(hw:‖w‖≤ t)(hA: ReserveQ L p Y w ℓ) {X:Seats L.ForestQ}(hx:(X.card:ℝ)≤ z)(hX:Training L p X ℓ)(hp:Funded L X q a k)(hr:0≤ ℓ)
noncomputable abbrev wallet3 (G:Gauge)(k:ℕ)(s c v u C t z a β:ℝ):= ‖Λ_B G k s c u C t z a 1‖+(‖price2 G k 4 s c u C t z a c‖+‖price2 G k 2 s c u C t z a (v+4*β)‖)+‖price2 G k 3 s c u C t z a c‖+‖price3 G k 3 3 s c u C t z a c c‖
private lemma Dadd {x x' y y' a b:ℝ}(h:‖x-x'‖≤ a)(he:‖y-y'‖≤ b): ‖(x+y)-(x'+y')‖≤ a+b:=by rw [show x+y-(x'+y')=x-x'+(y-y') from by ring]; exact (norm_add_le ..).trans (add_le_add h he)
include hN H h ht hc he hβ hv hw hA hx hX hp hr
local notation "Λφ"=> Λ_B G k s c u C t z a
lemma refunds (i:Phase):
       ‖(MuseY L q N Y).seq i.val-(MuseY L q N W!).seq i.val‖ ≤ wallet3 G k s c v u C t z a β * ζ! :=by
              let b(i:Phase):= Spex L Y q i; let b'(i:Phase):= Spex L W! q i; let k':= (v+4*β); let P:= ‖price2 G k 2 s c u C t z a k'‖; let Q:= ‖price2 G k 3 s c u C t z a c‖; let T:= ‖price2 G k 4 s c u C t z a c‖; let W:= ‖price3 G k 3 3 s c u C t z a c c‖; let Z := burst (Gov s u) ℓ; have He := BitsG L Y hN H h he ht hc hβ q X hp; have Ht:= BitsG L W! hN H h he ht hc hβ q X hp; obtain ⟨hl,hU⟩:= leafE L h he hc; have hf:=taper L hN H h he hβ
              let A:= ‖Λφ 1‖
              have hz'(i:Rubric G X): Rebound L Y w ℓ (Sum.inr (shout G X i)):= hides L p Y w hA hr _ (le_trans (hX (shout G X i) i.1.property) (by linarith only[hr])); have hZ:0≤Z:=Real.exp_nonneg _; have hg (i:Phase): ‖a_ Y.μφ (b i)-a_ (W!).μφ (b' i)‖≤ A*Z:=by
                    apply (Wonk i h ht hc he hv hx hp hw hz').trans; have hu :oer u ℓ ≤ Z:=Real.exp_monotone (show -(u/2*ℓ) ≤ -(Gov s u)*ℓ from (neg_le_neg (mul_le_mul_of_nonneg_right (show Gov s u≤u/2 from (by have he:=Gov_price ht h.vein.warmth; linarith only[he.2.2,he.1])) hr)).trans_eq (by ring)); exact mul_le_mul (Real.le_norm_self _) hu (Real.exp_nonneg _) (norm_nonneg _)
              have hh(i:Phase): ‖Push2 L q Y i (Rate3 L)-Push2 L q W! i (Rate3 L)‖≤ Q*Z:=(StemV p i h ht hc he hv hw hA hx hX hp hr hl).trans (mul_le_mul_of_nonneg_right (Real.le_norm_self _) hZ);
              change _ ≤ (A+(T+P)+Q+W)*Z; have hV:0 ≤T:= norm_nonneg _; have hp':0 ≤P:=norm_nonneg _; have ht':0 ≤Q:= norm_nonneg _; have hW:0 ≤W:=norm_nonneg _; have hY:A+Q≤ A+(T+P)+Q+W:=by linarith only [hp',hV,hW]
              rw [He,Ht]; fin_cases i
              · apply (hg 0).trans; exact mul_le_mul_of_nonneg_right ((le_add_of_nonneg_right ht').trans hY) hZ
              · apply (Dadd (hg 1) (hh 0)).trans; exact (add_mul A Q Z|>.symm.trans_le (mul_le_mul_of_nonneg_right hY hZ))
              let t:= StemV p 0 h ht hc he hv hw hA hx hX hp hr hf; let B:= StemV p 0 h ht hc he hv hw hA hx hX hp hr hU; have hΦ:=StemW p 0 h ht hc he hv hw hA hx hX hp hr hl hl; let V:= Push3 L q Y 0 (Rate3 L) (Rate3 L); let σ:= Push3 L q W! 0 (Rate3 L) (Rate3 L); have hf: ‖(2:ℝ)⁻¹ * V-2⁻¹*σ‖ ≤ W*Z:=by rw [←mul_sub,norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) (by norm_num)).trans (hΦ.trans (mul_le_mul_of_nonneg_right (Real.le_norm_self _) hZ));
              have ht : ‖Push2 L q Y 0 (χ4 L)-Push2 L q W! 0 (χ4 L)‖ ≤ T*Z:= B.trans (mul_le_mul_of_nonneg_right (Real.le_norm_self _) hZ); exact (Dadd (Dadd (Dadd (hg 2) (Dadd ht (t.trans (mul_le_mul_of_nonneg_right (Real.le_norm_self _) hZ)))) (hh 1)) hf).trans_eq (by ring)
end
end YM.OPE.Borealis.Galea
