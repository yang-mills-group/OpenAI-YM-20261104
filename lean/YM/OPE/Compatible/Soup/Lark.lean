import YM.OPE.Compatible.Soup.Purse
/-!
# Epoch growth. Limited trajectory tape. variance observables without spectral cost loss
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
variable {A:∀ x:I,HillZ (T:=T) S i r d τ (β x) (n x)}{U: Scaffold φ (Counters β) n (Mnd i S A) r}
variable (D:I→ Law (Merchant.Chamber G r))(hs:G.Simple)
open Merchant.SiteL
variable (h:Tendsto β φ atTop)(hD: GaugeD A U D)
open Cinders Jargon Metric
section
variable {D}
variable (A)
noncomputable abbrev Bounty (j:I):= (Stru A j).beta
noncomputable abbrev Barrier (j:I):= (Meta A j).threshold
set_option quotPrecheck false
local notation "ε▷" => et A
include h
lemma hymn :∀ᶠ i in φ, 0<et A i∧ et A i≤1:=by
       let t:= Tango A h; filter_upwards [t.1, ((t.pays (carth h)).tends (by norm_num) (carth h)).eventually (ge_mem_nhds zero_lt_one)] with i hi hx; exact ⟨hi,hx⟩
lemma ηO : ∀ᶠ i in φ,Bounty A i=((et A i)^2)⁻¹∧0<Bounty A i:=by
       filter_upwards [h.eventually_gt_atTop 0] with i hi; have he: 0< Bounty A i:=(half_pos hi).trans_le ((A i).gen.TagQ.beta).1; exact ⟨(βδ he).trans (by rw[← inv_pow]),he⟩
lemma ηP : Wax β φ (Bounty A) 1:=((boothP (Eventually.of_forall fun i=> (A i).gen.TagQ.beta)).Ray h).pays (carth h)
lemma poleV : Wax β φ (et A) (-(1/2)):= (Tango A h).pays (carth h)
lemma poseS {x:I→ℝ} (he:Receipt β φ x): Tendsto (fun i=> et A i*x i) φ (𝓝 0):= (((poleV A h).mul (waitG h he)).tends (by norm_num) (carth h))
lemma haste {x:I→ℝ}(hv:Receipt β φ x): Tendsto (fun i=> et A i/Barrier A i*x i) φ (𝓝 0):=by
       have hz:= (πlag (torν i S A h).Lamp).dot hv; refine (Wickρ.zero hz h).congr' (Eventually.of_forall fun j=>?_ ); change x j*θh (et A j) (Meta A j)= (et A j)/Barrier A j*x j; unfold θh; rw[div_eq_mul_inv,_root_.mul_comm (x j)]
lemma rentGate {x:I→ℝ}(he:Receipt β φ x):∀ᶠ i in φ,(et A i)*(x i)≤ Barrier A i:=by
       filter_upwards [(haste A h he).eventually (ge_mem_nhds zero_lt_one)] with i hi; change _/_*_ ≤ 1 at hi; rw [div_mul_eq_mul_div, div_le_one (Meta A i).threshold_pos] at hi; exact hi
noncomputable abbrev EC (j:I) (x:Bid.Dir G (n j)):=represent (et A j • x)
variable (V:∀ j,Bid.Dir G (n j)) (hp:Lyd A φ V)
open Zeph
omit h
lemma CoatD {N:ChartRatio G} {s c a t:ℝ}(H:Sweep N s c) (j:I) (v:Bid.Dir G (n j)) (ht:‖v‖≤a)(hp:t*a < s)(hg: 0≤ t) (p:Edge (Site (n j))) : G.chord ((represent (t • v)) p) ≤2*t*a:=by
        let w:= t • v (arkE p); rw[arkL, Pi.smul_apply,mul_assoc]; have hx: ‖w‖≤ t*a:= (norm_smul_of_nonneg hg _).trans_le (mul_le_mul_of_nonneg_left ((norm_le_pi_norm v _).trans ht) hg); exact ((H.price _ (mem_ball_zero_iff.mpr (hx.trans_lt hp))).2).trans (mul_le_mul_of_nonneg_left hx zero_le_two)
include h hp
lemma CapeF {N:ChartRatio G} {s c:ℝ}(H:Sweep N s c): ∀ᶠ i in φ, (et A i)*‖V i‖ < s ∧ ∀ p:Edge (Site (n i)),G.chord (EC A i (V i) p)≤2*(et A i)*‖V i‖:=by
       filter_upwards [hymn A h,(poseS A h hp.brim).eventually (gt_mem_nhds H.sizes.1)] with i hi ht; exact ⟨ht, fun p=> CoatD H i (V i) le_rfl ht hi.1.le p⟩
lemma flagFree {N:ChartRatio G} {s c:ℝ}(H:Sweep N s c): ∀ᶠ i in φ, flags (Barrier A i) (EC A i (V i))=∅:=by
       let L:= (YM.OPE.Score.steady (8:ℝ) (carth h)).product hp.brim; filter_upwards [CapeF A h V hp H,rentGate A h L] with i hi ht; apply Finset.eq_empty_iff_forall_notMem.mpr; intro p h; obtain ⟨F,hp,hF⟩:= (RG.flags_spec ..).1 h; have he:= Next.Fluctuations.travel_chord (EC A i (V i)) (square F.2.val.1 F.2.val.2) F.1 _ hi.2; rw [show ((square F.2.val.1 F.2.val.2).length:ℝ)=4 from by simp [square]] at he; exact (not_lt.mpr (he.trans (by change _≤ Barrier A i; linarith only [show ε▷ i*(8*‖V i‖)≤Barrier A i from ht]))) hF -- type defeq
end
end YM.OPE.Owl.HillZ
