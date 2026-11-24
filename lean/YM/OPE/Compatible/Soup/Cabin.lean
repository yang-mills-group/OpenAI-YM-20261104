import YM.OPE.Compatible.Soup.Mint
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
variable (h:Tendsto β φ atTop) (A U)
open Source Labels Metric Cinders Zeph
set_option quotPrecheck false
variable (g:ℂ→L[ℝ]ℝ) (x:∀ j, Bid.Dir G (n j))
local notation "FW!"=> Merchant.Chamber G r
noncomputable def reb (j:I):= PriceΩ A j (EC A j (x j))
noncomputable def Bo (j:I)(p:Palace G r):ℝ:= g (ωZ A j (install (Punched A U j) (EC A j (x j)) p)) / Real.exp (reb A x j)
private lemma ibo (j:I):Integrable (Bo A U g x j) (Duo G r):= (show Continuous (Bo A U g x j) from (g.continuous.comp ((A j).realm.comp (monoInst ..))).div_const _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
include h
private lemma wickδ :Wick β φ (fun i=> Owl.δerror (β i)):=by
       intro s a ha; let C:= Counters β; filter_upwards [((turns h).pow 2 (carth h) (1/2:ℝ) (by norm_num)),h.eventually_gt_atTop 1,(carth h).eventually_ge_atTop (-a)] with i hi hv hν; rw [Real.norm_of_nonneg (Real.exp_nonneg _)]; apply Real.exp_monotone; have hz: 0 < C i:= Real.log_pos hv; change ‖C i^2‖≤ Real.exp (1/2*C i) at hi; have he : C i^2 ≤ β i:= (Real.le_norm_self _).trans (hi.trans ((Real.exp_monotone (show 1/2*C i ≤ C i from by linarith only[hz])).trans (le_of_eq (Real.exp_log (by linarith only [hv]))))); linarith only [he,hν,mul_le_mul_of_nonneg_right hν hz.le]
lemma grant_B : Wick β φ (fun i=> ∫ b,Bo A U g x i b ∂Duo G r):=by
        intro a; let X:= Counters β; have hp:= (RateLE.const ‖g‖ (carth h)).mul (wickδ h a); apply RateLE.of_norm_le (hp.mono (by simp)); filter_upwards with i
        let V:=EC A i (x i); let F:= reb A x i; let y:= Real.exp F; let v:=innC (Punched A U i) (ωZ A i) V; have he : ‖v‖ ≤ y*δerror (β i) := punt (Punched A U i) _ (A i).realm (fish A i) (y*δerror (β i)) (fun p hp he=>(A i).outlook V p hp he) V
        have hh: (∫ b,Bo A U g x i b ∂Duo G r)=g v/y:=by unfold Bo; erw [integral_div]; congr 1; apply g.integral_comp_comm; exact ((A i).realm.comp (monoInst (Punched A U i) V)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
        rw [hh,norm_div,Real.norm_of_nonneg (Real.exp_nonneg _),div_le_iff₀ (Real.exp_pos F)]; exact (g.le_opNorm _).trans ((mul_le_mul_of_nonneg_left he (norm_nonneg g)).trans_eq (by simp only[← mul_assoc];ring))
open Set
noncomputable abbrev storm (P:I→ℝ)(i:I):= Zeph.Chamber G (fieldP r) (et A i*P i)
structure Village (P:I→ℝ):Prop where
       hue : Receipt β φ P
       debt : ∀ᶠ i in φ,∀ z:Palace G r,z∉ storm A P i → PriceΩ A i (install (Punched A U i) (EC A i (x i)) z)-reb A x i ≤ - ‖(Counters β i)^2‖
section
variable {A U g x}
-- area output after selecting V.C. Needs lower bound only.Era truncate
lemma VillRise {P:I→ℝ}(W:Village A U x P) (P':I→ℝ)(h':Receipt β φ P')(he:∀ᶠ i in φ,P i ≤ P' i): Village A U x P':=by
       refine ⟨h',?_⟩; filter_upwards [hymn A h, W.debt,he] with i hi hp hB x hx; exact hp x (fun he=>hx (fun j=> (he j).trans (mul_le_mul_of_nonneg_left hB hi.1.le)))
-- P ≥ dynamic offers too. produces representative.
include hs
variable (x U)
lemma villageG {N:ChartRatio G}{b:ℝ}(H:Sweep N s b)(Q:I→ℝ)(hQ:Receipt β φ Q)(hp:Lyd A φ x):∃ v:I→ℝ,Village A U x v∧ ∀ i,Q i ≤ v i:=by
       obtain ⟨P,hP,Hh⟩:= biasQ hs h H x _ U hp ((sans h).power 2 (carth h)); let p(i):=max (P i) (Q i); have hu:Village A U x P:=⟨hP,Hh.mono fun _ hi=>hi.2⟩; exact ⟨p, VillRise h hu p (hP.maxS hQ (carth h)) (Eventually.of_forall fun _=>le_max_left ..),fun i=> le_max_right ..⟩ -- order params
omit hs
variable {x U} (g) {P:I→ℝ} (V:Village A U x P)
include V
lemma BadW : Wick β φ (fun i=>∫ y in (storm A P i)ᶜ,Bo A U g x i y ∂Duo G r):=by
       obtain ⟨c,hc,H⟩:= healthyMint A h; intro a; let z:=Burl 1 (Counters β); have ht(i):z i=Real.exp (-‖Counters β i^2‖):=by unfold z Burl; rw [Real.norm_of_nonneg (sq_nonneg _),neg_one_mul]
       have he:Wax β φ z a:= Wick_bill h zero_lt_one a; have hp:=((he.mul (waitG h hc).norm).mul (RateLE.const ‖g‖ (carth h))).mono (le_of_eq (by ring: a+0+0=a)); refine RateLE.of_norm_le hp ?_; filter_upwards [V.debt,H] with i hi hh; let K:=z i*‖c i‖*‖g‖; let ν:= Duo G r; have hk:0 ≤ K:=mul_nonneg (mul_nonneg (Real.exp_nonneg _) (norm_nonneg _)) (norm_nonneg _); refine le_trans (norm_setIntegral_le_of_norm_le_const (C:=K) (measure_lt_top ..) ?_) (mul_le_of_le_one_right hk (le_trans (measureReal_mono (Set.subset_univ _) (measure_ne_top _ _)) (le_of_eq (probReal_univ)))); intro v hv
       let u:=install (Punched A U i) (EC A i (x i)) v; let f:=PriceΩ A i u; let p:= reb A x i; have hz:f-p ≤ - ‖Counters β i^2‖:= hi v hv; have hb : Real.exp f ≤ z i * Real.exp p:=by rw[ht,← Real.exp_add]; exact Real.exp_monotone (by linarith)
       let Y:=ωZ A i; unfold Bo; rw [norm_div,Real.norm_of_nonneg (Real.exp_nonneg _),div_le_iff₀ (Real.exp_pos _)]; calc
          _ ≤ ‖g‖*(Real.exp f * ‖c i‖):=(g.le_opNorm _).trans (mul_le_mul_of_nonneg_left ((hh u).trans (mul_le_mul_of_nonneg_left (Real.le_norm_self _) (Real.exp_nonneg f))) (norm_nonneg _))
          _ ≤ ‖g‖*(z i*Real.exp p* ‖c i‖):= mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb (norm_nonneg _)) (norm_nonneg _)
          _ = _ :=by unfold K p;ring
lemma sparkW : Wick β φ (fun i=> ∫ y in (storm A P i),Bo A U g x i y ∂Duo G r):=by
       intro a; refine ((grant_B A U h g x a).sub (BadW h g V a) (carth h)).congr ?_; filter_upwards with i; rw [← integral_add_compl chamberMeas (ibo A U g x i),add_sub_cancel_right] -- h binder
end
end YM.OPE.Owl.HillZ
