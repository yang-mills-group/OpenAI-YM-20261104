import YM.OPE.Compatible.Soup.Metro
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
open Cinders Metric Set Zeph Jargon
open Crown Silt.Phere PertExtension Score Flock Paver -- names
variable {N:ChartRatio G} {s c:ℝ} (H:Sweep N s c) (x:∀ i,Bid.Dir G (n i))(P:Spells.Pad G)(g:ℂ→L[ℝ]ℝ)
noncomputable abbrev TorC(j:I) := TourF P (Meta A j) g (k:=d+6+6) (b:=νsize A j) (t:=feeτ A j) (et A j)
noncomputable abbrev ArtY (j:I) (v:Bid.Dir G (n j)):= Incl 0 P (hNu A j) (Meta A j) (ScoreX A j) g (et A j) (charW 0 v)
-- Adapt μnorm from Compatible.Camo; arbitrary mean-ready spaces, no comparison necessary. Exposes lips.V.B interpolation
variable {t C:ℝ}
section
variable {n':Side}{b:ℕ}
lemma turnTime (x:Bid.Dir G n')(b:ℕ): ‖InLine b (charW 0 x)‖ ≤ ‖x‖:= (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j=> norm_le_pi_norm x ((0:Site n')+wrap n' j.val.1,Merchant.arkE (n:=n') (0,j.val.2)|>.2)
lemma apB (x:Bid.Dir G n')(k:ℕ)(h:‖x‖≤t) (b:ℕ): ‖PlateB k b (charW 0 x)‖ ≤ Mā G k b t:=by
      let u:=charW 0 x; have hh: ‖InLine (4*b) u‖≤ t:= (turnTime x _).trans h; apply (PriceFl ..).trans; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (add_le_add le_rfl hh) _) (by simpa only [Mā,add_zero,one_pow,mul_one] using Māhi G k b le_rfl)
lemma φpay (x:Bid.Dir G n')(h:‖x‖ ≤ t) (b:ℕ): TagN (BFilm b (charW 0 x)) ≤ RedG G b t:=by
       unfold TagN RedG CxT; rw [← add_assoc,← add_assoc]; exact add_le_add (add_le_add (add_le_add le_rfl (apB x 1 h b)) (apB x 2 h b)) (apB x 3 h b)
lemma senseT {E:Type}[NormedAddCommGroup E](p:JetS E) : scope p (TagN p):=by
        intro i; have h:=norm_nonneg p.h; have ht:=norm_nonneg p.l; have hs:=norm_nonneg p.s; fin_cases i
        · change ‖p.s‖ ≤ 1+‖p.s‖+_+_; linarith only[h,ht]
        · change ‖p.l‖≤ TagN p; unfold TagN; linarith only[hs,h]
        change ‖p.h‖≤TagN p; unfold TagN; linarith only[hs,ht]
open Exterior Silt.Phere
lemma clap (x y:Bid.Dir G n')(hx:‖x‖≤t)(hy:‖y‖≤t)(h:1 ≤ t)(k b:ℕ) : ‖PlateB k b (charW 0 x)-PlateB k b (charW 0 y)‖ ≤ Glee k*Mā G k b (3*t)*‖x-y‖:=by
        let f(z:Bid.Dir G n'):=charW 0 z; apply (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg (GleeHi _) (Māhi G k b (by linarith))) (norm_nonneg _))).2; intro i; have ht:‖x-y‖ ≤ 2*t:=(norm_sub_le ..).trans (by linarith); have hr:= Clippy (b:=b) (0:Site n') (flats G n').toContinuousLinearMap k i -- infer. climbsF
        apply Lap2 (f:=fun x=> PlateB k b (f x) i) ?_ y x (t:=2*t) (by linarith) ht fun v hv=> (norm_le_pi_norm _ _).trans (apB v k (hv.trans (by linarith)) _); simp_rw [← climbsF] at hr; change Cloud.anthem k (fun z=> PlateB k b (f ((flats G n').symm (flats G n' z))) i) at hr; simpa only [ContinuousLinearEquiv.symm_apply_apply] using hr -- check defeq
lemma wyr (p q:Bid.Dir G n')(hb:1 ≤ t)(hp:‖p‖ ≤ t)(hq:‖q‖≤ t)(b:ℕ): fuel (BFilm b (charW 0 p)) (BFilm b (charW 0 q)) (DxT G b t*‖p-q‖):=by
       have he(i:ℕ):= clap p q hp hq hb i b; have hh(i:ℕ):0 ≤ Glee i*Mā G i b (3*t)*‖p-q‖:=(norm_nonneg _).trans (he i); intro i;fin_cases i <;>first| (apply (he 1).trans; unfold DxT; linarith only [hh 2,hh 3])|(apply (he 2).trans; unfold DxT; linarith only [hh 1,hh 3]) | (apply (he 3).trans; unfold DxT; linarith only [hh 1,hh 2])
end
local notation "R!"=> TorC A P g
lemma TorPos (j:I): 0 ≤ TorC A P g j:=(GrowE _ (Meta A j) P (ScoreX A j) g (et A j) (νsize A j) 0 (AuthCap A j) (by omega) (hNu A j)).pos
lemma AmpF (j:I)(x:Bid.Dir G (n j))(ht: ‖x‖≤t): scope (ArtY A P g j x) (Jfare (RedG G (νsize A j) t) (TorC A P g j)):=by
       let Q:= GrowE _ _ P (ScoreX A j) g (et A j) (νsize A j) 0 (AuthCap A j) (by omega) (hNu A j); let V:=BFilm (νsize A j) (charW 0 x); exact thickP (W:=V) (t:=RedG G (νsize A j) t) (fun i=> (senseT V i).trans (φpay x ht _)) Q.roll (fun i hi x _=> by simpa only [pow_zero,mul_one] using Q.seats i hi x) Q.pos -- arguments
lemma AmpG (j:I)(x y:Bid.Dir G (n j))(ht:‖x‖≤ t)(hx:‖y‖≤t)(hp:1≤ t): fuel (ArtY A P g j x) (ArtY A P g j y) (Jfair (RedG G (νsize A j) t) (TorC A P g j)*(DxT G (νsize A j) t*‖x-y‖)):=by
       let b:=νsize A j
       let W:=GrowE _ _ P (ScoreX A j) g (et A j) b 0 (AuthCap A j) (by omega) (hNu A j); exact Sun (W:=BFilm b (charW 0 x)) (t:=RedG G b t) (fun i=> (senseT _ i).trans (φpay x ht b)) W.roll (fun i hi x _=> by simpa only [pow_zero,mul_one] using W.seats i hi x) (fun i=> (senseT (BFilm b (charW 0 y)) i).trans (φpay y hx b)) (wyr _ _ hp ht hx b) W.pos
include h
lemma TorFunds: Receipt β φ (TorC A P g):= receiptK (torν i S A h).Lamp G P g (νGrow A h) (ηSal A h) (d+6+6)
end YM.OPE.Owl.HillZ
