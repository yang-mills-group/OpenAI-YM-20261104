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
variable (h:Tendsto β φ atTop)(hD: GaugeD A U D) (A U)
open Cinders Metric Set Zeph Jargon
variable {N:ChartRatio G} {s c R:ℝ} (H:StackP N s c R)(hN:LocalRatio N)
variable (x:∀ i,Bid.Dir G (n i)) (g:ℂ→L[ℝ]ℝ)
local notation "K!"=> Merchant.Chamber G r
noncomputable abbrev cEye (i:I):= mixT A U D i (x i)
noncomputable abbrev liftedM (i:I)(p:Merchant.Chamber G r):= Yfar A U (cEye A U D x) i p
--raw
noncomputable def Tresp (N:ChartRatio G)(i:I)(p:Merchant.Chamber G r):=feeX N (et A i •(p +PinT G (cEye A U D x i))) + (D i).P p p/2 + PriceΩ A i (EC A i (liftedM A U D x i p))- reb A (cEye A U D x) i
noncomputable abbrev TJar (i:I)(p:Merchant.Chamber G r):=(PolV A i (liftedM A U D x i p)).l-(PolV A i (cEye A U D x i)).l
noncomputable abbrev TJjr (N:ChartRatio G)(i:I)(p:Merchant.Chamber G r):=(PolV A i (liftedM A U D x i p)).h-(PolV A i (cEye A U D x i)).h+ jet (feeX N) 2 (p+PinT G (cEye A U D x i))
noncomputable def Tact (N:ChartRatio G)(i:I)(p: Merchant.Chamber G r):Token:= ⟨1,TJar A U D x i p,TJjr A U D x N i p+(TJar A U D x i p)^2/2⟩
private lemma LBound {n:Side} (W: Merchant.Chamber G r→L[ℝ] Bid.Dir G n)(f:Bid.Dir G n→ℝ)(P: Law (Merchant.Chamber G r))(x:Bid.Dir G n)(hP: SiteL W (chrom f) P) (p:Merchant.Chamber G r) : let K:=mate W (chrom f) P x; -jet f 2 (K+ W p)-(-jet f 2 K)= -P.P p p/2:=by
       intro K; have h:= SiteL.reduce W (chrom f) P hP x p; rw [chrom2,chrom2] at h; change 2*jet f _ (K+W p)=2*(jet f 2 K)+P.P p p at h; linarith only[h]
include hD in
lemma sourZ (j:I)(p:Merchant.Chamber G r) : (PolV A j (liftedM A U D x j p)).s - (PolV A j (cEye A U D x j)).s= -(D j).P p p /2 :=by
  have rule:=hD.obey j
  have paid:=LBound (n:=n j) (G:=G) (r:=r) (Stair A U j) (KPole A j)
    (D j) (x j) (by match_account_types rule) p
  dsimp only [PolV,liftedM,Yfar,cEye,mixT]
  match_account_types paid
lemma ΘLaw (i:I)(p:Merchant.Chamber G r)(ht:flags (Barrier A i) (EC A i (liftedM A U D x i p))=∅): ConV A U D (cEye A U D x) g N i p= g (signalF A i (EC A i (liftedM A U D x i p)))*Real.exp (Tresp A U D x N i p):=by
       let z:= EC A i (liftedM A U D x i p); let S:=PriceΩ A i z; let C:=cEye A U D x; let F:= reb A C i
       unfold ConV Bo; rw [chatE A U,φ_s A _ (EC A i (liftedM A U D x i p)) ht, ← Complex.real_smul, map_smul]; let K:=feeX N ((et A i) • (p+Odds C i)) +(D i).P p p / 2; let y:= g (signalF A i z); change Real.exp S * y / Real.exp F * Real.exp K= y*Real.exp (K+S-F); rw[Real.exp_sub,Real.exp_add K S]; ring
variable {A U D}
include h hD hs
variable (y:I→ Merchant.Chamber G r)(hp:Lyd A φ x)(hv:Receipt β φ y)
include hp
lemma Lyn : Lyd A φ (cEye A U D x):= hp.pinned hs h hD
include hv
lemma Lynx : Lyd A φ (fun i=> liftedM A U D x i (y i)):= Lyd.both A (Lyn hs h hD x hp) (stanza A U y hv) h
-- phase coefficients rates and exponential conversion
omit hD hp hv in lemma rope_φ (W:∀ i,Bid.Dir G (n i))(he:Lyd A φ W): Wax β φ (fun j=>(PolV A j (W j)).l) 0∧ Wax β φ (fun j=>(PolV A j (W j)).h) 0:=by
       let f(k:ℕ)(j:I):= jet (KPole A j) k (W j); let g(k:ℕ)(j:I):=jet (LPole A j) k (W j); have h(k:ℕ)(hk:1 ≤ k)(hx:k≤ 2): Wax β φ (fun j=> -f (k+2) j-g k j) 0:= ((waitG h (appeals hs h he (k:=k+2) (by omega) (by omega))).neg).sub (gloss hs h he hk (by omega)) (carth h); exact ⟨h 1 (by omega) (by omega), h 2 (by omega) (by omega)⟩
noncomputable abbrev gazeP (i:I):= y i+ Odds (r:=r) (cEye A U D x) i
lemma ferr: Receipt β φ (fun i=>‖gazeP (A:=A) (U:=U) (D:=D) x y i‖):=by
       let Y:=Odds (r:=r) (cEye A U D x); have he:=OddsFee A _ (Lyn hs h hD x hp); let τ(i):= gazeP (A:=A) (U:=U) (D:=D) x y i; have hx:Receipt β φ τ:= hv.plus he (carth h); exact hx.liftp (Eventually.of_forall fun i=> (norm_norm (τ i)).le)
include H hN
lemma feel : Wax β φ (fun i=> jet (feeX N) 2 (gazeP (A:=A) (U:=U) (D:=D) x y i)) 0:=by
       have he:= waitG h (ferr hs h hD x y hp hv); let b(c:ℝ):=RateLE.const c (carth h); apply RateLE.of_norm_le (((b (Fintype.card (fieldP r))).mul ((b R).mul (he.pow 2 (carth h)))).mono (by norm_num)); filter_upwards with i; exact feeCapital hN H (gazeP (A:=A) (U:=U) (D:=D) x y i) (by decide)
lemma plightJ : Wax β φ (fun i=>TJar A U D x i (y i)) 0∧ Wax β φ (fun i=>TJjr A U D x N i (y i)) 0:=by
        have hx:= rope_φ hs h (cEye A U D x) (Lyn hs h hD x hp); have hy:= rope_φ hs h _ (Lynx hs h hD x y hp hv); let b:=carth h; exact ⟨hy.1.sub hx.1 b, (hy.2.sub hx.2 b).add (feel hs h hD H hN x y hp hv) b⟩
lemma taxT : Wax β φ (fun i=> feeX N ((et A i) • (gazeP (A:=A) (U:=U) (D:=D) x y i))-(et A i)^2*jet (feeX N) 2 (gazeP (A:=A) (U:=U) (D:=D) x y i)) (-(3/2)):=by
       let p(i):=‖gazeP (A:=A) (U:=U) (D:=D) x y i‖; have hx:=ferr hs h hD x y hp hv; let b(c:ℝ):=RateLE.const c (carth h); let s:=(↑(Fintype.card (fieldP r)):ℝ) 
       apply RateLE.of_norm_le (((b s).mul ((((b R).mul ((waitG h hx).pow 3 (carth h))).mul ((poleV A h).pow 3 (carth h))))).mono (by norm_num)); filter_upwards [hymn A h, (poseS A h hx).eventually (gt_mem_nhds H.sweep.sizes.1)] with i hi hp; exact feeTime hN H _ hi.1 (mem_ball_zero_iff.mpr ((norm_smul_of_nonneg hi.1.le _).trans_lt hp)) le_rfl
lemma tribut : Wax β φ (fun i=> Tresp A U D x N i (y i)- (et A i*TJar A U D x i (y i)+(et A i)^2*TJjr A U D x N i (y i))) Deb:=by
        let V:= pricePol hs h (Lyn hs h hD x hp) H.sweep; have he:=pricePol hs h (Lynx hs h hD x y hp hv) H.sweep; apply RateLE.congr ((he.sub V (carth h)).add ((taxT hs h hD H hN x y hp hv).mono (by norm_num [Deb])) (carth h)); filter_upwards with i
        let U':= liftedM A U D x i (y i); let p:= PolV A i U'; let q:= PolV A i (cEye A U D x i); let y':=(D i).P (y i) (y i); let E':= EC A i U'; have hz : p.s-q.s=-y'/2:= sourZ A U D hD x i (y i); let t:=et A i; let j:= jet (feeX N) 2 (gazeP (A:=A) (U:=U) (D:=D) x y i); let ν:=feeX N (t • (gazeP (A:=A) (U:=U) (D:=D) x y i)); change ((PriceΩ A i E'-_-p.atK t)-(reb A _ i-_-q.atK t))+ (ν-t^2*j)= (ν+y'/2+PriceΩ A i E'-reb A _ i)-(t*(p.l-q.l)+t^2*(p.h-q.h+j)); simp only [JetS.atK,smul_eq_mul]; linarith only [hz]
end YM.OPE.Owl.HillZ
