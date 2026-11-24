import YM.OPE.Compatible.Soup.Mask
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
variable (h:Tendsto β φ atTop)
open Cinders Jargon Metric YM.PhysicalNext.Repeat.Aroma
section
private lemma truant {w:I→ℝ} (he:Tendsto β φ atTop)(hp:Wax β φ w s)(hs:s<0): Receipt β φ w:= YM.OPE.Score.bound 1 (carth he) (((hp.tends hs (carth he)).norm).eventually (ge_mem_nhds (by simp)))
include h
variable (A U)
noncomputable abbrev loopsΩ (j:I):= Shoal (WorkB A j)*PathData.loopsPrice (Meta A j) (Bounty A j) S.paths (DialK A j)
lemma scoreLoop :Receipt β φ (loopsΩ A):=by
        let P:= Barrier A; have hp:Wax β φ P (-(1/2)):=by rw[←neg_div]; exact (boltP (torν i S A h).Lamp).pays (carth h)
        let B(c:ℝ):=RateLE.const c (carth h); have ht(k:ℕ): Wax β φ (fun i=>S.paths*P i^k) (0+(k:ℝ)*(-(1/2))) := (B S.paths).mul (hp.pow k (carth h)); let z:= (ηP A h).mul ((ht 3).add ((ht 4).mono (by norm_num)) (carth h)); let v:= (mUses A h).mul (hp.pow 2 (carth h)); have he:= z.add (v.mono (by norm_num)) (carth h); apply YM.OPE.Score.product _ (truant h he (by norm_num)); let x:= fun (i:I)=>(WorkB A i+2); let q:=(MintW A h).plus (YM.OPE.Score.steady (2:ℝ) (carth h)) (carth h); apply ((q.plus q (carth h)).plus (YM.OPE.Score.steady (1:ℝ) (carth h)) (carth h)).power 4 (carth h)|>.congr; filter_upwards with j; unfold Shoal; push_cast;rfl
variable {A} {c a:ℝ} {X:∀ i,Bid.Dir G (n i)} (hp:Lyd A φ X) {N:ChartRatio G}
open Zeph
include hs hp
lemma roast (H:Sweep N s a): Receipt β φ (fun i=>CoinΩ A i (EC A i (X i))):=by
        let V:= fun i=> CoinΩ A i (EC A i (X i)); let p(j:I):=PolV A j (X j); let f(i:I):=(p i).atK (et A i); have hP : Receipt β φ f:=by
             let w(k:ℕ)(i):= jet (KPole A i) k (X i); let y(k:ℕ)(i):= jet (LPole A i) k (X i)
             have hv(k:ℕ)(hk:1≤k)(he:k<4) : Wax β φ (fun i=> -w (k+2) i-y k i) 0:= ((waitG h (appeals hs h hp (k:=k+2) (by omega) (by omega))).neg).sub (gloss hs h hp hk (by omega)) (carth h)
             have hz : Receipt β φ (fun i=> -w 2 i):=(appeals hs h hp (k:=2) (by decide) (by decide)).liftp (Eventually.of_forall fun i=> le_of_eq (norm_neg (w 2 i))); exact (hz.plus (truant h ((poleV A h).mul (hv 1 (by omega) (by omega))) (by norm_num)) (carth h)).plus (truant h (((poleV A h).pow 2 (carth h)).mul (hv 2 (by decide) (by decide))) (by norm_num)) (carth h) -- index fix w(k+2), k=1 and2
        let v':= pricePol hs h hp H; have hQ:Receipt β φ (fun i=>(V i-f i)+f i):=(truant h v' (by unfold Deb;norm_num)).plus hP (carth h); apply hQ.congr; filter_upwards with i; exact sub_add_cancel ..
end
end YM.OPE.Owl.HillZ
