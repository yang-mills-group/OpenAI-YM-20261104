import YM.OPE.Compatible.Fiord.EnD
import YM.OPE.Compatible.Fiord.Rein
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
section
variable {J:I→Type}[∀ i, MeasurableSpace (J i)]{μ:∀ i,Measure (J i)}[∀ i, IsProbabilityMeasure (μ i)]
variable (X:(i:I)→J i→Bid.Dir G (n i))(Y:(i:I)→J i→ Merchant.Chamber G r)
open Merchant.Sleeve.Scaffold
local notation "qK"=> KPole A
local notation "qL"=> LPole A
local notation "ΓZ"=> Counters β
local notation "V!"=> Punched A U
local notation "Q!"=> SkinQ n ΓZ μ φ
local notation "A!"=> SkyQ r ΓZ μ φ
section
abbrev C_Ra (J:I→Type)(i:I) := J i × Merchant.Chamber G r
noncomputable def Vmix (D:I→Law (Merchant.Chamber G r))(μ:(i:I)→Measure (J i)):= ProductS μ (ShoreP D)
noncomputable abbrev RentRa (D:I→Law (Merchant.Chamber G r))(μ:(i:I)→Measure (J i)):=ProductS μ (ShoreP D)
noncomputable def Bx (i:I) (p: C_Ra J (r:=r) (G:=G) i):=X i p.1
noncomputable def By (G:Gauge)(J:I→Type)(r:ℕ)(i:I) (p:C_Ra J (r:=r) (G:=G) i):=p.2
local notation "X!"=> Bx (r:=r) X
local notation "Y!"=> By G J r
local notation "μ_p"=> RentRa D μ
variable (hp:SkinQ n (Counters β) μ φ X)
include hp
omit [∀ i, IsProbabilityMeasure (μ i)] in lemma Sender: SkinQ n ΓZ (μ_p) φ (Bx (r:=r) X):=⟨hp.meat.mono fun _ hi=> hi.comp measurable_fst,hp.Φ.loco⟩ -- warning μ
omit hp
variable (μ)
include h hD
lemma TailZ : SkyQ r ΓZ (RentRa D μ) φ 0 (By G J r):=⟨Eventually.of_forall fun _=>measurable_snd, (D_Grain (D:=D) hD h).Pagain⟩ -- μ binder
include hN hs hp
variable {μ}
local notation "Z'"=> Counters β
local notation "xT"=> XTarg A X
noncomputable abbrev Ωwt (P:ChartRatio G) := FogO A U D (Bx (r:=r) X) (By G J r) P
noncomputable def peg (N:ChartRatio G)(j:I)(z:J j):= Eday A U D N j (X j z)
omit [∀ i, IsProbabilityMeasure (μ i)][∀ i, MeasurableSpace (J i)] hp hs hD hN h in
private lemma pegα (p:ChartRatio G)(j:Fin 3)(i:I)(z:J i):run_H (peg A U D X p) j.val i z=∫ y, run_H (Ωwt A U D X p) j.val i (z,y) ∂ShoreP D i:=by fin_cases j<;>exact (has_p ..).symm
omit hN
lemma lev (P:ChartRatio G) : Butte (RentRa D μ) φ ΓZ (Ωwt A U D X P):= recept A U D hs h hD _ _ (Sender D X hp) (TailZ A U D h hD μ) P -- arg U? Sender?
lemma Emb (P:ChartRatio G): Butte μ φ (Counters β) (peg A U D X P):=by
       have ht:=lev A U D hs h hD X hp P; intro i; apply Grain.shift ((ht i).ault _); filter_upwards with j; exact funext fun _=> (pegα ..).symm
lemma levE (hc:c≤0)(P:ChartRatio G): Pine (RentRa D μ) φ ΓZ (Ωwt A U D X P-Ωwt A U D (XTarg A X) P) c:=by
       exact Resp A U D hs h hD (X!) (Y!) (Sender D X hp) (TailZ A U D h hD μ) P hc
omit h hs hD hp [∀ i, IsProbabilityMeasure (μ i)][∀ i,MeasurableSpace (J i)] in lemma pegComp (j:Fin 3)(X Y:Hang J) : run_H (X-Y) j.val=run_H X j.val-run_H Y j.val:=by fin_cases j<;>rfl -- includes unused
lemma Camp (hc:c≤0)(P:ChartRatio G): Pine μ φ ΓZ (peg A U D X P-peg A U D (XTarg A X) P) c:=by
       let Q:= Ωwt A U D X P; let R:=Ωwt A U D (XTarg A X) P; let M:=peg A U D X P; let N:=peg A U D (XTarg A X) P; let V:= RentRa D μ; have he:= lev A U D hs h hD (XTarg A X) (hp.Rise X) P -- incorrect
       have hP:= lev A U D hs h hD X hp P; have hU:= levE A U D hs h hD X hp hc P; intro i; let v:=i.val; let x:=run_H Q v; let y:=run_H R v; have ht := (hU i).ault (run_H (Q-R) v); rw[pegComp i Q R] at ht; rw[pegComp i M N]; -- `pegComp i where implicit h` simplify
       -- integrate equality ae, not pointwise. Need Grain.congr_ae. use Gr.of_le with Emb for target measurable.
       apply ht.of_le (((Emb A U D hs h hD X hp P i).integral.1.and ((Emb A U D hs h hD (XTarg A X) (hp.Rise X) P i).integral.1)).mono fun j hj=> (hj.1.sub hj.2).aestronglyMeasurable); filter_upwards[(hP i).integral.1,(he i).integral.1] with j hj hk; filter_upwards [hj.prod_right_ae,hk.prod_right_ae] with z hz hL; change ‖run_H _ v j z-run_H _ v j z‖ ≤ ‖∫ y', (x j (z,y')-y j (z,y')) ∂ShoreP D j‖; rw [integral_sub hz hL,pegα A U D X P i,pegα A U D (XTarg A X) P i]
end
end
end YM.OPE.Owl.HillZ
