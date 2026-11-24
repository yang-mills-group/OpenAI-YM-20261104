import YM.OPE.Compatible.Fiord.Paul
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
open StepsL Silt.Phere
lemma ΦHint (j:I): 4*νsize A j≤ WorkB A j:=by
       apply le_trans (?_ : 4*νsize A j ≤ Xbt i S (A j)); swap; · unfold Xbt PinB; let k:= d+6+6; let b:=νsize A j; have hx:1 ≤ k:=(by omega); change 4*b≤1+(k+2)*((2*k+3)*(1+k*(4*(4*b)))); have hz : 4*b ≤ 1+k*(4*(4*b)):=(by nlinarith); exact hz.trans ((le_mul_of_one_le_left (Nat.zero_le _) (by omega: 1 ≤ 2*k+3)).trans ((le_mul_of_one_le_left (Nat.zero_le _) (by omega:1 ≤ k+2)).trans (Nat.le_add_left ..)))
       unfold WorkB Mnd Mender; omega
include U
lemma eraSeal (j:I): Board (n j) (WorkB A j):=(U.top.room j).board
lemma EmBound (j:I)(x:Bid.Dir G (n j)): ArtY A P g j (Cpit G n (Mnd i S A) j x)=ArtY A P g j x:=by
       let W:=WorkB A j; let S:=SillV (n j) G W; let f:=S x; let v:=charW 0 f; let p:=charW 0 x; let k:=νsize A j; have he : InLine (4*k) v=InLine (4*k) p:=by
          funext e; let y:= (Moor e.val (n j)); have hh:S x (arkE y)=x (arkE y):=by unfold S; rw [viewζ,if_pos (guardM (eraSeal A U j) e.val ((cross_def e.val).mpr (show _ from voles (ΦHint A j) e)))] -- opens ?
          change f ((0:Site (n j))+wrap (n j) e.val.1, (arkE y).2)=x ((0:Site (n j))+wrap (n j) e.val.1,(arkE y).2); rw[zero_add]; exact hh -- ext
       have hz:= Crown.vents _ _ he; unfold ArtY Incl Autum; congr 1
section
omit U
variable {J:I→Type}[∀ i, MeasurableSpace (J i)]{μ:∀ i,Measure (J i)}[∀ i, IsProbabilityMeasure (μ i)]
variable (x:PayR J)(hp:Grain μ φ (Counters β) x 0)
include hp h
local notation "Φ"=> Grain μ φ (Counters β)
lemma ΛPrice : Φ (fun i t=> Jfair (RedG G (νsize A i) (x i t)) (TorC A P g i)*DxT G (νsize A i) (x i t)) 0 :=by
       let L:=carth h; have hv:= waitG h (νGrow A h); have he:= waitG h (TorFunds A h P g); let f(r:ℝ): Φ (fun _ _=>r) 0:= Grain.const (RateLE.const _ L); have ht': Φ (fun i _=> RoadK (νsize A i)) 0:= ((((f 2).mul ((f 4).mul (Grain.const (μ:=μ) hv))|>.mint (by norm_num)).add (f 2) L).add (f 1) L)
       let m(y:PayR J)(k:ℕ)(h:Grain μ φ (Counters β) y 0): Φ (fun i t=> Mā G k (νsize A i) (y i t)) 0:= (((f _).mul (ht'.pow L _)).mul (((f 1).add h L).pow L _)).mint (by simp)
       have hc: Φ (fun i t=> RedG G (νsize A i) (x i t)) 0:= (f 1).add (((m x 1 hp).add (m x 2 hp) L).add (m x 3 hp) L) L; let a:=Grain.const (μ:=μ) he; let b(y z:PayR J)(h:Φ y 0)(hp:Φ z 0): Φ (fun i x=>y i x*z i x) 0 :=(h.mul hp).mint (by norm_num); let Y:= fun i t=>3*x i t; let j(k:ℕ):Φ (fun i t=>Glee k*Mā G k (νsize A i) (Y i t)) 0:= b _ _ (f _) (m Y k (b _ x (f 3) hp)); have hA: Φ (fun i t=> DxT G (νsize A i) (x i t)) 0:= ((j 1).add (j 2) L).add (j 3) L; let v:= b _ _ a (hc.add (f 1) L); exact b _ _ ((a.add v L).add (v.add (b _ _ a ((hc.pow L 2).add (b _ _ (f 2) hc) L)) L) L) hA
end
end YM.OPE.Owl.HillZ
