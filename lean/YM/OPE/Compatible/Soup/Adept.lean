import YM.OPE.Compatible.Soup.Vital
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
open Cinders Metric Set Zeph Jargon Crown PertExtension Flock
variable {N:ChartRatio G} {s c R:ℝ} (H:StackP N s c R)(hN:LocalRatio N)
variable (x:∀ i,Bid.Dir G (n i)) (g:ℂ→L[ℝ]ℝ) (P:Pad G)
section
open ScriptJ
variable (A)
lemma Art_port (j:I)(k:Libra.Char.Phase): Continuous (fun x=> (ArtY A P g j x).seq k.val):=by
        let f(v:Bid.Dir G (n j)):=(ArtY A P g j v).seq k.val; apply continuous_iff_continuousAt.mpr; intro x; let t:=‖x‖+1; let p:=DxT G (νsize A j) t; let c:=Jfair (RedG G (νsize A j) t) (TorC A P g j); have hc:1 ≤ t:= le_add_of_nonneg_left (norm_nonneg x); have hh: ‖x‖<t:=lt_add_one _
        have ht: Tendsto (fun y=>c*(p*‖y-x‖)) (𝓝 x) (𝓝 0):=by simpa using ((tendsto_norm_sub_self x).const_mul p|>.const_mul c)
        change Tendsto f (𝓝 x) _; rw [tendsto_iff_norm_sub_tendsto_zero]; refine squeeze_zero' (Eventually.of_forall fun i=>norm_nonneg _) ?_ ht; filter_upwards [(continuous_norm.tendsto x).eventually (ge_mem_nhds hh)] with i hi; exact AmpG A P g j i x hi hh.le hc k
end
section
variable {X:I→Type}[∀ i,MeasurableSpace (X i)]{μ:∀ i,Measure (X i)} [∀ i,IsProbabilityMeasure (μ i)] (V:∀ i,X i→ Bid.Dir G (n i))
variable (Y:PayR X)
local notation "Ch"=> Counters β
open ScriptJ
include h
set_option quotPrecheck false
local notation "W?"=> Grain μ φ (Counters β)
-- reusable later Φ.Tier
lemma FearCost (A:∀ x:I,HillZ (T:=T) S i r d τ (β x) (n x))(hy:Grain μ φ (Counters β) Y 0): Grain μ φ (Counters β) (fun i x=>Jfare (RedG G (νsize A i) (Y i x)) (TorC A P g i)) 0:=by
       let b:=carth h; have ht:= waitG h (νGrow A h); have hc(q:ℝ): W? (fun _ _=>q) 0:= Grain.const (RateLE.const q b); have hg:= (hc 1).add hy b; have hB:=Grain.const (μ:=μ) ht; have hp: W? (fun i _=>RoadK (νsize A i)) 0:= ((((hc 2).mul ((hc 4).mul hB)|>.mint (by norm_num)).add (hc 2) b).add (hc 1) b); have he(k:ℕ): Grain μ φ Ch (fun i x=> Mā G k (νsize A i) (Y i x)) 0:=(((hc _).mul (hp.pow b k)).mul (hg.pow b k)).mint (by simp); have hm: W? (fun i x=> RedG G (νsize A i) (Y i x)) 0:=(hc 1).add (((he 1).add (he 2) b).add (he 3) b) b; have hf:= Grain.const (μ:=μ) (waitG h (TorFunds A h P g)); have hE:= (hf.mul hm).mint (le_of_eq (zero_add _)); exact (hf.add hE b).add (hE.add ((hf.mul (hm.pow b 2)).mint (by norm_num)) b) b
lemma moneyArt (A:∀ x:I,HillZ (T:=T) S i r d τ (β x) (n x)) (he:Grain μ φ (Counters β) (fun i x=>‖V i x‖) 0)(hz:∀ᶠ i in φ, Measurable (V i)):Butte μ φ (Counters β) (fun i x=> ArtY A P g i (V i x)) :=by
       intro p; apply (FearCost h g P _ A he).of_le ?_ (Eventually.of_forall fun i=> Eventually.of_forall fun x=> le_trans (AmpF A P g i (V i x) le_rfl p) (Real.le_norm_self _)); filter_upwards [hz] with i hi; exact ((Art_port A g P i p).measurable.comp hi).aestronglyMeasurable -- P g order?
-- kernel jets
variable (hy:Grain μ φ (Counters β) (fun i x=>‖V i x‖) 0)(hz:∀ᶠ i in φ, Measurable (V i))(hp:∀ᶠ i in φ, ∀ x,SerT (V i x) (WorkB A i))
include hy hz hp hs
lemma πp (hk:0<k)(hI:k ≤ 5): W? (fun i x=> jet (KPole A i) k (V i x)) 0∧ W? (fun i x=> jet (LPole A i) k (V i x)) 0:=by
       obtain ⟨f,g,H⟩:=merit A h; let K(i:I)(x:X i):=‖V i x‖+1; let t:=carth h; have hv:W? K 0:=hy.add (Grain.const (RateLE.const 1 t)) t; have hq :∀ᶠ i in φ, ∀ x:X i, Past (KPole A i) (V i x) 5 (K i x) (f i)∧Past (LPole A i) (V i x) 5 (K i x) (g i):= hp.mono fun i hi x=>H.ν _ _ (hi x) _ (lt_add_one _)
       have h(i x):0≤K i x:=(norm_nonneg (V i x)).trans (lt_add_one _).le
       have hB(Q: ∀ i,Bid.Dir G (n i)→ℝ)(c:I→ℝ)(hc:∀ i,0 ≤ c i)(he:Wax β φ c 0)(hC:∀ i, ContDiffAt ℝ ω (Q i) 0)(hh:∀ᶠ i in φ, ∀ x:X i,Past (Q i) (V i x) 5 (K i x) (c i)): W? (fun i x=> jet (Q i) k (V i x)) 0:=by
             refine Grain.of_le (((hv.pow t k).mul (Grain.const (μ:=μ) he)).mint (by norm_num)) ?_ ?_; · filter_upwards [hz] with i hi; exact (((Raucous.Host.jetSun (Q i) k).measurable).comp hi).aestronglyMeasurable
             exact hh.mono fun i hi=>Eventually.of_forall fun x=> (Pat_charge (hC _) (hi x) hk hI (h i x) (hc _)).trans (Real.le_norm_self _)
       exact ⟨hB _ f (fun i=>(H.fare i).1) (waitG (by assumption) H.meat) (fun i=>(Variance.DuneAt _ hs).sm) (hq.mono fun i hi v=>(hi v).1), hB _ g (fun i=>(H.fare i).2) H.lite (fun i=>(Variance.DuneAt _ hs).sg) (hq.mono fun i hi v=>(hi v).2)⟩ -- h shadow
end
end YM.OPE.Owl.HillZ
