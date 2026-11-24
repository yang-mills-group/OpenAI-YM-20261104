import YM.OPE.Compatible.Anchor.Carm
/-! # Sensor readiness. Registration. Uses ∑ r-1 tours. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset Labels
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Work.F08
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver FreeResolvent WithLp
open Drift Char Silt Silt.Float Module Page Planned.PrimaryIntegral295.Carrier
variable {i j d k m r l:ℕ}{Z I J M E F:Type}{n:Side}
local notation "Q!"=>CoverConfig G
variable {α:Fin r→ℕ}(A:SpiceD G α)(e:RootEdge)
local notation "θ"=> 𝓝[>] (0:ℝ)
local notation "B"=> Phone G
lemma Moment_b (s:Finset RootEdge)(h:∀ v w:Q!,EqOn v w s→Cloudy A e v=Cloudy A e w):
   ∃ f:Libra.Keys G (↥s)→G.Color, ContDiff ℝ ω f ∧ ∀ z:fieldX (Shade G), f (fronds (fun i:↥s=>i.val) z)=Cloudy A e (lotU z):=by
      let q(x:Libra.Keys G (↥s))(i:RootEdge):= if hi:i∈s then G.lieExp (x ⟨i,hi⟩) else 1; refine ⟨fun x=>Cloudy A e (q x), Coat A e|>.sense (Libra.Keys G (↥s)) q (fun i=> ?_),fun z=> h _ _ ?_⟩
      · unfold q; split; next h=> exact G.exp_jet.comp (contDiff_apply ..)
        exact contDiff_const
      intro i hi; unfold q; rw [dif_pos (show i∈s from hi)]; rfl
lemma signalInk (v:ℝ→G.Color)(f:G.Color)(x:G.ColorIndex)(h:Tendsto (fun i:ℝ=>(i^r)⁻¹ • v i) θ (𝓝 f)) : Tendsto (fun i:ℝ=> (i^r)⁻¹ • (Phone G).coord x (v i)) θ (𝓝 ((Phone G).coord x f)):=by
     simp_rw [← map_smul]; exact ((Phone G).coord x).continuous_of_finiteDimensional.continuousAt.tendsto.comp h
lemma tailAt (Z: fieldX (Shade G))(t:ℝ)(s:Finset RootEdge) : fronds (fun i:↥s=>i.val) (t • Z)=t • fronds (fun i:↥s=>i.val) Z:=rfl
lemma dipped (s:Finset RootEdge)(u: Site n)(x:Bid.Dir G n): dip (fun i:↥s=>i.val) n u x=fronds (fun i:↥s=>i.val) (upl u (spool G n x)):=by
    ext1 j; ext1 i;rfl
lemma tradeP (hp:Abalo A):∃ (s:Finset RootEdge)(f:Libra.Keys G s →G.Color),
    BudY e false r (fun i:↥s=>i.val) f∧∀ v:fieldX (Shade G),∀ i:G.ColorIndex, jet ((Phone G).coord i∘ f) r (fronds (fun i:↥s=>i.val) v)=(ClearW A v) i:=by
      obtain ⟨s,h⟩:= (Coat A e).see; obtain ⟨f,hf,H⟩:=Moment_b A e s h; let U:=fun i:↥s=>i.val; let Y (i: G.ColorIndex):= (Phone G).coord i ∘ f; have he(i):ContDiff ℝ ω (Y i):=((Phone G).coord i).toContinuousLinearMap.contDiff.comp hf
      have ht(i:G.ColorIndex)(k:ℕ)(v:fieldX (Shade G))(hv:k≤r): jet (Y i) k (fronds U v)= if k=r then (Phone G).coord i (ClearW A v) else 0:=by
           let p:= fronds U v; rw [show jet _ _ _=_ from (show jet (Y i) k p = WardBin.leading k (fun t:ℝ=>Y i (t • p)) from (WardBin.leading_tensor _ _ ((he i).of_le le_top|>.contDiffAt)).symm)]; have hS:ContDiffAt ℝ (k:WithTop ℕ∞) (fun t:ℝ=>Y i (t • p)) 0:= ((he i).of_le le_top|>.contDiffAt).comp _ (contDiffAt_id.smul contDiffAt_const); have hm :Tendsto (fun t:ℝ=>(t^r)⁻¹ • Y i (t • p)) θ (𝓝 ((Phone G).coord i (ClearW A v))) :=by
                 unfold p Y U; simp_rw [Function.comp_apply, ← tailAt,H]; exact signalInk _ _ _ (forTer A e v)
           split; next h=> subst k; exact WardBin.leading_of_lim hS _ hm
           next h=> exact WardBin.leading_of_lim hS _ (WardBin.falls (lt_of_le_of_ne hv h) hm)
      have hx(n:Side)(x:Site n)(v:Bid.Dir G n): f (dip U n x v)=Cloudy A e (expandAt x (represent v)):=by rw [show dip U _ x v= _ from dipped s x v,H,Grid.plank]
      refine ⟨s,f,⟨hf.contDiffAt,fun n x=>?_,fun n x=>?_⟩,fun v i=> by rw [show (jet _ _ _)= _ from (ht i r v le_rfl),if_pos rfl, phone_eq]⟩
      · let V:= dip U n x (G:=G); refine ⟨(hf.comp V.contDiff).contDiffAt,fun i v k hk=>?_⟩; change jet (Y i∘V) k v=0; rw [ show jet (Y i ∘ V) k _=jet (Y i) k (V v) from congr_arg JetS.s (congr_fun (moldC V _ (he i|>.contDiffAt) k) v)]; erw [show V v=fronds U _ from dipped s x v, ht i k _ hk.le, if_neg (ne_of_lt hk)] -- tail casts
      refine ⟨fun u y k hk=>?_⟩; let t:= k ∘ fun i:Cover=>wrap n i+x; have h: G.adjoint (t e.1) (Cloudy A e (expandAt x (represent u)))= Cloudy A e (expandAt x (represent y)):=by rw [← show Lattice.gauge k (represent u)=_ from (Mar_ord ..).1 hk,expandAt_gauge]; exact (clocksAw A e hp t _).symm
      change f (dip U _ x y)=G.adjoint _ (f (dip U _ x u)); rw [hx,hx,← h]; apply congr_arg (fun t=>G.adjoint t _); change k (wrap n e.1+x)= k (x+wrap _ e.1); rw[add_comm]
end YM.OPE.Variance
