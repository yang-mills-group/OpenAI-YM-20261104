import YM.OPE.Compatible.Tony.Cool
/-!
# Costume reconstruction Economy. Work at the sequence with b=Ω taller
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant
open Function Filter MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset Tensor
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
attribute [local instance] Gauge.frobInner
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Variance StepsL Claw Prom Ibis Merchant.SiteL Flume.Page StepsL Wool
variable {i j d k m r l b:ℕ}{n:Side}
namespace Sleeve
variable {I:Type}{A:I→ Side}{a c:ℝ} {φ:Filter I}{Z:I→ℝ} {b:I→ℕ}{p:GlyphQ G A}(h: ∀ i,Board (A i) (b i+1)) (ht:Tendsto Z φ atTop) (hx:RateLE φ Z (fun i=>(b i:ℝ)) 0)
include ht hx
lemma lance (p: GlyphQ G A)(hc:∀ᶠ i in φ,ContDiffAt ℝ ω (p i) 0)(hp:Rated φ Z a p)(k:ℕ): Photos φ Z a (Article (G:=G) (A:=A) (fun i=>p i ∘ Λace G (h i)) k):=by
       obtain ⟨C,hC,H⟩:=holds_P G k; let f(i:I)(k):= ‖iteratedFDeriv ℝ k (p i ∘ (tellerT G (A i)).toContinuousLinearMap) 0‖; let P(i):=∑ j∈range (k+1), f i j; let F(i):=C*(1+↑(b i+1))^(2*k); have hF: RateLE φ Z F 0:=by unfold F; push_cast; exact ((RateLE.const _ ht).mul (((RateLE.const _ ht).add (hx.add (RateLE.const _ ht) ht) ht).pow (2*k) ht)).mono (by norm_num)
       exact ⟨_,(hF.mul (RateLE.sum (S:=range (k+1)) (f:=fun j i=>f i j) ht fun j _=>hp.beam j)).mono (by norm_num),hc.mono fun i hi x hx=> H _ _ (h i) _ (P i) hi (fun j hj=>single_le_sum (s:=range (k+1)) (f:=f i) (fun _ _=>norm_nonneg _) (mem_range.mpr (by omega))) x hx⟩ -- braces record
noncomputable def moldQ (p:GlyphQ G A)(k:I→ℕ):GlyphQ G A:=fun i=>p i- p i ∘ sillM G (A i) (k i + 1)
lemma kernPhoto (hc:∀ᶠ i in φ,ContDiffAt ℝ ω (p i) 0)(hp:Rated φ Z a (moldQ p b))(k:ℕ) : Photos φ Z a (Article p k-Article (G:=G) (A:=A) (fun i=>p i ∘ Λace G (h i)) k):=by
       let q:=moldQ p b; let m(i):= Λace G (h i); have hxq(i): q i - (q i ∘ m i)=p i-p i ∘ m i:=by funext y; unfold q m moldQ; simp only[Function.comp_apply,Pi.sub_apply,sillSave]; abel
       have hR:∀ᶠ i in φ, ContDiffAt ℝ ω (q i) 0:=by
               refine hc.mono fun i hi=>?_ ; let K:=sillM G (A i) (b i+1); exact hi.sub ((K.map_zero.symm ▸ hi:ContDiffAt ℝ ω (p i) _).comp (f:=K) _ K.contDiff.contDiffAt)
       let P:=lance h ht hx q hR hp k; apply ((Rates.toy hp hR ht).sink P ht).cone; filter_upwards [hR,hc] with i hq hi
       have he:m i 0=0:= eΛ ..; let v:=haloStage (h i) G; have hk : ContDiffAt ℝ ω (q i ∘ m i) 0:=(he.symm ▸ hq:ContDiffAt ℝ ω _ _).comp (f:=m i) _ v; have hm : ContDiffAt ℝ ω (p i ∘ m i) 0:=(he.symm ▸ hi:ContDiffAt ℝ ω _ _).comp (f:=m i) _ v
       have hZ{P Q:Bid.Dir G (A i)→ℝ}(he: ContDiffAt ℝ ω P 0)(hp:ContDiffAt ℝ ω Q 0): jet (P-Q) k=jet P k - jet Q k:=by funext x; unfold jet; rw[iteratedFDeriv_sub_apply (he.of_le le_top) (hp.of_le le_top), _root_.sub_apply,mul_sub]; rfl
       change jet (q i) k-jet (q i ∘ m i) k=jet (p i) k-jet (p i ∘ m i) k; rw [←hZ hq hk, hxq, hZ hi hm]
omit ht hx
structure Ears (b:I→ℕ)(φ:Filter I)(Z:I→ℝ):Prop where
       top :∀ (a c:ℝ),0 < c→∀ᶠ i in φ,a*Z i ≤ c*(b i)
lemma Ears.sense (p:Ears b φ Z) (h:0<c): RateLE φ Z (fun i=> Real.exp (-c*b i)) a:=by intro r hr; filter_upwards [p.top (-r) c h] with i hi; rw[Real.norm_of_nonneg (Real.exp_nonneg _)]; apply Real.exp_monotone; linarith
-- analytic symbol payments
variable {e:RootEdge}
structure Warm (p:GlyphQ G A)(φ:Filter I)(Z:I→ℝ) :Prop where
       rays :∀ k:ℕ,∃ a:ℝ,0 < a ∧∃ f:I→ℝ,RateLE φ Z f 0∧∀ᶠ i in φ,∃ q: Script (Shade G) (k+1), ContDiffAt ℝ ω (p i) 0 ∧ Felt q a (f i) ∧ Voice q (spool G (A i)).toContinuousLinearMap (p i)
include ht
lemma Warm.sheet (hv: Warm p φ Z)(q:G.ColorIndex): Rated φ Z 0 (A:=A) (G:=G) (fun i=> tfan e q (A i) (p i)):=by
       constructor; intro k; obtain ⟨c,hc,f,hf,H⟩:=hv.rays k; obtain ⟨s,hs,F⟩:=Tenter G c hc e k; apply RateLE.of_norm_le (((RateLE.const s ht).mul hf).mono (by norm_num: (0:ℝ)+0 ≤ 0)); filter_upwards [H] with i ⟨x,hx,hP,hQ⟩; rw [Real.norm_of_nonneg (norm_nonneg _)]; exact (F (A i) q _ x _ hx hP hQ 0).1
lemma Warm.hears (hp:Ears b φ Z)(hv:Warm p φ Z)(q:G.ColorIndex):Rated φ Z a (moldQ (G:=G) (A:=A) (fun i=>tfan e q (A i) (p i)) b):=by
       constructor; intro k; obtain ⟨c,hc,f,hf,H⟩:=hv.rays k; obtain ⟨s,hs,F⟩:=Tenter G c hc e k; apply RateLE.of_norm_le ((((RateLE.const s ht).mul hf).mul (hp.sense (a:=a) (show 0<c/4 from by positivity))).mono (by simp)); filter_upwards [H] with i ⟨x,hx,hP,hQ⟩; rw [Real.norm_of_nonneg (norm_nonneg _)]; exact (F (A i) q _ x (f i) hx hP hQ (b i)).2
end Sleeve
end YM.OPE.Merchant
