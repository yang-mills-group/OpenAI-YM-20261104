import YM.OPE.Compatible.Draft.Bars
/-!
# Fare at horizontal stand
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Rill
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Score Libra Votive
open scoped Topology BigOperators ComplexConjugate Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {G:Gauge}{n c f:Side}
open Wilson RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Terp Pilot
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent GaussianScore Radial Flock Metric Glass
attribute [local instance] Gauge.frobInner
variable {i j:ℕ}{l b:ℝ}{B:Sponsor G}{Q:Seasons B} (S: StepData c f) (H: Even c.val)
local notation "μ"=> even_both S.ratio H
local notation "J!"=> Rill.rollB S H
variable (t:S.Choices)
def noiseC (x:Keys G J!):ℝ:= noiseTaylor S (coat H (put (lo_right S H G x))) (coat μ (put (lo_left S H G x))) t/4
def worldF (A:Alps B Q i l)(x:Keys G J!):ℝ:= mural μ A (lo_left S H G x)-mural μ A 0+noiseC S H t x
def worldW (b:ℝ)(A:Alps B Q i l)(x:Keys G J!):ℝ:= tintT μ A b (lo_left S H G x)*Real.exp (-b*noiseC S H t x)
variable (T:Plot (even_both S.ratio H))
variable (h:S.patch.Branches S.kernel G)
include h
lemma nPole : noiseC S H t (0:Keys G J!) = 0:=by
       unfold noiseC noiseTaylor; rw [map_zero, map_zero, put_zero,put_zero,coatOne,coatOne, show S.prediction (1:Config G f) t=1 from funext fun i=>Push.settled S h i t]; simp -- include
include h
lemma pulseZ {u:Tile G T.Free→Tile G (Limb H)}(F:Pilot.Hark u)(hx: u =ᶠ[𝓝 1] braveP S H T t):
   (∀ᶠ i:Keys G (StemX S H T).Free in 𝓝 0, noiseC S H t ((StemX S H T).rollX (F.crown (piBond S H T) i))=raysN S H (Pilot.prR (piBond S H T) G i)):=by
       let X:= StemX S H T; let p:=piBond S H T; 
       let L:=Pilot.prL p G; let E:=Pilot.prR p G; let W:=F.suite p; have hl:Tendsto L (𝓝 0) (𝓝 0):=by simpa only [L.map_zero] using! L.continuous.tendsto 0
       have hU:Tendsto (put (I:=T.Free) (G:=G)) (𝓝 0) (𝓝 1):=by simpa [put_zero] using! putC.tendsto (0:Keys G T.Free) -- check fn
       have hy:Tendsto (fun x=> T.cite (1:Tile G T.Stable) x) (𝓝 1) (𝓝 1):=by
           have hh:Continuous (fun p=> T.cite 1 (p:Tile G T.Free)):= T.citeC.comp (continuous_const.prodMk continuous_id)
           simpa only [T.dress1] using! hh.tendsto 1
       filter_upwards [(hy.comp (hU.comp hl)).eventually (echo_odd S H h t), (hU.comp hl).eventually hx, F.outlookZ p] with y he hz hr;
       obtain ⟨hq,hk⟩:=hr; change L (W.gradient y)= L y at hq; change put (E (W.gradient y))=put (E y)*u (put (L y)) at hk; let a:= put (L y); let x:=put (E y)
       change u a=braveP S H T t a at hz; rw [hz] at hk
       unfold noiseC noiseTaylor; rw [beamAt,beamRt]; change S.kernel.penalty* (∑ e,G.price (coat H (put (E (W.gradient y))) e * (S.prediction (coat μ (put (T.rollX (L (W.gradient y))))) t e)⁻¹))/4 = _
       rw [hq, T.rollPut,hk]; change S.prediction (coat μ (T.cite 1 a)) t=coat H (braveP S H T t a) at he; change _*(∑ e,G.price (coat H (x*_) e*(S.prediction (coat μ (T.cite 1 a)) t e)⁻¹))/4 = _; rw [he, cogs]
       simp only [Pi.mul_apply,mul_inv_cancel_right]; change _= S.kernel.penalty * ∑ i:Limb H,G.price (x i);ring
end YM.OPE.Cascade.Rill
